import NonUniqueEuler.Verify.Comp.Contour

/-!
# Part 2 algorithms: the certification of one cell (`certifyCell`) and adaptive halving

Checker design decision D7 (see `FORMALIZATION_NOTES.md`). Manuscript: §A.6, "certification" and
"run" (`A_verification.tex:559-608`), Proposition A.4 (`prop:winding`).
Reference: `euler-ring-certificate/src/ringcert/winding.py` (`certify_cell`,
`certify_cell_adaptive`), a line-by-line port.

## Soundness without verifying the search

The search (rounds, bisection, the segment limit, halving) needs no proof. What it returns
carries its own evidence:
* an accepted segment is an `AccSeg cx`: a pair `(s, ty)` with the proof
  `segAccept cx s = some ty`, i.e. `evansEncl` on `segBox s` returned a box that `classify`
  accepted with type `ty` (`tryAccept` is the only producer);
* the indicators are computed by `indAt cx t`, a plain function of the point parameter `t`;
* `finishCell` re-checks, in exact rational arithmetic, that the accepted segments form a
  closed chain `0 = t₀ < … < t_n = 4` with every segment inside one edge (`chainOK`; Python
  only asserts consecutiveness), and that every junction indicator is decided (`allDecided`);
  its result is then the junction sum `junctionSumC`, which is the sum `junctionSum` of
  `Defs/Verify/Winding.lean` (same terms, `cycPrev`/`cycNext` as there);
* a certified sub-cell of `certifyAdaptive` is a `{r // (cert r.lo r.hi).winding = some r.winding}`.

So `certifyCell_sound` (`P/Verify/Sound/CertifyCell.lean`) only reads `finishCell`, never
`runRounds`.

## Python → Lean

| `winding.py` (`certify_cell`) | Lean |
|---|---|
| `base = rect_points(...)`, `segs = zip(...)` | `baseSegs` (`Comp/Contour.lean`) |
| `Gb = G_ball(cell)` | `CellCtx.Gb` |
| `B = ev.evans(seg_box(p, q), Gb, m, grid)`; `t = classify(B)`; `accepted[(p,q)] = t` | `segAccept`, `tryAccept` |
| one pass `for (p, q) in pending` (with `nevals += 1`, the test `len(segs) > max_seg`, the split at the midpoint) | `oneRound` |
| `while pending and it < max_iter`; `if pending: return None` | `runRounds` |
| `assert all(segs[i][1] == segs[(i+1) % n][0] …)` | `chainOK` (fail closed; also `t0 < t1` and one edge per segment) |
| junctions `(tp_prev == 2) != (tp == 2)` | `isJunction` |
| indicator: `B = evans(pt_box(p))`, `1` if `Im B < 0`, `0` if `Im B > 0`, else `None` | `indAt` |
| `w`, `amb` (sum over the type-N segments) | `junctionSumC`, `ambCount` |
| `winding = w if amb == 0 else None` | `finishCell` (`amb = 0` and `allDecided`; equivalent, see below) |
| the record `nseg, ambiguous, nN, nind, nevals` | `CellOut` |
| `certify_cell_adaptive` | `certifyAdaptive` |

`amb = 0` holds iff every junction indicator is decided (each junction is the end point of
exactly one type-N segment adjacent to it, cyclically). `finishCell` tests both conditions,
which is equivalent to Python's test and gives the soundness proof the second form directly.

Order of evaluation: Python halves cells breadth first (level by level); `certifyAdaptive`
recurses depth first (left half, then right half). The certified sub-cells, the failed
sub-cells and the number of evaluations are the same; the results come out sorted by `G`
(Python sorts them afterwards).

Core only. Every recursion is structural.
-/

namespace NonUniqueEuler.Verify

/-- The fixed data of one certification: precision, grid, `ℓ`, rectangle and `G`-ball. -/
structure CellCtx where
  p : Nat
  gr : Grid
  ℓ : Nat
  R : Rect
  Gb : Ball

/-- `classify(evans(seg_box(s), Gb, m, grid))` (`none`: rejected, including failure of
`evans`). -/
def segAccept (cx : CellCtx) (s : Seg) : Option SegTy :=
  (evansEncl cx.p cx.gr cx.ℓ (segBox cx.p cx.R s) cx.Gb).bind classify

/-- An accepted segment with its type, carrying the evidence of its acceptance. -/
def AccSeg (cx : CellCtx) : Type := {x : Seg × SegTy // segAccept cx x.1 = some x.2}

/-- Try to accept a segment (one Evans evaluation). -/
def tryAccept (cx : CellCtx) (s : Seg) : Option (AccSeg cx) :=
  match h : segAccept cx s with
  | some ty => some ⟨(s, ty), h⟩
  | none => none

/-- A slot of the contour, in contour order: an accepted segment, or a segment still pending. -/
inductive Slot (cx : CellCtx) where
  | done (a : AccSeg cx)
  | todo (s : Seg)

/-- One round over the slots in contour order (the `for (p, q) in pending` loop): every pending
segment is tried; a rejected one is cut at its midpoint if the current number of segments
`cnt` is at most `maxSeg`, otherwise the certification fails (`none`). Returns the new slots,
the number of segments and the number of Evans evaluations. -/
def oneRound (cx : CellCtx) (maxSeg : Nat) :
    List (Slot cx) → Nat → Nat → Option (List (Slot cx)) × Nat × Nat
  | [], cnt, nev => (some [], cnt, nev)
  | .done a :: rest, cnt, nev =>
    let r := oneRound cx maxSeg rest cnt nev
    (r.1.map (Slot.done a :: ·), r.2)
  | .todo s :: rest, cnt, nev =>
    match tryAccept cx s with
    | some a =>
      let r := oneRound cx maxSeg rest cnt (nev + 1)
      (r.1.map (Slot.done a :: ·), r.2)
    | none =>
      if maxSeg < cnt then (none, cnt, nev + 1)
      else
        let m := s.mid
        let r := oneRound cx maxSeg rest (cnt + 1) (nev + 1)
        (r.1.map (fun l => Slot.todo ⟨s.t0, m⟩ :: Slot.todo ⟨m, s.t1⟩ :: l), r.2)

/-- All slots are accepted: the accepted segments in contour order. -/
def allDone (cx : CellCtx) : List (Slot cx) → Option (List (AccSeg cx))
  | [] => some []
  | .done a :: rest => (allDone cx rest).map (a :: ·)
  | .todo _ :: _ => none

/-- At most `fuel` rounds (`while pending and it < max_iter`; `if pending: return None`).
Returns the accepted segments (or `none`: a dead cell) and the number of evaluations. -/
def runRounds (cx : CellCtx) (maxSeg : Nat) :
    Nat → List (Slot cx) → Nat → Nat → Option (List (AccSeg cx)) × Nat
  | 0, slots, _, nev => (allDone cx slots, nev)
  | fuel + 1, slots, cnt, nev =>
    match allDone cx slots with
    | some segs => (some segs, nev)
    | none =>
      match oneRound cx maxSeg slots cnt nev with
      | (none, _, nev') => (none, nev')
      | (some slots', cnt', nev') => runRounds cx maxSeg fuel slots' cnt' nev'

/-- The cyclic successor of a segment index among `n` (as in `Defs/Verify/Winding.lean`). -/
def cycNext (n i : Nat) : Nat := if i + 1 = n then 0 else i + 1

/-- The cyclic predecessor of a segment index among `n` (as in `Defs/Verify/Winding.lean`). -/
def cycPrev (n i : Nat) : Nat := if i = 0 then n - 1 else i - 1

/-- The start point of segment `i` is a junction: exactly one of the segments `cycPrev n i`, `i`
is of type N. -/
def isJunction (n : Nat) (κ : Nat → SegTy) (i : Nat) : Bool :=
  (κ (cycPrev n i)).isN != (κ i).isN

/-- The term of segment `i` in the indicator sum (as `junctionSum` of `Defs/Verify/Winding.lean`):
for a type-N segment, `+x(i+1)` if its end point is a junction and `-x(i)` if its start point is
one. -/
def junctionTerm (n : Nat) (κ : Nat → SegTy) (x : Nat → Int) (i : Nat) : Int :=
  if (κ i).isN then
    (if (κ (cycNext n i)).isN then 0 else x (cycNext n i)) -
      (if (κ (cycPrev n i)).isN then 0 else x i)
  else 0

/-- The indicator sum `Σ_{i<n} junctionTerm n κ x i` (Python's `w`). -/
def junctionSumC (n : Nat) (κ : Nat → SegTy) (x : Nat → Int) : Int :=
  (List.range n).foldl (fun acc i => acc + junctionTerm n κ x i) 0

/-- Python's `amb`: the number of junction end points of type-N segments whose indicator is
undecided. -/
def ambCount (n : Nat) (κ : Nat → SegTy) (ind : Nat → Option Int) : Nat :=
  (List.range n).foldl (fun acc i =>
    acc + (if (κ i).isN then
      (if !(κ (cycNext n i)).isN && (ind (cycNext n i)).isNone then 1 else 0) +
        (if !(κ (cycPrev n i)).isN && (ind i).isNone then 1 else 0)
      else 0)) 0

/-- The indicator `1[Im E(p) < 0]` at the point with parameter `t`, from the point box:
`some 1` if the box certainly has negative imaginary part, `some 0` if positive, `none`
(undecided) otherwise or if `evans` fails. -/
def indAt (cx : CellCtx) (t : Rat) : Option Int :=
  match evansEncl cx.p cx.gr cx.ℓ (ptBox cx.p cx.R t) cx.Gb with
  | some B =>
    if B.isFinite && B.im.negC then some 1
    else if B.isFinite && B.im.posC then some 0
    else none
  | none => none

/-- `[t0, t1]` lies in one edge `[e, e+1]`, `e = ⌊t0⌋`. -/
def edgeOK (s : Seg) : Bool :=
  let e : Int := Rat.floor s.t0
  decide ((e : Rat) ≤ s.t0) && decide (s.t1 ≤ (e : Rat) + 1)

/-- The segments form a closed chain of the contour: `n > 0`, `t0` of the first is `0`, `t1` of
the last is `4`, consecutive segments share their end points, `t0 < t1`, and each segment lies
in one edge. -/
def chainOK (ts : Array Seg) : Bool :=
  let n := ts.size
  let t := fun i => ts.getD i default
  decide (0 < n) && decide ((t 0).t0 = 0) && decide ((t (n - 1)).t1 = 4) &&
    (List.range n).all fun i =>
      decide ((t i).t0 < (t i).t1) && edgeOK (t i) &&
        (decide (i + 1 = n) || decide ((t i).t1 = (t (i + 1)).t0))

/-- The record of one certification (Python's `record` and `nevals`). `winding = none` means
that the certification did not succeed (a dead cell, `dead = true`, or an ambiguous one). -/
structure CellOut where
  winding : Option Int
  nseg : Nat
  nN : Nat
  nind : Nat
  ambiguous : Nat
  nevals : Nat
  dead : Bool
deriving Repr, Inhabited

/-- A dead cell (the subdivision did not converge). -/
def CellOut.deadOut (nev : Nat) : CellOut :=
  { winding := none, nseg := 0, nN := 0, nind := 0, ambiguous := 0, nevals := nev, dead := true }

/-- The parameter intervals of the accepted segments, in contour order. -/
def segTs {cx : CellCtx} (segs : List (AccSeg cx)) : Array Seg := (segs.map fun a => a.1.1).toArray

/-- The types of the accepted segments, in contour order. -/
def segKs {cx : CellCtx} (segs : List (AccSeg cx)) : Array SegTy :=
  (segs.map fun a => a.1.2).toArray

/-- The type of segment `i` (`P` out of range). -/
def kindAt (ks : Array SegTy) (i : Nat) : SegTy := ks.getD i SegTy.P

/-- The indicators: `indAt` at the start point of every junction segment, `some 0` (unused)
elsewhere. -/
def cellInds (cx : CellCtx) (ts : Array Seg) (κ : Nat → SegTy) : Array (Option Int) :=
  Array.ofFn (n := ts.size) fun i =>
    if isJunction ts.size κ i.val then indAt cx (ts.getD i.val default).t0 else some 0

/-- The value of indicator `i` (`0` if undecided or out of range). -/
def indVal (inds : Array (Option Int)) (i : Nat) : Int := (inds.getD i none).getD 0

/-- Every junction indicator is decided. -/
def allDecided (n : Nat) (κ : Nat → SegTy) (ind : Nat → Option Int) : Bool :=
  (List.range n).all fun i => !isJunction n κ i || (ind i).isSome

/-- The end of `certify_cell`, after all segments were accepted: the contour check, the
indicators at the junctions, and the indicator sum. -/
def finishCell (cx : CellCtx) (segs : List (AccSeg cx)) (nev : Nat) : CellOut :=
  let ts := segTs segs
  let ks := segKs segs
  let n := ts.size
  if !chainOK ts then CellOut.deadOut nev
  else
    let κ := kindAt ks
    let inds := cellInds cx ts κ
    let ind := fun i => inds.getD i none
    let nind := ((List.range n).filter fun i => isJunction n κ i).length
    let amb := ambCount n κ ind
    { winding := if amb = 0 && allDecided n κ ind then some (junctionSumC n κ (indVal inds))
        else none
      nseg := n
      nN := (ks.toList.filter SegTy.isN).length
      nind
      ambiguous := amb
      nevals := nev + nind
      dead := false }

/-- **`certify_cell(m, rect, cell, grid, npu, max_iter, max_seg)`** for the cell `[lo, hi]`:
the certified winding number of `E_ℓ(·; G)` along the boundary of `R`, for all `G` in the cell.
The extra guard `0 < x0` (the contour lies in `{Re λ > 0}`) is implied by the success of
`evans` on the left edge; it is checked to simplify the soundness proof. -/
def certifyCell (p : Nat) (gr : Grid) (ℓ : Nat) (R : Rect) (lo hi : Rat) (ν : Rat)
    (maxIter maxSeg : Nat) : CellOut :=
  if !decide (0 < R.x0) then CellOut.deadOut 0
  else
    let cx : CellCtx := ⟨p, gr, ℓ, R, gBall p lo hi⟩
    let base := baseSegs R ν
    match runRounds cx maxSeg maxIter (base.map Slot.todo) base.length 0 with
    | (none, nev) => CellOut.deadOut nev
    | (some segs, nev) => finishCell cx segs nev

/-- A certified sub-cell `[lo, hi]` (halving `level`), with its result and record. -/
structure SubRes where
  lo : Rat
  hi : Rat
  winding : Int
  level : Nat
  out : CellOut
deriving Repr, Inhabited

/-- **`certify_cell_adaptive`**: certify `[lo, hi]` with `cert`; if that does not succeed, halve
the cell at its midpoint and recurse, at most `fuel` times in succession. Returns the certified
sub-cells (with the evidence `(cert lo hi).winding = some w`), the sub-cells still not
certified (as in Python, the two halves of a cell that fails at the last level), and the number
of evaluations. -/
def certifyAdaptive (cert : Rat → Rat → CellOut) :
    Nat → Nat → Rat → Rat →
      List {r : SubRes // (cert r.lo r.hi).winding = some r.winding} × List (Rat × Rat) × Nat
  | fuel, level, lo, hi =>
    let o := cert lo hi
    match h : o.winding with
    | some w => ([⟨⟨lo, hi, w, level, o⟩, h⟩], [], o.nevals)
    | none =>
      let m := (lo + hi) / 2
      match fuel with
      | 0 => ([], [(lo, m), (m, hi)], o.nevals)
      | fuel + 1 =>
        let r1 := certifyAdaptive cert fuel (level + 1) lo m
        let r2 := certifyAdaptive cert fuel (level + 1) m hi
        (r1.1 ++ r2.1, r1.2.1 ++ r2.2.1, o.nevals + r1.2.2 + r2.2.2)

end NonUniqueEuler.Verify
