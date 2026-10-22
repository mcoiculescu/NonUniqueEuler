import NonUniqueEuler.Verify.Comp.Evans

/-!
# Part 2 algorithms: rectangles, contour segments, boxes and classification

Checker design decision D8 (see `FORMALIZATION_NOTES.md`).
Manuscript: §A.6, the certification (`A_verification.tex:559-600`).
Reference: `euler-ring-certificate/src/ringcert/winding.py` (`seg_box`, `pt_box`,
`G_ball`, `classify`, `rect_points`).

**Parametrized contour (deviation W3).** The boundary of `R = [x0, x1] × [y0, y1]` is traversed
counterclockwise from `(x0, y0)` with parameter `t ∈ [0, 4]`; edge `e` (bottom, right, top,
left) is `[e, e+1]`. `Rect.ptQ R t` is the point with parameter `t`, by the closed form of
`QRect.bdryPtQ` (`Defs/Verify/Contour.lean`; the same formula, written in core). Segments are
parameter intervals `Seg = [t0, t1]`. Python works with the points themselves; the two agree:
* `rect_points` with density `ν` gives the points `ptQ (e + j/k_e)`, `j < k_e`,
  `k_e = max 2 ⌈ν L_e⌉`, and finally `ptQ 4 = (x0, y0)` (`baseParams`);
* on an edge the parametrization is affine, so the point of the midpoint parameter is the
  midpoint `((p+q)/2)` that Python uses for bisection;
* hence the boxes `seg_box(p, q)` and `pt_box(p)` are the same rational balls.

| `winding.py` | Lean |
|---|---|
| `seg_box(p, q)` | `segBox p R s` |
| `pt_box(p)` | `ptBox p R t` |
| `G_ball(cell)` | `gBall p lo hi` |
| `classify(B)` (0 / 1 / 2) | `classify B` (`none` / `some .P` / `some .N`) |
| `rect_points(x0, x1, y0, y1, npu)` | `baseParams R ν` (parameters), `baseSegs R ν` (consecutive pairs) |

Core only.
-/

namespace NonUniqueEuler.Verify

/-- A rectangle `[x0, x1] × [y0, y1]` with rational vertices (JSON order `[x0, x1, y0, y1]`;
the core mirror of the statement-layer `QRect`). -/
structure Rect where
  x0 : Rat
  x1 : Rat
  y0 : Rat
  y1 : Rat
deriving Repr, DecidableEq, Inhabited

/-- `max 0 (min u 1)` (`clamp01Q` of `Defs/Verify/Contour.lean`). -/
def clampQ (u : Rat) : Rat := max 0 (min u 1)

/-- The boundary point with parameter `t` (the formula of `QRect.bdryPtQ`):
`(x0 + (x1 - x0)(c(t) - c(t-2)), y0 + (y1 - y0)(c(t-1) - c(t-3)))`, `c = clampQ`. -/
def Rect.ptQ (R : Rect) (t : Rat) : Rat × Rat :=
  (R.x0 + (R.x1 - R.x0) * (clampQ t - clampQ (t - 2)),
   R.y0 + (R.y1 - R.y0) * (clampQ (t - 1) - clampQ (t - 3)))

/-- A segment of the contour: the parameter interval `[t0, t1]`. -/
structure Seg where
  t0 : Rat
  t1 : Rat
deriving Repr, DecidableEq, Inhabited

/-- The midpoint parameter (Python: the midpoint of the two end points). -/
def Seg.mid (s : Seg) : Rat := (s.t0 + s.t1) / 2

/-- `seg_box(p, q)`: the box `(X_p ∪ X_q) + i(Y_p ∪ Y_q)` of the balls containing the
coordinates of the end points. -/
def segBox (p : Nat) (R : Rect) (s : Seg) : CBox :=
  let a := R.ptQ s.t0
  let b := R.ptQ s.t1
  ⟨Ball.union p (Ball.ofRat p a.1) (Ball.ofRat p b.1),
   Ball.union p (Ball.ofRat p a.2) (Ball.ofRat p b.2)⟩

/-- `pt_box(p)`: the box of the balls containing the coordinates of the point. -/
def ptBox (p : Nat) (R : Rect) (t : Rat) : CBox :=
  let a := R.ptQ t
  CBox.ofRat p a.1 a.2

/-- `G_ball(cell)`: the union of the balls containing the end points of `[lo, hi]`. -/
def gBall (p : Nat) (lo hi : Rat) : Ball :=
  Ball.union p (Ball.ofRat p lo) (Ball.ofRat p hi)

/-- The two segment types of Proposition A.4: `P` (the box misses `(-∞, 0]`) and `N` (the box
misses `[0, ∞)`). The core mirror of `SegKind` (`Defs/Verify/Winding.lean`). -/
inductive SegTy where
  | P
  | N
deriving Repr, DecidableEq, Inhabited

/-- `true` for type `N`. -/
def SegTy.isN : SegTy → Bool
  | .P => false
  | .N => true

/-- `classify(B)`: type P if `Im B > 0`, `Im B < 0` or `Re B > 0` (certainly), else type N if
`Re B < 0`; rejected (`none`) otherwise or if `B` is not finite. -/
def classify (B : CBox) : Option SegTy :=
  if !B.isFinite then none
  else if B.im.posC || B.im.negC || B.re.posC then some .P
  else if B.re.negC then some .N
  else none

/-- The length of edge `e` (`|x1 - x0|` for the bottom and top edges, `|y1 - y0|` for the
right and left edges; Python `abs(b[0]-a[0]) + abs(b[1]-a[1])`). -/
def Rect.edgeLen (R : Rect) (e : Nat) : Rat :=
  if e % 2 = 0 then Rat.abs (R.x1 - R.x0) else Rat.abs (R.y1 - R.y0)

/-- The number of sub-segments of an edge of length `L`: `max(2, ⌈L ν⌉)`. -/
def edgeCount (L ν : Rat) : Nat := max 2 (Rat.ceil (L * ν)).toNat

/-- `rect_points` as parameters: `e + j/k_e` (`e < 4`, `j < k_e`), then `4`. -/
def baseParams (R : Rect) (ν : Rat) : List Rat :=
  ((List.range 4).flatMap fun (e : Nat) =>
      let k := edgeCount (R.edgeLen e) ν
      (List.range k).map fun (j : Nat) => ((e : Nat) : Rat) + ((j : Nat) : Rat) / ((k : Nat) : Rat)) ++ [4]

/-- The segments between consecutive parameters. -/
def consecSegs : List Rat → List Seg
  | [] => []
  | a :: rest =>
    match rest with
    | [] => []
    | b :: _ => ⟨a, b⟩ :: consecSegs rest

/-- The initial segments `zip(base[:-1], base[1:])` of `certify_cell`. -/
def baseSegs (R : Rect) (ν : Rat) : List Seg := consecSegs (baseParams R ν)

end NonUniqueEuler.Verify
