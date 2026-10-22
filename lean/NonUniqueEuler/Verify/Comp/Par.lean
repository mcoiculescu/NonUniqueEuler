import NonUniqueEuler.Verify.Comp.RunCore

/-!
# Part 2 algorithms: the multithreaded evaluation `checkCorePar` of the check

`checkCorePar p spec` computes the same Boolean as `checkCore p spec` (`Comp/RunCore.lean`):
`checkCorePar_eq : checkCorePar p spec = checkCore p spec`. It differs only in *how* the
compiled code evaluates it: the independent pieces of work are wrapped in `Task.spawn`, and
their values are read back with `Task.get`. In the logic `Task.spawn f = ⟨f ()⟩` and
`Task.get ⟨x⟩ = x` (`Init/Core.lean`), so `(Task.spawn f).get = f ()` holds by `rfl`
(`spawn_get`) and every equation below is proved by unfolding plus induction on lists or on
the fuel. In the compiled code `Task.spawn` hands the closure to the runtime thread pool
(`lean_task_spawn`), which runs it on a worker thread; `Task.get` waits for the result.

The parallel pieces, from the coarsest to the finest:
1. **cells** (`spawnCells`, priority `prioCell = 0`): `runCell` of every cell of both runs,
   spawned at once, the (N1′) cells first (they are the long ones), then the (N2′) cells
   (`parSpawn`); `joinCells` reads them back in order and concatenates them exactly as
   `runCells` does (`joinCells_spawnCells`);
2. **halves** (`certifyAdaptiveP`, priority `prioHalf = 1`): when a cell is halved, the right
   half runs in a new task while the current thread does the left half;
3. **Evans evaluations** (priority `prioEval = 2`): in every round of `runRounds`, the
   evaluations `tryAccept` of all pending segments are spawned before the round is processed
   (`spawnSlot`, `oneRoundR`, `oneRoundP`), and so are the junction indicators `indAt` of
   `finishCell` (`cellIndsP`).

The runtime takes higher priorities first, so the Evans evaluations of the cells in progress run
before a new cell is started; a new cell is started when a worker would otherwise be idle.
The number of workers is the runtime's thread pool size: the environment variable
`LEAN_NUM_THREADS` if set (read by `lean_init_task_manager`), otherwise the number of hardware
threads. A thread that blocks in `Task.get` inside a task temporarily raises the pool size by one
(documented at `Task.get`), so the nesting cannot deadlock and the number of busy threads stays
at the pool size (checked: nested tasks with `LEAN_NUM_THREADS=1` run, sequentially).

Differences in *work* (not in value) from the sequential evaluation: when a round fails
(`maxSeg < cnt`), the evaluations of the remaining segments of that round were already started
(their results are discarded); the (N2′) cells are evaluated even if the (N1′) run fails (the
sequential `&&` skips them). Neither happens on the certificate.

The proofs do not depend on the priorities, on the runtime or on the order of evaluation.

Core only (the executable `Verify/Main.lean` imports it). No `partial`, `implemented_by`,
`extern`, `unsafe` or `Float`. The attributes `noinline` (on `parSpawn` and `alongside`) and
`never_extract` (on `parSpawn`) are compiler hints with no effect in the logic. The compiler may
move a pure `let t := Task.spawn …` down to the first use of `t` (it did so for the halves, which
then ran one after the other); a task is therefore always started either inside a strict data
structure that is complete before the first `Task.get` (`List.map`, `Array.ofFn`, the structure
returned by the `noinline` function `parSpawn`), or as an argument of the `noinline` function
`alongside`. `never_extract` keeps `parSpawn` on closed arguments from becoming a lazily
initialized constant (the generated C was checked: `tools/ncert_build.sh` output,
`.lake/build/ir/NonUniqueEuler/Verify/Comp/Par.c`).

`check_eq_checkCorePar : check cert = checkCorePar defaultPrec certLits` is in
`Data/CellsPar.lean`.
-/

namespace NonUniqueEuler.Verify

/-- The priority of the cell tasks (the lowest, `Task.Priority.default`). -/
def prioCell : Task.Priority := Task.Priority.default

/-- The priority of the right halves of halved cells. -/
def prioHalf : Task.Priority := 1

/-- The priority of the single Evans evaluations (segments and indicators). -/
def prioEval : Task.Priority := 2

/-- `Task.spawn` followed by `Task.get` is the function application (definitionally). -/
theorem spawn_get {α : Type} (f : Unit → α) (prio : Task.Priority) :
    (Task.spawn f prio).get = f () := rfl

/-! ## One round with the evaluations in tasks -/

/-- A slot of a round whose Evans evaluation (if pending) runs in a task. -/
inductive PSlot (cx : CellCtx) where
  | done (a : AccSeg cx)
  | todo (s : Seg) (t : Task (Option (AccSeg cx)))

/-- Start the evaluation `tryAccept` of a pending slot in a task. -/
def spawnSlot (cx : CellCtx) : Slot cx → PSlot cx
  | .done a => .done a
  | .todo s => .todo s (Task.spawn (prio := prioEval) fun _ => tryAccept cx s)

/-- `oneRound` on slots whose evaluations were started (`t.get` in place of `tryAccept cx s`). -/
def oneRoundR (cx : CellCtx) (maxSeg : Nat) :
    List (PSlot cx) → Nat → Nat → Option (List (Slot cx)) × Nat × Nat
  | [], cnt, nev => (some [], cnt, nev)
  | .done a :: rest, cnt, nev =>
    let r := oneRoundR cx maxSeg rest cnt nev
    (r.1.map (Slot.done a :: ·), r.2)
  | .todo s t :: rest, cnt, nev =>
    match t.get with
    | some a =>
      let r := oneRoundR cx maxSeg rest cnt (nev + 1)
      (r.1.map (Slot.done a :: ·), r.2)
    | none =>
      if maxSeg < cnt then (none, cnt, nev + 1)
      else
        let m := s.mid
        let r := oneRoundR cx maxSeg rest (cnt + 1) (nev + 1)
        (r.1.map (fun l => Slot.todo ⟨s.t0, m⟩ :: Slot.todo ⟨m, s.t1⟩ :: l), r.2)

/-- One round: all pending evaluations are started (`List.map` is strict: every task exists
before the first `Task.get`), then the round is processed in contour order. -/
def oneRoundP (cx : CellCtx) (maxSeg : Nat) (slots : List (Slot cx)) (cnt nev : Nat) :
    Option (List (Slot cx)) × Nat × Nat :=
  oneRoundR cx maxSeg (slots.map (spawnSlot cx)) cnt nev

theorem oneRoundP_eq (cx : CellCtx) (maxSeg : Nat) (slots : List (Slot cx)) (cnt nev : Nat) :
    oneRoundP cx maxSeg slots cnt nev = oneRound cx maxSeg slots cnt nev := by
  unfold oneRoundP
  induction slots generalizing cnt nev with
  | nil => rfl
  | cons sl rest ih =>
    cases sl with
    | done a => simp only [List.map_cons, spawnSlot, oneRoundR, oneRound, ih]
    | todo s =>
      simp only [List.map_cons, spawnSlot, oneRoundR, oneRound, spawn_get, ih] <;> rfl

/-- `runRounds` with `oneRoundP`. -/
def runRoundsP (cx : CellCtx) (maxSeg : Nat) :
    Nat → List (Slot cx) → Nat → Nat → Option (List (AccSeg cx)) × Nat
  | 0, slots, _, nev => (allDone cx slots, nev)
  | fuel + 1, slots, cnt, nev =>
    match allDone cx slots with
    | some segs => (some segs, nev)
    | none =>
      match oneRoundP cx maxSeg slots cnt nev with
      | (none, _, nev') => (none, nev')
      | (some slots', cnt', nev') => runRoundsP cx maxSeg fuel slots' cnt' nev'

theorem runRoundsP_eq (cx : CellCtx) (maxSeg fuel : Nat) (slots : List (Slot cx))
    (cnt nev : Nat) :
    runRoundsP cx maxSeg fuel slots cnt nev = runRounds cx maxSeg fuel slots cnt nev := by
  induction fuel generalizing slots cnt nev with
  | zero => rfl
  | succ fuel ih => simp only [runRoundsP, runRounds, oneRoundP_eq, ih] <;> rfl

/-! ## The indicators with the evaluations in tasks -/

/-- `cellInds` with the evaluations `indAt` started in tasks (`Array.ofFn` builds all tasks
before `Array.map Task.get` reads the first). -/
def cellIndsP (cx : CellCtx) (ts : Array Seg) (κ : Nat → SegTy) : Array (Option Int) :=
  (Array.ofFn (n := ts.size) fun i =>
    if isJunction ts.size κ i.val then
      Task.spawn (prio := prioEval) fun _ => indAt cx (ts.getD i.val default).t0
    else Task.pure (some 0)).map Task.get

theorem cellIndsP_eq (cx : CellCtx) (ts : Array Seg) (κ : Nat → SegTy) :
    cellIndsP cx ts κ = cellInds cx ts κ := by
  unfold cellIndsP cellInds
  rw [Array.map_ofFn]
  congr 1
  funext i
  simp only [Function.comp_apply]
  split <;> rfl

/-- `finishCell` with `cellIndsP`. -/
def finishCellP (cx : CellCtx) (segs : List (AccSeg cx)) (nev : Nat) : CellOut :=
  let ts := segTs segs
  let ks := segKs segs
  let n := ts.size
  if !chainOK ts then CellOut.deadOut nev
  else
    let κ := kindAt ks
    let inds := cellIndsP cx ts κ
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

theorem finishCellP_eq (cx : CellCtx) (segs : List (AccSeg cx)) (nev : Nat) :
    finishCellP cx segs nev = finishCell cx segs nev := by
  unfold finishCellP finishCell
  simp only [cellIndsP_eq]

/-- `certifyCell` with `runRoundsP` and `finishCellP`. -/
def certifyCellP (p : Nat) (gr : Grid) (ℓ : Nat) (R : Rect) (lo hi : Rat) (ν : Rat)
    (maxIter maxSeg : Nat) : CellOut :=
  if !decide (0 < R.x0) then CellOut.deadOut 0
  else
    let cx : CellCtx := ⟨p, gr, ℓ, R, gBall p lo hi⟩
    let base := baseSegs R ν
    match runRoundsP cx maxSeg maxIter (base.map Slot.todo) base.length 0 with
    | (none, nev) => CellOut.deadOut nev
    | (some segs, nev) => finishCellP cx segs nev

theorem certifyCellP_eq (p : Nat) (gr : Grid) (ℓ : Nat) (R : Rect) (lo hi : Rat) (ν : Rat)
    (maxIter maxSeg : Nat) :
    certifyCellP p gr ℓ R lo hi ν maxIter maxSeg = certifyCell p gr ℓ R lo hi ν maxIter maxSeg := by
  unfold certifyCellP certifyCell
  simp only [runRoundsP_eq, finishCellP_eq] <;> rfl

/-- `runCert` with `certifyCellP`. -/
def runCertP (p : Nat) (gr : Grid) (item : Item) (spec : RunSpec) (R : Rect) (lo hi : Rat) :
    CellOut :=
  certifyCellP p gr ellSector R lo hi (cellDensity item spec R) spec.maxRounds spec.maxSegments

theorem runCertP_eq (p : Nat) (gr : Grid) (item : Item) (spec : RunSpec) (R : Rect)
    (lo hi : Rat) : runCertP p gr item spec R lo hi = runCert p gr item spec R lo hi :=
  certifyCellP_eq _ _ _ _ _ _ _ _ _

/-! ## Adaptive halving with the right half in a task -/

/-- `f ()` paired with `t` (in the logic just the pair). It is a call boundary (`noinline`):
the compiled code has started the task `t` (an argument) before it evaluates `f ()`. Without
it the compiler is free to move the pure `let t := Task.spawn …` after the evaluation of the
left half, which would serialize the two halves. -/
@[noinline] def alongside {α β : Type} (t : Task β) (f : Unit → α) : α × Task β := (f (), t)

theorem alongside_fst {α β : Type} (t : Task β) (f : Unit → α) : (alongside t f).1 = f () := rfl

theorem alongside_snd {α β : Type} (t : Task β) (f : Unit → α) : (alongside t f).2 = t := rfl

/-- `certifyAdaptive cert`, evaluated with `certP` (equal to `cert`, `h`) and with the right
half of a halved cell in a task. The evidence of a certified sub-cell is about `cert`, so the
result has the type of `certifyAdaptive cert`. -/
def certifyAdaptiveP (cert certP : Rat → Rat → CellOut)
    (h : ∀ lo hi, certP lo hi = cert lo hi) :
    Nat → Nat → Rat → Rat →
      List {r : SubRes // (cert r.lo r.hi).winding = some r.winding} × List (Rat × Rat) × Nat
  | fuel, level, lo, hi =>
    let o := certP lo hi
    match hw : o.winding with
    | some w => ([⟨⟨lo, hi, w, level, o⟩, (congrArg CellOut.winding (h lo hi)).symm.trans hw⟩],
        [], o.nevals)
    | none =>
      let m := (lo + hi) / 2
      match fuel with
      | 0 => ([], [(lo, m), (m, hi)], o.nevals)
      | fuel + 1 =>
        let rt := alongside
          (Task.spawn (prio := prioHalf) fun _ => certifyAdaptiveP cert certP h fuel (level + 1) m hi)
          (fun _ => certifyAdaptiveP cert certP h fuel (level + 1) lo m)
        let r1 := rt.1
        let r2 := rt.2.get
        (r1.1 ++ r2.1, r1.2.1 ++ r2.2.1, o.nevals + r1.2.2 + r2.2.2)

theorem certifyAdaptiveP_eq (cert certP : Rat → Rat → CellOut)
    (h : ∀ lo hi, certP lo hi = cert lo hi) (fuel level : Nat) (lo hi : Rat) :
    certifyAdaptiveP cert certP h fuel level lo hi = certifyAdaptive cert fuel level lo hi := by
  have hc : certP = cert := funext fun lo => funext (h lo)
  subst hc
  induction fuel generalizing level lo hi with
  | zero =>
    rw [certifyAdaptiveP, certifyAdaptive]
    rfl
  | succ fuel ih =>
    rw [certifyAdaptiveP, certifyAdaptive]
    simp only [alongside_fst, alongside_snd, spawn_get, ih] <;> rfl

/-! ## Cells -/

/-- `runCell` with `runCertP` and `certifyAdaptiveP`. -/
def runCellP (p : Nat) (gr : Grid) (item : Item) (spec : RunSpec) (c : CellSpec) :
    List (CertRes p gr item spec) × List (Rat × Rat) × Nat :=
  let r := certifyAdaptiveP (runCert p gr item spec c.rect) (runCertP p gr item spec c.rect)
    (runCertP_eq p gr item spec c.rect) spec.maxHalvings 0 c.lo c.hi
  (r.1.map fun x => ⟨(c.rect, x.1), x.2⟩, r.2)

theorem runCellP_eq (p : Nat) (gr : Grid) (item : Item) (spec : RunSpec) (c : CellSpec) :
    runCellP p gr item spec c = runCell p gr item spec c := by
  unfold runCellP runCell
  rw [certifyAdaptiveP_eq]

/-- The result of one cell of a run (the type of `runCell`). -/
abbrev CellRes (p : Nat) (gr : Grid) (item : Item) (spec : RunSpec) : Type :=
  List (CertRes p gr item spec) × List (Rat × Rat) × Nat

/-- Start `runCellP` of every cell in a task (in order). -/
def spawnCells (p : Nat) (gr : Grid) (item : Item) (spec : RunSpec) (cells : List CellSpec) :
    List (Task (CellRes p gr item spec)) :=
  cells.map fun c => Task.spawn (prio := prioCell) fun _ => runCellP p gr item spec c

/-- Read back the cell results in order and concatenate them as `runCells` does. -/
def joinCells {p : Nat} {gr : Grid} {item : Item} {spec : RunSpec} :
    List (Task (CellRes p gr item spec)) → CellRes p gr item spec
  | [] => ([], [], 0)
  | t :: rest =>
    let r := t.get
    let r' := joinCells rest
    (r.1 ++ r'.1, r.2.1 ++ r'.2.1, r.2.2 + r'.2.2)

theorem joinCells_spawnCells (p : Nat) (gr : Grid) (item : Item) (spec : RunSpec)
    (cells : List CellSpec) :
    joinCells (spawnCells p gr item spec cells) = runCells p gr item spec cells := by
  induction cells with
  | nil => rfl
  | cons c rest ih =>
    simp only [spawnCells, List.map_cons, joinCells, spawn_get, runCellP_eq, runCells] at ih ⊢
    rw [ih]

/-! ## The check -/

/-- The started cell tasks of both runs. -/
structure ParRun (p : Nat) (gr : Grid) (spec : CertSpec) where
  count : List (Task (CellRes p gr .count spec.countParams))
  gap : List (Task (CellRes p gr .gap spec.gapParams))

/-- Start every cell of both runs: first the (N1′) cells, then the (N2′) cells. One call
(`noinline`), evaluated where it is called (`never_extract`). -/
@[noinline, never_extract]
def parSpawn (p : Nat) (gr : Grid) (spec : CertSpec) : ParRun p gr spec :=
  { count := spawnCells p gr .count spec.countParams spec.countCells
    gap := spawnCells p gr .gap spec.gapParams spec.gapCells }

/-- The conjunction of `checkCore`, with the results of the runs read back from the tasks. -/
def parJoin (p : Nat) (gr : Grid) (spec : CertSpec) (r : ParRun p gr spec) : Bool :=
  decide (spec.countParams = pinnedParams .count) &&
  decide (spec.gapParams = pinnedParams .gap) &&
  decide ((1 : Rat) / 50 < gmaxQ) && decide (rectA.x0 < sigmaGap) &&
  (itemOK .count (joinCells r.count) && itemOK .gap (joinCells r.gap))

/-- **The check, multithreaded**, on core data at precision `p`, with the grid `gr` given. -/
def checkCoreParWith (p : Nat) (gr : Grid) (spec : CertSpec) : Bool :=
  parJoin p gr spec (parSpawn p gr spec)

/-- **The check, multithreaded**: the same Boolean as `checkCore p spec`
(`checkCorePar_eq`). -/
def checkCorePar (p : Nat) (spec : CertSpec) : Bool :=
  checkCoreParWith p (Grid.build p gridHpow gridOrder) spec

/-- What the executable evaluates (`Verify/Main.lean`, mode `par`) is `checkCorePar`, by
definition. -/
theorem checkCorePar_def (p : Nat) (spec : CertSpec) :
    checkCorePar p spec =
      parJoin p (Grid.build p gridHpow gridOrder) spec
        (parSpawn p (Grid.build p gridHpow gridOrder) spec) := rfl

/-- **The multithreaded check is the check.** -/
theorem checkCorePar_eq (p : Nat) (spec : CertSpec) : checkCorePar p spec = checkCore p spec := by
  unfold checkCorePar checkCoreParWith parJoin parSpawn checkCore
  simp only [joinCells_spawnCells]

end NonUniqueEuler.Verify
