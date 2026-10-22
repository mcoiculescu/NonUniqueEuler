import NonUniqueEuler.Verify.Comp.RunCore
import NonUniqueEuler.Verify.Comp.Par
import NonUniqueEuler.Verify.Data.CellLits

/-!
# Part 2: the executable `ncert` (compiled run of the checker)

Not imported by any proof. Core only, so the executable links
only the Lean runtime (no Mathlib).

Lakefile stanza (not in `lakefile.toml`; `tools/ncert_build.sh` builds the same executable):
```
[[lean_exe]]
name = "ncert"
root = "NonUniqueEuler.Verify.Main"
```

Commands (exit code `0` = certified / passed, `1` = not certified, `2` = usage error):
* `ncert` or `ncert all`: evaluates `checkCore defaultPrec certLits`, which equals
  `Verify.check Verify.cert` (`Verify.check_cert`), and prints `true` or `false`.
  This is the hypothesis of the final theorem. Single-threaded: many CPU-hours (see `README.md`).
* `ncert par`: evaluates `checkCorePar defaultPrec certLits` (`Comp/Par.lean`), the same
  Boolean (`check_eq_checkCorePar : check cert = checkCorePar defaultPrec certLits`,
  `Data/CellsPar.lean`), multithreaded: every cell, every right half of a halved cell and every
  Evans evaluation of a round runs in a `Task`. The number of worker threads is the runtime's
  thread pool size: `LEAN_NUM_THREADS` if set, else the number of hardware threads. Precisely,
  it evaluates `parJoin defaultPrec gr certLits (parSpawn defaultPrec gr certLits)` with
  `gr = Grid.build defaultPrec gridHpow gridOrder`, which is `checkCorePar defaultPrec certLits`
  by definition (`checkCorePar_def`). While the tasks run, it only *watches* them
  (`IO.hasFinished`, then `Task.get` of a finished task) and prints to stderr, as each cell
  finishes, the JSON records of its certified sub-cells and a progress line. The value is
  printed on stdout; exit code `0` iff `true`.
  Performance (macOS): run it with `MallocNanoZone=1`. The arbitrary-precision integers (GMP)
  allocate through the system `malloc`; without the nano zone, 6 threads of one process
  contend in `malloc` and need about 1.6 times the CPU time per Evans evaluation (measured:
  6 (N2′) cells, 6 threads, 325 s wall without, 202 s with; single-threaded 1.87 s per
  evaluation). The variable only selects the system allocator; it does not change the
  computation.
  Full run (see `tools/ncert_par_run.sh`):
  `MallocNanoZone=1 LEAN_NUM_THREADS=6 nice -n 10 ncert par > par_all.out 2> par_all.log`.
* `ncert par count I [J]`, `ncert par gap I [J]` (test): the parallel machinery (`parSpawn`,
  `joinCells`) on the sub-certificate made of the cells `I, …, J-1` of one run; prints the
  same lines as `ncert count I [J]` / `ncert gap I [J]` (only the times differ), so the two
  outputs can be compared.
* `ncert par watch I J` (test): the code path of `ncert par` (`parSpawn`, the progress output,
  `parJoin`) on the sub-certificate made of the (N2′) cells `I, …, J-1` (value `false`: not a
  cover); exit code `0`.
* `ncert count I [J]`, `ncert gap I [J]`: certifies the cells `I, …, J-1` (default `J = I+1`)
  of the (N1′) / (N2′) run with `runCell` (as `ringcert cell count I`), printing one JSON line
  per certified sub-cell (the fields of the package's result records), the failed sub-cells and
  the time. A partial run is not a verification; it is evidence and a regression test.
* `ncert verbose`: the whole check cell by cell, with the same functions as `checkCore`
  (`runCell` on every cell, `itemOK` on the concatenated results), printing progress.
* `ncert bench K`: times the grid construction and `K` Evans enclosures (the first `K`
  initial segments of the first (N2′) cell).
* `ncert grid`: prints the grid summary.
* `ncert point X Y G`: the enclosure at the exact point `λ = X + iY` and the exact `G` (rationals
  `n`, `n/d` or decimals), as exact end points `re_lo re_hi im_lo im_hi`.
-/

namespace NonUniqueEuler.Verify.CLI

open NonUniqueEuler.Verify

/-- The item name of the package. -/
def itemName : Item → String
  | .count => "N1'"
  | .gap => "N2'"

/-- A JSON string literal of a rational, as the package writes it (`str(Fraction)`). -/
def jq (q : Rat) : String := "\"" ++ toString q ++ "\""

/-- The JSON record of a certified sub-cell (the fields of `certify_cell`'s record). -/
def recordJson (item : Item) (idx : Nat) (R : Rect) (r : SubRes) : String :=
  "{\"item\": \"" ++ itemName item ++ "\", \"index\": " ++ toString idx ++
  ", \"G\": [" ++ jq r.lo ++ ", " ++ jq r.hi ++ "], \"rect\": [" ++ jq R.x0 ++ ", " ++
  jq R.x1 ++ ", " ++ jq R.y0 ++ ", " ++ jq R.y1 ++ "], \"winding\": " ++ toString r.winding ++
  ", \"nseg\": " ++ toString r.out.nseg ++ ", \"ambiguous\": " ++ toString r.out.ambiguous ++
  ", \"nN\": " ++ toString r.out.nN ++ ", \"nind\": " ++ toString r.out.nind ++
  ", \"nevals\": " ++ toString r.out.nevals ++ ", \"level\": " ++ toString r.level ++ "}"

/-- The cells and parameters of an item. -/
def itemData : Item → List CellSpec × RunSpec
  | .count => (certLits.countCells, certLits.countParams)
  | .gap => (certLits.gapCells, certLits.gapParams)

/-- Seconds since `t0` (nanoseconds), with millisecond resolution. -/
def secondsSince (t0 : Nat) : IO String := do
  let t1 ← IO.monoNanosNow
  let ms := (t1 - t0) / 1000000
  return s!"{ms / 1000}.{toString (1000 + ms % 1000) |>.drop 1}"

/-- Certify the cells `I, …, J-1` of an item, printing the records. Returns `true` if every
cell gave only certified sub-cells with result `1` and rectangles as required. -/
def runRange (gr : Grid) (item : Item) (I J : Nat) : IO Bool := do
  let (cells, spec) := itemData item
  let mut good := true
  let mut nev := 0
  for i in [I:J] do
    match cells[i]? with
    | none =>
      IO.println s!"no cell {i} (the run has {cells.length} cells)"
      good := false
    | some c =>
      let t0 ← IO.monoNanosNow
      let r := runCell defaultPrec gr item spec c
      for x in r.1 do
        IO.println (recordJson item i x.1.1 x.1.2)
      let failed := r.2.1.map fun f => s!"[{jq f.1}, {jq f.2}]"
      let ok := r.2.1.isEmpty && !r.1.isEmpty && r.1.all (fun x => decide (x.1.2.winding = 1)) &&
        rectOK item c.rect
      nev := nev + r.2.2
      let dt ← secondsSince t0
      IO.println s!"cell {i} of {itemName item}: {if ok then "CERTIFIED, winding 1" else "NOT CERTIFIED"}; subcells {r.1.length}, failed {failed}, evals {r.2.2}, {dt} s"
      good := good && ok
  IO.println s!"cells {I}..{J}: evaluations {nev}"
  return good

/-- The whole check, cell by cell, with progress output. -/
def runVerbose (gr : Grid) : IO Bool := do
  let mut res := true
  for item in [Item.count, Item.gap] do
    let (cells, spec) := itemData item
    let mut acc : List (CertRes defaultPrec gr item spec) × List (Rat × Rat) × Nat := ([], [], 0)
    let mut i := 0
    for c in cells do
      let t0 ← IO.monoNanosNow
      let r := runCell defaultPrec gr item spec c
      for x in r.1 do
        IO.println (recordJson item i x.1.1 x.1.2)
      acc := (acc.1 ++ r.1, acc.2.1 ++ r.2.1, acc.2.2 + r.2.2)
      let dt ← secondsSince t0
      IO.println s!"cell {i}: subcells {r.1.length}, failed {r.2.1.length}, evals {r.2.2}, {dt} s"
      i := i + 1
    let ok := itemOK item acc
    IO.println s!"RESULT {itemName item}: {ok}; certified sub-cells {acc.1.length}, failed {acc.2.1.length}, evaluations {acc.2.2}"
    res := res && ok
  return res

/-- Parse a rational: `"n"`, `"n/d"` or a decimal `"-0.045"` (no exponent). -/
def parseRat (s : String) : Option Rat :=
  let neg := s.startsWith "-"
  let t := if neg then (s.drop 1).toString else s
  let v : Option Rat :=
    match t.splitOn "/" with
    | [n, d] => do
      let n ← n.toNat?
      let d ← d.toNat?
      if d = 0 then none else some ((n : Rat) / (d : Rat))
    | [x] =>
      match x.splitOn "." with
      | [i] => i.toNat?.map fun n => (n : Rat)
      | [i, f] => do
        let a ← (if i.isEmpty then some 0 else i.toNat?)
        let b ← f.toNat?
        some ((a : Rat) + (b : Rat) / ((10 ^ f.length : Nat) : Rat))
      | _ => none
    | _ => none
  v.map fun q => if neg then -q else q

/-- The enclosure at the exact point `x + iy` and the exact `G`, printed as the exact rational
end points `re_lo re_hi im_lo im_hi` (diagnostics and known-answer tests). -/
def point (x y G : Rat) : IO Bool := do
  let gr := Grid.build defaultPrec gridHpow gridOrder
  match evansEncl defaultPrec gr ellSector (CBox.ofRat defaultPrec x y) (Ball.ofRat defaultPrec G) with
  | some B =>
    match B.re.lower?, B.re.upper?, B.im.lower?, B.im.upper? with
    | some a, some b, some c, some d =>
      IO.println s!"{a.toRatExact} {b.toRatExact} {c.toRatExact} {d.toRatExact}"
      return true
    | _, _, _, _ => IO.println "infinite"; return false
  | none => IO.println "failed"; return false

/-- Time the grid and `k` enclosures. -/
def bench (k : Nat) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let gr := Grid.build defaultPrec gridHpow gridOrder
  IO.println s!"grid: ok {gr.ok}, steps {gr.steps.length}, N {gr.N}"
  let dt ← secondsSince t0
  IO.println s!"grid build: {dt} s"
  match certLits.gapCells.head? with
  | none => IO.println "no gap cell"
  | some c =>
    let ν := cellDensity .gap certLits.gapParams c.rect
    let segs := (baseSegs c.rect ν).take k
    let Gb := gBall defaultPrec c.lo c.hi
    let t1 ← IO.monoNanosNow
    let mut nok := 0
    for s in segs do
      match evansEncl defaultPrec gr ellSector (segBox defaultPrec c.rect s) Gb with
      | some B =>
        nok := nok + 1
        IO.println s!"[{s.t0}, {s.t1}]: re {B.re.mid.man.natAbs.log2 + 1} bits, rad {repr B.re.rad}"
      | none => IO.println s!"[{s.t0}, {s.t1}]: failed"
    let t2 ← IO.monoNanosNow
    let us := (t2 - t1) / 1000 / (max segs.length 1)
    IO.println s!"{segs.length} enclosures ({nok} finite): {us / 1000} ms each"

/-! ## The multithreaded run (`ncert par`)

The value is computed by `parSpawn` (all cell tasks started) and `parJoin` (`Comp/Par.lean`);
the IO code below only watches the started tasks and prints. -/

/-- A cell is certified: no failed sub-cell, at least one certified sub-cell, every result `1`,
the rectangle as required (the per-cell part of `itemOK`, as `runRange` prints it). -/
def cellVerdict {p : Nat} {gr : Grid} {spec : RunSpec} (item : Item) (c : CellSpec)
    (r : CellRes p gr item spec) : Bool :=
  r.2.1.isEmpty && !r.1.isEmpty && r.1.all (fun x => decide (x.1.2.winding = 1)) &&
    rectOK item c.rect

/-- The summary line of a cell, as `runRange` prints it (without the time). -/
def cellSummary {p : Nat} {gr : Grid} {spec : RunSpec} (item : Item) (i : Nat) (c : CellSpec)
    (r : CellRes p gr item spec) : String :=
  let failed := r.2.1.map fun f => s!"[{jq f.1}, {jq f.2}]"
  s!"cell {i} of {itemName item}: {if cellVerdict item c r then "CERTIFIED, winding 1" else "NOT CERTIFIED"}; subcells {r.1.length}, failed {failed}, evals {r.2.2}"

/-- A started cell task, watched for the progress output. -/
structure Watched where
  /-- The task has finished. -/
  finished : BaseIO Bool
  /-- Print (with the given printer) the records of the finished cell, then its summary line
  after the given prefix. -/
  report : (String → IO Unit) → String → IO Unit

/-- The watched cells `i, i+1, …` of a run. -/
def watchCells {p : Nat} {gr : Grid} (item : Item) {spec : RunSpec} :
    Nat → List CellSpec → List (Task (CellRes p gr item spec)) → List Watched
  | i, c :: cs, t :: ts =>
    { finished := IO.hasFinished t
      report := fun out pre => do
        let r := t.get
        for x in r.1 do
          out (recordJson item i x.1.1 x.1.2)
        out (pre ++ cellSummary item i c r) } :: watchCells item (i + 1) cs ts
  | _, _, _ => []

/-- Watch started cells until all have finished, reporting each one on stderr when it finishes
(in the order of completion; polled every 2 s). -/
def watchAll (ws : List Watched) (t0 : Nat) : IO Unit := do
  let total := ws.length
  let mut pending := ws
  let mut done := 0
  for _ in [0:1000000000] do
    if pending.isEmpty then break
    let mut rest : List Watched := []
    for w in pending do
      if ← w.finished then
        done := done + 1
        let dt ← secondsSince t0
        w.report IO.eprintln s!"[{dt} s, {done}/{total} cells] "
      else
        rest := w :: rest
    pending := rest.reverse
    if !pending.isEmpty then IO.sleep 2000

/-- The multithreaded check on core data `spec`, watched: `parJoin defaultPrec gr spec
(parSpawn defaultPrec gr spec)` with `gr = Grid.build defaultPrec gridHpow gridOrder`, i.e.
`checkCorePar defaultPrec spec` (`checkCorePar_def`). Progress on stderr; the value is printed
on stdout after `what`. -/
def runParSpec (spec : CertSpec) (what : String) : IO Bool := do
  let t0 ← IO.monoNanosNow
  let nt ← IO.getEnv "LEAN_NUM_THREADS"
  let nz ← IO.getEnv "MallocNanoZone"
  let hw := (System.Platform.Internal.getHardwareConcurrency ()).toNat
  IO.eprintln s!"ncert par: {spec.countCells.length} cells (N1'), {spec.gapCells.length} cells (N2'); LEAN_NUM_THREADS = {nt.getD "(unset)"}, hardware threads {hw}, MallocNanoZone = {nz.getD "(unset)"}"
  let gr := Grid.build defaultPrec gridHpow gridOrder
  let run := parSpawn defaultPrec gr spec
  watchAll (watchCells .count 0 spec.countCells run.count ++
    watchCells .gap 0 spec.gapCells run.gap) t0
  IO.eprintln s!"RESULT N1': {itemOK .count (joinCells run.count)}; RESULT N2': {itemOK .gap (joinCells run.gap)}"
  let b := parJoin defaultPrec gr spec run
  let dt ← secondsSince t0
  IO.println s!"{what} = {b}  ({dt} s)"
  return b

/-- **`ncert par`**: `runParSpec certLits`, i.e. `parJoin defaultPrec gr certLits
(parSpawn defaultPrec gr certLits)` with `gr = Grid.build defaultPrec gridHpow gridOrder`, which
is `checkCorePar defaultPrec certLits` (`checkCorePar_def`), which is `check cert`
(`check_eq_checkCorePar`). -/
def runPar : IO Bool :=
  runParSpec certLits "checkCorePar defaultPrec certLits = check cert"

/-- **`ncert par watch I J`** (test of the `ncert par` code path): `runParSpec` on the
sub-certificate made of the (N2′) cells `I, …, J-1` and no (N1′) cell. Its value is `false`
(no (N1′) cell, and the cells do not cover `[0, d]`); the per-cell records on stderr are those of
`ncert gap I J`. -/
def runParWatch (I J : Nat) : IO Bool :=
  runParSpec { certLits with countCells := [], gapCells := (certLits.gapCells.drop I).take (J - I) }
    s!"checkCorePar defaultPrec (gap cells {I}..{J} only; expected false)"

/-- Print the results of started cells `I, I+1, …` in order, in the format of `runRange` (the
time is the time since `t0` at which the cell is printed), then the total number of evaluations
of `joinCells`. -/
def reportRange {p : Nat} {gr : Grid} (item : Item) {spec : RunSpec} (I J : Nat)
    (cells : List CellSpec) (ts : List (Task (CellRes p gr item spec))) (t0 : Nat) :
    IO Bool := do
  let mut good := true
  let mut i := I
  for (c, t) in cells.zip ts do
    let r ← IO.wait t
    for x in r.1 do
      IO.println (recordJson item i x.1.1 x.1.2)
    let dt ← secondsSince t0
    IO.println s!"{cellSummary item i c r}, {dt} s"
    good := good && cellVerdict item c r
    i := i + 1
  for k in [i:J] do
    IO.println s!"no cell {k} (the run has {(itemData item).1.length} cells)"
    good := false
  IO.println s!"cells {I}..{J}: evaluations {(joinCells ts).2.2}"
  return good

/-- **`ncert par count I J`, `ncert par gap I J`** (test): `parSpawn` on the sub-certificate
made of the cells `I, …, J-1` of one run (the other run empty); prints what `runRange` prints. -/
def runParRange (item : Item) (I J : Nat) : IO Bool := do
  let t0 ← IO.monoNanosNow
  let sub := ((itemData item).1.drop I).take (J - I)
  let spec : CertSpec := match item with
    | .count => { certLits with countCells := sub, gapCells := [] }
    | .gap => { certLits with countCells := [], gapCells := sub }
  let gr := Grid.build defaultPrec gridHpow gridOrder
  let run := parSpawn defaultPrec gr spec
  match item with
  | .count => reportRange .count I J sub run.count t0
  | .gap => reportRange .gap I J sub run.gap t0

end NonUniqueEuler.Verify.CLI

open NonUniqueEuler.Verify NonUniqueEuler.Verify.CLI in
/-- The entry point of `lake exe ncert` (see the module docstring). -/
def main (args : List String) : IO UInt32 := do
  let parseItem : String → Option Item := fun s =>
    if s == "count" then some .count else if s == "gap" then some .gap else none
  match args with
  | [] | ["all"] =>
    let t0 ← IO.monoNanosNow
    let b := checkCore defaultPrec certLits
    let dt ← secondsSince t0
    IO.println s!"checkCore defaultPrec certLits = check cert = {b}  ({dt} s)"
    return if b then 0 else 1
  | ["par"] =>
    let b ← runPar
    return if b then 0 else 1
  | ["par", "watch", i, j] =>
    match i.toNat?, j.toNat? with
    | some I, some J =>
      let _ ← runParWatch I J
      return 0
    | _, _ =>
      IO.println "usage: ncert par watch I J"
      return 2
  | ["par", it, i] | ["par", it, i, _] =>
    match parseItem it, i.toNat? with
    | some item, some I =>
      let J := match args with
        | [_, _, _, j] => j.toNat!
        | _ => I + 1
      let b ← runParRange item I J
      return if b then 0 else 1
    | _, _ =>
      IO.println "usage: ncert par [count I [J] | gap I [J]]"
      return 2
  | ["verbose"] =>
    let gr := Grid.build defaultPrec gridHpow gridOrder
    let b ← runVerbose gr
    IO.println s!"ALL: {b}"
    return if b then 0 else 1
  | ["grid"] =>
    bench 0
    return 0
  | ["bench", k] =>
    bench k.toNat!
    return 0
  | ["point", x, y, g] =>
    match parseRat x, parseRat y, parseRat g with
    | some x, some y, some g =>
      let b ← point x y g
      return if b then 0 else 1
    | _, _, _ => IO.println "point: cannot parse the rationals"; return 2
  | [it, i] | [it, i, _] =>
    match parseItem it, i.toNat? with
    | some item, some I =>
      let J := match args with
        | [_, _, j] => j.toNat!
        | _ => I + 1
      let gr := Grid.build defaultPrec gridHpow gridOrder
      let b ← runRange gr item I J
      return if b then 0 else 1
    | _, _ =>
      IO.println "usage: ncert [all | par | par count I [J] | par gap I [J] | par watch I J | verbose | grid | bench K | point X Y G | count I [J] | gap I [J]]"
      return 2
  | _ =>
    IO.println "usage: ncert [all | par | par count I [J] | par gap I [J] | par watch I J | verbose | grid | bench K | point X Y G | count I [J] | gap I [J]]"
    return 2
