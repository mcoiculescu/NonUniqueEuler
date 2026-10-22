import NonUniqueEuler.Verify.Comp.Certify

/-!
# Part 2 algorithms: the two runs and the exact checks (core part of `check`)

Manuscript: §A.6 "The Two Computations" and §A.7 "Reproduction" (the re-check),
`A_verification.tex:507-649, 692-735`.
Reference: `euler-ring-certificate/src/ringcert/sector3.py` (`COUNT_PARAMS`,
`GAP_PARAMS`, `rectangle_ok`, `_jobs`, `run`) and `results.py` (`check_sector3`, the exact
re-check of `ringcert check`).

The certificate data in core form (`CertSpec`; the statement-layer `CertificateData` is
converted in `Comp/Runs.lean`, which defines `Verify.check`):
* `countCells`, `gapCells`: lists of cells `[lo, hi]` of `G` with a rectangle (`CellSpec`);
* `countParams`, `gapParams`: density, rounds, segments, halvings (`RunSpec`). For the (N2′)
  run the density field is the numerator `3` of `ν = 3/(x1 - 211/2500)`.

`checkCore p spec` is the conjunction of
1. the pinned parameters (`sector3.run` refuses a certificate whose parameters differ from
   `COUNT_PARAMS`, `GAP_PARAMS`), the constant facts `d > 1/50` and `211/2500 > 9/200`
   (`check_sector3`);
2. for each of the two runs (`runCells`): every cell is certified adaptively with `ℓ = 3`;
   `itemOK`: no failed sub-cell, at least one certified sub-cell, every result `= 1`, every
   rectangle as required (`rectangle_ok`), and the certified sub-cells, in order, partition
   `[0, d]` (`coverOK`: start `0`, end `d = G_max`, consecutive, positive widths;
   `check_sector3`).

The `&&` are evaluated left to right, so the (N2′) run is skipped if the (N1′) run fails.

Deviation W2: the certified sub-cells are not sorted before the coverage check (they come out in
order when the cells are given in order, which the certificate files do); an unsorted input
fails the check (fail closed).

Core only.
-/

namespace NonUniqueEuler.Verify

/-- A cell of a certificate file: an interval `[lo, hi]` of `G` and a rectangle (the core
mirror of the statement-layer `CertCell`). -/
structure CellSpec where
  lo : Rat
  hi : Rat
  rect : Rect
deriving Repr, DecidableEq, Inhabited

/-- Run parameters (the core mirror of `RunParams`). -/
structure RunSpec where
  density : Rat
  maxRounds : Nat
  maxSegments : Nat
  maxHalvings : Nat
deriving Repr, DecidableEq, Inhabited

/-- The certificate data (the core mirror of `CertificateData`). -/
structure CertSpec where
  countCells : List CellSpec
  countParams : RunSpec
  gapCells : List CellSpec
  gapParams : RunSpec
deriving Repr, Inhabited

/-- The two runs: (N1′) (`sector3-count`) and (N2′) (`sector3-gap`). -/
inductive Item where
  | count
  | gap
deriving Repr, DecidableEq

/-- `M_SECTOR = 3`. -/
def ellSector : Nat := 3

/-- The grid: `HPOW = 8` (steps of about `2^-8`), `ORDER = 16`. -/
def gridHpow : Nat := 8

/-- The Taylor order `N = 16`. -/
def gridOrder : Nat := 16

/-- `G_max = d = 5764607523034235 · 2^-58` (`G_MAX_Q`). -/
def gmaxQ : Rat := 5764607523034235 / 288230376151711744

/-- `R_A = [9/200, 3] × [-5, 3]` (`RECT_A`). -/
def rectA : Rect := ⟨9 / 200, 3, -5, 3⟩

/-- `211/2500` (`SIGMA_GAP`). -/
def sigmaGap : Rat := 211 / 2500

/-- `COUNT_PARAMS = (npu 20, max_iter 16, max_seg 6000, depth 4)` and
`GAP_PARAMS = (npu_numerator 3, max_iter 10, max_seg 800, depth 5)`. -/
def pinnedParams : Item → RunSpec
  | .count => ⟨20, 16, 6000, 4⟩
  | .gap => ⟨3, 10, 800, 5⟩

/-- `rectangle_ok(item, rect)`: for (N1′) the rectangle is `R_A`; for (N2′),
`x0 = 211/2500 < x1`, `y0 < y1`, and the rectangle lies in `R_A`. -/
def rectOK : Item → Rect → Bool
  | .count, R => decide (R = rectA)
  | .gap, R =>
    decide (R.x0 = sigmaGap) && decide (R.x0 < R.x1) && decide (R.y0 < R.y1) &&
      decide (rectA.x0 ≤ R.x0) && decide (R.x1 ≤ rectA.x1) && decide (rectA.y0 ≤ R.y0) &&
      decide (R.y1 ≤ rectA.y1)

/-- The contour density of a cell (`_jobs`): `ν = npu` for (N1′), `ν = 3/(x1 - x0)` for (N2′). -/
def cellDensity : Item → RunSpec → Rect → Rat
  | .count, s, _ => s.density
  | .gap, s, R => s.density / (R.x1 - R.x0)

/-- The certification used by a run for the rectangle `R`. -/
def runCert (p : Nat) (gr : Grid) (item : Item) (spec : RunSpec) (R : Rect) (lo hi : Rat) :
    CellOut :=
  certifyCell p gr ellSector R lo hi (cellDensity item spec R) spec.maxRounds spec.maxSegments

/-- A certified sub-cell of a run, with its rectangle and the evidence of its certification. -/
def CertRes (p : Nat) (gr : Grid) (item : Item) (spec : RunSpec) : Type :=
  {x : Rect × SubRes // (runCert p gr item spec x.1 x.2.lo x.2.hi).winding = some x.2.winding}

/-- `_work_cell` / `certify_cell_adaptive` for one cell of a run. -/
def runCell (p : Nat) (gr : Grid) (item : Item) (spec : RunSpec) (c : CellSpec) :
    List (CertRes p gr item spec) × List (Rat × Rat) × Nat :=
  let r := certifyAdaptive (runCert p gr item spec c.rect) spec.maxHalvings 0 c.lo c.hi
  (r.1.map fun x => ⟨(c.rect, x.1), x.2⟩, r.2)

/-- All cells of a run, in order: the certified sub-cells, the failed sub-cells and the number
of evaluations. -/
def runCells (p : Nat) (gr : Grid) (item : Item) (spec : RunSpec) :
    List CellSpec → List (CertRes p gr item spec) × List (Rat × Rat) × Nat
  | [] => ([], [], 0)
  | c :: rest =>
    let r := runCell p gr item spec c
    let r' := runCells p gr item spec rest
    (r.1 ++ r'.1, r.2.1 ++ r'.2.1, r.2.2 + r'.2.2)

/-- The intervals, in order, partition `[a, b]`: the first starts at `a`, each starts where the
previous one ends, each has positive width, and the last ends at `b`. -/
def coverOK : List (Rat × Rat) → Rat → Rat → Bool
  | [], a, b => decide (a = b)
  | c :: rest, a, b => decide (c.1 = a) && decide (c.1 < c.2) && coverOK rest c.2 b

/-- The run flags `ok` and `gapfree` of `sector3.run`, recomputed as in `check_sector3`. -/
def itemOK {p : Nat} {gr : Grid} {spec : RunSpec} (item : Item)
    (out : List (CertRes p gr item spec) × List (Rat × Rat) × Nat) : Bool :=
  out.2.1.isEmpty && !out.1.isEmpty &&
    out.1.all (fun r => decide (r.1.2.winding = 1)) &&
    out.1.all (fun r => rectOK item r.1.1) &&
    coverOK (out.1.map fun r => (r.1.2.lo, r.1.2.hi)) 0 gmaxQ

/-- **The check** on core data, at midpoint precision `p` (`Verify.check` uses
`defaultPrec = 128`, as the package). -/
def checkCore (p : Nat) (spec : CertSpec) : Bool :=
  decide (spec.countParams = pinnedParams .count) &&
  decide (spec.gapParams = pinnedParams .gap) &&
  decide ((1 : Rat) / 50 < gmaxQ) && decide (rectA.x0 < sigmaGap) &&
  (let gr := Grid.build p gridHpow gridOrder
   itemOK .count (runCells p gr .count spec.countParams spec.countCells) &&
   itemOK .gap (runCells p gr .gap spec.gapParams spec.gapCells))

end NonUniqueEuler.Verify
