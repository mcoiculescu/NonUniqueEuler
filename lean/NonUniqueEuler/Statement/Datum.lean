import NonUniqueEuler.Statement.Ring
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Statement layer: the datum `f`

Statement layer: definitions and statements only, no proofs.

Manuscript sources: `06_datum.tex:15-25` (Definition `def:datum`), `01_intro.tex:131-139`
(Equation `(eq:datum)`), `06_datum.tex:27-34` (Proposition `prop:integrability`).

Indexing. The manuscript indexes rings by `k ≥ 1`. The functions `amp`, `ratio`, `radius`
below are defined for all `k : ℕ` and agree with `A_k`, `s_k`, `r_k` for `k ≥ 1`; the sum
defining `f` runs over `k = j + 1`, `j : ℕ`. The value at `k = 0` is never used.

The sum `f(x) = Σ_k A_k Φ(x / r_k)` is a `tsum`. For every `x` at most one term is nonzero
(the annuli `{a r_k ≤ |x| ≤ r_k}` are disjoint, `prop:integrability`), so the series is
summable and `tsum` is its value; this is part of what the proof layer establishes.
-/

noncomputable section

open MeasureTheory

namespace NonUniqueEuler

open RingData

/-- The amplitudes `A_k = A₁ μ^{k-1}` (`06_datum.tex:19`). -/
def amp (A₁ μ : ℝ) (k : ℕ) : ℝ := A₁ * μ ^ (k - 1)

/-- The ratios `s_k = s̄ (2μ)^{-k}` (`06_datum.tex:19`). -/
def ratio (sbar μ : ℝ) (k : ℕ) : ℝ := sbar / (2 * μ) ^ k

/-- The radii `r_1 = 1`, `r_{k+1} = s_k r_k` (`06_datum.tex:19`), i.e.
`r_k = ∏_{1 ≤ j < k} s_j`. -/
def radius (sbar μ : ℝ) (k : ℕ) : ℝ := ∏ j ∈ Finset.Ico 1 k, ratio sbar μ j

/-- **The datum** `f = Σ_{k ≥ 1} A_k Φ(· / r_k)` (`06_datum.tex:22-23`), for an admissible cutoff
`χ` (through `Φ = ringPhi χ`) and parameters `A₁ > 0`, `μ ∈ (1, 2]`, `s̄ ∈ (0, a/16]`. -/
def datum (χ : ℝ → ℝ) (A₁ μ sbar : ℝ) (x : ℂ) : ℝ :=
  ∑' j : ℕ, amp A₁ μ (j + 1) * ringPhi χ (x / ((radius sbar μ (j + 1) : ℝ) : ℂ))

/-- The parameter ranges of Definition `def:datum` (`06_datum.tex:17`). -/
structure DatumParams (A₁ μ sbar : ℝ) : Prop where
  A₁_pos : 0 < A₁
  one_lt_μ : 1 < μ
  μ_le_two : μ ≤ 2
  sbar_pos : 0 < sbar
  sbar_le : sbar ≤ a / 16

/-- Statement of `prop:integrability` (`06_datum.tex:27-34`), for an admissible cutoff and
parameters as in `def:datum`: the annuli `{a r_k ≤ |x| ≤ r_k}`, `k ≥ 1`, are pairwise disjoint;
`f` is radial (pointwise) and nonnegative; `f ∈ L^q` for every `q ∈ [1, ∞)`; `f ∉ L^∞`.
Proved in `P/Sec6/Integrability.lean` (`integrability`). -/
def DatumProperties (χ : ℝ → ℝ) (A₁ μ sbar : ℝ) : Prop :=
  (∀ k l : ℕ, 1 ≤ k → 1 ≤ l → k ≠ l →
      Disjoint {x : ℂ | a * radius sbar μ k ≤ ‖x‖ ∧ ‖x‖ ≤ radius sbar μ k}
        {x : ℂ | a * radius sbar μ l ≤ ‖x‖ ∧ ‖x‖ ≤ radius sbar μ l}) ∧
    IsRadialPointwise (datum χ A₁ μ sbar) ∧
    (∀ x, 0 ≤ datum χ A₁ μ sbar x) ∧
    (∀ q : ℝ, 1 ≤ q → MemLp (datum χ A₁ μ sbar) (ENNReal.ofReal q)) ∧
    ¬ MemLp (datum χ A₁ μ sbar) ⊤

end NonUniqueEuler
