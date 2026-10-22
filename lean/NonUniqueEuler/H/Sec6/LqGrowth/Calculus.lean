import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Helpers for `lem:Lq-growth`: elementary real analysis

Helpers for `P/Sec6/LqGrowth.lean` (`lem:Lq-growth`, `06_datum.tex:529-591`). All proved.

* `sq_one_add_half_mul_le_exp_mul_exp`: `(1 + ab/2)² ≤ e^a e^b` for `a, b ≥ 0`. This replaces the
  arithmetic–geometric mean step of the manuscript (`ε log y + α/ε ≥ 2(α log y)^{1/2}`) in the proof
  of (2): with `a = ε log y`, `b = α/ε` it gives `y^ε e^{α/ε} ≥ (1 + α log y / 2)²`, a lower bound
  independent of `ε` that is still integrable against `dy/y` (deviation).
* `integrableOn_Ioi_one_log_decay`: `y ↦ γ y⁻¹ (1 + γ log y)⁻²` is integrable on `(1, ∞)` for
  `γ > 0` (it is the derivative of `-(1 + γ log y)⁻¹`, which tends to `0`).
* `floor_exponent_ineq`: the arithmetic of the choice `j = ⌊q log μ/(2L)⌋` in the proof of (1).
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace NonUniqueEuler

namespace Datum

namespace LqGrowthH

/-- `(1 + ab/2)² ≤ e^a e^b` for `a, b ≥ 0`, from `1 + x + x²/2 ≤ e^x`. -/
theorem sq_one_add_half_mul_le_exp_mul_exp {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (1 + a * b / 2) ^ 2 ≤ Real.exp a * Real.exp b := by
  have h1 := Real.quadratic_le_exp_of_nonneg ha
  have h2 := Real.quadratic_le_exp_of_nonneg hb
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  calc (1 + a * b / 2) ^ 2
      ≤ (1 + a + a ^ 2 / 2) * (1 + b + b ^ 2 / 2) := by
        have : (1 + a + a ^ 2 / 2) * (1 + b + b ^ 2 / 2) - (1 + a * b / 2) ^ 2
            = a + b + a ^ 2 / 2 + b ^ 2 / 2 + a * b * b / 2 + a * b * a / 2 := by ring
        have : 0 ≤ a + b + a ^ 2 / 2 + b ^ 2 / 2 + a * b * b / 2 + a * b * a / 2 := by positivity
        linarith
    _ ≤ Real.exp a * Real.exp b :=
        mul_le_mul h1 h2 (by positivity) (Real.exp_pos a).le

/-- `y ↦ γ y⁻¹ / (1 + γ log y)²` is integrable on `(1, ∞)` for `γ > 0`: it is the derivative of
`y ↦ -(1 + γ log y)⁻¹`, which is continuous at `1` and tends to `0` at infinity. -/
theorem integrableOn_Ioi_one_log_decay {γ : ℝ} (hγ : 0 < γ) :
    IntegrableOn (fun y : ℝ => γ * y⁻¹ / (1 + γ * Real.log y) ^ 2) (Ioi 1) := by
  refine integrableOn_Ioi_deriv_of_nonneg (g := fun y : ℝ => -(1 + γ * Real.log y)⁻¹)
    (l := 0) ?_ ?_ ?_ ?_
  · have h1 : (1 : ℝ) + γ * Real.log 1 ≠ 0 := by simp
    exact ((continuousAt_const.add (continuousAt_const.mul
      (Real.continuousAt_log one_ne_zero))).inv₀ h1).neg.continuousWithinAt
  · intro x hx
    have hx0 : x ≠ 0 := (lt_trans zero_lt_one hx).ne'
    have hlog : 0 < Real.log x := Real.log_pos hx
    have hne : (1 : ℝ) + γ * Real.log x ≠ 0 := by positivity
    have h := (((Real.hasDerivAt_log hx0).const_mul γ).const_add 1).inv hne
    have h2 : HasDerivAt (fun y : ℝ => -(1 + γ * Real.log y)⁻¹)
        (-(-(γ * x⁻¹) / (1 + γ * Real.log x) ^ 2)) x := h.neg
    convert h2 using 1
    ring
  · intro x hx
    have hx0 : 0 ≤ x⁻¹ := inv_nonneg.2 (lt_trans zero_lt_one hx).le
    exact div_nonneg (mul_nonneg hγ.le hx0) (sq_nonneg _)
  · have h : Tendsto (fun y : ℝ => 1 + γ * Real.log y) atTop atTop :=
      tendsto_atTop_add_const_left atTop 1 (Real.tendsto_log_atTop.const_mul_atTop hγ)
    have := (tendsto_inv_atTop_zero.comp h).neg
    simpa using this

/-- The arithmetic of the choice `j = ⌊q l/(2L)⌋` (`06_datum.tex:551-566`): with `l = log μ`,
`L = log(2μ)`, `S = log(1/s̄)`, if `0 ≤ j`, `j ≤ q l/(2L) < j + 1`, then
`-l - S l/L + (l²/(4L)) q ≤ j l - (2/q)(j S + (j+1) j/2 · L)`. -/
theorem floor_exponent_ineq {l L S q j : ℝ} (hl : 0 < l) (hL : 0 < L) (hS : 0 ≤ S) (hq : 1 ≤ q)
    (hj0 : 0 ≤ j) (hj1 : j ≤ q * l / (2 * L)) (hj2 : q * l / (2 * L) < j + 1) :
    -l - S * l / L + l ^ 2 / (4 * L) * q ≤ j * l - 2 / q * (j * S + (j + 1) * j / 2 * L) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hjL : 2 * L * j ≤ q * l := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * L)).1 hj1
    linarith
  have hjL' : q * l < 2 * L * (j + 1) := by
    have := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * L)).1 hj2
    linarith
  -- `(j+1) j L / q ≤ (j+1) l / 2`
  have h1 : (j + 1) * j * L / q ≤ (j + 1) * l / 2 := by
    rw [div_le_iff₀ hq0]
    have : 0 ≤ j + 1 := by linarith
    nlinarith
  -- `2 j S / q ≤ S l / L`
  have h2 : 2 * j * S / q ≤ S * l / L := by
    rw [div_le_div_iff₀ hq0 hL]
    nlinarith
  -- `(l²/(4L)) q ≤ (j+1) l / 2`
  have h3 : l ^ 2 / (4 * L) * q ≤ (j + 1) * l / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hexp : 2 / q * (j * S + (j + 1) * j / 2 * L) = 2 * j * S / q + (j + 1) * j * L / q := by
    field_simp
  rw [hexp]
  nlinarith

end LqGrowthH

end Datum

end NonUniqueEuler
