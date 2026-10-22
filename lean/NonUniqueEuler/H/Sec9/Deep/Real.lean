import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Helpers for `P/Sec9/Deep`: elementary real estimates

Helper file of `P/Sec9/Deep.lean` (`lem:deep`(3), `09_relay.tex:1159-1177`). Pure real
analysis, no project objects:
* `integral_exp_neg_mul_eq`, `integral_exp_neg_mul_le`: `∫_{-T}^0 e^{-xτ} dτ = (e^{xT} - 1)/x
  ≤ e^{xT}/x` (`x > 0`);
* `kappa_mul_exp_eq`: `κ e^{xT_g} = δ₀(κ/δ₀)^{1 - x/σ₁}` for `T_g = σ₁⁻¹ log(δ₀/κ)`
  (`09_relay.tex:1163-1164`);
* `one_le_log_of_le_rpow`: `κ ≤ δ₀4^{-μ/(μ-1)}` implies `log(δ₀/κ) ≥ 1` (`09_relay.tex:1161`).
Everything here is proved.
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler

namespace Relay

namespace DeepAux

/-- `∫_{-T}^0 e^{-xτ} dτ = (e^{xT} - 1)/x` for `x ≠ 0`. -/
theorem integral_exp_neg_mul_eq (x T : ℝ) (hx : x ≠ 0) :
    ∫ τ in (-T)..0, Real.exp (-(x * τ)) = (Real.exp (x * T) - 1) / x := by
  have hderiv : ∀ τ ∈ uIcc (-T) 0,
      HasDerivAt (fun τ : ℝ => -Real.exp (-(x * τ)) / x) (Real.exp (-(x * τ))) τ := by
    intro τ _
    have h : HasDerivAt (fun τ : ℝ => -Real.exp (-(x * τ)) / x)
        (-(Real.exp (-(x * τ)) * -(x * 1)) / x) τ :=
      (((hasDerivAt_id τ).const_mul x).neg.exp.neg).div_const x
    refine h.congr_deriv ?_
    field_simp
  have hint : IntervalIntegrable (fun τ : ℝ => Real.exp (-(x * τ))) volume (-T) 0 :=
    (by fun_prop : Continuous fun τ : ℝ => Real.exp (-(x * τ))).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [mul_zero, neg_zero, Real.exp_zero, mul_neg, neg_neg]
  field_simp
  ring

/-- `∫_{-T}^0 e^{-xτ} dτ ≤ e^{xT}/x` for `x > 0`. -/
theorem integral_exp_neg_mul_le {x : ℝ} (hx : 0 < x) (T : ℝ) :
    ∫ τ in (-T)..0, Real.exp (-(x * τ)) ≤ Real.exp (x * T) / x := by
  rw [integral_exp_neg_mul_eq x T hx.ne']
  exact div_le_div_of_nonneg_right (by linarith) hx.le

/-- `κ e^{x T_g} = δ₀ (κ/δ₀)^{1 - x/σ₁}` for `T_g = σ₁⁻¹ log(δ₀/κ)` (`09_relay.tex:1163-1164`). -/
theorem kappa_mul_exp_eq {κ δ₀ σ₁ : ℝ} (x : ℝ) (hκ : 0 < κ) (hδ : 0 < δ₀) (hσ : σ₁ ≠ 0) :
    κ * Real.exp (x * (σ₁⁻¹ * Real.log (δ₀ / κ))) = δ₀ * (κ / δ₀) ^ (1 - x / σ₁) := by
  have hq : 0 < κ / δ₀ := div_pos hκ hδ
  rw [Real.rpow_def_of_pos hq]
  have hlog : Real.log (κ / δ₀) = -Real.log (δ₀ / κ) := by
    rw [← Real.log_inv, inv_div]
  rw [hlog]
  have hsplit : -Real.log (δ₀ / κ) * (1 - x / σ₁) =
      -Real.log (δ₀ / κ) + x * (σ₁⁻¹ * Real.log (δ₀ / κ)) := by
    field_simp
    ring
  rw [hsplit, Real.exp_add, Real.exp_neg, Real.exp_log (div_pos hδ hκ), inv_div]
  field_simp

/-- `1 < log 4`. -/
theorem one_lt_log_four : 1 < Real.log 4 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

/-- `κ ≤ δ₀ 4^{-μ/(μ-1)}` with `κ > 0`, `μ > 1` gives `log(δ₀/κ) ≥ (μ/(μ-1)) log 4 ≥ 1`
(`09_relay.tex:1161`). -/
theorem one_le_log_of_le_rpow {κ δ₀ μ : ℝ} (hκ : 0 < κ) (hμ : 1 < μ)
    (h : κ ≤ δ₀ * (4 : ℝ) ^ (-(μ / (μ - 1)))) : 1 ≤ Real.log (δ₀ / κ) := by
  set p : ℝ := μ / (μ - 1) with hp
  have h4p : 0 < (4 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) p
  have h4np : (4 : ℝ) ^ (-p) = ((4 : ℝ) ^ p)⁻¹ := Real.rpow_neg (by norm_num) p
  have hle : (4 : ℝ) ^ p ≤ δ₀ / κ := by
    rw [le_div_iff₀ hκ]
    rw [h4np] at h
    have := mul_le_mul_of_nonneg_left h h4p.le
    calc (4 : ℝ) ^ p * κ ≤ (4 : ℝ) ^ p * (δ₀ * ((4 : ℝ) ^ p)⁻¹) := this
      _ = δ₀ := by field_simp
  have hp1 : 1 ≤ p := by
    rw [hp, one_le_div (by linarith)]
    linarith
  have hlog : p * Real.log 4 ≤ Real.log (δ₀ / κ) := by
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_le_log h4p hle
  have hl4 := one_lt_log_four
  nlinarith

end DeepAux

end Relay

end NonUniqueEuler
