import NonUniqueEuler.Defs.Infra.Polar
import NonUniqueEuler.I.Infra.Polar.Radial
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Proof of `I/Infra/Polar/Power.lean`: powers and logarithms of `‖x‖` (I-POLAR)

Every statement is a radial formula of `I/Infra/Polar/Radial.lean` followed by a
one-variable computation (`integral_rpow`, `integral_Ioi_rpow_of_lt`, `integral_inv_of_pos`,
and the antiderivative `r/2 · (r log r) - r²/4` of `r log r`).
-/

noncomputable section

open MeasureTheory Set Metric Real
open scoped ENNReal

namespace NonUniqueEuler.Polar

/-! ### One-variable helpers -/

/-- `r · r^s = r^(s+1)` for `r > 0`. -/
private theorem mul_rpow_eq_rpow_add_one {r : ℝ} (hr : 0 < r) (s : ℝ) :
    r • r ^ s = r ^ (s + 1) := by
  rw [smul_eq_mul, rpow_add_one hr.ne', mul_comm]

/-- `∫₀^ρ r · r^s dr = ρ^{s+2}/(s+2)` for `s > -2`, `ρ ≥ 0`. -/
private theorem integral_zero_mul_rpow {s : ℝ} (hs : -2 < s) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∫ r in (0 : ℝ)..ρ, r • r ^ s = ρ ^ (s + 2) / (s + 2) := by
  have hcongr : ∫ r in (0 : ℝ)..ρ, r • r ^ s = ∫ r in (0 : ℝ)..ρ, r ^ (s + 1) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun r hr => ?_)
    rw [uIoc_of_le hρ] at hr
    exact mul_rpow_eq_rpow_add_one hr.1 s
  rw [hcongr, integral_rpow (Or.inl (by linarith)),
    zero_rpow (by linarith : s + 1 + 1 ≠ 0), sub_zero, show s + 1 + 1 = s + 2 by ring]

/-- `ρ ↦ ∫ r log r` on `[0, ρ]` is `ρ²/2 log ρ - ρ²/4`. -/
private theorem integral_zero_mul_log {ρ : ℝ} (hρ : 0 < ρ) :
    ∫ r in (0 : ℝ)..ρ, r * Real.log r = ρ / 2 * (ρ * Real.log ρ) - ρ ^ 2 / 4 := by
  have hF : ∀ x ∈ Ioo (0 : ℝ) ρ,
      HasDerivAt (fun r : ℝ => r / 2 * (r * Real.log r) - r ^ 2 / 4) (x * Real.log x) x := by
    intro x hx
    have h1 := ((hasDerivAt_id x).div_const 2).mul (hasDerivAt_mul_log hx.1.ne')
    have h2 := (hasDerivAt_pow 2 x).div_const 4
    have hd : 1 / 2 * (x * Real.log x) + id x / 2 * (Real.log x + 1) -
        ((2 : ℕ) : ℝ) * x ^ (2 - 1) / 4 = x * Real.log x := by
      simp only [id, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
      ring
    exact (h1.sub h2).congr_deriv hd
  have hcont : ContinuousOn (fun r : ℝ => r / 2 * (r * Real.log r) - r ^ 2 / 4) (Icc 0 ρ) :=
    (((continuous_id.div_const 2).mul continuous_mul_log).sub
      ((continuous_pow 2).div_const 4)).continuousOn
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hρ.le hcont hF
    (continuous_mul_log.intervalIntegrable 0 ρ)]
  simp

/-! ### Disks -/

theorem integrableOn_ball_norm_rpow {s : ℝ} (hs : -2 < s) (ρ : ℝ) :
    IntegrableOn (fun x : ℂ => ‖x‖ ^ s) (ball 0 ρ) := by
  rcases le_or_gt ρ 0 with hρ | hρ
  · rw [ball_eq_empty.mpr hρ]
    exact integrableOn_empty
  rw [integrableOn_ball_comp_norm_iff (f := fun r : ℝ => r ^ s) hρ.le]
  have h : IntegrableOn (fun r : ℝ => r ^ (s + 1)) (Ioo 0 ρ) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hρ).mpr (by linarith)
  refine h.congr_fun (fun r hr => ?_) measurableSet_Ioo
  exact (mul_rpow_eq_rpow_add_one hr.1 s).symm

/-- `∫_{B_ρ} ‖x‖^s dx = 2π ρ^{s+2}/(s+2)` for `s > -2`. -/
theorem setIntegral_ball_norm_rpow {s : ℝ} (hs : -2 < s) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∫ x in ball (0 : ℂ) ρ, ‖x‖ ^ s = 2 * π * ρ ^ (s + 2) / (s + 2) := by
  rw [setIntegral_ball_comp_norm (fun r : ℝ => r ^ s) hρ, integral_zero_mul_rpow hs hρ,
    smul_eq_mul]
  ring

/-- Lower-integral version of `setIntegral_ball_norm_rpow`. -/
theorem lintegral_ball_norm_rpow {s : ℝ} (hs : -2 < s) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∫⁻ x in ball (0 : ℂ) ρ, ENNReal.ofReal (‖x‖ ^ s) =
      ENNReal.ofReal (2 * π * ρ ^ (s + 2) / (s + 2)) := by
  rw [← setIntegral_ball_norm_rpow hs hρ]
  exact (ofReal_integral_eq_lintegral_ofReal (integrableOn_ball_norm_rpow hs ρ)
    (Filter.Eventually.of_forall fun x => rpow_nonneg (norm_nonneg x) s)).symm

/-! ### Exteriors of disks -/

theorem integrableOn_compl_ball_norm_rpow {s : ℝ} (hs : s < -2) {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun x : ℂ => ‖x‖ ^ s) {x | R < ‖x‖} := by
  have hmeas : MeasurableSet {x : ℂ | R < ‖x‖} := measurableSet_lt measurable_const measurable_norm
  rw [← integrable_indicator_iff hmeas]
  have heq : {x : ℂ | R < ‖x‖}.indicator (fun x : ℂ => ‖x‖ ^ s) =
      fun x : ℂ => (Ioi R).indicator (fun r : ℝ => r ^ s) ‖x‖ := by
    funext x
    rfl
  rw [heq, integrable_comp_norm_iff]
  have h1 : IntegrableOn (fun r : ℝ => r ^ (s + 1)) (Ioi R) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hR
  have h2 : Integrable ((Ioi R).indicator (fun r : ℝ => r ^ (s + 1))) :=
    h1.integrable_indicator measurableSet_Ioi
  have h3 : (fun r : ℝ => r • (Ioi R).indicator (fun r : ℝ => r ^ s) r) =
      (Ioi R).indicator (fun r : ℝ => r ^ (s + 1)) := by
    funext r
    by_cases hr : r ∈ Ioi R
    · rw [indicator_of_mem hr, indicator_of_mem hr]
      exact mul_rpow_eq_rpow_add_one (hR.trans hr) s
    · rw [indicator_of_notMem hr, indicator_of_notMem hr, smul_zero]
  rw [h3]
  exact h2.integrableOn

/-- `∫_{‖x‖>R} ‖x‖^s dx = -2π R^{s+2}/(s+2)` for `s < -2`. -/
theorem setIntegral_compl_ball_norm_rpow {s : ℝ} (hs : s < -2) {R : ℝ} (hR : 0 < R) :
    ∫ x in {x : ℂ | R < ‖x‖}, ‖x‖ ^ s = -(2 * π * R ^ (s + 2) / (s + 2)) := by
  rw [setIntegral_compl_ball_comp_norm (fun r : ℝ => r ^ s) hR.le, smul_eq_mul]
  have hcongr : ∫ r in Ioi R, r • r ^ s = ∫ r in Ioi R, r ^ (s + 1) :=
    setIntegral_congr_fun measurableSet_Ioi fun r hr =>
      mul_rpow_eq_rpow_add_one (hR.trans hr) s
  rw [hcongr, integral_Ioi_rpow_of_lt (by linarith) hR,
    show s + 1 + 1 = s + 2 by ring]
  ring

/-! ### Annuli -/

/-- `∫_{a<‖x‖<b} ‖x‖^s dx = 2π (b^{s+2} - a^{s+2})/(s+2)` for `s ≠ -2`, `0 < a ≤ b`. -/
theorem setIntegral_annulus_norm_rpow {s : ℝ} (hs : s ≠ -2) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) :
    ∫ x in annulus a b, ‖x‖ ^ s = 2 * π * (b ^ (s + 2) - a ^ (s + 2)) / (s + 2) := by
  rw [setIntegral_annulus_comp_norm (fun r : ℝ => r ^ s) ha.le hab, smul_eq_mul]
  have hpos : ∀ r ∈ uIcc a b, 0 < r := fun r hr => by
    rw [uIcc_of_le hab] at hr
    exact ha.trans_le hr.1
  have hcongr : ∫ r in a..b, r • r ^ s = ∫ r in a..b, r ^ (s + 1) :=
    intervalIntegral.integral_congr fun r hr => mul_rpow_eq_rpow_add_one (hpos r hr) s
  have h0 : (0 : ℝ) ∉ uIcc a b := fun h => (hpos 0 h).false
  rw [hcongr, integral_rpow (Or.inr ⟨fun h => hs (by linarith), h0⟩),
    show s + 1 + 1 = s + 2 by ring]
  ring

/-- `∫_{a<‖x‖<b} ‖x‖^{-2} dx = 2π log(b/a)`, `0 < a ≤ b`. -/
theorem setIntegral_annulus_norm_sq_inv {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in annulus a b, (‖x‖ ^ 2)⁻¹ = 2 * π * Real.log (b / a) := by
  rw [setIntegral_annulus_comp_norm (fun r : ℝ => (r ^ 2)⁻¹) ha.le hab, smul_eq_mul]
  have hcongr : ∫ r in a..b, r • (r ^ 2)⁻¹ = ∫ r in a..b, r⁻¹ := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le hab] at hr
    have hr0 : r ≠ 0 := (ha.trans_le hr.1).ne'
    simp only [smul_eq_mul]
    field_simp
  rw [hcongr, integral_inv_of_pos ha (ha.trans_le hab)]

/-! ### Local integrability and the logarithm -/

theorem locallyIntegrable_norm_rpow {s : ℝ} (hs : -2 < s) :
    LocallyIntegrable (fun x : ℂ => ‖x‖ ^ s) := by
  intro x
  exact ⟨ball 0 (‖x‖ + 1), isOpen_ball.mem_nhds (by simp),
    integrableOn_ball_norm_rpow hs _⟩

private theorem integrableOn_ball_log_norm (ρ : ℝ) :
    IntegrableOn (fun x : ℂ => Real.log ‖x‖) (ball 0 ρ) := by
  rcases le_or_gt ρ 0 with hρ | hρ
  · rw [ball_eq_empty.mpr hρ]
    exact integrableOn_empty
  rw [integrableOn_ball_comp_norm_iff (f := Real.log) hρ.le]
  have h : IntegrableOn (fun r : ℝ => r * Real.log r) (Icc 0 ρ) :=
    continuous_mul_log.integrableOn_Icc
  simpa only [smul_eq_mul] using h.mono_set Ioo_subset_Icc_self

theorem locallyIntegrable_log_norm : LocallyIntegrable (fun x : ℂ => Real.log ‖x‖) := by
  intro x
  exact ⟨ball 0 (‖x‖ + 1), isOpen_ball.mem_nhds (by simp), integrableOn_ball_log_norm _⟩

/-- `∫_{B_ρ} log ‖x‖ dx = π ρ² (log ρ - 1/2)` for `ρ > 0`. -/
theorem setIntegral_ball_log_norm {ρ : ℝ} (hρ : 0 < ρ) :
    ∫ x in ball (0 : ℂ) ρ, Real.log ‖x‖ = π * ρ ^ 2 * (Real.log ρ - 1 / 2) := by
  rw [setIntegral_ball_comp_norm Real.log hρ.le, smul_eq_mul]
  simp only [smul_eq_mul]
  rw [integral_zero_mul_log hρ]
  ring

end NonUniqueEuler.Polar
