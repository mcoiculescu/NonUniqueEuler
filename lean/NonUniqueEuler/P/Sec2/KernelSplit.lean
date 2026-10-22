import NonUniqueEuler.Defs.Sec2.BiotSavart
import NonUniqueEuler.I.Infra.Polar.Power
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Proof: the near/far splitting of the Biot–Savart kernel

Proof of `I/Sec2/KernelSplit.lean` (`02_prelim.tex:129-140`). The norm of the kernel is computed
directly from the definition (`norm_biotSavartKernel'`, valid for every `z`, including `z = 0`
where both sides are `0`); the radial integral is `Polar.setIntegral_ball_norm_rpow` with
exponent `-s`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace NonUniqueEuler.BS

/-- `‖K_BS(z)‖ = (2π‖z‖)⁻¹` for every `z` (both sides vanish at `z = 0`). -/
private theorem norm_biotSavartKernel' (z : ℂ) :
    ‖biotSavartKernel z‖ = (2 * Real.pi * ‖z‖)⁻¹ := by
  have hpi : 0 < 2 * Real.pi := by positivity
  rcases eq_or_ne z 0 with rfl | hz
  · simp [biotSavartKernel]
  have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [biotSavartKernel, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity)]
  field_simp

private theorem measurable_biotSavartKernel : Measurable biotSavartKernel := by
  unfold biotSavartKernel
  fun_prop

private theorem measurable_kernelNear : Measurable kernelNear :=
  measurable_biotSavartKernel.indicator measurableSet_ball

private theorem measurable_kernelFar : Measurable kernelFar :=
  measurable_biotSavartKernel.indicator measurableSet_ball.compl

/-- `‖K_near(z)‖^s = 1_{B₁}(z) (2π)^{-s} ‖z‖^{-s}` for `s > 0`. -/
private theorem norm_kernelNear_rpow {s : ℝ} (hs : 0 < s) (z : ℂ) :
    ‖kernelNear z‖ ^ s =
      (ball (0 : ℂ) 1).indicator (fun z => (2 * Real.pi) ^ (-s) * ‖z‖ ^ (-s)) z := by
  have hpi : 0 < 2 * Real.pi := by positivity
  by_cases hz : z ∈ ball (0 : ℂ) 1
  · rw [indicator_of_mem hz, kernelNear, indicator_of_mem hz, norm_biotSavartKernel',
      Real.inv_rpow (by positivity), Real.mul_rpow hpi.le (norm_nonneg _),
      Real.rpow_neg hpi.le, Real.rpow_neg (norm_nonneg _), mul_inv]
  · rw [indicator_of_notMem hz, kernelNear, indicator_of_notMem hz, norm_zero,
      Real.zero_rpow hs.ne']

private theorem integrable_norm_kernelNear_rpow {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    Integrable (fun z => ‖kernelNear z‖ ^ s) := by
  simp_rw [norm_kernelNear_rpow hs0]
  rw [integrable_indicator_iff measurableSet_ball]
  exact (Polar.integrableOn_ball_norm_rpow (by linarith) 1).const_mul _

/-- `K_near ∈ L^s(ℝ²)` for `s ∈ [1, 2)` (`02_prelim.tex:135-137`). -/
theorem memLp_kernelNear {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s < 2) :
    MemLp kernelNear (ENNReal.ofReal s) volume := by
  have hs0 : 0 < s := by linarith
  rw [← integrable_norm_rpow_iff measurable_kernelNear.aestronglyMeasurable
    (by simpa using hs0) ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hs0.le]
  exact integrable_norm_kernelNear_rpow hs0 hs2

/-- `‖K_near‖_{L^s}^s = (2π)^{1-s}/(2-s)` for `s ∈ [1, 2)` (`02_prelim.tex:138-139`). -/
theorem integral_norm_kernelNear_rpow {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s < 2) :
    ∫ z, ‖kernelNear z‖ ^ s = (2 * Real.pi) ^ (1 - s) / (2 - s) := by
  have hs0 : 0 < s := by linarith
  have hpi : 0 < 2 * Real.pi := by positivity
  simp_rw [norm_kernelNear_rpow hs0]
  rw [integral_indicator measurableSet_ball, integral_const_mul,
    Polar.setIntegral_ball_norm_rpow (by linarith) zero_le_one, Real.one_rpow,
    show (1 : ℝ) - s = -s + 1 by ring, Real.rpow_add hpi, Real.rpow_one,
    show -s + 2 = 2 - s by ring]
  ring

/-- `|K_far(z)| ≤ min{1, |z|⁻¹}/(2π)` for every `z ∈ ℝ²` (`02_prelim.tex:138-139`). -/
theorem norm_kernelFar_le (z : ℂ) : ‖kernelFar z‖ ≤ min 1 ‖z‖⁻¹ / (2 * Real.pi) := by
  have hpi : 0 < 2 * Real.pi := by positivity
  rcases lt_or_ge ‖z‖ 1 with hz | hz
  · rw [kernelFar_of_norm_lt hz, norm_zero]
    exact div_nonneg (le_min zero_le_one (inv_nonneg.mpr (norm_nonneg _))) hpi.le
  · rw [kernelFar_of_one_le_norm hz, norm_biotSavartKernel',
      min_eq_right (inv_le_one_of_one_le₀ hz), mul_inv, div_eq_mul_inv, mul_comm]

/-- Consequence: `K_far ∈ L^∞` with `‖K_far‖_{L^∞} ≤ 1/(2π)`. -/
theorem memLp_kernelFar_top :
    MemLp kernelFar ⊤ volume ∧ eLpNorm kernelFar ⊤ volume ≤ ENNReal.ofReal (1 / (2 * Real.pi)) := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have hb : ∀ᵐ z ∂(volume : Measure ℂ), ‖kernelFar z‖ ≤ 1 / (2 * Real.pi) :=
    Filter.Eventually.of_forall fun z =>
      (norm_kernelFar_le z).trans (div_le_div_of_nonneg_right (min_le_left _ _) hpi.le)
  refine ⟨memLp_top_of_bound measurable_kernelFar.aestronglyMeasurable _ hb, ?_⟩
  rw [eLpNorm_exponent_top]
  exact eLpNormEssSup_le_of_ae_bound hb

end NonUniqueEuler.BS
