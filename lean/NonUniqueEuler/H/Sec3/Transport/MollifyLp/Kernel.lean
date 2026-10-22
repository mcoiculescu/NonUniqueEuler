import NonUniqueEuler.Defs.Sec3.Auxiliary
import NonUniqueEuler.Defs.Infra.ConvMinkowski
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Helper for `P/Sec3/Transport/MollifyLp`: the rescaled kernel `ρ_ε` and the mollification

Basic facts on `ρ_ε = scaled ρ ε` and on `g ⋆ ρ_ε = mollify ρ ε g`
(`03_compactness.tex:27-30`), for a mollifier `ρ` (`IsMollifier`):

* `ρ_ε` is continuous, nonnegative, has compact support in `B_ε`, and `∫ ρ_ε = 1`
  (scaling `x ↦ ε⁻¹ x` in real dimension `2`, `Measure.integral_comp_inv_smul`);
* `mollify ρ ε g` is Mathlib's convolution `ρ_ε ⋆[lsmul ℝ ℝ] g` (`mollify_eq_convolution`), hence
  continuous for `g ∈ L¹_loc`, linear in `g`, and close to `g x₀` when `g` is close to `g x₀` on
  `B_ε(x₀)` (`dist_mollify_le`, from Mathlib's `dist_convolution_le`);
* `|g ⋆ ρ_ε| ≤ |ρ_ε| ⋆ |g|` (`enorm_mollify_le`, the majorant `Conv.convAbs`).

All lemmas are in the namespace `NonUniqueEuler.Weak.MollifyLpH` to avoid clashes.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal Convolution

namespace NonUniqueEuler.Weak.MollifyLpH

variable {ρ : ℂ → ℝ}

theorem scaled_eq_smul (ρ : ℂ → ℝ) (ε : ℝ) :
    scaled ρ ε = fun x => (ε ^ 2)⁻¹ * ρ (ε⁻¹ • x) := by
  funext x
  simp [scaled, Complex.real_smul, Complex.ofReal_inv]

theorem continuous_scaled (hρ : IsMollifier ρ) (ε : ℝ) : Continuous (scaled ρ ε) := by
  rw [scaled_eq_smul]
  exact continuous_const.mul (hρ.contDiff.continuous.comp (continuous_const_smul _))

theorem hasCompactSupport_scaled (hρ : IsMollifier ρ) {ε : ℝ} (hε : ε ≠ 0) :
    HasCompactSupport (scaled ρ ε) := by
  rw [scaled_eq_smul]
  refine (hρ.hasCompactSupport.comp_smul (inv_ne_zero hε)).mono fun x hx => ?_
  rw [Function.mem_support] at hx ⊢
  intro h
  exact hx (by rw [h, mul_zero])

theorem scaled_nonneg (hρ : IsMollifier ρ) (ε : ℝ) (x : ℂ) : 0 ≤ scaled ρ ε x :=
  mul_nonneg (inv_nonneg.2 (sq_nonneg ε)) (hρ.nonneg _)

theorem integrable_scaled (hρ : IsMollifier ρ) {ε : ℝ} (hε : ε ≠ 0) :
    Integrable (scaled ρ ε) volume :=
  (continuous_scaled hρ ε).integrable_of_hasCompactSupport (hasCompactSupport_scaled hρ hε)

/-- `∫ ρ_ε = 1`. -/
theorem integral_scaled (hρ : IsMollifier ρ) {ε : ℝ} (hε : ε ≠ 0) :
    ∫ x, scaled ρ ε x = 1 := by
  rw [scaled_eq_smul]
  simp only
  rw [integral_const_mul, Measure.integral_comp_inv_smul, Complex.finrank_real_complex,
    hρ.integral_eq_one, smul_eq_mul, mul_one, abs_of_nonneg (sq_nonneg ε)]
  exact inv_mul_cancel₀ (pow_ne_zero 2 hε)

/-- `supp ρ_ε ⊆ B_ε`. -/
theorem support_scaled_subset (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) :
    Function.support (scaled ρ ε) ⊆ ball (0 : ℂ) ε := by
  intro x hx
  rw [Function.mem_support, scaled_eq_smul] at hx
  have h1 : ε⁻¹ • x ∈ ball (0 : ℂ) 1 :=
    hρ.tsupport_subset (subset_tsupport _ (right_ne_zero_of_mul hx))
  rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hε.le)] at h1
  rw [mem_ball_zero_iff]
  rwa [inv_mul_lt_iff₀ hε, mul_one] at h1

/-- `‖ρ_ε‖₁ = 1`. -/
theorem lintegral_enorm_scaled (hρ : IsMollifier ρ) {ε : ℝ} (hε : ε ≠ 0) :
    ∫⁻ z, ‖scaled ρ ε z‖ₑ = 1 := by
  rw [← ofReal_integral_norm_eq_lintegral_enorm (integrable_scaled hρ hε)]
  simp_rw [Real.norm_of_nonneg (scaled_nonneg hρ ε _)]
  rw [integral_scaled hρ hε, ENNReal.ofReal_one]

/-- `g ⋆ ρ_ε = ρ_ε ⋆[lsmul] g` (Mathlib's convolution). -/
theorem mollify_eq_convolution (ρ : ℂ → ℝ) (ε : ℝ) (g : ℂ → ℝ) :
    mollify ρ ε g = scaled ρ ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g := by
  funext x
  rw [convolution_lsmul_swap]
  simp only [mollify, smul_eq_mul]
  congr 1
  funext y
  ring

/-- For `g ∈ L¹_loc`, the integrand of `mollify` is integrable at every point. -/
theorem integrable_mollify_integrand (hρ : IsMollifier ρ) {ε : ℝ} (hε : ε ≠ 0) {g : ℂ → ℝ}
    (hg : LocallyIntegrable g volume) (x : ℂ) :
    Integrable (fun y => g y * scaled ρ ε (x - y)) volume := by
  have h := (hasCompactSupport_scaled hρ hε).convolutionExists_right
    (ContinuousLinearMap.mul ℝ ℝ) hg (continuous_scaled hρ ε) x
  simpa only [ConvolutionExistsAt, ContinuousLinearMap.mul_apply'] using h

/-- For `g ∈ L¹_loc`, `g ⋆ ρ_ε` is continuous. -/
theorem continuous_mollify (hρ : IsMollifier ρ) {ε : ℝ} (hε : ε ≠ 0) {g : ℂ → ℝ}
    (hg : LocallyIntegrable g volume) : Continuous (mollify ρ ε g) := by
  rw [mollify_eq_convolution]
  exact (hasCompactSupport_scaled hρ hε).continuous_convolution_left _
    (continuous_scaled hρ ε) hg

/-- Linearity: `(g - h) ⋆ ρ_ε = g ⋆ ρ_ε - h ⋆ ρ_ε` for `g, h ∈ L¹_loc`. -/
theorem mollify_sub (hρ : IsMollifier ρ) {ε : ℝ} (hε : ε ≠ 0) {g h : ℂ → ℝ}
    (hg : LocallyIntegrable g volume) (hh : LocallyIntegrable h volume) (x : ℂ) :
    mollify ρ ε (fun y => g y - h y) x = mollify ρ ε g x - mollify ρ ε h x := by
  simp only [mollify, sub_mul]
  exact integral_sub (integrable_mollify_integrand hρ hε hg x)
    (integrable_mollify_integrand hρ hε hh x)

/-- If `g` is `δ`-close to `z₀` on `B_ε(x₀)`, then so is `(g ⋆ ρ_ε)(x₀)`. -/
theorem dist_mollify_le (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) {g : ℂ → ℝ}
    (hmg : AEStronglyMeasurable g volume) {x₀ : ℂ} {z₀ δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ y ∈ ball x₀ ε, dist (g y) z₀ ≤ δ) : dist (mollify ρ ε g x₀) z₀ ≤ δ := by
  rw [mollify_eq_convolution]
  exact dist_convolution_le hδ (support_scaled_subset hρ hε) (scaled_nonneg hρ ε)
    (integral_scaled hρ hε.ne') hmg hclose

/-- `|g ⋆ ρ_ε| ≤ |ρ_ε| ⋆ |g|` pointwise. -/
theorem enorm_mollify_le (ρ : ℂ → ℝ) (ε : ℝ) (g : ℂ → ℝ) (x : ℂ) :
    ‖mollify ρ ε g x‖ₑ ≤ Conv.convAbs (scaled ρ ε) g x := by
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  unfold Conv.convAbs
  refine lintegral_congr fun y => ?_
  rw [enorm_mul, mul_comm]

end NonUniqueEuler.Weak.MollifyLpH
