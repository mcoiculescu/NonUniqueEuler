import NonUniqueEuler.Defs.Infra.Polar
import NonUniqueEuler.Defs.Infra.Multipole
import NonUniqueEuler.I.Infra.Polar.Fubini
import NonUniqueEuler.I.Infra.Polar.Radial
import NonUniqueEuler.I.Infra.Polar.AngularAverage
import NonUniqueEuler.I.Infra.Polar.Power
import NonUniqueEuler.I.Infra.Multipole.Geometric
import NonUniqueEuler.I.Infra.ConvMinkowski.Measurable
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Proof: Newton's theorem for radial vorticities (I-POLAR)

Proof of `NonUniqueEuler/I/Infra/Polar/Newton.lean`: same declarations, same statements.
The argument is the manuscript's (`03_compactness.tex:840-857`, first paragraph of the proof of
`lem:radial-stationary`).

* `circ_comp_norm`: `setIntegral_ball_comp_norm` (`I/Infra/Polar/Radial.lean`).
* Kernel split (private `ae_integrable_kernel_mul`): `K = K 1_{B_1} + K 1_{B_1ᶜ}` with
  `‖K z‖ = (2π)⁻¹ ‖z‖⁻¹`, so `K 1_{B_1} ∈ L¹` (`integrableOn_ball_norm_rpow`, `s = -1`) and
  `‖K 1_{B_1ᶜ}‖ ≤ (2π)⁻¹`; then `Conv.ae_integrable_conv_of_split` gives the absolute convergence
  of `∫ K(x - y) h(y) dy` for a.e. `x` (`lem:BS-basic`(e)).
* Cauchy transform (private `cauchyTransform_comp_norm`): for every `x` at which
  `w ↦ h₀(|w|) (x - w)⁻¹` is integrable, polar Fubini (`integral_eq_integral_Ioi_intervalIntegral`)
  and the angular means `intervalIntegral_inv_sub_circleMap` (`2π/x` for `s < |x|`, `0` for
  `s > |x|`; the radius `s = |x|` is a null set) give `C[h](x) = Circ_h(|x|) x⁻¹`.
* `velocity_comp_norm`: `velocity_eq_conj_cauchyTransform` and
  `conj ((2πi)⁻¹ x⁻¹) = K(x)` (`conj_biotSavartKernel`).
* `velocity_of_isRadial`: `h =ᵐ angAvg h` (`ae_eq_angAvg_of_isRadial`), and `angAvg h` is
  `h₀(‖·‖)` with `h₀ = circleAverage h 0` by definition; `velocity` and `circ` see `h` only up
  to a.e. equality.
-/

noncomputable section

open MeasureTheory Set Metric Real ComplexConjugate

namespace NonUniqueEuler.Polar

/-- `Circ_h(r) = 2π ∫₀^r s h₀(s) ds` for `h = h₀(‖·‖)`. -/
theorem circ_comp_norm (h₀ : ℝ → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    circ (fun y => h₀ ‖y‖) r = 2 * π * ∫ s in (0 : ℝ)..r, s * h₀ s := by
  rw [circ, setIntegral_ball_comp_norm h₀ hr]
  simp only [smul_eq_mul]

/-! ### The Biot–Savart kernel: modulus, measurability, split -/

/-- `‖K z‖ = (2π)⁻¹ ‖z‖⁻¹` (both sides vanish at `z = 0`). -/
private theorem norm_biotSavartKernel (z : ℂ) :
    ‖biotSavartKernel z‖ = (2 * π)⁻¹ * ‖z‖ ^ (-1 : ℝ) := by
  rw [Real.rpow_neg_one]
  rcases eq_or_ne z 0 with rfl | hz
  · simp [biotSavartKernel]
  · have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
    simp only [biotSavartKernel, norm_div, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity)]
    field_simp
    rw [abs_of_pos Real.pi_pos, abs_of_nonneg (by positivity)]
    ring

private theorem measurable_biotSavartKernel : Measurable biotSavartKernel := by
  unfold biotSavartKernel
  fun_prop

/-- Absolute convergence of the Biot–Savart integral for a.e. `x`, for `g ∈ L¹`
(`lem:BS-basic`(e)), via the split `K = K 1_{B_1} + K 1_{B_1ᶜ}`. -/
private theorem ae_integrable_kernel_mul {g : ℂ → ℝ} (hg : Integrable g) :
    ∀ᵐ x : ℂ, Integrable (fun y => biotSavartKernel (x - y) * (g y : ℂ)) := by
  have hKm := measurable_biotSavartKernel
  refine Conv.ae_integrable_conv_of_split (K₁ := (ball (0 : ℂ) 1).indicator biotSavartKernel)
    (K₂ := (ball (0 : ℂ) 1)ᶜ.indicator biotSavartKernel) hKm.aestronglyMeasurable ?_ ?_ ?_
    (memLp_one_iff_integrable.mpr hg)
  · rw [memLp_one_iff_integrable, integrable_indicator_iff measurableSet_ball]
    refine Integrable.mono'
      ((integrableOn_ball_norm_rpow (s := -1) (by norm_num) 1).const_mul (2 * π)⁻¹)
      hKm.aestronglyMeasurable.restrict (Filter.Eventually.of_forall fun z => ?_)
    rw [norm_biotSavartKernel]
  · refine memLp_top_of_bound (hKm.aestronglyMeasurable.indicator measurableSet_ball.compl)
      (2 * π)⁻¹ (Filter.Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ (ball (0 : ℂ) 1)ᶜ
    · rw [indicator_of_mem hz, norm_biotSavartKernel]
      have h1 : 1 ≤ ‖z‖ := by simpa using hz
      have h2 : ‖z‖ ^ (-1 : ℝ) ≤ 1 := by
        rw [Real.rpow_neg_one]
        exact inv_le_one_of_one_le₀ h1
      have h3 : 0 ≤ (2 * π)⁻¹ := by positivity
      calc (2 * π)⁻¹ * ‖z‖ ^ (-1 : ℝ) ≤ (2 * π)⁻¹ * 1 := mul_le_mul_of_nonneg_left h2 h3
        _ = (2 * π)⁻¹ := mul_one _
    · rw [indicator_of_notMem hz, norm_zero]
      positivity
  · intro z
    have hsum := congrFun (indicator_self_add_compl (ball (0 : ℂ) 1) biotSavartKernel) z
    calc ‖biotSavartKernel z‖
        = ‖(ball (0 : ℂ) 1).indicator biotSavartKernel z +
            (ball (0 : ℂ) 1)ᶜ.indicator biotSavartKernel z‖ := by
          rw [← Pi.add_apply, hsum]
      _ ≤ _ := norm_add_le _ _

/-- The Cauchy integrand `g(w) (x - w)⁻¹ = 2πi · conj (K(x - w) g(w))` is integrable when the
Biot–Savart integrand is. -/
private theorem integrable_cauchy_of_integrable_kernel {g : ℂ → ℝ} {x : ℂ}
    (hx : Integrable (fun y => biotSavartKernel (x - y) * (g y : ℂ))) :
    Integrable (fun w => (g w : ℂ) * (x - w)⁻¹) := by
  have h2 : Integrable (fun w =>
      (2 * π * Complex.I) * conj (biotSavartKernel (x - w) * (g w : ℂ))) := by
    have := (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hx
    exact this.const_mul _
  refine h2.congr (Filter.Eventually.of_forall fun w => ?_)
  have hne : (2 * π * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  simp only [map_mul, Multipole.conj_biotSavartKernel, Complex.conj_ofReal]
  rw [mul_inv (2 * π * Complex.I : ℂ) (x - w)]
  rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hne, one_mul, mul_comm]

/-! ### The Cauchy transform of a radial function -/

/-- For every `x` at which the Cauchy integrand is integrable,
`∫ h₀(|w|) (x - w)⁻¹ dw = Circ_h(|x|) x⁻¹` (`03_compactness.tex:845-857`). -/
private theorem cauchyTransform_comp_norm {h₀ : ℝ → ℝ} (x : ℂ)
    (hint : Integrable (fun w : ℂ => ((h₀ ‖w‖ : ℝ) : ℂ) * (x - w)⁻¹)) :
    Multipole.cauchyTransform (fun w => ((h₀ ‖w‖ : ℝ) : ℂ)) x =
      (circ (fun y => h₀ ‖y‖) ‖x‖ : ℂ) * x⁻¹ := by
  rw [Multipole.cauchyTransform, integral_eq_integral_Ioi_intervalIntegral hint]
  have hae : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))),
      r • (∫ θ in (0 : ℝ)..2 * π, ((h₀ ‖circleMap 0 r θ‖ : ℝ) : ℂ) * (x - circleMap 0 r θ)⁻¹) =
      (Iio ‖x‖).indicator (fun r => ((2 * π * (r * h₀ r) : ℝ) : ℂ) * x⁻¹) r := by
    filter_upwards [(volume.restrict (Ioi (0 : ℝ))).ae_ne ‖x‖,
      ae_restrict_mem measurableSet_Ioi] with r hr hpos
    have hnorm : ∀ θ, ‖circleMap 0 r θ‖ = r := fun θ => by
      rw [norm_circleMap_zero, abs_of_pos (mem_Ioi.mp hpos)]
    simp_rw [hnorm]
    rw [intervalIntegral.integral_const_mul,
      Multipole.intervalIntegral_inv_sub_circleMap (le_of_lt (mem_Ioi.mp hpos)) hr]
    by_cases hlt : r < ‖x‖
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hlt), indicator_of_mem (mem_Iio.mpr hlt), Complex.real_smul]
      push_cast
      ring
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hlt), indicator_of_notMem (by simpa using hlt), mul_zero, smul_zero]
  rw [integral_congr_ae hae, integral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi, integral_mul_const,
    integral_complex_ofReal, circ_comp_norm h₀ (norm_nonneg x), intervalIntegral.integral_of_le
      (norm_nonneg x), integral_Ioc_eq_integral_Ioo, integral_const_mul]

/-! ### Newton's theorem -/

/-- Newton's theorem for `h = h₀(‖·‖) ∈ L¹`: `K ⋆ h (x) = Circ_h(|x|) K(x)` for a.e. `x`. -/
theorem velocity_comp_norm {h₀ : ℝ → ℝ} (hint : Integrable (fun y : ℂ => h₀ ‖y‖)) :
    ∀ᵐ x : ℂ, velocity (fun y => h₀ ‖y‖) x =
      (circ (fun y => h₀ ‖y‖) ‖x‖ : ℂ) * biotSavartKernel x := by
  filter_upwards [ae_integrable_kernel_mul hint] with x hx
  rw [Multipole.velocity_eq_conj_cauchyTransform,
    cauchyTransform_comp_norm x (integrable_cauchy_of_integrable_kernel hx),
    ← Complex.conj_conj (biotSavartKernel x), Multipole.conj_biotSavartKernel]
  rw [mul_inv (2 * π * Complex.I : ℂ) x]
  simp only [map_mul, Complex.conj_ofReal]
  ring

/-- Newton's theorem for (a.e.) radial `h ∈ L¹`: `K ⋆ h (x) = Circ_h(|x|) K(x)` for a.e. `x`
(`03_compactness.tex:834`). -/
theorem velocity_of_isRadial {h : ℂ → ℝ} (hrad : IsRadial h) (hint : Integrable h) :
    ∀ᵐ x : ℂ, velocity h x = (circ h ‖x‖ : ℂ) * biotSavartKernel x := by
  have hae : h =ᵐ[volume] angAvg h := ae_eq_angAvg_of_isRadial hrad hint.aestronglyMeasurable
  have hdef : angAvg h = fun y => (fun r : ℝ => Real.circleAverage h 0 r) ‖y‖ := rfl
  rw [hdef] at hae
  have hint' : Integrable (fun y : ℂ => (fun r : ℝ => Real.circleAverage h 0 r) ‖y‖) :=
    hint.congr hae
  have hv : ∀ x, velocity h x =
      velocity (fun y => (fun r : ℝ => Real.circleAverage h 0 r) ‖y‖) x := fun x =>
    integral_congr_ae (hae.mono fun y hy => by simp only [hy])
  have hc : ∀ r, circ h r = circ (fun y => (fun r : ℝ => Real.circleAverage h 0 r) ‖y‖) r :=
    fun r => integral_congr_ae (ae_restrict_of_ae hae)
  filter_upwards [velocity_comp_norm hint'] with x hx
  rw [hv, hc, hx]

end NonUniqueEuler.Polar
