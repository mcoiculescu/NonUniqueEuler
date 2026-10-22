import NonUniqueEuler.H.Infra.AngularFourier.Parseval.Circle
import NonUniqueEuler.I.Infra.Polar.Fubini
import NonUniqueEuler.Defs.Infra.Sobolev

/-!
# Helper for `P/Infra/AngularFourier/Parseval`: Parseval in polar coordinates

* `ae_circle_eq_of_ae_eq`: an a.e. equality on `ℂ` restricts to a.e. equality on almost every
  circle;
* `ae_angularSector_eq`, `aestronglyMeasurable_angularSector`: consequences for the sectors;
* `lintegral_enorm_sq_eq_tsum`: `∫ |g|² = ∑_ℓ 2π ∫₀^∞ |g_ℓ(r)|² r dr` in `ℝ≥0∞`, by Tonelli in
  polar coordinates (`Polar.lintegral_eq_lintegral_Ioi_circle`), Parseval on almost every circle
  (`ParsevalH.lintegral_circle_eq_tsum`) and monotone convergence (`lintegral_tsum`);
* `hasSum_angularSector_sq'`: the real form, for `g ∈ L²`.
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace NonUniqueEuler.Ang.ParsevalH

/-- `x ↦ φ (r e^{iθ})` is measurable in `(r, θ)`. -/
theorem measurable_comp_circleMap {β : Type*} [MeasurableSpace β] {φ : ℂ → β}
    (hφ : Measurable φ) : Measurable (fun p : ℝ × ℝ => φ (circleMap 0 p.1 p.2)) :=
  hφ.comp continuous_circleMap_zero_uncurried.measurable

/-- The inner circle integral of a measurable function is measurable in the radius. -/
theorem measurable_lintegral_circle {φ : ℂ → ℝ≥0∞} (hφ : Measurable φ) :
    Measurable (fun r : ℝ => ∫⁻ θ in Ioc 0 (2 * π), φ (circleMap 0 r θ)) :=
  (measurable_comp_circleMap hφ).lintegral_prod_right'

/-- An a.e. equality on `ℂ` gives a.e. equality on almost every circle. -/
theorem ae_circle_eq_of_ae_eq {f f' : ℂ → ℂ} (h : f =ᵐ[volume] f') :
    ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))),
      (fun θ : ℝ => f (circleMap 0 r θ)) =ᵐ[volume.restrict (Ioc 0 (2 * π))]
        fun θ => f' (circleMap 0 r θ) := by
  set N : Set ℂ := toMeasurable volume {x | f x ≠ f' x} with hN
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : volume N = 0 := by
    rw [hN, measure_toMeasurable]
    exact ae_iff.1 h
  set φ : ℂ → ℝ≥0∞ := N.indicator 1 with hφ
  have hφm : Measurable φ := measurable_one.indicator hNm
  have hpol := Polar.lintegral_eq_lintegral_Ioi_circle hφm
  rw [hφ, lintegral_indicator_one hNm, hN0] at hpol
  have hmeas : Measurable (fun r : ℝ => ENNReal.ofReal r *
      ∫⁻ θ in Ioc 0 (2 * π), φ (circleMap 0 r θ)) :=
    ENNReal.measurable_ofReal.mul (measurable_lintegral_circle hφm)
  have h0 := (lintegral_eq_zero_iff hmeas).1 hpol.symm
  filter_upwards [h0, ae_restrict_mem measurableSet_Ioi] with r hr hrpos
  have hr' : ∫⁻ θ in Ioc 0 (2 * π), φ (circleMap 0 r θ) = 0 := by
    have := (mul_eq_zero.1 hr)
    rcases this with h1 | h1
    · exact absurd h1 (by simpa using hrpos)
    · exact h1
  have h2 := (lintegral_eq_zero_iff ((hφm.comp
    (continuous_circleMap 0 r).measurable))).1 hr'
  filter_upwards [h2] with θ hθ
  have hθN : circleMap 0 r θ ∉ N := by
    intro hmem
    have : φ (circleMap 0 r θ) = 1 := by simp [hφ, hmem]
    simp only [Function.comp_apply, Pi.zero_apply] at hθ
    rw [this] at hθ
    exact one_ne_zero hθ
  by_contra hne
  exact hθN (subset_toMeasurable _ _ hne)

/-- The sectors of a.e. equal functions agree for almost every radius. -/
theorem ae_angularSector_eq {f f' : ℂ → ℂ} (h : f =ᵐ[volume] f') :
    ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ ℓ : ℤ, Polar.angularSector f ℓ r = Polar.angularSector f' ℓ r := by
  filter_upwards [ae_circle_eq_of_ae_eq h] with r hr ℓ
  simp only [Polar.angularSector, intervalIntegral.integral_of_le two_pi_pos.le]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hr] with θ hθ
  simp only [circleMap_zero] at hθ
  rw [hθ]

/-- For `g` a.e. strongly measurable, `r ↦ g_ℓ(r)` is a.e. strongly measurable on `(0, ∞)`. -/
theorem aestronglyMeasurable_angularSector {g : ℂ → ℂ} (hg : AEStronglyMeasurable g volume)
    (ℓ : ℤ) :
    AEStronglyMeasurable (Polar.angularSector g ℓ) (volume.restrict (Ioi (0 : ℝ))) := by
  refine (stronglyMeasurable_angularSector hg.stronglyMeasurable_mk ℓ).aestronglyMeasurable.congr
    ?_
  filter_upwards [ae_angularSector_eq hg.ae_eq_mk] with r hr
  exact (hr ℓ).symm

/-- `eLpNorm f 2 μ ^ 2 = ∫⁻ ‖f‖ₑ²`. -/
theorem eLpNorm_two_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : α → ℂ) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := f) (p := (2 : NNReal)) two_ne_zero
  simpa [ENNReal.rpow_two] using h

/-- **Parseval in polar coordinates** (`ℝ≥0∞` form), for strongly measurable `g ∈ L²`. -/
theorem lintegral_enorm_sq_eq_tsum {g : ℂ → ℂ} (hg : StronglyMeasurable g)
    (hfin : ∫⁻ x, ‖g x‖ₑ ^ 2 ≠ ∞) :
    ∫⁻ x, ‖g x‖ₑ ^ 2 = ∑' ℓ : ℤ,
      ENNReal.ofReal (2 * π) * ∫⁻ r in Ioi 0, ‖Polar.angularSector g ℓ r‖ₑ ^ 2 * ENNReal.ofReal r := by
  have hφm : Measurable (fun x => ‖g x‖ₑ ^ 2) := hg.measurable.enorm.pow_const 2
  have hpol := Polar.lintegral_eq_lintegral_Ioi_circle hφm
  set J : ℝ → ℝ≥0∞ := fun r => ∫⁻ θ in Ioc 0 (2 * π), ‖g (circleMap 0 r θ)‖ₑ ^ 2 with hJ
  have hJm : Measurable J := measurable_lintegral_circle hφm
  have hfin' : ∫⁻ r in Ioi 0, ENNReal.ofReal r * J r ≠ ∞ := by
    rw [← hpol]; exact hfin
  have hlt := ae_lt_top (ENNReal.measurable_ofReal.mul hJm) hfin'
  have hJ_eq : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), ENNReal.ofReal r * J r =
      ∑' ℓ : ℤ, ENNReal.ofReal (2 * π) *
        (‖Polar.angularSector g ℓ r‖ₑ ^ 2 * ENNReal.ofReal r) := by
    filter_upwards [hlt, ae_restrict_mem measurableSet_Ioi] with r hr hrpos
    have hJfin : J r ≠ ∞ := by
      intro htop
      simp only [Pi.mul_apply] at hr
      rw [htop, ENNReal.mul_top (by simpa using hrpos)] at hr
      exact lt_irrefl _ hr
    have hm : AEStronglyMeasurable (fun θ : ℝ => g (circleMap 0 r θ))
        (volume.restrict (Ioc 0 (2 * π))) :=
      (hg.comp_measurable (continuous_circleMap 0 r).measurable).aestronglyMeasurable
    rw [hJ]
    simp only
    rw [lintegral_circle_eq_tsum hm hJfin, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun ℓ => ?_
    ring
  rw [hpol, lintegral_congr_ae hJ_eq, lintegral_tsum]
  · refine tsum_congr fun ℓ => ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  · intro ℓ
    exact (((stronglyMeasurable_angularSector hg ℓ).measurable.enorm.pow_const 2).mul
      ENNReal.measurable_ofReal).const_mul _ |>.aemeasurable

/-- `2π ∫₀^∞ |h|² r dr` as the real part of the `ℝ≥0∞` integral. -/
theorem integral_sq_mul_eq_toReal {h : ℝ → ℂ}
    (hm : AEStronglyMeasurable h (volume.restrict (Ioi (0 : ℝ)))) :
    2 * π * ∫ r in Ioi 0, ‖h r‖ ^ 2 * r =
      (ENNReal.ofReal (2 * π) * ∫⁻ r in Ioi 0, ‖h r‖ₑ ^ 2 * ENNReal.ofReal r).toReal := by
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun r => ‖h r‖ ^ 2 * r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have : (0 : ℝ) < r := hr
    positivity
  have hmeas : AEStronglyMeasurable (fun r => ‖h r‖ ^ 2 * r) (volume.restrict (Ioi (0 : ℝ))) :=
    (hm.norm.pow 2).mul measurable_id.aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal two_pi_pos.le]
  congr 2
  refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have : (0 : ℝ) ≤ r := le_of_lt hr
  rw [ENNReal.ofReal_mul (by positivity), ← enorm_norm_sq, Real.enorm_eq_ofReal (by positivity)]

/-- **Parseval in polar coordinates**, real form, for strongly measurable `g ∈ L²`. -/
theorem hasSum_angularSector_sq_of_stronglyMeasurable {g : ℂ → ℂ} (hg : StronglyMeasurable g)
    (hL2 : MemLp g 2 volume) :
    HasSum (fun ℓ : ℤ => 2 * π * ∫ r in Ioi 0, ‖Polar.angularSector g ℓ r‖ ^ 2 * r)
      (Sob.l2 g ^ 2) := by
  have hfin : ∫⁻ x, ‖g x‖ₑ ^ 2 ≠ ∞ := by
    rw [← eLpNorm_two_sq]
    exact ENNReal.pow_ne_top hL2.2.ne
  have hsum := lintegral_enorm_sq_eq_tsum hg hfin
  set T : ℤ → ℝ≥0∞ := fun ℓ =>
    ENNReal.ofReal (2 * π) * ∫⁻ r in Ioi 0, ‖Polar.angularSector g ℓ r‖ₑ ^ 2 * ENNReal.ofReal r
    with hT
  have hTfin : ∑' ℓ, T ℓ ≠ ∞ := by rw [← hsum]; exact hfin
  have hl2 : Sob.l2 g ^ 2 = ∑' ℓ, (T ℓ).toReal := by
    rw [Sob.l2, ← ENNReal.toReal_pow, eLpNorm_two_sq, hsum,
      ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top hTfin)]
  rw [hl2]
  convert ENNReal.hasSum_toReal hTfin using 1
  funext ℓ
  exact integral_sq_mul_eq_toReal
    (stronglyMeasurable_angularSector hg ℓ).aestronglyMeasurable

end NonUniqueEuler.Ang.ParsevalH
