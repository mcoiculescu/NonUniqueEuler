import NonUniqueEuler.Defs.Infra.AngularFourier
import NonUniqueEuler.I.Infra.Polar.Fubini
import NonUniqueEuler.I.Infra.AngularFourier.Sector
import NonUniqueEuler.I.Infra.AngularFourier.SectorL2
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Proof (step of `P/Infra/AngularFourier/Derivatives`): profiles of `L²` functions supported in an annulus

Proof of `I/Infra/AngularFourier/Derivatives/ProfileL2.lean` (same declaration, statement copied
verbatim). For `g ∈ L²(ℂ)` vanishing a.e. outside `{ρ₋ ≤ |x| ≤ ρ₊}`, `0 < ρ₋`, the profile
`g_ℓ = Polar.angularSector g ℓ` lies in `L²((0, ∞), dr)` and vanishes a.e. outside `[ρ₋, ρ₊]`.

Steps (as in the docstring of the I file).
1. `ProfileL2Aux.angularSector_congr_ae`: a.e. congruence on circles, by Tonelli in polar
   coordinates (`Polar.lintegral_eq_lintegral_Ioi_circle`) applied to the indicator of a
   measurable null set containing `{g ≠ g'}`.
2. Vanishing: step 1 with `g' = 1_K g`.
3. Measurability: a strongly measurable representative and
   `StronglyMeasurable.integral_prod_right'`.
4. `L²`: `Ang.memLp_sectorProj`, `Ang.sectorProj_eq_angularSector`, `Ang.memLp_ofProfile_iff`,
   then `|g_ℓ(r)|² ≤ ρ₋⁻¹ |g_ℓ(r)|² r` a.e. on `(0,∞)`.
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace NonUniqueEuler.Ang

namespace ProfileL2Aux

/-- The polar parametrisation `(r, θ) ↦ r e^{iθ}` is continuous. -/
theorem continuous_polarParam :
    Continuous fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I) := by
  fun_prop

/-- Step 1: a.e. equal functions on `ℂ` have a.e. equal angular sectors on `(0, ∞)`. -/
theorem angularSector_congr_ae {g g' : ℂ → ℂ} (h : g =ᵐ[volume] g') (ℓ : ℤ) :
    Polar.angularSector g ℓ =ᵐ[volume.restrict (Ioi 0)] Polar.angularSector g' ℓ := by
  have h0 : volume {x | ¬ g x = g' x} = 0 := ae_iff.1 h
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null h0
  -- Tonelli in polar coordinates applied to `1_N`.
  have hmeasN : Measurable (N.indicator (1 : ℂ → ℝ≥0∞)) := measurable_one.indicator hNm
  have hT := Polar.lintegral_eq_lintegral_Ioi_circle hmeasN
  rw [lintegral_indicator_one hNm, hN0] at hT
  have hFm : Measurable fun p : ℝ × ℝ => N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 p.1 p.2) := by
    refine hmeasN.comp ?_
    have : (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) =
        fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I) := by
      funext p; simp [circleMap]
    rw [this]
    exact continuous_polarParam.measurable
  have hGm : Measurable fun r : ℝ => ENNReal.ofReal r *
      ∫⁻ θ in Ioc (0 : ℝ) (2 * π), N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 r θ) :=
    ENNReal.measurable_ofReal.mul (hFm.lintegral_prod_right' (ν := volume.restrict (Ioc 0 (2 * π))))
  have hae := (lintegral_eq_zero_iff hGm).1 hT.symm
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioi] with r hr hrpos
  have hrpos' : (0 : ℝ) < r := hrpos
  have hr' : ∫⁻ θ in Ioc (0 : ℝ) (2 * π), N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 r θ) = 0 := by
    have hr2 : ENNReal.ofReal r *
        ∫⁻ θ in Ioc (0 : ℝ) (2 * π), N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 r θ) = 0 := hr
    rcases mul_eq_zero.1 hr2 with h1 | h1
    · exact absurd h1 (ENNReal.ofReal_pos.2 hrpos').ne'
    · exact h1
  have hθm : Measurable fun θ : ℝ => N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 r θ) :=
    hFm.comp (measurable_const.prodMk measurable_id)
  have hθ := (lintegral_eq_zero_iff hθm).1 hr'
  unfold Polar.angularSector
  congr 1
  rw [intervalIntegral.integral_of_le (by positivity), intervalIntegral.integral_of_le (by positivity)]
  refine integral_congr_ae ?_
  filter_upwards [hθ] with θ hθ'
  have hnot : circleMap 0 r θ ∉ N := by
    intro hmem
    have : N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 r θ) = 1 := indicator_of_mem hmem _
    simp [this] at hθ'
  have hcm : circleMap 0 r θ = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    simp [circleMap]
  rw [hcm] at hnot
  have heq : g ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
      g' ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
    by_contra hne
    exact hnot (hNsub hne)
  simp only [heq]

/-- Step 3: the angular sector of a strongly measurable function is strongly measurable. -/
theorem stronglyMeasurable_angularSector {g : ℂ → ℂ} (hg : StronglyMeasurable g) (ℓ : ℤ) :
    StronglyMeasurable (Polar.angularSector g ℓ) := by
  set F : ℝ × ℝ → ℂ := fun p =>
    g ((p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)) *
      Complex.exp (-((ℓ : ℂ) * p.2 * Complex.I)) with hFdef
  have hF : StronglyMeasurable F := by
    refine (hg.comp_measurable continuous_polarParam.measurable).mul ?_
    exact Continuous.stronglyMeasurable (by fun_prop)
  have hI := hF.integral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) (2 * π)))
  have hfun : Polar.angularSector g ℓ =
      fun r => (2 * π : ℂ)⁻¹ * ∫ θ, F (r, θ) ∂(volume.restrict (Ioc (0 : ℝ) (2 * π))) := by
    funext r
    unfold Polar.angularSector
    rw [intervalIntegral.integral_of_le (by positivity)]
  rw [hfun]
  exact stronglyMeasurable_const.mul hI

/-- Step 3 for `L²` (or merely a.e. strongly measurable) functions. -/
theorem aestronglyMeasurable_angularSector {g : ℂ → ℂ} (hg : AEStronglyMeasurable g volume)
    (ℓ : ℤ) : AEStronglyMeasurable (Polar.angularSector g ℓ) (volume.restrict (Ioi 0)) :=
  (stronglyMeasurable_angularSector hg.stronglyMeasurable_mk ℓ).aestronglyMeasurable.congr
    (angularSector_congr_ae hg.ae_eq_mk ℓ).symm

/-- Step 2: the profile vanishes a.e. on `(0, ∞) \ [ρ₋, ρ₊]`. -/
theorem ae_angularSector_eq_zero {ρm ρp : ℝ} {g : ℂ → ℂ}
    (hgK : ∀ᵐ x, ¬ (ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp) → g x = 0) (ℓ : ℤ) :
    ∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc ρm ρp → Polar.angularSector g ℓ r = 0 := by
  set K : Set ℂ := {x | ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp} with hKdef
  have hgg : g =ᵐ[volume] K.indicator g := by
    filter_upwards [hgK] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK]
    · rw [indicator_of_notMem hxK, hx hxK]
  filter_upwards [angularSector_congr_ae hgg ℓ, ae_restrict_mem measurableSet_Ioi] with r hr hrpos
  intro hrK
  have hrpos' : (0 : ℝ) < r := hrpos
  rw [hr]
  unfold Polar.angularSector
  have hzero : ∀ θ : ℝ, K.indicator g ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = 0 := by
    intro θ
    apply indicator_of_notMem
    have hn : ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = r := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg hrpos'.le]
    simp only [hKdef, mem_ofPred_eq, hn]
    exact hrK
  simp [hzero]

end ProfileL2Aux

open ProfileL2Aux in
/-- The profile of an `L²` function supported in `{ρ₋ ≤ |x| ≤ ρ₊}` is in `L²((0,∞), dr)` and
vanishes a.e. outside `[ρ₋, ρ₊]`. -/
theorem memLp_angularSector_of_support {ρm ρp : ℝ} (hρm : 0 < ρm) {g : ℂ → ℂ}
    (hg : MemLp g 2 volume) (hgK : ∀ᵐ x, ¬ (ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp) → g x = 0) (ℓ : ℤ) :
    MemLp (Polar.angularSector g ℓ) 2 (volume.restrict (Ioi 0)) ∧
      ∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc ρm ρp → Polar.angularSector g ℓ r = 0 := by
  have hvan := ae_angularSector_eq_zero hgK ℓ
  refine ⟨?_, hvan⟩
  have hmeas := aestronglyMeasurable_angularSector hg.1 ℓ
  -- `P_ℓ g = g_ℓ(|x|) e^{iℓθ}` a.e., hence `ofProfile ℓ g_ℓ ∈ L²`.
  have hPeq : sectorProj ℓ g =ᵐ[volume] ofProfile ℓ (Polar.angularSector g ℓ) := by
    have h0 : ∀ᵐ x : ℂ ∂volume, x ≠ 0 := by
      rw [ae_iff]
      simp only [ne_eq, not_not, ofPred_eq_eq_singleton]
      exact measure_singleton 0
    filter_upwards [h0] with x hx
    rw [sectorProj_eq_angularSector ℓ g hx]
    rfl
  have hmem : MemLp (ofProfile ℓ (Polar.angularSector g ℓ)) 2 volume :=
    (memLp_sectorProj hg ℓ).1.ae_eq hPeq
  have hint : IntegrableOn (fun r => ‖Polar.angularSector g ℓ r‖ ^ 2 * r) (Ioi 0) :=
    ((memLp_ofProfile_iff (ℓ := ℓ) hmeas).1).1 hmem
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  refine (hint.const_mul ρm⁻¹).mono' (hmeas.norm.pow 2) ?_
  filter_upwards [hvan] with r hr
  rw [Real.norm_of_nonneg (by positivity)]
  by_cases h0 : Polar.angularSector g ℓ r = 0
  · simp [h0]
  · have hrK : r ∈ Icc ρm ρp := by
      by_contra hrK
      exact h0 (hr hrK)
    have hr1 : 1 ≤ ρm⁻¹ * r := by
      rw [inv_mul_eq_div, one_le_div hρm]
      exact hrK.1
    have hsq : 0 ≤ ‖Polar.angularSector g ℓ r‖ ^ 2 := by positivity
    calc ‖Polar.angularSector g ℓ r‖ ^ 2 = 1 * ‖Polar.angularSector g ℓ r‖ ^ 2 := by ring
      _ ≤ (ρm⁻¹ * r) * ‖Polar.angularSector g ℓ r‖ ^ 2 := by gcongr
      _ = ρm⁻¹ * (‖Polar.angularSector g ℓ r‖ ^ 2 * r) := by ring

end NonUniqueEuler.Ang
