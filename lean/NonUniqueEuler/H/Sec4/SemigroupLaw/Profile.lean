import NonUniqueEuler.H.Sec4.SemigroupLaw.Basic
import NonUniqueEuler.Defs.Sec4.Setting
import NonUniqueEuler.I.Infra.Polar.Fubini
import NonUniqueEuler.I.Infra.AngularFourier.Sector

/-!
# Helpers for `P/Sec4/SemigroupLaw`: sector profiles of a.e. equal functions

* `angularSector_congr_ae`: a.e. equal plane functions have a.e. (in `r > 0`) equal sector
  profiles (Tonelli in polar coordinates, `Polar.lintegral_eq_lintegral_Ioi_circle`);
* `angularSector_sectorProj`: `(P_ℓ f)_ℓ = f_ℓ` on `r > 0`;
* `green_congr_ae`, `LsecFn_congr_ae`: `𝒢_ℓ` and `L_ℓ(G)` on profiles only see the a.e. class
  on `(0, ∞)`;
* `ofProfile_congr_ae`: `h(|x|)e^{iℓθ}` only depends on the a.e. class of `h` on `(0, ∞)`;
* `ofProfile_LsecFn_congr(_sectorProj)`: the combination used for `L_ℓ(G)` on `Y^s_ℓ`.
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace NonUniqueEuler.Sect.SgLawH

open Sob Ang

/-- A.e. equal plane functions have a.e. equal sector profiles on `(0, ∞)`. -/
theorem angularSector_congr_ae {f₁ f₂ : ℂ → ℂ} (h : f₁ =ᵐ[volume] f₂) (ℓ : ℤ) :
    Polar.angularSector f₁ ℓ =ᵐ[volume.restrict (Ioi (0 : ℝ))] Polar.angularSector f₂ ℓ := by
  set N := toMeasurable (volume : Measure ℂ) {x | f₁ x ≠ f₂ x} with hNdef
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : (volume : Measure ℂ) N = 0 := by
    rw [hNdef, measure_toMeasurable]
    exact h
  have hind : Measurable (N.indicator (1 : ℂ → ℝ≥0∞)) := measurable_one.indicator hNm
  have key := Polar.lintegral_eq_lintegral_Ioi_circle hind
  rw [lintegral_indicator_one hNm, hN0] at key
  have hcont : Continuous fun p : ℝ × ℝ => circleMap 0 p.1 p.2 := by
    unfold circleMap
    fun_prop
  have hF : Measurable fun p : ℝ × ℝ => N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 p.1 p.2) :=
    hind.comp hcont.measurable
  have hmeas : Measurable fun r : ℝ => ENNReal.ofReal r *
      ∫⁻ θ in Ioc (0 : ℝ) (2 * π), N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 r θ) :=
    ENNReal.measurable_ofReal.mul (hF.lintegral_prod_right' (ν := volume.restrict (Ioc 0 (2 * π))))
  have hae := (lintegral_eq_zero_iff hmeas).1 key.symm
  filter_upwards [hae, self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
    with r hr hr0
  have hint : ∫⁻ θ in Ioc (0 : ℝ) (2 * π), N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 r θ) = 0 := by
    rcases mul_eq_zero.1 hr with h1 | h1
    · exact absurd (ENNReal.ofReal_eq_zero.1 h1) (not_le.2 hr0)
    · exact h1
  have hm : Measurable fun θ : ℝ => N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 r θ) :=
    hind.comp (continuous_circleMap 0 r).measurable
  have hθ : ∀ᵐ θ ∂(volume.restrict (Ioc (0 : ℝ) (2 * π))), circleMap 0 r θ ∉ N := by
    filter_upwards [(lintegral_eq_zero_iff hm).1 hint] with θ hθ hmem
    simp only [Pi.zero_apply] at hθ
    rw [indicator_of_mem hmem] at hθ
    exact one_ne_zero hθ
  unfold Polar.angularSector
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  rw [uIoc_of_le (by positivity), ← ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hθ] with θ hθ
  have hx : (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) = circleMap 0 r θ := by
    simp [circleMap]
  have heq : f₁ (circleMap 0 r θ) = f₂ (circleMap 0 r θ) := by
    by_contra hne
    exact hθ (subset_toMeasurable _ _ hne)
  rw [hx, heq]

/-- `angPhase ℓ (r e^{iθ}) = e^{iℓθ}` for `r > 0`. -/
theorem angPhase_polar (ℓ : ℤ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    angPhase ℓ ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
      Complex.exp ((ℓ : ℂ) * θ * Complex.I) := by
  have hn : ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = r := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  unfold angPhase
  rw [hn, mul_div_cancel_left₀ _ (by exact_mod_cast hr.ne'), ← Complex.exp_int_mul]
  congr 1
  ring

theorem norm_polar {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = r := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
    Complex.norm_exp_ofReal_mul_I, mul_one]

/-- The sector-`ℓ` profile of `P_ℓ f` is that of `f` (on `r > 0`). -/
theorem angularSector_sectorProj (ℓ : ℤ) (f : ℂ → ℂ) {r : ℝ} (hr : 0 < r) :
    Polar.angularSector (sectorProj ℓ f) ℓ r = Polar.angularSector f ℓ r := by
  have hpt : ∀ θ : ℝ, sectorProj ℓ f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
      Complex.exp (-((ℓ : ℂ) * θ * Complex.I)) = Polar.angularSector f ℓ r := by
    intro θ
    have hx : (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hr.ne') (Complex.exp_ne_zero _)
    rw [sectorProj_eq_angularSector ℓ f hx, norm_polar hr θ, angPhase_polar ℓ hr θ, mul_assoc,
      ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
  conv_lhs => rw [Polar.angularSector]
  simp_rw [hpt]
  rw [intervalIntegral.integral_const, sub_zero, Complex.real_smul]
  have hπ : (2 * π : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  push_cast
  field_simp

theorem angularSector_sectorProj_ae (ℓ : ℤ) (f : ℂ → ℂ) :
    Polar.angularSector (sectorProj ℓ f) ℓ =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      Polar.angularSector f ℓ := by
  filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
    with r hr
  exact angularSector_sectorProj ℓ f hr

/-- `𝒢_ℓ` only depends on the a.e. class of the profile on `(0, ∞)`. -/
theorem green_congr_ae {ℓ : ℤ} {h₁ h₂ : ℝ → ℂ}
    (h : h₁ =ᵐ[volume.restrict (Ioi (0 : ℝ))] h₂) (r : ℝ) :
    SectorSetting.green ℓ h₁ r = SectorSetting.green ℓ h₂ r := by
  unfold SectorSetting.green
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [h] with ρ hρ
  rw [hρ]

theorem LsecFn_congr_ae (S : SectorSetting) (ℓ : ℤ) (G : ℝ) {h₁ h₂ : ℝ → ℂ}
    (h : h₁ =ᵐ[volume.restrict (Ioi (0 : ℝ))] h₂) :
    S.LsecFn ℓ G h₁ =ᵐ[volume.restrict (Ioi (0 : ℝ))] S.LsecFn ℓ G h₂ := by
  filter_upwards [h] with r hr
  simp only [SectorSetting.LsecFn, SectorSetting.KsecFn, hr, green_congr_ae h r]

/-- `h(|x|) e^{iℓθ}` only depends on the a.e. class of `h` on `(0, ∞)`. -/
theorem ofProfile_congr_ae {ℓ : ℤ} {h₁ h₂ : ℝ → ℂ}
    (h : h₁ =ᵐ[volume.restrict (Ioi (0 : ℝ))] h₂) :
    ofProfile ℓ h₁ =ᵐ[volume] ofProfile ℓ h₂ := by
  filter_upwards [ae_comp_norm h] with x hx
  simp only [ofProfile, hx]

theorem ofProfile_LsecFn_congr (S : SectorSetting) (ℓ : ℤ) (G : ℝ) {f₁ f₂ : ℂ → ℂ}
    (h : f₁ =ᵐ[volume] f₂) :
    ofProfile ℓ (S.LsecFn ℓ G (Polar.angularSector f₁ ℓ)) =ᵐ[volume]
      ofProfile ℓ (S.LsecFn ℓ G (Polar.angularSector f₂ ℓ)) :=
  ofProfile_congr_ae (LsecFn_congr_ae S ℓ G (angularSector_congr_ae h ℓ))

theorem ofProfile_LsecFn_congr_sectorProj (S : SectorSetting) (ℓ : ℤ) (G : ℝ) {f₁ f₂ : ℂ → ℂ}
    (h : f₁ =ᵐ[volume] sectorProj ℓ f₂) :
    ofProfile ℓ (S.LsecFn ℓ G (Polar.angularSector f₁ ℓ)) =ᵐ[volume]
      ofProfile ℓ (S.LsecFn ℓ G (Polar.angularSector f₂ ℓ)) :=
  ofProfile_congr_ae (LsecFn_congr_ae S ℓ G
    ((angularSector_congr_ae h ℓ).trans (angularSector_sectorProj_ae ℓ f₂)))

end NonUniqueEuler.Sect.SgLawH
