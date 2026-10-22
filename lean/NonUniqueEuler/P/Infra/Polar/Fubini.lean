import NonUniqueEuler.Defs.Infra.Polar
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Proof: Fubini in polar coordinates on `ℂ` (I-POLAR)

Proof of `NonUniqueEuler/I/Infra/Polar/Fubini.lean` (`02_prelim.tex:26-29`).

Strategy. Instead of the polar chart `polarCoord` (whose target is `(0,∞) × (-π,π)`), we apply
the change of variables theorem (`Mathlib/MeasureTheory/Function/Jacobian.lean`) directly to the
map `polarCoord.symm : (r, θ) ↦ (r cos θ, r sin θ)` on the domain
`polarDom = (0,∞) × (0,2π]`:
* it is injective there (`injOn_polarDom`, from `eq_of_circleMap_eq`);
* its image contains `polarCoord.source`, hence is a.e. everything (`image_polarDom_ae_eq_univ`);
* its Jacobian determinant is `r` (`det_fderivPolarCoordSymm`).
This gives integrability, the Bochner formula and the Tonelli formula on `(0,∞) × (0,2π]`
without any periodicity argument; Fubini/Tonelli on the product finishes.
-/

noncomputable section

open MeasureTheory Set Metric Real
open scoped ENNReal

namespace NonUniqueEuler.Polar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-! ### Helpers: polar coordinates on `(0,∞) × (0,2π]` -/

/-- The polar domain `(0,∞) × (0,2π]`. -/
private abbrev polarDom : Set (ℝ × ℝ) := Ioi (0 : ℝ) ×ˢ Ioc (0 : ℝ) (2 * π)

private theorem measurableSet_polarDom : MeasurableSet polarDom :=
  measurableSet_Ioi.prod measurableSet_Ioc

/-- `polarCoord.symm`, read in `ℂ`, is `circleMap 0`. -/
private theorem equivRealProd_symm_polarCoord_symm (p : ℝ × ℝ) :
    Complex.measurableEquivRealProd.symm (polarCoord.symm p) = circleMap 0 p.1 p.2 := by
  rw [Complex.measurableEquivRealProd_symm_polarCoord_symm_apply, Complex.polarCoord_symm_apply,
    circleMap_zero, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

private theorem injOn_polarDom : InjOn polarCoord.symm polarDom := by
  rintro ⟨r, θ⟩ hp ⟨r', θ'⟩ hq h
  simp only [polarDom, mem_prod, mem_Ioi, mem_Ioc] at hp hq
  have h2 : circleMap 0 r θ = circleMap 0 r' θ' := by
    have := congrArg Complex.measurableEquivRealProd.symm h
    simpa only [equivRealProd_symm_polarCoord_symm] using this
  have hrr : r = r' := by
    have := congrArg norm h2
    simp only [norm_circleMap_zero] at this
    rwa [abs_of_pos hp.1, abs_of_pos hq.1] at this
  subst hrr
  have hθ : θ = θ' := by
    refine eq_of_circleMap_eq (ne_of_gt hp.1) ?_ h2
    rw [abs_lt]
    constructor <;> linarith [hp.2.1, hp.2.2, hq.2.1, hq.2.2]
  rw [hθ]

private theorem source_subset_image_polarDom :
    polarCoord.source ⊆ polarCoord.symm '' polarDom := by
  intro x hx
  have ht := polarCoord.map_source hx
  have hl := polarCoord.left_inv hx
  set p := polarCoord x with hp
  rw [polarCoord_target, mem_prod, mem_Ioi, mem_Ioo] at ht
  by_cases h0 : 0 < p.2
  · exact ⟨p, ⟨ht.1, h0, by linarith [ht.2.2, Real.pi_pos]⟩, hl⟩
  · refine ⟨(p.1, p.2 + 2 * π), ⟨ht.1, by linarith [ht.2.1], by linarith⟩, ?_⟩
    rw [← hl]
    simp only [polarCoord_symm_apply, Real.cos_add_two_pi, Real.sin_add_two_pi]

private theorem image_polarDom_ae_eq_univ :
    polarCoord.symm '' polarDom =ᵐ[volume] (univ : Set (ℝ × ℝ)) := by
  rw [ae_eq_univ]
  have h := ae_eq_univ.mp polarCoord_source_ae_eq_univ
  exact measure_mono_null (compl_subset_compl.mpr source_subset_image_polarDom) h

private theorem hasFDerivWithinAt_polarDom :
    ∀ p ∈ polarDom, HasFDerivWithinAt polarCoord.symm (fderivPolarCoordSymm p) polarDom p :=
  fun p _ => (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt

private theorem volume_restrict_polarDom :
    (volume : Measure (ℝ × ℝ)).restrict polarDom =
      (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioc (0 : ℝ) (2 * π))) := by
  rw [Measure.prod_restrict, Measure.volume_eq_prod]

omit [NormedSpace ℝ E] [CompleteSpace E] in
private theorem integrable_comp_equivRealProd_symm {f : ℂ → E} (hf : Integrable f) :
    Integrable (f ∘ Complex.measurableEquivRealProd.symm) :=
  ((Complex.volume_preserving_equiv_real_prod.symm).integrable_comp_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding).mpr hf

private theorem measurable_circleMap_prod :
    Measurable (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by
  have : (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) =
      fun p => Complex.measurableEquivRealProd.symm (polarCoord.symm p) :=
    funext fun p => (equivRealProd_symm_polarCoord_symm p).symm
  rw [this]
  exact Complex.measurableEquivRealProd.symm.measurable.comp continuous_polarCoord_symm.measurable

/-! ### Fubini in polar coordinates -/

set_option linter.unusedSectionVars false in
/-- The polar integrand is integrable on `(0,∞) × (0,2π)` (with the weight `r`). -/
theorem integrableOn_polar {f : ℂ → E} (hf : Integrable f) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 • f (circleMap 0 p.1 p.2))
      (Ioi (0 : ℝ) ×ˢ Ioc (0 : ℝ) (2 * π)) := by
  have := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume measurableSet_polarDom
    hasFDerivWithinAt_polarDom injOn_polarDom
    (f ∘ Complex.measurableEquivRealProd.symm)).mp
    (integrable_comp_equivRealProd_symm hf).integrableOn
  refine this.congr_fun (fun p hp => ?_) measurableSet_polarDom
  simp only [det_fderivPolarCoordSymm, Function.comp_apply, equivRealProd_symm_polarCoord_symm,
    abs_of_pos (show 0 < p.1 from hp.1)]

/-- Fubini in polar coordinates: `∫ f = ∫₀^∞ r ∫₀^{2π} f(r e^{iθ}) dθ dr` for integrable `f`. -/
theorem integral_eq_integral_Ioi_intervalIntegral {f : ℂ → E} (hf : Integrable f) :
    ∫ x, f x = ∫ r in Ioi (0 : ℝ), r • ∫ θ in (0 : ℝ)..2 * π, f (circleMap 0 r θ) := by
  have h1 : ∫ x, f x = ∫ p : ℝ × ℝ, f (Complex.measurableEquivRealProd.symm p) :=
    ((Complex.volume_preserving_equiv_real_prod.symm).integral_comp
      Complex.measurableEquivRealProd.symm.measurableEmbedding f).symm
  have h2 : ∫ p : ℝ × ℝ, f (Complex.measurableEquivRealProd.symm p) =
      ∫ p in polarDom, p.1 • f (circleMap 0 p.1 p.2) := by
    rw [← setIntegral_univ, ← setIntegral_congr_set image_polarDom_ae_eq_univ,
      integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_polarDom
        hasFDerivWithinAt_polarDom injOn_polarDom]
    refine setIntegral_congr_fun measurableSet_polarDom (fun p hp => ?_)
    simp only [det_fderivPolarCoordSymm, equivRealProd_symm_polarCoord_symm,
      abs_of_pos (show 0 < p.1 from hp.1)]
  have hint := integrableOn_polar hf
  rw [IntegrableOn, volume_restrict_polarDom] at hint
  rw [h1, h2, volume_restrict_polarDom, integral_prod _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  simp only [integral_smul, intervalIntegral.integral_of_le Real.two_pi_pos.le]

/-- Fubini in polar coordinates, circle-average form: `∫ f = 2π ∫₀^∞ r ⨍_{C(0,r)} f dr`. -/
theorem integral_eq_integral_Ioi_circleAverage {f : ℂ → E} (hf : Integrable f) :
    ∫ x, f x = (2 * π) • ∫ r in Ioi (0 : ℝ), r • Real.circleAverage f 0 r := by
  rw [integral_eq_integral_Ioi_intervalIntegral hf, ← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  simp only [Real.circleAverage_def]
  rw [smul_comm (2 * π) r, smul_inv_smul₀ (ne_of_gt Real.two_pi_pos)]

/-- Tonelli in polar coordinates. -/
theorem lintegral_eq_lintegral_Ioi_circle {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x = ∫⁻ r in Ioi (0 : ℝ),
      ENNReal.ofReal r * ∫⁻ θ in Ioc (0 : ℝ) (2 * π), f (circleMap 0 r θ) := by
  have h1 : ∫⁻ x, f x = ∫⁻ p : ℝ × ℝ, f (Complex.measurableEquivRealProd.symm p) :=
    ((Complex.volume_preserving_equiv_real_prod.symm).lintegral_comp_emb
      Complex.measurableEquivRealProd.symm.measurableEmbedding f).symm
  have h2 : ∫⁻ p : ℝ × ℝ, f (Complex.measurableEquivRealProd.symm p) =
      ∫⁻ p in polarDom, ENNReal.ofReal p.1 * f (circleMap 0 p.1 p.2) := by
    rw [← setLIntegral_univ, ← setLIntegral_congr image_polarDom_ae_eq_univ,
      lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_polarDom
        hasFDerivWithinAt_polarDom injOn_polarDom]
    refine setLIntegral_congr_fun measurableSet_polarDom (fun p hp => ?_)
    simp only [det_fderivPolarCoordSymm, equivRealProd_symm_polarCoord_symm,
      abs_of_pos (show 0 < p.1 from hp.1)]
  have hmeas : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * f (circleMap 0 p.1 p.2)) :=
    (ENNReal.measurable_ofReal.comp measurable_fst).mul (hf.comp measurable_circleMap_prod)
  rw [h1, h2, volume_restrict_polarDom, lintegral_prod _ hmeas.aemeasurable]
  refine lintegral_congr fun r => ?_
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- For integrable `f`, `θ ↦ f(r e^{iθ})` is integrable on `[0, 2π]` for almost every `r > 0`. -/
theorem ae_circleIntegrable_of_integrable {f : ℂ → E} (hf : Integrable f) :
    ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), CircleIntegrable f 0 r := by
  have hint := integrableOn_polar hf
  rw [IntegrableOn, volume_restrict_polarDom] at hint
  filter_upwards [hint.prod_right_ae, ae_restrict_mem measurableSet_Ioi] with r hr hr0
  have hr0' : r ≠ 0 := ne_of_gt hr0
  have h : Integrable (fun θ => f (circleMap 0 r θ)) (volume.restrict (Ioc (0 : ℝ) (2 * π))) := by
    refine (hr.smul r⁻¹).congr (Filter.Eventually.of_forall fun θ => ?_)
    simp only [Pi.smul_apply, smul_smul, inv_mul_cancel₀ hr0', one_smul]
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mpr h

/-- For `f ∈ L¹_loc`, `θ ↦ f(r e^{iθ})` is integrable on `[0, 2π]` for almost every `r > 0`
(`02_prelim.tex:26-29`). -/
theorem ae_circleIntegrable_of_locallyIntegrable {f : ℂ → E} (hf : LocallyIntegrable f) :
    ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), CircleIntegrable f 0 r := by
  have h : ∀ n : ℕ, ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))),
      CircleIntegrable ((closedBall (0 : ℂ) n).indicator f) 0 r := fun n =>
    ae_circleIntegrable_of_integrable ((integrable_indicator_iff measurableSet_closedBall).mpr
      (hf.integrableOn_isCompact (isCompact_closedBall 0 n)))
  filter_upwards [ae_all_iff.mpr h, ae_restrict_mem measurableSet_Ioi] with r hr hr0
  obtain ⟨n, hn⟩ := exists_nat_ge r
  have heq : (fun θ => (closedBall (0 : ℂ) n).indicator f (circleMap 0 r θ)) =
      fun θ => f (circleMap 0 r θ) := by
    funext θ
    apply indicator_of_mem
    rw [mem_closedBall, dist_zero_right, norm_circleMap_zero, abs_of_pos hr0]
    exact hn
  have := hr n
  rw [circleIntegrable_def, heq] at this
  exact this

end NonUniqueEuler.Polar
