import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import NonUniqueEuler.Defs.Infra.AngularFourier
import NonUniqueEuler.I.Infra.AngularFourier.Sector
import NonUniqueEuler.I.Infra.Polar.Radial
import NonUniqueEuler.I.Infra.ConvMinkowski.Minkowski

/-!
# Proof: the sector projections on `L²` (library I-ANG)

Proof of `NonUniqueEuler/I/Infra/AngularFourier/SectorL2.lean` (same declarations, statements
copied verbatim).

Method.
* A.e. congruence (`sectorProj_congr_ae`): a null set `N ⊇ {f ≠ g}` pulls back under the
  measure-preserving rotations to null sets, so by Fubini (`Measure.ae_ae_comm` on
  `ℂ × (0, 2π]`) for a.e. `x` the integrands agree for a.e. `φ`.
* `L²` contraction (`memLp_sectorProj`): reduce to a strongly measurable representative; then
  `‖P_ℓ g(x)‖ ≤ (2π)⁻¹ ∫ |g(O_φ x)| dφ` and Minkowski's integral inequality
  (`Conv.eLpNorm_lintegral_le`, `I/Infra/ConvMinkowski/Minkowski`) with
  `‖g ∘ O_φ‖_{L²} = ‖g‖_{L²}`.  The same bound shows that `φ ↦ g(O_φ x)` is integrable for
  a.e. `x`, which gives the a.e. linearity of `P_ℓ` and the continuous linear map
  `sectorProjL` (`LinearMap.mkContinuous`).
* Sector functions (`isSectorFn_iff`): Fubini as above for `g(O_φ x) = e^{iℓφ} g(x)`, the
  equivariance `sectorProj_rot` and the polar form `sectorProj_eq_angularSector`
  (`I/Infra/AngularFourier/Sector`).
* Norm of a sector function (`memLp_ofProfile_iff`): `|e^{iℓθ}| = 1` off `0`, the radial
  formulas `Polar.integral_comp_norm`, `Polar.integrable_comp_norm_iff` and, for
  measurability of `x ↦ h(|x|)`, `Polar.lintegral_comp_norm` (the image of `volume` under
  `‖·‖` is absolutely continuous with respect to `volume` on `(0, ∞)`).
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace NonUniqueEuler.Ang

namespace SectorL2Aux

/-! ### Helpers -/

/-- The measure `dφ` on `(0, 2π]`. -/
abbrev μφ : Measure ℝ := (volume : Measure ℝ).restrict (Ioc (0 : ℝ) (2 * π))

theorem continuous_rot_uncurry : Continuous (fun q : ℂ × ℝ => rot q.2 q.1) := by
  unfold rot; fun_prop

/-- Fubini for null sets: a measurable predicate holding for every `φ` and a.e. `x` holds
for a.e. `x` and a.e. `φ ∈ (0, 2π]`. -/
theorem ae_ae_of_forall_ae {p : ℝ → ℂ → Prop}
    (hp : MeasurableSet {q : ℂ × ℝ | p q.2 q.1}) (h : ∀ φ, ∀ᵐ x ∂(volume : Measure ℂ), p φ x) :
    ∀ᵐ x ∂(volume : Measure ℂ), ∀ᵐ φ ∂μφ, p φ x := by
  rw [Measure.ae_ae_comm hp]
  exact Filter.Eventually.of_forall h

theorem ae_ae_rot_eq {f g : ℂ → ℂ} (hfg : f =ᵐ[volume] g) :
    ∀ᵐ x ∂(volume : Measure ℂ), ∀ᵐ φ ∂μφ, f (rot φ x) = g (rot φ x) := by
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hfg)
  have key : ∀ᵐ x ∂(volume : Measure ℂ), ∀ᵐ φ ∂μφ, rot φ x ∉ N := by
    apply ae_ae_of_forall_ae
    · exact (hNm.preimage continuous_rot_uncurry.measurable).compl
    · intro φ
      have : volume (rot φ ⁻¹' N) = 0 := by
        rw [(Polar.measurePreserving_rot φ).measure_preimage hNm.nullMeasurableSet]; exact hN0
      exact measure_eq_zero_iff_ae_notMem.1 this
  filter_upwards [key] with x hx
  filter_upwards [hx] with φ hφ
  by_contra hne
  exact hφ (hNsub hne)

end SectorL2Aux

open SectorL2Aux

theorem sectorProj_congr_ae (ℓ : ℤ) {f g : ℂ → ℂ} (hfg : f =ᵐ[volume] g) :
    sectorProj ℓ f =ᵐ[volume] sectorProj ℓ g := by
  filter_upwards [ae_ae_rot_eq hfg] with x hx
  unfold sectorProj
  congr 1
  apply intervalIntegral.integral_congr_ae
  rw [uIoc_of_le (by positivity)]
  filter_upwards [(ae_restrict_iff' measurableSet_Ioc).1 hx] with φ hφ hmem
  rw [hφ hmem]

namespace SectorL2Aux

theorem sectorProj_eq_integral (ℓ : ℤ) (g : ℂ → ℂ) (x : ℂ) :
    sectorProj ℓ g x = (2 * π : ℂ)⁻¹ *
      ∫ φ, Complex.exp (-((ℓ : ℂ) * φ * Complex.I)) * g (rot φ x) ∂μφ := by
  rw [sectorProj, intervalIntegral.integral_of_le (by positivity)]

theorem stronglyMeasurable_integrand {g : ℂ → ℂ} (hg : StronglyMeasurable g) (ℓ : ℤ) :
    StronglyMeasurable
      (fun q : ℂ × ℝ => Complex.exp (-((ℓ : ℂ) * q.2 * Complex.I)) * g (rot q.2 q.1)) := by
  refine StronglyMeasurable.mul ?_ ?_
  · exact (by fun_prop : Continuous fun q : ℂ × ℝ =>
      Complex.exp (-((ℓ : ℂ) * q.2 * Complex.I))).stronglyMeasurable
  · exact hg.comp_measurable continuous_rot_uncurry.measurable

theorem stronglyMeasurable_sectorProj {g : ℂ → ℂ} (hg : StronglyMeasurable g) (ℓ : ℤ) :
    StronglyMeasurable (sectorProj ℓ g) := by
  have : sectorProj ℓ g = fun x => (2 * π : ℂ)⁻¹ *
      ∫ φ, Complex.exp (-((ℓ : ℂ) * φ * Complex.I)) * g (rot φ x) ∂μφ := by
    funext x; exact sectorProj_eq_integral ℓ g x
  rw [this]
  exact ((stronglyMeasurable_integrand hg ℓ).integral_prod_right' (ν := μφ)).const_mul _


theorem norm_exp_neg_mul_I (ℓ : ℤ) (φ : ℝ) : ‖Complex.exp (-((ℓ : ℂ) * φ * Complex.I))‖ = 1 := by
  rw [Complex.norm_exp]; simp

theorem enorm_exp_neg_mul_I (ℓ : ℤ) (φ : ℝ) : ‖Complex.exp (-((ℓ : ℂ) * φ * Complex.I))‖ₑ = 1 := by
  rw [← ofReal_norm, norm_exp_neg_mul_I, ENNReal.ofReal_one]

/-- Minkowski: `‖∫⁻ |g(O_φ ·)| dφ‖_{L²} ≤ 2π ‖g‖_{L²}`. -/
theorem eLpNorm_lintegral_rot_le {g : ℂ → ℂ} (hg : StronglyMeasurable g) :
    eLpNorm (fun x => ∫⁻ φ, ‖g (rot φ x)‖ₑ ∂μφ) 2 volume ≤
      ENNReal.ofReal (2 * π) * eLpNorm g 2 volume := by
  have hF : AEMeasurable (Function.uncurry fun (x : ℂ) (φ : ℝ) => ‖g (rot φ x)‖ₑ)
      ((volume : Measure ℂ).prod μφ) :=
    (hg.comp_measurable continuous_rot_uncurry.measurable).measurable.enorm.aemeasurable
  refine (Conv.eLpNorm_lintegral_le hF (by norm_num) (by norm_num)).trans_eq ?_
  have : ∀ φ : ℝ, eLpNorm (fun x => ‖g (rot φ x)‖ₑ) 2 volume = eLpNorm g 2 volume := by
    intro φ
    rw [eLpNorm_enorm]
    exact eLpNorm_comp_measurePreserving hg.aestronglyMeasurable (Polar.measurePreserving_rot φ)
  simp_rw [this]
  rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero, mul_comm]

theorem enorm_two_pi_inv_mul : ‖(2 * π : ℂ)⁻¹‖ₑ * ENNReal.ofReal (2 * π) = 1 := by
  have h : ‖(2 * π : ℂ)⁻¹‖ = (2 * π)⁻¹ := by
    rw [norm_inv]
    congr 1
    have : (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [← ofReal_norm, h, ← ENNReal.ofReal_mul (by positivity),
    inv_mul_cancel₀ (by positivity), ENNReal.ofReal_one]

theorem eLpNorm_sectorProj_le {g : ℂ → ℂ} (hg : StronglyMeasurable g) (ℓ : ℤ) :
    eLpNorm (sectorProj ℓ g) 2 volume ≤ eLpNorm g 2 volume := by
  have hfun : sectorProj ℓ g = (2 * π : ℂ)⁻¹ • fun x =>
      ∫ φ, Complex.exp (-((ℓ : ℂ) * φ * Complex.I)) * g (rot φ x) ∂μφ := by
    funext x; rw [sectorProj_eq_integral]; rfl
  rw [hfun, eLpNorm_const_smul]
  calc ‖(2 * π : ℂ)⁻¹‖ₑ * eLpNorm (fun x =>
          ∫ φ, Complex.exp (-((ℓ : ℂ) * φ * Complex.I)) * g (rot φ x) ∂μφ) 2 volume
      ≤ ‖(2 * π : ℂ)⁻¹‖ₑ * eLpNorm (fun x => ∫⁻ φ, ‖g (rot φ x)‖ₑ ∂μφ) 2 volume := by
        gcongr
        refine eLpNorm_mono_enorm fun x => (enorm_integral_le_lintegral_enorm _).trans_eq ?_
        rw [enorm_eq_self]
        congr 1; funext φ
        rw [enorm_mul, enorm_exp_neg_mul_I, one_mul]
    _ ≤ ‖(2 * π : ℂ)⁻¹‖ₑ * (ENNReal.ofReal (2 * π) * eLpNorm g 2 volume) := by
        gcongr; exact eLpNorm_lintegral_rot_le hg
    _ = eLpNorm g 2 volume := by rw [← mul_assoc, enorm_two_pi_inv_mul, one_mul]

theorem ae_lintegral_rot_lt_top {g : ℂ → ℂ} (hg : StronglyMeasurable g)
    (hgL : MemLp g 2 volume) :
    ∀ᵐ x ∂(volume : Measure ℂ), ∫⁻ φ, ‖g (rot φ x)‖ₑ ∂μφ < ∞ := by
  set G : ℂ → ℝ≥0∞ := fun x => ∫⁻ φ, ‖g (rot φ x)‖ₑ ∂μφ with hGdef
  have hGm : Measurable G :=
    Measurable.lintegral_prod_right'
      (hg.comp_measurable continuous_rot_uncurry.measurable).measurable.enorm
  have hfin : eLpNorm G 2 volume < ∞ :=
    (eLpNorm_lintegral_rot_le hg).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hgL.2)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top] at hfin
  have h2 : ∫⁻ x, ‖G x‖ₑ ^ (2 : ℝ≥0∞).toReal ∂volume ≠ ∞ := by
    intro htop
    rw [htop, ENNReal.top_rpow_of_pos (by norm_num)] at hfin
    exact lt_irrefl _ hfin
  filter_upwards [ae_lt_top' (hGm.enorm.pow_const _).aemeasurable h2] with x hx
  by_contra hcon
  rw [not_lt_top_iff] at hcon
  have hcon' : G x = ∞ := hcon
  rw [enorm_eq_self, hcon', ENNReal.top_rpow_of_pos (by norm_num)] at hx
  exact lt_irrefl _ hx

end SectorL2Aux

/-- `P_ℓ` is a contraction on `L²`. -/
theorem memLp_sectorProj {g : ℂ → ℂ} (hg : MemLp g 2 volume) (ℓ : ℤ) :
    MemLp (sectorProj ℓ g) 2 volume ∧ eLpNorm (sectorProj ℓ g) 2 volume ≤ eLpNorm g 2 volume := by
  have hgg' : g =ᵐ[volume] hg.1.mk g := hg.1.ae_eq_mk
  have hsm : StronglyMeasurable (hg.1.mk g) := hg.1.stronglyMeasurable_mk
  have hP := sectorProj_congr_ae ℓ hgg'
  have hle : eLpNorm (sectorProj ℓ g) 2 volume ≤ eLpNorm g 2 volume := by
    rw [eLpNorm_congr_ae hP]
    exact (eLpNorm_sectorProj_le hsm ℓ).trans_eq (eLpNorm_congr_ae hgg').symm
  exact ⟨⟨(stronglyMeasurable_sectorProj hsm ℓ).aestronglyMeasurable.congr hP.symm,
    hle.trans_lt hg.2⟩, hle⟩

namespace SectorL2Aux

/-- For `g ∈ L²`, the integrand of `P_ℓ g (x)` is integrable for a.e. `x`. -/
theorem ae_integrable_rot {g : ℂ → ℂ} (hg : MemLp g 2 volume) (ℓ : ℤ) :
    ∀ᵐ x ∂(volume : Measure ℂ),
      Integrable (fun φ : ℝ => Complex.exp (-((ℓ : ℂ) * φ * Complex.I)) * g (rot φ x)) μφ := by
  have hgg' : g =ᵐ[volume] hg.1.mk g := hg.1.ae_eq_mk
  have hsm : StronglyMeasurable (hg.1.mk g) := hg.1.stronglyMeasurable_mk
  have hL' : MemLp (hg.1.mk g) 2 volume := hg.ae_eq hgg'
  filter_upwards [ae_lintegral_rot_lt_top hsm hL', ae_ae_rot_eq hgg'] with x hx hxe
  have hint : Integrable (fun φ : ℝ =>
      Complex.exp (-((ℓ : ℂ) * φ * Complex.I)) * hg.1.mk g (rot φ x)) μφ := by
    refine ⟨?_, ?_⟩
    · exact ((stronglyMeasurable_integrand hsm ℓ).comp_measurable
        (by fun_prop : Measurable fun φ : ℝ => (x, φ))).aestronglyMeasurable
    · unfold HasFiniteIntegral
      simp_rw [enorm_mul, enorm_exp_neg_mul_I, one_mul]
      exact hx
  refine hint.congr ?_
  filter_upwards [hxe] with φ hφ
  rw [hφ]

theorem sectorProj_add_ae {f g : ℂ → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (ℓ : ℤ) :
    sectorProj ℓ (f + g) =ᵐ[volume] sectorProj ℓ f + sectorProj ℓ g := by
  filter_upwards [ae_integrable_rot hf ℓ, ae_integrable_rot hg ℓ] with x hfx hgx
  simp only [sectorProj_eq_integral, Pi.add_apply, mul_add]
  rw [integral_add hfx hgx, mul_add]

theorem sectorProj_smul (ℓ : ℤ) (c : ℂ) (f : ℂ → ℂ) :
    sectorProj ℓ (c • f) = c • sectorProj ℓ f := by
  funext x
  simp only [sectorProj, Pi.smul_apply, smul_eq_mul]
  have : ∀ φ : ℝ, Complex.exp (-((ℓ : ℂ) * φ * Complex.I)) * (c * f (rot φ x)) =
      c * (Complex.exp (-((ℓ : ℂ) * φ * Complex.I)) * f (rot φ x)) := fun φ => by ring
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul, mul_left_comm]

theorem exists_sectorProjL (ℓ : ℤ) :
    ∃ P : Lp ℂ 2 (volume : Measure ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure ℂ),
      ∀ f, (P f : ℂ → ℂ) =ᵐ[volume] sectorProj ℓ f := by
  let T : Lp ℂ 2 (volume : Measure ℂ) →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
    { toFun := fun f => (memLp_sectorProj (Lp.memLp f) ℓ).1.toLp _
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (memLp_sectorProj (Lp.memLp (f + g)) ℓ).1,
          MemLp.coeFn_toLp (memLp_sectorProj (Lp.memLp f) ℓ).1,
          MemLp.coeFn_toLp (memLp_sectorProj (Lp.memLp g) ℓ).1,
          Lp.coeFn_add ((memLp_sectorProj (Lp.memLp f) ℓ).1.toLp _)
            ((memLp_sectorProj (Lp.memLp g) ℓ).1.toLp _),
          sectorProj_congr_ae ℓ (Lp.coeFn_add f g),
          sectorProj_add_ae (Lp.memLp f) (Lp.memLp g) ℓ] with x h1 h2 h3 h4 h5 h6
        rw [h1, h4, Pi.add_apply, h2, h3, h5, h6]
        rfl
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (memLp_sectorProj (Lp.memLp (c • f)) ℓ).1,
          MemLp.coeFn_toLp (memLp_sectorProj (Lp.memLp f) ℓ).1,
          Lp.coeFn_smul c ((memLp_sectorProj (Lp.memLp f) ℓ).1.toLp _),
          sectorProj_congr_ae ℓ (Lp.coeFn_smul c f)] with x h1 h2 h3 h4
        rw [RingHom.id_apply, h1, h3, Pi.smul_apply, h2, h4, sectorProj_smul, Pi.smul_apply] }
  refine ⟨T.mkContinuous 1 (fun f => ?_), fun f => ?_⟩
  · rw [one_mul]
    change ‖(memLp_sectorProj (Lp.memLp f) ℓ).1.toLp _‖ ≤ ‖f‖
    rw [Lp.norm_toLp, Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (memLp_sectorProj (Lp.memLp f) ℓ).2
  · exact MemLp.coeFn_toLp (memLp_sectorProj (Lp.memLp f) ℓ).1

end SectorL2Aux

/-- The `L²` operator `sectorProjL ℓ` is `P_ℓ`. -/
theorem sectorProjL_spec (ℓ : ℤ) (f : Lp ℂ 2 (volume : Measure ℂ)) :
    (sectorProjL ℓ f : ℂ → ℂ) =ᵐ[volume] sectorProj ℓ f := by
  have h := exists_sectorProjL ℓ
  rw [sectorProjL, dite_eq_left h]
  exact h.choose_spec f

namespace SectorL2Aux

theorem ae_ne_zero : ∀ᵐ x ∂(volume : Measure ℂ), x ≠ 0 := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_singleton (0 : ℂ))] with x hx
  exact hx

theorem sectorProj_ae_eq_ofProfile (ℓ : ℤ) (g : ℂ → ℂ) :
    sectorProj ℓ g =ᵐ[volume] ofProfile ℓ (Polar.angularSector g ℓ) := by
  filter_upwards [ae_ne_zero] with x hx
  rw [sectorProj_eq_angularSector ℓ g hx, ofProfile]

theorem isSectorFn_congr {ℓ : ℤ} {g g' : ℂ → ℂ} (h : g =ᵐ[volume] g') (hg : IsSectorFn ℓ g) :
    IsSectorFn ℓ g' := by
  intro θ
  have h1 : (fun x => g (rot θ x)) =ᵐ[volume] fun x => g' (rot θ x) :=
    (Polar.measurePreserving_rot θ).quasiMeasurePreserving.ae_eq_comp h
  filter_upwards [h1, hg θ, h] with x hx1 hx2 hx3
  rw [← hx1, hx2, hx3]

theorem eq_sectorProj_of_isSectorFn_sm {ℓ : ℤ} {g : ℂ → ℂ} (hsm : StronglyMeasurable g)
    (hg : IsSectorFn ℓ g) : g =ᵐ[volume] sectorProj ℓ g := by
  have hmeas : MeasurableSet {q : ℂ × ℝ |
      g (rot q.2 q.1) = Complex.exp ((ℓ : ℂ) * q.2 * Complex.I) * g q.1} := by
    refine StronglyMeasurable.measurableSet_eq_fun ?_ ?_
    · exact hsm.comp_measurable continuous_rot_uncurry.measurable
    · exact ((by fun_prop : Continuous fun q : ℂ × ℝ =>
        Complex.exp ((ℓ : ℂ) * q.2 * Complex.I)).stronglyMeasurable).mul
          (hsm.comp_measurable measurable_fst)
  have key := ae_ae_of_forall_ae
    (p := fun φ x => g (rot φ x) = Complex.exp ((ℓ : ℂ) * φ * Complex.I) * g x) hmeas hg
  filter_upwards [key] with x hx
  unfold sectorProj
  have : ∫ φ in (0 : ℝ)..2 * π, Complex.exp (-((ℓ : ℂ) * φ * Complex.I)) * g (rot φ x) =
      ∫ φ in (0 : ℝ)..2 * π, g x := by
    apply intervalIntegral.integral_congr_ae
    rw [uIoc_of_le (by positivity)]
    filter_upwards [(ae_restrict_iff' measurableSet_Ioc).1 hx] with φ hφ hmem
    rw [hφ hmem, ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]
  have hpi : (2 * π : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  rw [this, intervalIntegral.integral_const, sub_zero, Complex.real_smul]
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ hpi, one_mul]

end SectorL2Aux

/-- Sector functions are exactly the fixed points of `P_ℓ`, and the functions
`g_ℓ(r) e^{iℓθ}`. -/
theorem isSectorFn_iff {ℓ : ℤ} {g : ℂ → ℂ} (hg : MemLp g 2 volume) :
    (IsSectorFn ℓ g ↔ g =ᵐ[volume] sectorProj ℓ g) ∧
      (IsSectorFn ℓ g ↔ g =ᵐ[volume] ofProfile ℓ (Polar.angularSector g ℓ)) := by
  have h1 : IsSectorFn ℓ g ↔ g =ᵐ[volume] sectorProj ℓ g := by
    constructor
    · intro hS
      have hgg' : g =ᵐ[volume] hg.1.mk g := hg.1.ae_eq_mk
      have hS' := isSectorFn_congr hgg' hS
      have := eq_sectorProj_of_isSectorFn_sm hg.1.stronglyMeasurable_mk hS'
      exact hgg'.trans (this.trans (sectorProj_congr_ae ℓ hgg').symm)
    · intro h θ
      have h1 : (fun x => g (rot θ x)) =ᵐ[volume] fun x => sectorProj ℓ g (rot θ x) :=
        (Polar.measurePreserving_rot θ).quasiMeasurePreserving.ae_eq_comp h
      filter_upwards [h1, h] with x hx1 hx2
      rw [hx1, sectorProj_rot, ← hx2]
  have hPO := sectorProj_ae_eq_ofProfile ℓ g
  exact ⟨h1, h1.trans ⟨fun h => h.trans hPO, fun h => h.trans hPO.symm⟩⟩

namespace SectorL2Aux

theorem quasiMeasurePreserving_norm :
    Measure.QuasiMeasurePreserving (fun x : ℂ => ‖x‖) volume (volume.restrict (Ioi (0 : ℝ))) := by
  refine ⟨continuous_norm.measurable, Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_⟩
  rw [Measure.map_apply continuous_norm.measurable hs]
  have h1 : volume ((fun x : ℂ => ‖x‖) ⁻¹' s) = ∫⁻ x : ℂ, s.indicator 1 ‖x‖ := by
    rw [← lintegral_indicator_one (continuous_norm.measurable hs)]; rfl
  have h2 : (fun r : ℝ => ENNReal.ofReal r * s.indicator 1 r) =ᵐ[volume.restrict (Ioi 0)] 0 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hs0] with r hr
    simp [indicator_of_notMem hr]
  rw [h1, Polar.lintegral_comp_norm (measurable_one.indicator hs), lintegral_congr_ae h2]
  simp

theorem measurable_angPhase (ℓ : ℤ) : Measurable (angPhase ℓ) := by
  unfold angPhase; fun_prop

theorem aestronglyMeasurable_ofProfile {ℓ : ℤ} {h : ℝ → ℂ}
    (hm : AEStronglyMeasurable h (volume.restrict (Ioi 0))) :
    AEStronglyMeasurable (ofProfile ℓ h) volume :=
  (hm.comp_quasiMeasurePreserving quasiMeasurePreserving_norm).mul
    (measurable_angPhase ℓ).aestronglyMeasurable

theorem ae_norm_ofProfile (ℓ : ℤ) (h : ℝ → ℂ) :
    ∀ᵐ x ∂(volume : Measure ℂ), ‖ofProfile ℓ h x‖ = ‖h ‖x‖‖ := by
  filter_upwards [ae_ne_zero] with x hx
  rw [ofProfile, norm_mul, norm_angPhase hx, mul_one]

theorem toReal_eLpNorm_two_sq {F : ℂ → ℂ} (hF : AEStronglyMeasurable F volume) :
    (eLpNorm F 2 volume).toReal ^ 2 = ∫ x, ‖F x‖ ^ 2 := by
  have hm2 : AEStronglyMeasurable (fun x => ‖F x‖ ^ 2) volume := hF.norm.pow 2
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => by positivity)
    hm2, eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    ← ENNReal.toReal_pow]
  congr 1
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  simp only [ENNReal.toReal_ofNat, Nat.cast_ofNat]
  norm_num

end SectorL2Aux

/-- `‖h(r) e^{iℓθ}‖²_{L²} = 2π ∫₀^∞ |h(r)|² r dr`, and membership in `L²` is equivalent to
the integrability of `|h|² r` on `(0, ∞)`. -/
theorem memLp_ofProfile_iff {ℓ : ℤ} {h : ℝ → ℂ}
    (hm : AEStronglyMeasurable h (volume.restrict (Ioi 0))) :
    (MemLp (ofProfile ℓ h) 2 volume ↔
        IntegrableOn (fun r => ‖h r‖ ^ 2 * r) (Ioi 0)) ∧
      Sob.l2 (ofProfile ℓ h) ^ 2 = 2 * π * ∫ r in Ioi 0, ‖h r‖ ^ 2 * r := by
  have hAE := aestronglyMeasurable_ofProfile (ℓ := ℓ) hm
  have hsq : (fun x => ‖ofProfile ℓ h x‖ ^ 2) =ᵐ[volume] fun x => ‖h ‖x‖‖ ^ 2 := by
    filter_upwards [ae_norm_ofProfile ℓ h] with x hx; rw [hx]
  have hfun : (fun r : ℝ => r • ‖h r‖ ^ 2) = fun r => ‖h r‖ ^ 2 * r := by
    funext r; rw [smul_eq_mul, mul_comm]
  refine ⟨?_, ?_⟩
  · rw [memLp_two_iff_integrable_sq_norm hAE, integrable_congr hsq, ← hfun]
    exact Polar.integrable_comp_norm_iff (f := fun r => ‖h r‖ ^ 2)
  · rw [Sob.l2, toReal_eLpNorm_two_sq hAE, integral_congr_ae hsq]
    have := Polar.integral_comp_norm (fun r => ‖h r‖ ^ 2)
    rw [this, hfun, smul_eq_mul]

end NonUniqueEuler.Ang
