import NonUniqueEuler.Defs.Sec4.Extra1Sector
import NonUniqueEuler.Defs.Infra.ConvMinkowski
import NonUniqueEuler.I.Infra.Polar.Radial
import NonUniqueEuler.I.Infra.AngularFourier.SectorL2

/-!
# Helper for `couplingFn_ofProfile`: rotations, profiles in `Y^0_ℓ`, almost every radius

Helper file of `P/Sec4/Sector/CouplingOfProfile.lean` (fully proved). Namespace
`NonUniqueEuler.CouplingOfProfileH`.

* Rotations: `rot_arg_norm`, `angPhase_rot`, `ofProfile_rot`, `angPhase_eq_exp_arg`
  (copies of the corresponding lemmas of `H/Sec4/Sector/LogPot.lean`, which no other proof may
  import).
* Almost every radius versus almost every point: `ae_of_ae_norm` (copy of
  `H/Sec4/Sector/Transport.lean`) and its converse `ae_restrict_Ioi_of_ae_norm` for measurable
  predicates.
* Profiles in `Y^0_ℓ`: `aestronglyMeasurable_profile`, `integrableOn_profile_sq`,
  `memLp_ofProfile`, `ofProfile_eq_zero_of_le`.
* The majorant `|K_BS| ⋆ |W|` of a sector function is radial (`convAbs_rot`, `convAbs_eq_norm`)
  and measurable (`measurable_convAbs`).
-/

noncomputable section

open MeasureTheory Set Real Filter
open scoped ENNReal

namespace NonUniqueEuler.CouplingOfProfileH

open Ang SectorSetting

/-! ### Rotations -/

theorem measurableEmbedding_rot (θ : ℝ) : MeasurableEmbedding (rot θ) := by
  rw [Polar.rot_eq_rotation]
  exact (rotation (Circle.exp θ)).toHomeomorph.measurableEmbedding

theorem rot_arg_norm (x : ℂ) : rot (Complex.arg x) (‖x‖ : ℂ) = x := by
  rw [rot, mul_comm]
  exact Complex.norm_mul_exp_arg_mul_I x

theorem angPhase_rot (ℓ : ℤ) (θ : ℝ) (y : ℂ) :
    angPhase ℓ (rot θ y) = Complex.exp ((ℓ : ℂ) * θ * Complex.I) * angPhase ℓ y := by
  rw [angPhase, angPhase, Polar.norm_rot, rot, mul_div_assoc, mul_zpow, mul_assoc,
    Complex.exp_int_mul]

theorem angPhase_ofReal (ℓ : ℤ) {r : ℝ} (hr : 0 < r) : angPhase ℓ (r : ℂ) = 1 := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [angPhase, Complex.norm_real, Real.norm_of_nonneg hr.le, div_self hr', one_zpow]

theorem ofProfile_rot (ℓ : ℤ) (g : ℝ → ℂ) (θ : ℝ) (y : ℂ) :
    ofProfile ℓ g (rot θ y) = Complex.exp ((ℓ : ℂ) * θ * Complex.I) * ofProfile ℓ g y := by
  rw [ofProfile, ofProfile, Polar.norm_rot, angPhase_rot]
  ring

theorem angPhase_eq_exp_arg (ℓ : ℤ) {x : ℂ} (hx : x ≠ 0) :
    angPhase ℓ x = Complex.exp ((ℓ : ℂ) * (Complex.arg x : ℝ) * Complex.I) := by
  conv_lhs => rw [← rot_arg_norm x]
  rw [angPhase_rot, angPhase_ofReal ℓ (norm_pos_iff.2 hx), mul_one]

theorem angPhase_circleMap (ℓ : ℤ) {ρ : ℝ} (hρ : 0 < ρ) (θ : ℝ) :
    angPhase ℓ (circleMap 0 ρ θ) = Complex.exp ((ℓ : ℂ) * θ * Complex.I) := by
  have : circleMap 0 ρ θ = rot θ (ρ : ℂ) := by
    simp only [circleMap, zero_add, rot]
    ring
  rw [this, angPhase_rot, angPhase_ofReal ℓ hρ, mul_one]

/-! ### Almost every radius, almost every point -/

theorem ae_of_ae_norm {P : ℝ → Prop} (h : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), P r) :
    ∀ᵐ x : ℂ, P ‖x‖ := by
  set N := toMeasurable (volume.restrict (Ioi (0 : ℝ))) {r | ¬ P r} with hN
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : volume.restrict (Ioi (0 : ℝ)) N = 0 := by
    rw [hN, measure_toMeasurable]
    exact h
  have hpre : MeasurableSet ((fun x : ℂ => ‖x‖) ⁻¹' N) := measurable_norm hNm
  have hvol : volume ((fun x : ℂ => ‖x‖) ⁻¹' N) = 0 := by
    have hF : Measurable (N.indicator (1 : ℝ → ℝ≥0∞)) := measurable_one.indicator hNm
    have h1 := Polar.lintegral_comp_norm hF
    have h2 : ∫⁻ x : ℂ, N.indicator (1 : ℝ → ℝ≥0∞) ‖x‖ =
        volume ((fun x : ℂ => ‖x‖) ⁻¹' N) := by
      rw [← lintegral_indicator_one hpre]
      congr 1
    have h3 : ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * N.indicator (1 : ℝ → ℝ≥0∞) r = 0 := by
      refine (lintegral_eq_zero_iff (measurable_id.ennreal_ofReal.mul hF)).2 ?_
      have : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), r ∉ N := by
        rw [ae_iff]
        simpa using hN0
      filter_upwards [this] with r hr
      simp [hr]
    rw [← h2, h1, h3, mul_zero]
  have hsub : {x : ℂ | ¬ P ‖x‖} ⊆ (fun x : ℂ => ‖x‖) ⁻¹' N := fun x hx =>
    subset_toMeasurable _ _ hx
  rw [ae_iff]
  exact measure_mono_null hsub hvol

/-- Converse of `ae_of_ae_norm` for a measurable set of bad radii. -/
theorem ae_restrict_Ioi_of_ae_norm {N : Set ℝ} (hN : MeasurableSet N)
    (h : ∀ᵐ x : ℂ, ‖x‖ ∉ N) : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), r ∉ N := by
  have hF : Measurable (N.indicator (1 : ℝ → ℝ≥0∞)) := measurable_one.indicator hN
  have hpre : MeasurableSet ((fun x : ℂ => ‖x‖) ⁻¹' N) := measurable_norm hN
  have hvol : volume ((fun x : ℂ => ‖x‖) ⁻¹' N) = 0 := by
    simp only [ae_iff, not_not] at h
    exact h
  have h1 := Polar.lintegral_comp_norm hF
  have h2 : ∫⁻ x : ℂ, N.indicator (1 : ℝ → ℝ≥0∞) ‖x‖ =
      volume ((fun x : ℂ => ‖x‖) ⁻¹' N) := by
    rw [← lintegral_indicator_one hpre]
    congr 1
  rw [h2, hvol] at h1
  have h3 : ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * N.indicator (1 : ℝ → ℝ≥0∞) r = 0 := by
    have h4 : (2 * ENNReal.ofReal π) ≠ 0 := by
      simp [Real.pi_pos]
    exact (mul_eq_zero.1 h1.symm).resolve_left h4
  have h5 := (lintegral_eq_zero_iff (measurable_id.ennreal_ofReal.mul hF)).1 h3
  rw [EventuallyEq] at h5
  filter_upwards [h5, ae_restrict_mem measurableSet_Ioi] with r hr hr0 hrN
  have hr0' : (0 : ℝ) < r := hr0
  have h6 : ENNReal.ofReal r * N.indicator (1 : ℝ → ℝ≥0∞) r = 0 := hr
  rw [indicator_of_mem hrN, Pi.one_apply, mul_one, ENNReal.ofReal_eq_zero] at h6
  linarith

/-! ### Profiles in `Y^0_ℓ` -/

theorem profile_ae_zero {S : SectorSetting} {g : ℝ → ℂ} (hg : S.IsProfileL2 g) :
    g =ᵐ[volume.restrict (Ioi 0 \ Icc S.ρm S.ρp)] 0 := by
  have h := hg.2
  rw [ae_restrict_iff' measurableSet_Ioi] at h
  rw [EventuallyEq, ae_restrict_iff' (measurableSet_Ioi.diff measurableSet_Icc)]
  filter_upwards [h] with r hr hr'
  exact hr hr'.1 hr'.2

theorem Ioi_subset_union (a b : ℝ) :
    Ioi (0 : ℝ) ⊆ Icc a b ∪ (Ioi 0 \ Icc a b) := by
  intro r hr
  by_cases h : r ∈ Icc a b
  · exact Or.inl h
  · exact Or.inr ⟨hr, h⟩

theorem aestronglyMeasurable_profile {S : SectorSetting} {g : ℝ → ℂ} (hg : S.IsProfileL2 g) :
    AEStronglyMeasurable g (volume.restrict (Ioi 0)) := by
  have h1 : AEStronglyMeasurable g (volume.restrict (Icc S.ρm S.ρp)) :=
    hg.1.aestronglyMeasurable
  have h2 : AEStronglyMeasurable g (volume.restrict (Ioi 0 \ Icc S.ρm S.ρp)) :=
    aestronglyMeasurable_zero.congr (profile_ae_zero hg).symm
  have h3 : AEStronglyMeasurable g
      (volume.restrict (Icc S.ρm S.ρp ∪ (Ioi 0 \ Icc S.ρm S.ρp))) :=
    aestronglyMeasurable_union_iff.2 ⟨h1, h2⟩
  exact h3.mono_measure (Measure.restrict_mono (Ioi_subset_union _ _) le_rfl)

theorem integrableOn_profile_sq {S : SectorSetting} {g : ℝ → ℂ} (hg : S.IsProfileL2 g) :
    IntegrableOn (fun r => ‖g r‖ ^ 2 * r) (Ioi 0) := by
  have h1 : IntegrableOn (fun r => ‖g r‖ ^ 2) (Icc S.ρm S.ρp) :=
    hg.1.integrable_norm_pow (by norm_num)
  have h2 : IntegrableOn (fun r => ‖g r‖ ^ 2 * r) (Icc S.ρm S.ρp) :=
    h1.mul_continuousOn continuousOn_id isCompact_Icc
  have h3 : IntegrableOn (fun r => ‖g r‖ ^ 2 * r) (Ioi 0 \ Icc S.ρm S.ρp) := by
    refine (integrable_zero _ _ _).congr ?_
    filter_upwards [profile_ae_zero hg] with r hr
    simp [hr]
  exact (h2.union h3).mono_set (Ioi_subset_union _ _)

theorem memLp_ofProfile {S : SectorSetting} {g : ℝ → ℂ} (hg : S.IsProfileL2 g) (ℓ : ℤ) :
    MemLp (ofProfile ℓ g) 2 volume :=
  ((memLp_ofProfile_iff (ℓ := ℓ) (aestronglyMeasurable_profile hg)).1).2
    (integrableOn_profile_sq hg)

theorem ofProfile_eq_zero_of_le {S : SectorSetting} {g : ℝ → ℂ} (hg : S.IsProfileL2 g)
    (ℓ : ℤ) : ∀ᵐ y : ℂ, S.ρp + 1 ≤ ‖y‖ → ofProfile ℓ g y = 0 := by
  filter_upwards [ae_of_ae_norm hg.2] with y hy hle
  have : ‖y‖ ∉ Icc S.ρm S.ρp := fun h => by linarith [h.2]
  rw [ofProfile, hy this, zero_mul]

/-! ### The majorant `|K_BS| ⋆ |W|` -/

theorem measurable_bsKernel : Measurable biotSavartKernel := by
  unfold biotSavartKernel
  fun_prop

theorem norm_bsKernel_rot (θ : ℝ) (z : ℂ) :
    ‖biotSavartKernel (rot θ z)‖ = ‖biotSavartKernel z‖ := by
  simp only [biotSavartKernel, norm_div, norm_mul, Polar.norm_rot, Complex.norm_I,
    Complex.norm_real]

theorem norm_exp_int_mul_I (ℓ : ℤ) (θ : ℝ) :
    ‖Complex.exp ((ℓ : ℂ) * θ * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem convAbs_rot (ℓ : ℤ) (g : ℝ → ℂ) (θ : ℝ) (x : ℂ) :
    Conv.convAbs biotSavartKernel (ofProfile ℓ g) (rot θ x) =
      Conv.convAbs biotSavartKernel (ofProfile ℓ g) x := by
  simp only [Conv.convAbs]
  rw [← (Polar.measurePreserving_rot θ).lintegral_comp_emb (measurableEmbedding_rot θ)]
  refine lintegral_congr fun y => ?_
  have e : rot θ x - rot θ y = rot θ (x - y) := by
    simp only [rot]
    ring
  rw [e, ofProfile_rot, enorm_mul, ← ofReal_norm, norm_bsKernel_rot, ofReal_norm,
    ← ofReal_norm (Complex.exp _), norm_exp_int_mul_I, ENNReal.ofReal_one, one_mul]

theorem convAbs_eq_norm (ℓ : ℤ) (g : ℝ → ℂ) (x : ℂ) :
    Conv.convAbs biotSavartKernel (ofProfile ℓ g) x =
      Conv.convAbs biotSavartKernel (ofProfile ℓ g) (‖x‖ : ℂ) := by
  conv_lhs => rw [← rot_arg_norm x]
  exact convAbs_rot ℓ g _ _

theorem measurable_convAbs {f : ℂ → ℂ} (hf : AEStronglyMeasurable f volume) :
    Measurable (Conv.convAbs biotSavartKernel f) := by
  obtain ⟨f', hf'm, hff'⟩ := hf
  have e : Conv.convAbs biotSavartKernel f = Conv.convAbs biotSavartKernel f' := by
    funext x
    simp only [Conv.convAbs]
    refine lintegral_congr_ae ?_
    filter_upwards [hff'] with y hy
    rw [hy]
  rw [e]
  have hm : Measurable (fun p : ℂ × ℂ => ‖biotSavartKernel (p.1 - p.2)‖ₑ * ‖f' p.2‖ₑ) :=
    ((measurable_bsKernel.comp (measurable_fst.sub measurable_snd)).enorm).mul
      (hf'm.measurable.comp measurable_snd).enorm
  exact hm.lintegral_prod_right'

end NonUniqueEuler.CouplingOfProfileH
