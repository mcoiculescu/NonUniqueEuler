import NonUniqueEuler.Defs.Sec4.Operators
import NonUniqueEuler.Defs.Sec4.Extra1Sector
import NonUniqueEuler.I.Infra.Polar.Radial
import NonUniqueEuler.I.Infra.SectorSpace.Decomposition
import NonUniqueEuler.I.Infra.AngularFourier.SectorL2
import NonUniqueEuler.I.Infra.AngularFourier.Derivatives.ProfileL2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Proof of `I/Sec4/SectorSetting.lean`: the facts stated inside `def:sector-setting`

Manuscript `04_ring.tex:140-185` (`def:sector-setting` and the remarks after it).

* `circ_eq_integral`: `ω̄` is radial, so `ω̄(y) = ω̄(|y|)` (`om_eq_omR`) and the disk integral is a
  radial integral (`Polar.setIntegral_ball_comp_norm`).
* `contDiffOn_Omega`: on `(0,∞)`, `Ω(r;G) = r⁻² (∫_0^r ω̄(ρ)ρ dρ + G)`; the primitive of the
  smooth function `ρ ↦ ω̄(ρ)ρ` is smooth (`contDiff_infty_iff_deriv`, FTC).
* `isProfileL2_angularSector`: `g ∈ Y^0_ℓ` vanishes a.e. off `N_*` (`Ysec.fn_eq_zero_outside`),
  so its profile is in `L²` and vanishes off `[ρ₋,ρ₊]` (`Ang.memLp_angularSector_of_support`);
  the `Y^0` norm is the `L²` norm (`norm_Ysec_zero`) and `g = g_ℓ(r)e^{iℓθ}` a.e.
  (`Sect.Ysec.fn_ae_eq_ofProfile`), whose `L²` norm is given by `Ang.memLp_ofProfile_iff`.
* `exists_Ysec_zero_of_isProfileL2`: `h ∈ H^0((0,∞))` (`memH1On_zero_of_isProfileL2`), so
  `Sect.exists_Ysec_ofProfile` applies; the profile of the resulting `g` is `h` a.e. because two
  sector functions `h₁(r)e^{iℓθ}`, `h₂(r)e^{iℓθ}` that agree a.e. on the plane have profiles that
  agree a.e. on `(0,∞)` (`ae_eq_of_ofProfile_ae_eq`, polar coordinates).
-/

noncomputable section

open MeasureTheory Set Real
open scoped ContDiff

namespace NonUniqueEuler

namespace SectorSetting

/-! ### Helpers -/

/-- A radial function equals its profile at `|y|`. -/
private theorem om_eq_omR (S : SectorSetting) (hS : S.Valid) (y : ℂ) : S.om y = S.omR ‖y‖ := by
  have h := hS.radial (Complex.arg y) ((‖y‖ : ℝ) : ℂ)
  have hy : rot (Complex.arg y) ((‖y‖ : ℝ) : ℂ) = y := by
    rw [rot, mul_comm]
    exact Complex.norm_mul_exp_arg_mul_I y
  rw [hy] at h
  exact h

/-- The profile `r ↦ ω̄(r)` is smooth on `ℝ`. -/
private theorem contDiff_omR (S : SectorSetting) (hS : S.Valid) : ContDiff ℝ ∞ S.omR := by
  have : S.omR = S.om ∘ Complex.ofRealCLM := by
    funext r
    simp [omR]
  rw [this]
  exact hS.contDiff.comp Complex.ofRealCLM.contDiff

/-- The primitive `r ↦ ∫_0^r ω̄(ρ)ρ dρ` is smooth on `ℝ`. -/
private theorem contDiff_primitive (S : SectorSetting) (hS : S.Valid) :
    ContDiff ℝ ∞ (fun r : ℝ => ∫ ρ in (0 : ℝ)..r, S.omR ρ * ρ) := by
  have hu : ContDiff ℝ ∞ (fun ρ : ℝ => S.omR ρ * ρ) := (contDiff_omR S hS).mul contDiff_id
  have hc : Continuous (fun ρ : ℝ => S.omR ρ * ρ) := hu.continuous
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun r => (hc.integral_hasStrictDerivAt 0 r).hasDerivAt.differentiableAt, ?_⟩
  have : deriv (fun r : ℝ => ∫ ρ in (0 : ℝ)..r, S.omR ρ * ρ) = fun ρ => S.omR ρ * ρ := by
    funext r
    exact Continuous.deriv_integral _ hc 0 r
  rw [this]
  exact hu

/-- The norm of `Y^0_ℓ(K)` is the `L²` norm of the function (there is one multi-index). -/
private theorem norm_Ysec_zero {K : Set ℂ} {ℓ : ℤ} (g : Sect.Ysec 0 K ℓ) : ‖g‖ = Sob.l2 g.fn := by
  have hsum : ∀ F : Sob.SobTuple 0,
      ∑ γ : Sob.SobIdx 0, ‖F.ofLp γ‖ ^ 2 = ‖F.ofLp (Sob.idx0 0)‖ ^ 2 := by
    intro F
    refine Fintype.sum_eq_single _ fun γ hγ => absurd ?_ hγ
    obtain ⟨⟨a, b⟩, hab⟩ := γ
    apply Subtype.ext
    simp only [Sob.multiIdx, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hab
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha hb
    rfl
  rw [Submodule.coe_norm, PiLp.norm_eq_of_L2, hsum, Real.sqrt_sq (norm_nonneg _), Lp.norm_def]
  rfl

/-- An element of `Y^s_ℓ(K)` vanishes almost everywhere outside `K`. -/
private theorem Ysec_fn_eq_zero_outside {s : ℕ} {K : Set ℂ} (hK : MeasurableSet K) {ℓ : ℤ}
    (g : Sect.Ysec s K ℓ) : ∀ᵐ x ∂volume, x ∉ K → g.fn x = 0 := by
  have hmem : (g : Sob.SobTuple s) ∈ Sect.YSub s K := Sect.YsecSub_le_YSub s K ℓ g.2
  have h0 : Sect.suppCLM s K (g : Sob.SobTuple s) = 0 := by
    have := LinearMap.mem_ker.1 (Submodule.mem_inf.1 hmem).2
    simpa using this
  have h1 := LpToLpRestrictCLM_coeFn ℂ Kᶜ (Sect.proj0 s (g : Sob.SobTuple s))
  have h2 : (Sect.suppCLM s K (g : Sob.SobTuple s) : ℂ → ℂ) =ᵐ[volume.restrict Kᶜ] 0 := by
    rw [h0]
    exact Lp.coeFn_zero _ _ _
  have h3 : (Sect.proj0 s (g : Sob.SobTuple s) : ℂ → ℂ) =ᵐ[volume.restrict Kᶜ] 0 :=
    h1.symm.trans h2
  rw [Filter.EventuallyEq, ae_restrict_iff' hK.compl] at h3
  filter_upwards [h3] with x hx hxK
  exact hx hxK

/-- If a nonnegative `φ` satisfies `φ(|x|) = 0` for a.e. `x ∈ ℂ`, then `φ = 0` a.e. on `(0,∞)`. -/
private theorem ae_restrict_Ioi_of_comp_norm {φ : ℝ → ℝ} (hφ : ∀ r, 0 ≤ φ r)
    (h : (fun x : ℂ => φ ‖x‖) =ᵐ[volume] 0) :
    ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), φ r = 0 := by
  have hint : Integrable (fun x : ℂ => φ ‖x‖) := (integrable_zero ℂ ℝ volume).congr h.symm
  have hint' := Polar.integrable_comp_norm_iff.1 hint
  have hI := Polar.integral_comp_norm φ
  have h0 : ∫ x : ℂ, φ ‖x‖ = 0 := by
    rw [integral_congr_ae h]
    simp
  rw [h0] at hI
  have hI0 : ∫ r in Ioi (0 : ℝ), r • φ r = 0 := by
    have := hI.symm
    rw [smul_eq_zero] at this
    exact this.resolve_left (by positivity)
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun r => r • φ r := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    exact mul_nonneg (le_of_lt hr) (hφ r)
  have hz := (integral_eq_zero_iff_of_nonneg_ae hnn hint').1 hI0
  filter_upwards [hz, self_mem_ae_restrict measurableSet_Ioi] with r hr hr0
  have : r * φ r = 0 := hr
  exact (mul_eq_zero.1 this).resolve_left (ne_of_gt hr0)

/-- Two sector functions `h₁(r)e^{iℓθ}`, `h₂(r)e^{iℓθ}` that agree a.e. on the plane have
profiles that agree a.e. on `(0,∞)`. -/
private theorem ae_eq_of_ofProfile_ae_eq {ℓ : ℤ} {h₁ h₂ : ℝ → ℂ}
    (h : Ang.ofProfile ℓ h₁ =ᵐ[volume] Ang.ofProfile ℓ h₂) :
    h₁ =ᵐ[volume.restrict (Ioi 0)] h₂ := by
  have hne : ∀ᵐ x : ℂ ∂volume, x ≠ 0 := by
    rw [ae_iff]
    simp
  have hφ : (fun x : ℂ => ‖h₁ ‖x‖ - h₂ ‖x‖‖) =ᵐ[volume] 0 := by
    filter_upwards [h, hne] with x hx hx0
    have h1 : ‖h₁ ‖x‖ - h₂ ‖x‖‖ = ‖Ang.ofProfile ℓ h₁ x - Ang.ofProfile ℓ h₂ x‖ := by
      rw [Ang.ofProfile, Ang.ofProfile, ← sub_mul, norm_mul, Ang.norm_angPhase hx0, mul_one]
    simp [h1, hx]
  have := ae_restrict_Ioi_of_comp_norm (φ := fun r => ‖h₁ r - h₂ r‖) (fun r => norm_nonneg _) hφ
  filter_upwards [this] with r hr
  exact sub_eq_zero.1 (norm_eq_zero.1 hr)

/-- A profile in `L²([ρ₋,ρ₊])` vanishing a.e. on `(0,∞) \ [ρ₋,ρ₊]` is in `H^0((0,∞))`. -/
private theorem memH1On_zero_of_isProfileL2 (S : SectorSetting) {h : ℝ → ℂ} (hh : S.IsProfileL2 h) :
    Sob.MemH1On 0 (Ioi 0) h := by
  obtain ⟨hL2, hvan⟩ := hh
  have h1 : MemLp ((Icc S.ρm S.ρp).indicator h) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_Icc).2 hL2
  have h2 : MemLp h 2 (volume.restrict (Ioi 0)) := by
    refine (h1.restrict (Ioi 0)).ae_eq ?_
    filter_upwards [hvan] with r hr
    by_cases hrI : r ∈ Icc S.ρm S.ρp
    · simp [indicator_of_mem hrI]
    · simp [indicator_of_notMem hrI, hr hrI]
  refine ⟨h2, fun j hj => ⟨h, h2, ?_⟩⟩
  obtain rfl : j = 0 := Nat.le_zero.1 hj
  intro φ _
  simp [Sob.derivList, Sob.iterDirDeriv]

/-! ### The statements of `I/Sec4/SectorSetting.lean` -/

/-- `Circ_ω̄(r) = 2π ∫_0^r ω̄(ρ) ρ dρ` (`04_ring.tex:174`). -/
theorem circ_eq_integral (S : SectorSetting) (hS : S.Valid) {r : ℝ} (hr : 0 ≤ r) :
    Polar.circ S.om r = 2 * π * ∫ ρ in (0 : ℝ)..r, S.omR ρ * ρ := by
  have h1 : Polar.circ S.om r = ∫ y in Metric.ball (0 : ℂ) r, S.omR ‖y‖ := by
    rw [Polar.circ]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => om_eq_omR S hS y)
  rw [h1, Polar.setIntegral_ball_comp_norm S.omR hr, smul_eq_mul]
  congr 1
  refine intervalIntegral.integral_congr fun ρ _ => ?_
  simp only [smul_eq_mul]
  ring

/-- `Ω(·;G)` is smooth on `(0,∞)` (`04_ring.tex:176-177`). -/
theorem contDiffOn_Omega (S : SectorSetting) (hS : S.Valid) (G : ℝ) :
    ContDiffOn ℝ ∞ (S.Omega G) (Ioi 0) := by
  have hF := contDiff_primitive S hS
  have h1 : ContDiffOn ℝ ∞ (fun r : ℝ => (r ^ 2)⁻¹) (Ioi 0) :=
    (contDiffOn_id.pow 2).inv fun r hr => pow_ne_zero 2 (ne_of_gt hr)
  have h2 : ContDiffOn ℝ ∞
      (fun r : ℝ => (r ^ 2)⁻¹ * ((∫ ρ in (0 : ℝ)..r, S.omR ρ * ρ) + G)) (Ioi 0) :=
    h1.mul ((hF.add (contDiff_const (c := G))).contDiffOn)
  refine h2.congr fun r hr => ?_
  simp only [Omega]
  rw [S.circ_eq_integral hS (le_of_lt hr),
    mul_div_cancel_left₀ _ (by positivity : (2 * π : ℝ) ≠ 0)]

/-- The profile of `g ∈ Y^0_ℓ` lies in `L²([ρ₋,ρ₊])`, vanishes off `[ρ₋,ρ₊]`, and
`‖g‖²_{Y^0_ℓ} = 2π ∫_0^∞ |g_ℓ|² r dr` (`04_ring.tex:159-160`). -/
theorem isProfileL2_angularSector (S : SectorSetting) (hS : S.Valid) (ℓ : ℤ)
    (g : Sect.Ysec 0 S.Nstar ℓ) :
    S.IsProfileL2 (Polar.angularSector g.fn ℓ) ∧
      ‖g‖ ^ 2 = 2 * π * ∫ r in Ioi (0 : ℝ), ‖Polar.angularSector g.fn ℓ r‖ ^ 2 * r := by
  have hK : MeasurableSet S.Nstar := (Sect.isClosed_closedAnnulus _ _).measurableSet
  have hfn : MemLp g.fn 2 volume := Lp.memLp _
  have hsupp : ∀ᵐ x ∂volume, ¬ (S.ρm ≤ ‖x‖ ∧ ‖x‖ ≤ S.ρp) → g.fn x = 0 :=
    Ysec_fn_eq_zero_outside hK g
  obtain ⟨hL2, hvan⟩ := Ang.memLp_angularSector_of_support hS.ρm_pos hfn hsupp ℓ
  refine ⟨⟨hL2.mono_measure (Measure.restrict_mono
    (fun r hr => lt_of_lt_of_le hS.ρm_pos hr.1) le_rfl), hvan⟩, ?_⟩
  have hae : g.fn =ᵐ[volume] Ang.ofProfile ℓ (Polar.angularSector g.fn ℓ) :=
    Sect.Ysec.fn_ae_eq_ofProfile (ρm := S.ρm) (ρp := S.ρp) hS.ρm_pos g
  have hl2 : Sob.l2 g.fn = Sob.l2 (Ang.ofProfile ℓ (Polar.angularSector g.fn ℓ)) := by
    simp only [Sob.l2]
    rw [eLpNorm_congr_ae hae]
  rw [norm_Ysec_zero, hl2]
  exact (Ang.memLp_ofProfile_iff hL2.aestronglyMeasurable).2

/-- Every profile in `L²([ρ₋,ρ₊])` vanishing off `[ρ₋,ρ₊]` is the profile of an element of
`Y^0_ℓ` (`04_ring.tex:159-160`). -/
theorem exists_Ysec_zero_of_isProfileL2 (S : SectorSetting) (hS : S.Valid) (ℓ : ℤ)
    {h : ℝ → ℂ} (hh : S.IsProfileL2 h) :
    ∃ g : Sect.Ysec 0 S.Nstar ℓ, g.fn =ᵐ[volume] Ang.ofProfile ℓ h ∧
      Polar.angularSector g.fn ℓ =ᵐ[volume.restrict (Ioi 0)] h := by
  have hH : Sob.MemH1On 0 (Ioi 0) h := memH1On_zero_of_isProfileL2 S hh
  obtain ⟨g, hg⟩ := Sect.exists_Ysec_ofProfile (s := 0) hS.ρm_pos hS.ρm_lt_ρp ℓ hH hh.2
  refine ⟨g, hg, ?_⟩
  have h2 : g.fn =ᵐ[volume] Ang.ofProfile ℓ (Polar.angularSector g.fn ℓ) :=
    Sect.Ysec.fn_ae_eq_ofProfile (ρm := S.ρm) (ρp := S.ρp) hS.ρm_pos g
  exact ae_eq_of_ofProfile_ae_eq (h2.symm.trans hg)

end SectorSetting

end NonUniqueEuler
