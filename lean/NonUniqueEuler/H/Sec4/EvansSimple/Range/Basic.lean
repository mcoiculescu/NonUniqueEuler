import NonUniqueEuler.Defs.Sec4.Evans
import NonUniqueEuler.Defs.Sec4.Extra1Sector
import NonUniqueEuler.I.Infra.Sobolev.Space
import NonUniqueEuler.I.Infra.Polar.Radial
import NonUniqueEuler.I.Infra.Polar.Fubini
import NonUniqueEuler.I.Infra.AngularFourier.Sector
import NonUniqueEuler.I.Infra.AngularFourier.Derivatives
import NonUniqueEuler.I.Infra.SectorSpace.Decomposition
import NonUniqueEuler.I.Sec4.SemigroupConstruct

/-!
# Helpers for `P/Sec4/EvansSimple/Range`: elements of the sector spaces and their profiles

Generic facts (fully proved), namespace `NonUniqueEuler.EvansRangeAux`:
* extensionality of `Ysec s K ℓ` by the function (`Ysec_ext_fn`), `MemH` of the function, its
  support, and the functions of differences and scalar multiples;
* `ae_comp_norm`: null sets of `(0,∞)` transfer to the plane through `x ↦ |x|`;
* `angularSector_congr_ae`, `green_congr_ae`, `LsecFn_congr_ae`, `ofProfile_congr_ae`: the
  profile objects only see a.e. classes;
* `angularSector_ofProfile`, `profile_of_fn`: `h(r)e^{iℓθ}` has profile `h`;
* `profile_memH1On`, `profile_isProfileL2`, `fn_ae_eq_ofProfile`, `Lsec_fn`, `sub_Lsec_fn`: the
  profile of `g ∈ Y^s_ℓ` and the sector operator through profiles.

Copied (namespace renamed) from `H/Sec4/Resolvent/Basic.lean` and `H/Sec4/Resolvent/Typed.lean`
(themselves copies of `H/Sec4/SemigroupLaw/*`, `H/Sec4/Eigendata/Basic.lean`), which this proof
may not import (import rules, `README.md`).
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace NonUniqueEuler.EvansRangeAux

open Sect Sob Ang

variable {s : ℕ} {K : Set ℂ}

/-! ### Tuples and their functions -/

theorem stronglyMeasurable_tupleFn (F : SobTuple s) : StronglyMeasurable (tupleFn F) :=
  Lp.stronglyMeasurable _

theorem tupleFn_add (F G : SobTuple s) :
    tupleFn (F + G) =ᵐ[volume] tupleFn F + tupleFn G :=
  Lp.coeFn_add (F.ofLp (idx0 s)) (G.ofLp (idx0 s))

theorem tupleFn_sub (F G : SobTuple s) :
    tupleFn (F - G) =ᵐ[volume] tupleFn F - tupleFn G :=
  Lp.coeFn_sub (F.ofLp (idx0 s)) (G.ofLp (idx0 s))

theorem tupleFn_smul (c : ℂ) (F : SobTuple s) :
    tupleFn (c • F) =ᵐ[volume] c • tupleFn F :=
  Lp.coeFn_smul c (F.ofLp (idx0 s))

theorem tuple_ext {F G : SobTuple s} (hF : F ∈ HkSub s) (hG : G ∈ HkSub s)
    (h : tupleFn F =ᵐ[volume] tupleFn G) : F = G := by
  have := Hk.ext_fn (F := (⟨F, hF⟩ : Hk s)) (G := ⟨G, hG⟩) h
  exact congrArg Subtype.val this

theorem suppCLM_eq_zero_iff (F : SobTuple s) :
    suppCLM s K F = 0 ↔ ∀ᵐ x ∂volume, x ∉ K → tupleFn F x = 0 := by
  have hc := LpToLpRestrictCLM_coeFn ℂ (μ := (volume : Measure ℂ)) (p := 2) Kᶜ (proj0 s F)
  have hmeas : MeasurableSet {x | tupleFn F x = 0} :=
    (stronglyMeasurable_tupleFn F).measurable (measurableSet_singleton 0)
  rw [suppCLM, ContinuousLinearMap.comp_apply, Lp.eq_zero_iff_ae_eq_zero]
  constructor
  · intro h
    have h2 : tupleFn F =ᵐ[volume.restrict Kᶜ] 0 := hc.symm.trans h
    exact (ae_restrict_iff hmeas).1 h2
  · intro h
    have h2 : ∀ᵐ x ∂volume.restrict Kᶜ, tupleFn F x = 0 := (ae_restrict_iff hmeas).2 h
    filter_upwards [hc, h2] with x hx h2x
    rw [hx]
    exact h2x

theorem mem_YSub_iff (F : SobTuple s) :
    F ∈ YSub s K ↔ F ∈ HkSub s ∧ ∀ᵐ x ∂volume, x ∉ K → tupleFn F x = 0 := by
  rw [YSub, Submodule.mem_inf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    suppCLM_eq_zero_iff]

/-! ### Elements of `Ysec s K ℓ` -/

theorem Ysec_ext_fn {ℓ : ℤ} {g h : Ysec s K ℓ} (hgh : g.fn =ᵐ[volume] h.fn) : g = h :=
  Subtype.ext (tuple_ext (YSub_le_HkSub s K (YsecSub_le_YSub s K ℓ g.2))
    (YSub_le_HkSub s K (YsecSub_le_YSub s K ℓ h.2)) hgh)

theorem Ysec_memH_fn {ℓ : ℤ} (g : Ysec s K ℓ) : MemH s g.fn :=
  (Hk.memH_fn (Y.toHk (inclSec s K ℓ g))).1

theorem Ysec_supp {ℓ : ℤ} (g : Ysec s K ℓ) : ∀ᵐ x ∂volume, x ∉ K → g.fn x = 0 :=
  ((mem_YSub_iff (g : SobTuple s)).1 (YsecSub_le_YSub s K ℓ g.2)).2

theorem Ysec_fn_add {ℓ : ℤ} (g h : Ysec s K ℓ) : (g + h).fn =ᵐ[volume] g.fn + h.fn :=
  tupleFn_add (g : SobTuple s) h

theorem Ysec_fn_sub {ℓ : ℤ} (g h : Ysec s K ℓ) : (g - h).fn =ᵐ[volume] g.fn - h.fn :=
  tupleFn_sub (g : SobTuple s) h

theorem Ysec_fn_smul {ℓ : ℤ} (c : ℂ) (g : Ysec s K ℓ) : (c • g).fn =ᵐ[volume] c • g.fn :=
  tupleFn_smul c (g : SobTuple s)

theorem Ysec_fn_zero {ℓ : ℤ} : (0 : Ysec s K ℓ).fn =ᵐ[volume] 0 := by
  have h := Ysec_fn_smul (0 : ℂ) (0 : Ysec s K ℓ)
  rw [zero_smul, zero_smul] at h
  exact h

/-! ### Null sets of `(0, ∞)` and the plane -/

/-- A property holding for a.e. `r > 0` holds at `|x|` for a.e. `x ∈ ℂ`. -/
theorem ae_comp_norm {P : ℝ → Prop} (hP : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), P r) :
    ∀ᵐ x : ℂ, P ‖x‖ := by
  set μ := (volume : Measure ℝ).restrict (Ioi (0 : ℝ))
  set N := toMeasurable μ {r | ¬ P r}
  have hNm : MeasurableSet N := measurableSet_toMeasurable μ _
  have hμN : μ N = 0 := by
    rw [measure_toMeasurable]
    exact hP
  have hNae : ∀ᵐ r ∂μ, r ∉ N := measure_eq_zero_iff_ae_notMem.1 hμN
  have hpre : MeasurableSet ((fun x : ℂ => ‖x‖) ⁻¹' N) := measurable_norm hNm
  have hvol : volume ((fun x : ℂ => ‖x‖) ⁻¹' N) = 0 := by
    rw [← lintegral_indicator_one hpre]
    have h1 : (fun x : ℂ => ((fun x : ℂ => ‖x‖) ⁻¹' N).indicator (1 : ℂ → ℝ≥0∞) x) =
        fun x : ℂ => N.indicator (1 : ℝ → ℝ≥0∞) ‖x‖ := by
      funext x
      by_cases hx : ‖x‖ ∈ N
      · rw [indicator_of_mem (show x ∈ (fun x : ℂ => ‖x‖) ⁻¹' N from hx),
          indicator_of_mem hx]
        rfl
      · rw [indicator_of_notMem (show x ∉ (fun x : ℂ => ‖x‖) ⁻¹' N from hx),
          indicator_of_notMem hx]
    rw [h1, Polar.lintegral_comp_norm (f := N.indicator (1 : ℝ → ℝ≥0∞))
      (measurable_one.indicator hNm)]
    have h2 : ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * N.indicator (1 : ℝ → ℝ≥0∞) r = 0 := by
      rw [← lintegral_zero (μ := μ)]
      refine lintegral_congr_ae ?_
      filter_upwards [hNae] with r hr
      rw [indicator_of_notMem hr, mul_zero]
    rw [h2, mul_zero]
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hvol] with x hx
  by_contra hPx
  exact hx (subset_toMeasurable μ {r | ¬ P r} hPx)

/-! ### Profiles of a.e. equal functions -/

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

/-! ### Profiles `h(r) e^{iℓθ}` -/

theorem angPhase_ofReal {r : ℝ} (hr : 0 < r) (m : ℤ) : angPhase m (r : ℂ) = 1 := by
  have h1 : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_of_nonneg hr.le]
  rw [angPhase, h1, div_self (Complex.ofReal_ne_zero.2 hr.ne'), one_zpow]

/-- The sectors of `h(r) e^{iℓθ}`: `h` in sector `ℓ`, `0` elsewhere (at every `r > 0`). -/
theorem angularSector_ofProfile (ℓ m : ℤ) (h : ℝ → ℂ) {r : ℝ} (hr : 0 < r) :
    Polar.angularSector (ofProfile ℓ h) m r = if m = ℓ then h r else 0 := by
  have hx : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  have h1 := sectorProj_eq_angularSector m (ofProfile ℓ h) hx
  have hn : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_of_nonneg hr.le]
  rw [sectorProj_ofProfile, hn, angPhase_ofReal hr, mul_one] at h1
  rw [← h1]
  split_ifs
  · simp [ofProfile, angPhase_ofReal hr, abs_of_pos hr]
  · rfl

theorem angularSector_ofProfile_self (ℓ : ℤ) (h : ℝ → ℂ) {r : ℝ} (hr : 0 < r) :
    Polar.angularSector (ofProfile ℓ h) ℓ r = h r := by
  rw [angularSector_ofProfile ℓ ℓ h hr]
  simp

theorem angularSector_ofProfile_ae (ℓ : ℤ) (h : ℝ → ℂ) :
    Polar.angularSector (ofProfile ℓ h) ℓ =ᵐ[volume.restrict (Ioi (0 : ℝ))] h := by
  filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
    with r hr
  exact angularSector_ofProfile_self ℓ h hr

/-- `h(r)e^{iℓθ}` determines `h` a.e. on `(0, ∞)`. -/
theorem ofProfile_ae_inj {ℓ : ℤ} {h₁ h₂ : ℝ → ℂ}
    (h : ofProfile ℓ h₁ =ᵐ[volume] ofProfile ℓ h₂) :
    h₁ =ᵐ[volume.restrict (Ioi (0 : ℝ))] h₂ :=
  (angularSector_ofProfile_ae ℓ h₁).symm.trans
    ((angularSector_congr_ae h ℓ).trans (angularSector_ofProfile_ae ℓ h₂))

theorem ofProfile_smul (ℓ : ℤ) (c : ℂ) (h : ℝ → ℂ) :
    ofProfile ℓ (fun r => c * h r) = c • ofProfile ℓ h := by
  funext x
  simp only [ofProfile, Pi.smul_apply, smul_eq_mul]
  ring

theorem ofProfile_sub (ℓ : ℤ) (h₁ h₂ : ℝ → ℂ) :
    ofProfile ℓ (fun r => h₁ r - h₂ r) = ofProfile ℓ h₁ - ofProfile ℓ h₂ := by
  funext x
  simp only [ofProfile, Pi.sub_apply]
  ring

/-! ### Typed facts -/

open SectorSetting in
theorem profile_memH1On (S : SectorSetting) (hS : S.Valid) {s : ℕ} {ℓ : ℤ}
    (g : Ysec s S.Nstar ℓ) :
    Sob.MemH1On s (Ioi 0) (Polar.angularSector g.fn ℓ) ∧
      ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), r ∉ Icc S.ρm S.ρp →
        Polar.angularSector g.fn ℓ r = 0 :=
  memH1On_angularSector hS.ρm_pos (Ysec_memH_fn g) (Ysec_supp g) ℓ

open SectorSetting in
theorem profile_isProfileL2 (S : SectorSetting) (hS : S.Valid) {s : ℕ} {ℓ : ℤ}
    (g : Ysec s S.Nstar ℓ) : S.IsProfileL2 (Polar.angularSector g.fn ℓ) := by
  obtain ⟨hH, hI⟩ := profile_memH1On S hS g
  refine ⟨hH.memLp.mono_measure (Measure.restrict_mono ?_ le_rfl), hI⟩
  exact fun r hr => lt_of_lt_of_le hS.ρm_pos hr.1

theorem fn_ae_eq_ofProfile (S : SectorSetting) (hS : S.Valid) {s : ℕ} {ℓ : ℤ}
    (g : Ysec s S.Nstar ℓ) : g.fn =ᵐ[volume] ofProfile ℓ (Polar.angularSector g.fn ℓ) :=
  Ysec.fn_ae_eq_ofProfile hS.ρm_pos g

theorem Lsec_fn (S : SectorSetting) (hS : S.Valid) {s : ℕ} {ℓ : ℤ} (G : ℝ)
    (g : Ysec s S.Nstar ℓ) :
    (S.Lsec s ℓ G g).fn =ᵐ[volume]
      ofProfile ℓ (S.LsecFn ℓ G (Polar.angularSector g.fn ℓ)) :=
  SectorSetting.semigroupConstruct_Lsec S hS s ℓ G g

/-- The profile of a function `a.e.` equal to `p(r)e^{iℓθ}` is `p`. -/
theorem profile_of_fn {ℓ : ℤ} {f : ℂ → ℂ} {p : ℝ → ℂ} (h : f =ᵐ[volume] ofProfile ℓ p) :
    Polar.angularSector f ℓ =ᵐ[volume.restrict (Ioi (0 : ℝ))] p :=
  (angularSector_congr_ae h ℓ).trans (angularSector_ofProfile_ae ℓ p)

/-- `z g - L_ℓ g = (z g_ℓ - L_ℓ g_ℓ)(r)e^{iℓθ}`. -/
theorem sub_Lsec_fn (S : SectorSetting) (hS : S.Valid) {s : ℕ} {ℓ : ℤ} (z : ℂ) (G : ℝ)
    (g : Ysec s S.Nstar ℓ) :
    (z • g - S.Lsec s ℓ G g).fn =ᵐ[volume]
      ofProfile ℓ (fun r => z * Polar.angularSector g.fn ℓ r -
        S.LsecFn ℓ G (Polar.angularSector g.fn ℓ) r) := by
  rw [ofProfile_sub, ofProfile_smul]
  filter_upwards [Ysec_fn_sub (z • g) (S.Lsec s ℓ G g), Ysec_fn_smul z g,
    fn_ae_eq_ofProfile S hS g, Lsec_fn S hS G g] with x h1 h2 h3 h4
  rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, h4]
  rfl

end NonUniqueEuler.EvansRangeAux
