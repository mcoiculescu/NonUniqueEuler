import NonUniqueEuler.Defs.Sec4.Setting
import NonUniqueEuler.I.Infra.Sobolev.Space
import NonUniqueEuler.I.Infra.Polar.Radial
import NonUniqueEuler.I.Infra.Polar.Fubini
import NonUniqueEuler.I.Infra.AngularFourier.Sector
import NonUniqueEuler.I.Infra.AngularFourier.Derivatives.ProfileL2

/-!
# Helper for `thm:evans-simple`: elements of `Y^s_ℓ`, sector profiles, `L²` pairings

Helper of `P/Sec4/EvansSimple.lean` (fully proved). Namespace `NonUniqueEuler.EvansSimpleAux`.
The first two groups are copied (namespace renamed) from `H/Sec4/SemigroupLaw/Basic.lean`,
`H/Sec4/SemigroupLaw/Profile.lean`, `H/Sec4/SemigroupLaw/Operators.lean` and
`H/Sec4/Eigendata/Basic.lean`, which this proof may not import
(import rules, `README.md`).

* elements of `Y^s_ℓ(K)`: extensionality by the function, support, `L²`, sums and multiples;
* sector profiles: `angularSector_congr_ae` (a.e. equal plane functions have a.e. equal sector
  profiles on `(0,∞)`), `angularSector_ofProfile`, `ofProfile_congr_ae`, `LsecFn_congr_ae`,
  `angPhase_neg`, `ofProfile_neg_conj`;
* `exists_profile_pairing`: for `φ` continuous on `(0,∞)`, `g ↦ ∫_0^∞ g_m(r) φ(r) r dr` is a
  continuous functional on `Y^s_m(closedAnnulus ρ₋ ρ₊)` (`ρ₋ > 0`): it is the `L²` pairing with
  the representer `(2π)⁻¹ φ(|x|) e^{-imθ} 1_{N}` (Fubini in polar coordinates).
-/

noncomputable section

open MeasureTheory Set Real Filter Topology ComplexConjugate
open scoped ENNReal

namespace NonUniqueEuler.EvansSimpleAux

open Sect Sob Ang

variable {s : ℕ} {K : Set ℂ}

/-! ### Tuples and elements of the sector spaces -/

theorem stronglyMeasurable_tupleFn (F : SobTuple s) : StronglyMeasurable (tupleFn F) :=
  Lp.stronglyMeasurable _

theorem tupleFn_add (F G : SobTuple s) :
    tupleFn (F + G) =ᵐ[volume] tupleFn F + tupleFn G :=
  Lp.coeFn_add (F.ofLp (idx0 s)) (G.ofLp (idx0 s))

theorem tupleFn_smul (c : ℂ) (F : SobTuple s) :
    tupleFn (c • F) =ᵐ[volume] c • tupleFn F :=
  Lp.coeFn_smul c (F.ofLp (idx0 s))

theorem tupleFn_sub (F G : SobTuple s) :
    tupleFn (F - G) =ᵐ[volume] tupleFn F - tupleFn G :=
  Lp.coeFn_sub (F.ofLp (idx0 s)) (G.ofLp (idx0 s))

/-- Two elements of `H^s` with a.e. equal functions are equal (as tuples). -/
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

theorem Ysec_ext_fn {ℓ : ℤ} {g h : Ysec s K ℓ} (hgh : g.fn =ᵐ[volume] h.fn) : g = h :=
  Subtype.ext (tuple_ext (YSub_le_HkSub s K (YsecSub_le_YSub s K ℓ g.2))
    (YSub_le_HkSub s K (YsecSub_le_YSub s K ℓ h.2)) hgh)

theorem Ysec_supp {ℓ : ℤ} (g : Ysec s K ℓ) : ∀ᵐ x ∂volume, x ∉ K → g.fn x = 0 :=
  ((mem_YSub_iff (K := K) (g : SobTuple s)).1 (YsecSub_le_YSub s K ℓ g.2)).2

theorem Ysec_memLp_fn {ℓ : ℤ} (g : Ysec s K ℓ) : MemLp g.fn 2 volume :=
  Lp.memLp _

theorem Ysec_fn_add {ℓ : ℤ} (g h : Ysec s K ℓ) : (g + h).fn =ᵐ[volume] g.fn + h.fn :=
  tupleFn_add (g : SobTuple s) h

theorem Ysec_fn_smul {ℓ : ℤ} (c : ℂ) (g : Ysec s K ℓ) : (c • g).fn =ᵐ[volume] c • g.fn :=
  tupleFn_smul c (g : SobTuple s)

theorem Ysec_fn_sub {ℓ : ℤ} (g h : Ysec s K ℓ) : (g - h).fn =ᵐ[volume] g.fn - h.fn :=
  tupleFn_sub (g : SobTuple s) h

/-! ### Sector profiles -/

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

theorem norm_polar {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = r := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
    Complex.norm_exp_ofReal_mul_I, mul_one]

/-- `angPhase ℓ (r e^{iθ}) = e^{iℓθ}` for `r > 0`. -/
theorem angPhase_polar (ℓ : ℤ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    angPhase ℓ ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
      Complex.exp ((ℓ : ℂ) * θ * Complex.I) := by
  unfold angPhase
  rw [norm_polar hr θ, mul_div_cancel_left₀ _ (by exact_mod_cast hr.ne'), ← Complex.exp_int_mul]
  congr 1
  ring

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

/-- The sector profile of a function a.e. equal to `h(r)e^{iℓθ}` is `h` a.e. on `(0,∞)`. -/
theorem angularSector_ae_of_ae_ofProfile {f : ℂ → ℂ} {ℓ : ℤ} {h : ℝ → ℂ}
    (hf : f =ᵐ[volume] ofProfile ℓ h) :
    Polar.angularSector f ℓ =ᵐ[volume.restrict (Ioi (0 : ℝ))] h := by
  filter_upwards [angularSector_congr_ae hf ℓ,
    self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))] with r hr hr0
  rw [hr, angularSector_ofProfile_self ℓ h hr0]

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

/-- `angPhase (-ℓ) = conj ∘ angPhase ℓ`. -/
theorem angPhase_neg (ℓ : ℤ) (x : ℂ) : angPhase (-ℓ) x = conj (angPhase ℓ x) := by
  unfold angPhase
  rw [map_zpow₀, zpow_neg, ← inv_zpow]
  congr 1
  by_cases hx : x = 0
  · subst hx
    simp
  · have hn : ‖x / (‖x‖ : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm,
        div_self (norm_ne_zero_iff.2 hx)]
    exact Complex.inv_eq_conj hn

/-- `ofProfile (-ℓ) (conj ∘ h) = conj ∘ ofProfile ℓ h`. -/
theorem ofProfile_neg_conj (ℓ : ℤ) (h : ℝ → ℂ) (x : ℂ) :
    ofProfile (-ℓ) (fun r => conj (h r)) x = conj (ofProfile ℓ h x) := by
  unfold ofProfile
  rw [angPhase_neg, map_mul]

/-! ### `L²` pairings with sector profiles -/

/-- `‖conj g‖_{L²} = ‖g‖_{L²}`. -/
theorem l2_conj (g : ℂ → ℂ) : l2 (fun x => conj (g x)) = l2 g := by
  unfold l2
  congr 1
  exact eLpNorm_congr_norm_ae (Eventually.of_forall fun x => by simp)

/-- For `e ∈ L²`, `g ↦ ∫ g e` is a continuous functional on `Y^s_m(K)`. -/
theorem exists_pairing_sec (s : ℕ) (K : Set ℂ) (m : ℤ) {e : ℂ → ℂ} (he : MemLp e 2 volume) :
    ∃ T : Ysec s K m →L[ℂ] ℂ, ∀ g : Ysec s K m, T g = ∫ x, g.fn x * e x := by
  set E : Lp ℂ 2 (volume : Measure ℂ) := he.star.toLp (star e) with hEdef
  refine ⟨(innerSL ℂ E).comp ((proj0 s).comp (YsecSub s K m).subtypeL), fun g => ?_⟩
  rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp he.star] with x hx
  rw [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, hx, RCLike.inner_apply]
  simp only [Pi.star_apply, RCLike.star_def, Complex.conj_conj]
  rfl

theorem continuousAt_angPhase (m : ℤ) {x : ℂ} (hx : x ≠ 0) : ContinuousAt (angPhase m) x := by
  have hn : ((‖x‖ : ℝ) : ℂ) ≠ 0 := by simpa using hx
  have h1 : ContinuousAt (fun y : ℂ => y / ((‖y‖ : ℝ) : ℂ)) x :=
    continuousAt_id.div (Complex.continuous_ofReal.comp continuous_norm).continuousAt hn
  exact h1.zpow₀ m (Or.inl (div_ne_zero hx hn))

/-- **The profile pairing.** For `0 < ρ₋` and `φ` continuous on `(0,∞)`,
`g ↦ ∫_0^∞ g_m(r) φ(r) r dr` is a continuous functional on `Y^s_m(closedAnnulus ρ₋ ρ₊)`. -/
theorem exists_profile_pairing (s : ℕ) {ρm ρp : ℝ} (hρm : 0 < ρm) (m : ℤ) {φ : ℝ → ℂ}
    (hφ : ContinuousOn φ (Ioi 0)) :
    ∃ T : Ysec s (closedAnnulus ρm ρp) m →L[ℂ] ℂ, ∀ g : Ysec s (closedAnnulus ρm ρp) m,
      T g = ∫ r in Ioi (0 : ℝ), Polar.angularSector g.fn m r * φ r * (r : ℂ) := by
  set N := closedAnnulus ρm ρp with hNdef
  have hNm : MeasurableSet N := (isClosed_closedAnnulus ρm ρp).measurableSet
  have hpos : ∀ x ∈ N, x ≠ 0 := by
    intro x hx h0
    rw [h0, hNdef, mem_closedAnnulus, norm_zero] at hx
    linarith [hx.1]
  set e₀ : ℂ → ℂ := fun x => (2 * π : ℂ)⁻¹ * φ ‖x‖ * conj (angPhase m x) with he₀
  have he₀c : ContinuousOn e₀ N := by
    intro x hx
    have hx0 := hpos x hx
    have h1 : ContinuousWithinAt (fun y : ℂ => φ ‖y‖) N x :=
      (hφ.comp continuous_norm.continuousOn fun y hy => norm_pos_iff.2 (hpos y hy)) x hx
    have h2 : ContinuousAt (fun y => conj (angPhase m y)) x :=
      Complex.continuous_conj.continuousAt.comp (continuousAt_angPhase m hx0)
    exact (continuousWithinAt_const.mul h1).mul h2.continuousWithinAt
  set e : ℂ → ℂ := N.indicator e₀ with hedef
  have he : MemLp e 2 volume := by
    rw [hedef, memLp_indicator_iff_restrict hNm]
    have : IsFiniteMeasure (volume.restrict N) :=
      isFiniteMeasure_restrict.2 (isCompact_closedAnnulus ρm ρp).measure_lt_top.ne
    obtain ⟨C, hC⟩ := (isCompact_closedAnnulus ρm ρp).exists_bound_of_continuousOn he₀c
    exact MemLp.of_bound (he₀c.aestronglyMeasurable hNm) C
      ((ae_restrict_iff' hNm).2 (Eventually.of_forall hC))
  obtain ⟨T, hT⟩ := exists_pairing_sec s N m he
  refine ⟨T, fun g => ?_⟩
  rw [hT g]
  have hint : Integrable (fun x => g.fn x * e x) := (Ysec_memLp_fn g).integrable_mul he
  rw [Polar.integral_eq_integral_Ioi_intervalIntegral hint]
  have h2π : (2 * π : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  have hinner : ∀ r : ℝ, 0 < r →
      ∫ θ in (0 : ℝ)..2 * π, g.fn (circleMap 0 r θ) * e (circleMap 0 r θ) =
        (Icc ρm ρp).indicator φ r * Polar.angularSector g.fn m r := by
    intro r hr
    have hmem : ∀ θ : ℝ, circleMap 0 r θ ∈ N ↔ r ∈ Icc ρm ρp := by
      intro θ
      have hc : circleMap 0 r θ = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
        simp [circleMap]
      rw [hNdef, mem_closedAnnulus, hc, norm_polar hr θ]
      rfl
    by_cases hrI : r ∈ Icc ρm ρp
    · rw [Set.indicator_of_mem hrI]
      have hpt : ∀ θ : ℝ, g.fn (circleMap 0 r θ) * e (circleMap 0 r θ) =
          (2 * π : ℂ)⁻¹ * φ r * (g.fn ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
            Complex.exp (-((m : ℂ) * θ * Complex.I))) := by
        intro θ
        have hc : circleMap 0 r θ = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
          simp [circleMap]
        rw [hedef, Set.indicator_of_mem ((hmem θ).2 hrI), hc]
        simp only [he₀]
        rw [norm_polar hr θ, angPhase_polar m hr θ, ← Complex.exp_conj]
        have hcj : conj ((m : ℂ) * θ * Complex.I) = -((m : ℂ) * θ * Complex.I) := by
          simp only [map_mul, map_intCast, Complex.conj_ofReal, Complex.conj_I]
          ring
        rw [hcj]
        ring
      rw [intervalIntegral.integral_congr (fun θ _ => hpt θ), intervalIntegral.integral_const_mul,
        Polar.angularSector]
      ring
    · rw [Set.indicator_of_notMem hrI, zero_mul]
      have hpt : ∀ θ : ℝ, g.fn (circleMap 0 r θ) * e (circleMap 0 r θ) = 0 := by
        intro θ
        rw [hedef, Set.indicator_of_notMem (fun h => hrI ((hmem θ).1 h)), mul_zero]
      simp only [hpt, intervalIntegral.integral_zero]
  have hsec := (memLp_angularSector_of_support hρm (Ysec_memLp_fn g)
    (by
      filter_upwards [Ysec_supp g] with x hx hx'
      exact hx hx') m).2
  rw [ae_restrict_iff' measurableSet_Ioi] at hsec
  refine setIntegral_congr_ae measurableSet_Ioi ?_
  filter_upwards [hsec] with r hr0' hr
  have hr0 := hr0' hr
  rw [hinner r hr, Complex.real_smul]
  by_cases hrI : r ∈ Icc ρm ρp
  · rw [Set.indicator_of_mem hrI]
    ring
  · rw [Set.indicator_of_notMem hrI, hr0 hrI]
    simp

end NonUniqueEuler.EvansSimpleAux
