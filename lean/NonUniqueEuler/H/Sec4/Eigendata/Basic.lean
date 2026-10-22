import NonUniqueEuler.Defs.Sec4.Extra2Eigendata
import NonUniqueEuler.I.Infra.Polar.Fubini
import NonUniqueEuler.I.Infra.AngularFourier.Sector
import NonUniqueEuler.I.Infra.Sobolev.Space
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

/-!
# Helpers for `def:eigendata`: generic facts (profiles, angular sectors, `Y^s(K)`)

Helper of `P/Sec4/Eigendata.lean` (fully proved). Namespace `NonUniqueEuler.Eig.EigendataH`.

* `ae_circle_of_ae`, `angularSector_congr_ae`, `ellFn_congr_ae`: `ℓ_*(G)` on functions only sees
  the a.e. class (Tonelli in polar coordinates);
* `mem_YSub_iff`, `Y_memH_fn`, `Y_fn_zero_outside`, `exists_Y_of_memH`, `Y_fn_add`, `Y_fn_smul`,
  `Y_ext_fn`, `memYsym_of_fn`: functions of elements of `Y^s(K)`;
* `angPhase_ofReal`, `angPhase_circleMap`, `angPhase_rot`, `angularSector_ofProfile`,
  `ofProfile_rot`: profiles `h(r)e^{iℓθ}`;
* `contDiff_ofProfile`, `hasCompactSupport_ofProfile`: a profile smooth on `(0,∞)` and vanishing
  off `[r₁, r₂] ⊂ (0,∞)` gives a smooth compactly supported function `h(r)e^{iℓθ}` (`ℓ ≠ 0`).

The first two groups are copied (namespace renamed) from `H/Sec5/Seed/Basic.lean` and
`H/Sec5/LinearPart/Bridge.lean`, the profile lemmas from
`H/Infra/AngularFourier/NormEquiv/Profile.lean` and
`H/Infra/AngularFourier/Derivatives/ProfileDeriv/Smooth.lean`, which this proof may not import
(import rules, `README.md`).
-/

noncomputable section

open MeasureTheory Set Real Filter Topology ComplexConjugate
open scoped ENNReal ContDiff

namespace NonUniqueEuler.Eig.EigendataH

open Sect Sob Ang

/-! ### `ℓ_*` only sees the a.e. class -/

/-- The polar parametrization `(r, θ) ↦ r e^{iθ}` is continuous. -/
theorem continuous_circleMap_prod :
    Continuous fun p : ℝ × ℝ => circleMap 0 p.1 p.2 := by
  simp only [circleMap, zero_add]
  exact (Complex.continuous_ofReal.comp continuous_fst).mul
    (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))

/-- If `f = g` a.e. on the plane, then for a.e. `r > 0`, `f = g` a.e. on the circle of
radius `r` (parametrized by `θ ∈ (0, 2π]`). -/
theorem ae_circle_of_ae {f g : ℂ → ℂ} (h : f =ᵐ[volume] g) :
    ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), ∀ᵐ θ ∂(volume.restrict (Ioc (0 : ℝ) (2 * π))),
      f (circleMap 0 r θ) = g (circleMap 0 r θ) := by
  set N : Set ℂ := toMeasurable volume {x | ¬ f x = g x} with hNdef
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : volume N = 0 := by
    rw [hNdef, measure_toMeasurable]
    exact h
  have hsub : {x | ¬ f x = g x} ⊆ N := subset_toMeasurable _ _
  set F : ℂ → ℝ≥0∞ := N.indicator 1 with hFdef
  have hFm : Measurable F := measurable_one.indicator hNm
  have hFc : Measurable fun p : ℝ × ℝ => F (circleMap 0 p.1 p.2) :=
    hFm.comp continuous_circleMap_prod.measurable
  have hI : ∫⁻ x, F x = 0 := by
    rw [hFdef, lintegral_indicator_one hNm]
    exact hN0
  rw [Polar.lintegral_eq_lintegral_Ioi_circle hFm] at hI
  have hmeas : Measurable fun r : ℝ =>
      ENNReal.ofReal r * ∫⁻ θ in Ioc (0 : ℝ) (2 * π), F (circleMap 0 r θ) :=
    ENNReal.measurable_ofReal.mul (hFc.lintegral_prod_right' (ν := volume.restrict _))
  have h0 := (lintegral_eq_zero_iff hmeas).1 hI
  have hpos : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), r ∈ Ioi (0 : ℝ) :=
    ae_restrict_mem measurableSet_Ioi
  filter_upwards [h0, hpos] with r hr hrpos
  have hr' : ENNReal.ofReal r * ∫⁻ θ in Ioc (0 : ℝ) (2 * π), F (circleMap 0 r θ) = 0 := hr
  rcases mul_eq_zero.1 hr' with h1 | h1
  · exact absurd h1 (ENNReal.ofReal_pos.2 hrpos).ne'
  · have h2 := (lintegral_eq_zero_iff (hFm.comp (continuous_circleMap 0 r).measurable)).1 h1
    filter_upwards [h2] with θ hθ
    by_contra hne
    have hmem : circleMap 0 r θ ∈ N := hsub hne
    have h3 : F (circleMap 0 r θ) = 1 := by
      rw [hFdef, Set.indicator_of_mem hmem]
      rfl
    have h4 : F (circleMap 0 r θ) = 0 := hθ
    rw [h3] at h4
    exact one_ne_zero h4

/-- The angular sectors of a.e. equal functions agree a.e. on `(0, ∞)`. -/
theorem angularSector_congr_ae {f g : ℂ → ℂ} (h : f =ᵐ[volume] g) (ℓ : ℤ) :
    Polar.angularSector f ℓ =ᵐ[volume.restrict (Ioi (0 : ℝ))] Polar.angularSector g ℓ := by
  filter_upwards [ae_circle_of_ae h] with r hr
  unfold Polar.angularSector
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  rw [uIoc_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
  rw [ae_restrict_iff' measurableSet_Ioc] at hr
  filter_upwards [hr] with θ hθ hmem
  have hc : ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = circleMap 0 r θ := by
    simp [circleMap]
  rw [hc, hθ hmem]

/-- `ℓ_*(G)` on functions (`Eig.ellFn`) only depends on the a.e. class. -/
theorem ellFn_congr_ae (χ : ℝ → ℝ) (G : ℝ) {f g : ℂ → ℂ} (h : f =ᵐ[volume] g) :
    Eig.ellFn χ G f = Eig.ellFn χ G g := by
  unfold Eig.ellFn SectorSetting.ellStar
  congr 2
  refine integral_congr_ae ?_
  filter_upwards [angularSector_congr_ae h 3] with r hr
  rw [hr]

/-! ### Functions of elements of `Y^s(K)` -/

section YFn

variable {s : ℕ} {K : Set ℂ}

theorem stronglyMeasurable_tupleFn (F : SobTuple s) : StronglyMeasurable (tupleFn F) :=
  Lp.stronglyMeasurable _

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

/-- The function of `w ∈ Y^s(K)` lies in `H^s`, with `‖w.fn‖_{H^s} = ‖w‖`. -/
theorem Y_memH_fn (w : Y s K) : MemH s w.fn ∧ normH s w.fn = ‖w‖ :=
  Hk.memH_fn (Y.toHk w)

/-- The function of `w ∈ Y^s(K)` vanishes a.e. outside `K`. -/
theorem Y_fn_zero_outside (w : Y s K) : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ K → w.fn x = 0 :=
  ((mem_YSub_iff (K := K) (w : SobTuple s)).1 w.2).2

/-- The function of `w ∈ Y^s(K)` is in `L²`. -/
theorem Y_memLp_fn (w : Y s K) : MemLp w.fn 2 volume :=
  Lp.memLp _

/-- An `H^s` function vanishing a.e. outside `K` is (a.e.) the function of an element of
`Y^s(K)`. -/
theorem exists_Y_of_memH {f : ℂ → ℂ} (hf : MemH s f)
    (hK : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ K → f x = 0) : ∃ w : Y s K, w.fn =ᵐ[volume] f := by
  obtain ⟨F, hF⟩ := memH_iff_exists_Hk.1 hf
  have hmem : (F : SobTuple s) ∈ YSub s K := by
    refine (mem_YSub_iff (F : SobTuple s)).2 ⟨F.2, ?_⟩
    have hF' : tupleFn (F : SobTuple s) =ᵐ[volume] f := hF
    filter_upwards [hF', hK] with x hx hKx hxK
    rw [hx]
    exact hKx hxK
  exact ⟨⟨(F : SobTuple s), hmem⟩, hF⟩

/-- An element of `Y^s(K)` is determined by its function. -/
theorem Y_ext_fn {w₁ w₂ : Y s K} (h : w₁.fn =ᵐ[volume] w₂.fn) : w₁ = w₂ := by
  have : Y.toHk w₁ = Y.toHk w₂ := Hk.ext_fn h
  exact Subtype.ext (show (w₁ : SobTuple s) = w₂ from
    congrArg (fun F : Hk s => (F : SobTuple s)) this)

/-- The function of a sum is the sum of the functions, a.e. -/
theorem Y_fn_add (v w : Y s K) : (v + w).fn =ᵐ[volume] fun x => v.fn x + w.fn x := by
  have h : ((v + w : Y s K) : SobTuple s).ofLp (idx0 s) =
      (v : SobTuple s).ofLp (idx0 s) + (w : SobTuple s).ofLp (idx0 s) := rfl
  have h2 := Lp.coeFn_add ((v : SobTuple s).ofLp (idx0 s)) ((w : SobTuple s).ofLp (idx0 s))
  unfold Y.fn tupleFn
  rw [h]
  exact h2

/-- The function of a scalar multiple is the scalar multiple of the function, a.e. -/
theorem Y_fn_smul (c : ℂ) (w : Y s K) : (c • w).fn =ᵐ[volume] fun x => c * w.fn x := by
  have h : ((c • w : Y s K) : SobTuple s).ofLp (idx0 s) =
      c • (w : SobTuple s).ofLp (idx0 s) := rfl
  have h2 := Lp.coeFn_smul c ((w : SobTuple s).ofLp (idx0 s))
  unfold Y.fn tupleFn
  rw [h]
  filter_upwards [h2] with x hx
  rw [hx]
  rfl

/-- `proj0` of `w ∈ Y^s(K)` is the `L²` class of `w.fn`. -/
theorem coeFn_proj0 (w : Y s K) :
    ((proj0 s (w : SobTuple s) : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) = w.fn := rfl

/-- If the function of `w ∈ Y^s(K)` is `m`-fold symmetric, then `w` lies in the `m`-fold
symmetric part. -/
theorem mem_YsymSub_of_fn {m : ℕ} (w : Y s K) (hw : IsMFoldSymmetricC m w.fn) :
    (w : SobTuple s) ∈ YsymSub s K m := by
  refine Submodule.mem_inf.2 ⟨w.2, LinearMap.mem_ker.2 ?_⟩
  rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
    sub_apply, ContinuousLinearMap.id_apply, sub_eq_zero]
  set F : Lp ℂ 2 (volume : Measure ℂ) := proj0 s (w : SobTuple s) with hFdef
  have hF : (F : ℂ → ℂ) = w.fn := rfl
  refine Lp.ext ?_
  refine (rotLp_coeFn (2 * π / (m : ℝ)) F).trans ?_
  rw [hF]
  exact hw

/-- `m`-fold symmetry transfers along a.e. equality. -/
theorem isMFoldSymmetricC_congr {m : ℕ} {f g : ℂ → ℂ} (hfg : f =ᵐ[volume] g)
    (hg : IsMFoldSymmetricC m g) : IsMFoldSymmetricC m f := by
  have h1 : (fun x => f (rot (2 * π / (m : ℝ)) x)) =ᵐ[volume]
      fun x => g (rot (2 * π / (m : ℝ)) x) :=
    (Polar.measurePreserving_rot _).quasiMeasurePreserving.ae_eq_comp hfg
  exact h1.trans ((hg : (fun x => g (rot (2 * π / (m : ℝ)) x)) =ᵐ[volume] g).trans hfg.symm)

end YFn

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

theorem angPhase_circleMap (m : ℤ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    angPhase m (circleMap 0 r θ) = Complex.exp ((m : ℂ) * (θ * Complex.I)) := by
  have hn : ‖circleMap 0 r θ‖ = r := by rw [norm_circleMap_zero, abs_of_pos hr]
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [angPhase, hn, circleMap_zero, Complex.exp_int_mul]
  congr 1
  field_simp

/-- The phase is equivariant: `angPhase ℓ (O_φ x) = e^{iℓφ} angPhase ℓ x`. -/
theorem angPhase_rot (ℓ : ℤ) (φ : ℝ) (x : ℂ) :
    angPhase ℓ (rot φ x) = Complex.exp ((ℓ : ℂ) * φ * Complex.I) * angPhase ℓ x := by
  unfold angPhase
  rw [Polar.norm_rot, rot, mul_div_assoc, mul_zpow, ← Complex.exp_int_mul, mul_assoc]

/-- `e^{3 i (2π/3)} = 1`. -/
theorem exp_three_two_pi_div_three :
    Complex.exp (((3 : ℤ) : ℂ) * ((2 * π / ((3 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) = 1 := by
  have h : ((3 : ℤ) : ℂ) * ((2 * π / ((3 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I =
      2 * (π : ℂ) * Complex.I := by
    push_cast
    field_simp
  rw [h, Complex.exp_two_pi_mul_I]

/-- `h(r)e^{3iθ}` is `3`-fold symmetric, pointwise. -/
theorem ofProfile_three_rot (h : ℝ → ℂ) (x : ℂ) :
    ofProfile 3 h (rot (2 * π / ((3 : ℕ) : ℝ)) x) = ofProfile 3 h x := by
  unfold ofProfile
  rw [Polar.norm_rot, angPhase_rot, exp_three_two_pi_div_three, one_mul]

/-! ### Smoothness of profiles -/

theorem contDiffAt_ofReal_norm {x : ℂ} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (fun y : ℂ => ((‖y‖ : ℝ) : ℂ)) x :=
  Complex.ofRealCLM.contDiff.contDiffAt.comp x (contDiffAt_norm ℝ hx)

theorem ofReal_norm_ne_zero {x : ℂ} (hx : x ≠ 0) : ((‖x‖ : ℝ) : ℂ) ≠ 0 := by
  simpa using hx

theorem contDiffAt_inv_ofReal_norm {x : ℂ} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (fun y : ℂ => ((‖y‖ : ℝ) : ℂ)⁻¹) x :=
  (contDiffAt_ofReal_norm hx).fun_inv (ofReal_norm_ne_zero hx)

theorem contDiffAt_unit {x : ℂ} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (fun y : ℂ => y / (‖y‖ : ℂ)) x := by
  have h := (contDiffAt_id (𝕜 := ℝ) (x := x)).mul (contDiffAt_inv_ofReal_norm hx)
  simpa [div_eq_mul_inv] using h

theorem contDiffAt_zpow_comp {u : ℂ → ℂ} {x : ℂ} (hu : ContDiffAt ℝ ∞ u x) (hx : u x ≠ 0)
    (m : ℤ) : ContDiffAt ℝ ∞ (fun y => u y ^ m) x := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · simpa [zpow_natCast] using hu.pow n
  · simp only [zpow_neg, zpow_natCast]
    exact (hu.pow n).fun_inv (pow_ne_zero n hx)

theorem contDiffAt_angPhase (m : ℤ) {x : ℂ} (hx : x ≠ 0) : ContDiffAt ℝ ∞ (angPhase m) x := by
  have hne : x / (‖x‖ : ℂ) ≠ 0 := div_ne_zero hx (ofReal_norm_ne_zero hx)
  exact contDiffAt_zpow_comp (contDiffAt_unit hx) hne m

/-- A profile smooth on `(0,∞)` and vanishing on `(0, r₁)` (`r₁ > 0`) gives a smooth function
`h(r)e^{iℓθ}` for `ℓ ≠ 0`. -/
theorem contDiff_ofProfile {ℓ : ℤ} (hℓ : ℓ ≠ 0) {h : ℝ → ℂ} (hh : ContDiffOn ℝ ∞ h (Ioi 0))
    {r₁ : ℝ} (hr₁ : 0 < r₁) (h0 : ∀ r : ℝ, 0 < r → r < r₁ → h r = 0) :
    ContDiff ℝ ∞ (ofProfile ℓ h) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    have hball : Metric.ball (0 : ℂ) r₁ ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds 0 hr₁
    filter_upwards [hball] with y hy
    rw [mem_ball_zero_iff] at hy
    by_cases hy0 : y = 0
    · subst hy0
      simp [ofProfile, angPhase, zero_zpow ℓ hℓ]
    · rw [ofProfile, h0 ‖y‖ (norm_pos_iff.2 hy0) hy, zero_mul]
  · have h1 : ContDiffAt ℝ ∞ (fun y : ℂ => h ‖y‖) x :=
      (hh.contDiffAt (Ioi_mem_nhds (norm_pos_iff.2 hx))).comp x (contDiffAt_norm ℝ hx)
    exact h1.mul (contDiffAt_angPhase ℓ hx)

/-- A profile vanishing beyond `r₂` gives a compactly supported `h(r)e^{iℓθ}`. -/
theorem hasCompactSupport_ofProfile {ℓ : ℤ} {h : ℝ → ℂ} {r₂ : ℝ}
    (h0 : ∀ r : ℝ, r₂ < r → h r = 0) : HasCompactSupport (ofProfile ℓ h) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) r₂) fun x hx => ?_
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
  rw [ofProfile, h0 ‖x‖ hx, zero_mul]

end NonUniqueEuler.Eig.EigendataH
