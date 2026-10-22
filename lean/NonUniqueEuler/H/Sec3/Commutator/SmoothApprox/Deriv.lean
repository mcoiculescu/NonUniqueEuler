import NonUniqueEuler.H.Sec3.Commutator.SmoothApprox.Conv
import NonUniqueEuler.Defs.Sec2.Conventions

/-!
# Helper for `P/Sec3/Commutator/SmoothApprox`: derivatives of the mollification

For a smooth compactly supported real kernel `ρ` and `f ∈ L¹_loc(ℝ²; ℂ)`:

* `fderiv_conv_apply`: `D(ρ ⋆ f)(x) v = ∫ (Dρ(t) v) f(x - t) dt`;
* `divFree_conv`: if `div f = 0` in `𝒟'`, then `div(ρ ⋆ f) = 0` classically
  (`03_compactness.tex:440-447`: "`div w_δ = 0`");
* `iterDirDeriv_conv_eq_conv`: if `G = ∂_{vs} f` weakly on `V` (`|vs| ≤ 1`) and
  `closedBall x r ⊆ V` with `supp ρ ⊆ B_r`, then `∂_{vs}(ρ ⋆ f)(x) = (ρ ⋆ G)(x)`
  (`03_compactness.tex:440-447`: "`∇w_δ = (∇w) ⋆ ρ_δ`"). The proof tests the weak derivative
  against `y ↦ ρ(x - y)`.
-/

noncomputable section

open MeasureTheory Set Filter Metric Function
open scoped ENNReal ContDiff Topology Convolution

namespace NonUniqueEuler.Weak.SmoothApproxAux

open NonUniqueEuler.Sob

/-- The derivative of the mollification: `D(ρ ⋆ f)(x) v = ∫ (Dρ(t) v) f(x - t) dt`. -/
theorem fderiv_conv_apply {ρ : ℂ → ℝ} (hρs : ContDiff ℝ 1 ρ) (hρ : HasCompactSupport ρ)
    {f : ℂ → ℂ} (hf : LocallyIntegrable f volume) (x v : ℂ) :
    fderiv ℝ (conv ρ f) x v = ∫ t, fderiv ℝ ρ t v • f (x - t) := by
  have hd := hρ.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hρs hf x
  have hex := (hρ.fderiv ℝ).convolutionExists_left
    ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).precompL ℂ)
    (hρs.continuous_fderiv one_ne_zero) hf x
  rw [conv, hd.fderiv, convolution_def, ContinuousLinearMap.integral_apply hex]
  simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply]

/-- Integrability of the integrand of `fderiv_conv_apply`. -/
theorem integrable_fderiv_smul {ρ : ℂ → ℝ} (hρs : ContDiff ℝ 1 ρ) (hρ : HasCompactSupport ρ)
    {f : ℂ → ℂ} (hf : LocallyIntegrable f volume) (x v : ℂ) :
    Integrable (fun t => fderiv ℝ ρ t v • f (x - t)) := by
  have hc : Continuous (fun t => fderiv ℝ ρ t v) :=
    (hρs.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcs : HasCompactSupport (fun t => fderiv ℝ ρ t v) :=
    (hρ.fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] ℝ => L v) (by simp)
  exact hcs.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hc hf x

/-- A real-linear form on `ℂ`: `L z = Re z · L 1 + Im z · L i`. -/
theorem clm_apply_eq_re_im (L : ℂ →L[ℝ] ℝ) (z : ℂ) :
    L z = z.re * L 1 + z.im * L Complex.I := by
  have h : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [h]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- The reflected kernel `y ↦ ρ(x - y)` has derivative `-Dρ(x - y)`. -/
theorem hasFDerivAt_reflect {ρ : ℂ → ℝ} (hρs : ContDiff ℝ 1 ρ) (x y : ℂ) :
    HasFDerivAt (fun y => ρ (x - y))
      ((fderiv ℝ ρ (x - y)).comp (-ContinuousLinearMap.id ℝ ℂ)) y :=
  ((hρs.differentiable one_ne_zero) (x - y)).hasFDerivAt.comp y
    ((hasFDerivAt_id y).const_sub x)

theorem fderiv_reflect_apply {ρ : ℂ → ℝ} (hρs : ContDiff ℝ 1 ρ) (x y w : ℂ) :
    fderiv ℝ (fun y => ρ (x - y)) y w = -fderiv ℝ ρ (x - y) w := by
  rw [(hasFDerivAt_reflect hρs x y).fderiv]
  simp

theorem contDiff_reflect {ρ : ℂ → ℝ} (hρs : ContDiff ℝ ∞ ρ) (x : ℂ) :
    ContDiff ℝ ∞ (fun y => ρ (x - y)) :=
  hρs.comp (contDiff_const.sub contDiff_id)

theorem support_reflect_subset {ρ : ℂ → ℝ} {r : ℝ} (hr : support ρ ⊆ ball 0 r) (x : ℂ) :
    support (fun y => ρ (x - y)) ⊆ ball x r := by
  intro y hy
  have h := hr hy
  rw [mem_ball_zero_iff] at h
  rw [mem_ball, dist_eq_norm, norm_sub_rev]
  exact h

theorem hasCompactSupport_reflect {ρ : ℂ → ℝ} {r : ℝ} (hr : support ρ ⊆ ball 0 r) (x : ℂ) :
    HasCompactSupport (fun y => ρ (x - y)) :=
  HasCompactSupport.intro (isCompact_closedBall x r) fun y hy => by
    by_contra h
    exact hy (ball_subset_closedBall (support_reflect_subset hr x h))

/-- **The mollification is divergence free** (`03_compactness.tex:440-447`). -/
theorem divFree_conv {ρ : ℂ → ℝ} (hρs : ContDiff ℝ ∞ ρ) {r : ℝ} (hr : support ρ ⊆ ball 0 r)
    {f : ℂ → ℂ} (hf : LocallyIntegrable f volume) (hdiv : Prelim.IsWeaklyDivFree f) (x : ℂ) :
    (fderiv ℝ (conv ρ f) x 1).re + (fderiv ℝ (conv ρ f) x Complex.I).im = 0 := by
  have hρ1 : ContDiff ℝ 1 ρ := hρs.of_le (by exact_mod_cast le_top)
  have hρc : HasCompactSupport ρ :=
    HasCompactSupport.intro (isCompact_closedBall 0 r) fun y hy => by
      by_contra h
      exact hy (ball_subset_closedBall (hr h))
  have h1 := integrable_fderiv_smul hρ1 hρc hf x 1
  have h2 := integrable_fderiv_smul hρ1 hρc hf x Complex.I
  rw [fderiv_conv_apply hρ1 hρc hf, fderiv_conv_apply hρ1 hρc hf]
  have hre := Complex.reCLM.integral_comp_comm h1
  have him := Complex.imCLM.integral_comp_comm h2
  simp only [Complex.reCLM_apply, Complex.imCLM_apply] at hre him
  have hi1 : Integrable (fun t => (fderiv ℝ ρ t 1 • f (x - t)).re) := by
    simpa using Complex.reCLM.integrable_comp h1
  have hi2 : Integrable (fun t => (fderiv ℝ ρ t Complex.I • f (x - t)).im) := by
    simpa using Complex.imCLM.integrable_comp h2
  rw [← hre, ← him, ← integral_add hi1 hi2]
  -- pointwise: the integrand is `Dρ(t)(f(x - t))`
  have hpt : ∀ t, (fderiv ℝ ρ t 1 • f (x - t)).re + (fderiv ℝ ρ t Complex.I • f (x - t)).im =
      fderiv ℝ ρ t (f (x - t)) := by
    intro t
    rw [clm_apply_eq_re_im (fderiv ℝ ρ t) (f (x - t)), Complex.smul_re, Complex.smul_im,
      smul_eq_mul, smul_eq_mul]
    ring
  simp_rw [hpt]
  -- change of variables `t = x - y`
  have hcv : ∫ t, fderiv ℝ ρ t (f (x - t)) = ∫ y, fderiv ℝ ρ (x - y) (f y) := by
    have := integral_sub_left_eq_self (fun t => fderiv ℝ ρ t (f (x - t))) volume x
    simp only [sub_sub_cancel] at this
    exact this.symm
  rw [hcv]
  -- the weak divergence tested against `y ↦ ρ(x - y)`
  have hd := (hdiv (fun y => ρ (x - y)) (contDiff_reflect hρs x)
    (hasCompactSupport_reflect hr x)).2
  simp_rw [fderiv_reflect_apply hρ1 x] at hd
  rw [integral_neg] at hd
  linarith

/-- The reflected kernel as a complex test function supported in `V`. -/
theorem isTestFn_reflect {ρ : ℂ → ℝ} (hρs : ContDiff ℝ ∞ ρ) {r : ℝ} (hr : support ρ ⊆ ball 0 r)
    {V : Set ℂ} {x : ℂ} (hxV : closedBall x r ⊆ V) :
    IsTestFn V (fun y => ((ρ (x - y) : ℝ) : ℂ)) := by
  refine ⟨Complex.ofRealCLM.contDiff.comp (contDiff_reflect hρs x), ?_, ?_⟩
  · exact (hasCompactSupport_reflect hr x).comp_left (g := fun a : ℝ => (a : ℂ)) (by simp)
  · refine (closure_minimal ?_ isClosed_closedBall).trans hxV
    intro y hy
    have hy' : y ∈ support (fun y => ρ (x - y)) := by
      simp only [mem_support, ne_eq, Complex.ofReal_eq_zero] at hy ⊢
      exact hy
    exact ball_subset_closedBall (support_reflect_subset hr x hy')

theorem dirDeriv_reflect {ρ : ℂ → ℝ} (hρs : ContDiff ℝ 1 ρ) (x v y : ℂ) :
    dirDeriv v (fun y => ((ρ (x - y) : ℝ) : ℂ)) y = -((fderiv ℝ ρ (x - y) v : ℝ) : ℂ) := by
  have h : HasFDerivAt (fun y => ((ρ (x - y) : ℝ) : ℂ))
      (Complex.ofRealCLM.comp ((fderiv ℝ ρ (x - y)).comp (-ContinuousLinearMap.id ℝ ℂ))) y :=
    Complex.ofRealCLM.hasFDerivAt.comp y (hasFDerivAt_reflect hρs x y)
  simp [dirDeriv, h.fderiv]

/-- Change of variables in the mollification: `(ρ ⋆ G)(x) = ∫ G(y) ρ(x - y) dy`. -/
theorem conv_eq_integral_reflect (ρ : ℂ → ℝ) (G : ℂ → ℂ) (x : ℂ) :
    conv ρ G x = ∫ y, G y * ((ρ (x - y) : ℝ) : ℂ) := by
  rw [conv_eq_integral]
  have := integral_sub_left_eq_self (fun t => ρ t • G (x - t)) volume x
  simp only [sub_sub_cancel] at this
  rw [← this]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [Complex.real_smul]
  ring

/-- **Weak derivatives commute with mollification at interior points**
(`03_compactness.tex:440-447`, `∇w_δ = (∇w) ⋆ ρ_δ`): if `G = ∂_{vs} f` weakly on `V`,
`|vs| ≤ 1`, `supp ρ ⊆ B_r` and `closedBall x r ⊆ V`, then `∂_{vs}(ρ ⋆ f)(x) = (ρ ⋆ G)(x)`. -/
theorem iterDirDeriv_conv_eq_conv {ρ : ℂ → ℝ} (hρs : ContDiff ℝ ∞ ρ) {r : ℝ}
    (hr : support ρ ⊆ ball 0 r) {V : Set ℂ} {x : ℂ} (hxV : closedBall x r ⊆ V)
    {vs : List ℂ} (hvs : vs.length ≤ 1) {f G : ℂ → ℂ} (hf : LocallyIntegrable f volume)
    (hfG : HasWeakDerivOn V vs f G) :
    iterDirDeriv vs (conv ρ f) x = conv ρ G x := by
  have hρ1 : ContDiff ℝ 1 ρ := hρs.of_le (by exact_mod_cast le_top)
  have hρc : HasCompactSupport ρ :=
    HasCompactSupport.intro (isCompact_closedBall 0 r) fun y hy => by
      by_contra h
      exact hy (ball_subset_closedBall (hr h))
  have hφ := isTestFn_reflect hρs hr hxV
  have key := hfG _ hφ
  match vs, hvs with
  | [], _ =>
    simp only [iterDirDeriv_nil, List.length_nil, pow_zero, one_mul] at key ⊢
    rw [conv_eq_integral_reflect, conv_eq_integral_reflect, key]
  | [v], _ =>
    simp only [iterDirDeriv_cons, iterDirDeriv_nil, List.length_singleton, pow_one,
      neg_one_mul] at key ⊢
    simp only [dirDeriv_reflect hρ1, mul_neg, integral_neg, neg_inj] at key
    rw [conv_eq_integral_reflect, ← key]
    show fderiv ℝ (conv ρ f) x v = _
    rw [fderiv_conv_apply hρ1 hρc hf]
    have := integral_sub_left_eq_self (fun t => fderiv ℝ ρ t v • f (x - t)) volume x
    simp only [sub_sub_cancel] at this
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [Complex.real_smul]
    ring
  | _ :: _ :: _, h => simp at h

end NonUniqueEuler.Weak.SmoothApproxAux
