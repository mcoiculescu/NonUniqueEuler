import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import NonUniqueEuler.Defs.Sec2.Conventions

/-!
# Helper for `lem:iter-cauchy`: the calculus of the energy estimate

`B_global_smooth.tex:368-370`: "We multiply by `δ` and integrate; the transport term vanishes,
because `div v^{[j]} = 0` and `δ(t)` has compact support." This file proves, for smooth real
data on `ℂ = ℝ²` (classical derivatives):

* `integral_mul_fderiv_apply_eq_zero`: `∫ g (v · ∇g) = 0` for `g ∈ C¹_c` and a `C¹` field `v`
  with `div v = 0` (integration by parts, `∫ g (v·∇g) = ½ ∫ v·∇(g²) = -½ ∫ (div v) g² = 0`);
* `hasDerivAt_integral_sq`: `d/dt ∫ F(t, x)² dx = ∫ 2 F ∂_t F dx` for `F ∈ C¹(ℝ × ℝ²)` whose
  support is bounded locally uniformly in time (differentiation under the integral sign);
* `toReal_eLpNorm_two_sq`: `‖g‖²_{L²} = ∫ g²`.

Fully proved.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler.Smooth.IterCauchyAux

/-! ### The transport term -/

/-- `∫ g (v · ∇g) = 0` for `g ∈ C¹_c(ℝ²)` real and `v ∈ C¹(ℝ²; ℝ²)` with `div v = 0`
(`B_global_smooth.tex:368-370`). -/
theorem integral_mul_fderiv_apply_eq_zero {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) {v : ℂ → ℂ} (hv : ContDiff ℝ 1 v)
    (hdiv : ∀ x, Prelim.divergence v x = 0) :
    ∫ x, g x * fderiv ℝ g x (v x) = 0 := by
  set h : ℂ → ℝ := fun x => g x * g x with hh_def
  have hhc : HasCompactSupport h := hgc.mul_left
  have hh : ContDiff ℝ 1 h := hg.mul hg
  have hgd : ∀ x, DifferentiableAt ℝ g x := fun x => (hg.differentiable one_ne_zero) x
  have hfh : ∀ x w, fderiv ℝ h x w = 2 * (g x * fderiv ℝ g x w) := by
    intro x w
    have : fderiv ℝ h x = g x • fderiv ℝ g x + g x • fderiv ℝ g x := fderiv_mul (hgd x) (hgd x)
    rw [this]
    show g x * fderiv ℝ g x w + g x * fderiv ℝ g x w = _
    ring
  set v1 : ℂ → ℝ := fun x => (v x).re with hv1_def
  set v2 : ℂ → ℝ := fun x => (v x).im with hv2_def
  have hv1 : ContDiff ℝ 1 v1 := Complex.reCLM.contDiff.comp hv
  have hv2 : ContDiff ℝ 1 v2 := Complex.imCLM.contDiff.comp hv
  have hvd : ∀ x, DifferentiableAt ℝ v x := fun x => (hv.differentiable one_ne_zero) x
  have hfv1 : ∀ x w, fderiv ℝ v1 x w = (fderiv ℝ v x w).re := by
    intro x w
    have : fderiv ℝ v1 x = Complex.reCLM.comp (fderiv ℝ v x) :=
      (Complex.reCLM.hasFDerivAt.comp x (hvd x).hasFDerivAt).fderiv
    rw [this]
    rfl
  have hfv2 : ∀ x w, fderiv ℝ v2 x w = (fderiv ℝ v x w).im := by
    intro x w
    have : fderiv ℝ v2 x = Complex.imCLM.comp (fderiv ℝ v x) :=
      (Complex.imCLM.hasFDerivAt.comp x (hvd x).hasFDerivAt).fderiv
    rw [this]
    rfl
  -- pointwise identity `g (v·∇g) = ½ (v₁ ∂₁(g²) + v₂ ∂₂(g²))`
  have hpt : ∀ x, g x * fderiv ℝ g x (v x) =
      (1 / 2) * (v1 x * fderiv ℝ h x 1 + v2 x * fderiv ℝ h x Complex.I) := by
    intro x
    have hvx : v x = (v x).re • (1 : ℂ) + (v x).im • Complex.I := by
      apply Complex.ext <;> simp
    rw [hfh, hfh]
    conv_lhs => rw [hvx]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    simp only [hv1_def, hv2_def]
    ring
  -- continuity and compact supports
  have hcDh : ∀ w, Continuous fun x => fderiv ℝ h x w := fun w =>
    (hh.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hsDh : ∀ w, HasCompactSupport fun x => fderiv ℝ h x w := fun w => hhc.fderiv_apply ℝ w
  have hcDv1 : Continuous fun x => fderiv ℝ v1 x 1 :=
    (hv1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcDv2 : Continuous fun x => fderiv ℝ v2 x Complex.I :=
    (hv2.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have i1 : Integrable (fun x => v1 x * fderiv ℝ h x 1) :=
    (hv1.continuous.mul (hcDh 1)).integrable_of_hasCompactSupport (hsDh 1).mul_left
  have i2 : Integrable (fun x => v2 x * fderiv ℝ h x Complex.I) :=
    (hv2.continuous.mul (hcDh Complex.I)).integrable_of_hasCompactSupport
      (hsDh Complex.I).mul_left
  have j1 : Integrable (fun x => fderiv ℝ v1 x 1 * h x) :=
    (hcDv1.mul hh.continuous).integrable_of_hasCompactSupport hhc.mul_left
  have j2 : Integrable (fun x => fderiv ℝ v2 x Complex.I * h x) :=
    (hcDv2.mul hh.continuous).integrable_of_hasCompactSupport hhc.mul_left
  have k1 : Integrable (fun x => v1 x * h x) :=
    (hv1.continuous.mul hh.continuous).integrable_of_hasCompactSupport hhc.mul_left
  have k2 : Integrable (fun x => v2 x * h x) :=
    (hv2.continuous.mul hh.continuous).integrable_of_hasCompactSupport hhc.mul_left
  -- integration by parts in the directions `e₁ = 1` and `e₂ = i`
  have ibp1 : ∫ x, v1 x * fderiv ℝ h x 1 = -∫ x, fderiv ℝ v1 x 1 * h x :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable j1 i1 k1
      (fun x _ => (hv1.differentiable one_ne_zero) x) (fun x _ => (hh.differentiable one_ne_zero) x)
  have ibp2 : ∫ x, v2 x * fderiv ℝ h x Complex.I = -∫ x, fderiv ℝ v2 x Complex.I * h x :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable j2 i2 k2
      (fun x _ => (hv2.differentiable one_ne_zero) x) (fun x _ => (hh.differentiable one_ne_zero) x)
  have hsum : ∀ x, fderiv ℝ v1 x 1 * h x + fderiv ℝ v2 x Complex.I * h x = 0 := by
    intro x
    rw [hfv1, hfv2, ← add_mul]
    have := hdiv x
    rw [Prelim.divergence_eq] at this
    rw [this, zero_mul]
  calc ∫ x, g x * fderiv ℝ g x (v x)
      = ∫ x, (1 / 2) * (v1 x * fderiv ℝ h x 1 + v2 x * fderiv ℝ h x Complex.I) := by
        simp_rw [hpt]
    _ = (1 / 2) * ((∫ x, v1 x * fderiv ℝ h x 1) + ∫ x, v2 x * fderiv ℝ h x Complex.I) := by
        rw [integral_const_mul, integral_add i1 i2]
    _ = -(1 / 2) * ∫ x, (fderiv ℝ v1 x 1 * h x + fderiv ℝ v2 x Complex.I * h x) := by
        rw [ibp1, ibp2, integral_add j1 j2]
        ring
    _ = 0 := by simp [hsum]

/-! ### Differentiation of `∫ F(t, x)² dx` -/

/-- The time derivative of a `C¹` space–time function as the derivative of the joint map in the
direction `(1, 0)`. -/
theorem hasDerivAt_time {F : ℝ → ℂ → ℝ} (hF : ContDiff ℝ 1 (Function.uncurry F)) (τ : ℝ)
    (x : ℂ) :
    HasDerivAt (fun s => F s x) (fderiv ℝ (Function.uncurry F) (τ, x) ((1 : ℝ), (0 : ℂ))) τ := by
  have h1 : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : ℂ)) τ :=
    (hasDerivAt_id τ).prodMk (hasDerivAt_const τ x)
  have h2 := ((hF.differentiable one_ne_zero) (τ, x)).hasFDerivAt.comp_hasDerivAt τ h1
  exact h2

/-- `d/dt ∫ F(t, x)² dx = ∫ 2 F(t, x) ∂_t F(t, x) dx` for `F ∈ C¹(ℝ × ℝ²)` real whose support in
`x` is bounded uniformly for `t` in bounded intervals. -/
theorem hasDerivAt_integral_sq {F : ℝ → ℂ → ℝ} (hF : ContDiff ℝ 1 (Function.uncurry F))
    (hsupp : ∀ T : ℝ, ∃ ρ : ℝ, ∀ τ ∈ Icc (-T) T, ∀ x : ℂ, ρ < ‖x‖ → F τ x = 0) (t : ℝ) :
    HasDerivAt (fun τ => ∫ x, F τ x ^ 2) (∫ x, 2 * F t x * deriv (fun τ => F τ x) t) t := by
  set D : ℝ → ℂ → ℝ := fun τ x => fderiv ℝ (Function.uncurry F) (τ, x) ((1 : ℝ), (0 : ℂ))
    with hD_def
  have hd : ∀ τ x, HasDerivAt (fun s => F s x) (D τ x) τ := fun τ x => hasDerivAt_time hF τ x
  have hderiv : ∀ x, deriv (fun τ => F τ x) t = D t x := fun x => (hd t x).deriv
  simp_rw [hderiv]
  have hd2 : ∀ τ x, HasDerivAt (fun s => F s x ^ 2) (2 * F τ x * D τ x) τ := by
    intro τ x
    have hm : HasDerivAt (fun s => F s x * F s x) (D τ x * F τ x + F τ x * D τ x) τ :=
      (hd τ x).mul (hd τ x)
    have e : (fun s => F s x ^ 2) = fun s => F s x * F s x := by
      funext s
      ring
    rw [e]
    exact hm.congr_deriv (by ring)
  have hcF : Continuous (Function.uncurry F) := hF.continuous
  have hcD : Continuous (Function.uncurry D) :=
    (hF.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcFt : ∀ τ, Continuous (F τ) := fun τ =>
    hcF.comp (continuous_const.prodMk continuous_id)
  have hcDt : ∀ τ, Continuous (D τ) := fun τ =>
    hcD.comp (continuous_const.prodMk continuous_id)
  set T : ℝ := |t| + 1
  obtain ⟨ρ, hρ⟩ := hsupp T
  have hK : IsCompact (Icc (-T) T ×ˢ closedBall (0 : ℂ) ρ) :=
    isCompact_Icc.prod (isCompact_closedBall 0 ρ)
  have hcG : Continuous fun p : ℝ × ℂ => 2 * Function.uncurry F p * Function.uncurry D p :=
    (continuous_const.mul hcF).mul hcD
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcG.continuousOn
  have hball : ∀ τ ∈ ball t 1, τ ∈ Icc (-T) T := by
    intro τ hτ
    rw [Real.ball_eq_Ioo] at hτ
    constructor
    · have := neg_abs_le t
      linarith [hτ.1]
    · have := le_abs_self t
      linarith [hτ.2]
  have hFt0 : ∀ τ ∈ Icc (-T) T, ∀ x : ℂ, x ∉ closedBall (0 : ℂ) ρ → F τ x = 0 := by
    intro τ hτ x hx
    apply hρ τ hτ x
    simpa [mem_closedBall, dist_zero_right, not_le] using hx
  have hsuppt : ∀ τ ∈ Icc (-T) T, HasCompactSupport (fun x => F τ x ^ 2) := by
    intro τ hτ
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) ρ) fun x hx => ?_
    simp [hFt0 τ hτ x hx]
  have htT : t ∈ Icc (-T) T := hball t (mem_ball_self one_pos)
  have hint : Integrable (fun x => F t x ^ 2) :=
    ((hcFt t).pow 2).integrable_of_hasCompactSupport (hsuppt t htT)
  set bound : ℂ → ℝ := (closedBall (0 : ℂ) ρ).indicator fun _ => C with hbound_def
  have hbint : Integrable bound := by
    rw [hbound_def, integrable_indicator_iff measurableSet_closedBall]
    exact integrableOn_const (measure_closedBall_lt_top).ne
  have hb : ∀ x : ℂ, ∀ τ ∈ ball t 1, ‖2 * F τ x * D τ x‖ ≤ bound x := by
    intro x τ hτ
    have hτT := hball τ hτ
    by_cases hx : x ∈ closedBall (0 : ℂ) ρ
    · rw [hbound_def, indicator_of_mem hx]
      exact hC (τ, x) ⟨hτT, hx⟩
    · rw [hbound_def, indicator_of_notMem hx, hFt0 τ hτT x hx]
      simp
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun τ x => F τ x ^ 2) (F' := fun τ x => 2 * F τ x * D τ x) (x₀ := t)
    (bound := bound) (ball_mem_nhds t one_pos)
    (Eventually.of_forall fun τ => ((hcFt τ).pow 2).aestronglyMeasurable) hint
    (((continuous_const.mul (hcFt t)).mul (hcDt t)).aestronglyMeasurable)
    (ae_of_all _ hb) hbint (ae_of_all _ fun x τ _ => hd2 τ x)
  exact key.2

/-! ### `‖g‖²_{L²} = ∫ g²` -/

/-- `‖g‖²_{L²} = ∫ g²` for real `g ∈ L²`. -/
theorem toReal_eLpNorm_two_sq {g : ℂ → ℝ} (hg : MemLp g 2 volume) :
    (eLpNorm g 2 volume).toReal ^ 2 = ∫ x, g x ^ 2 := by
  rw [hg.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  have hnn : 0 ≤ ∫ x, ‖g x‖ ^ (ENNReal.toReal 2) :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hnn _)]
  simp only [ENNReal.toReal_ofNat] at hnn ⊢
  rw [← Real.rpow_natCast, ← Real.rpow_mul hnn]
  norm_num

end NonUniqueEuler.Smooth.IterCauchyAux
