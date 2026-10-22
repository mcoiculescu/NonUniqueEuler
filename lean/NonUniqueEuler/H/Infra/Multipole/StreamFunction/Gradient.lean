import NonUniqueEuler.Defs.Infra.Multipole
import NonUniqueEuler.I.Infra.Multipole.CauchySmooth
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

noncomputable section

open MeasureTheory Set Metric Real Filter Topology

namespace NonUniqueEuler.Multipole

/-- `∇_x log‖x - y‖ = (x - y)/‖x - y‖²` at `x = z ≠ y`. -/
theorem hasFDerivAt_log_norm_sub {y z : ℂ} (h : z ≠ y) :
    HasFDerivAt (fun x : ℂ => Real.log ‖x - y‖) ((‖z - y‖ ^ 2)⁻¹ • innerSL ℝ (z - y)) z := by
  have hne : ‖z - y‖ ^ 2 ≠ 0 := by
    have : z - y ≠ 0 := sub_ne_zero.mpr h
    positivity
  have h1 := (hasFDerivAt_sub_const (𝕜 := ℝ) (x := z) y).norm_sq
  have h2 := (h1.log hne).const_mul (2⁻¹ : ℝ)
  have hfun : (fun x : ℂ => Real.log ‖x - y‖) =
      fun x => (2⁻¹ : ℝ) * Real.log (‖x - y‖ ^ 2) := by
    funext x
    rw [Real.log_pow]
    push_cast
    ring
  rw [hfun]
  refine h2.congr_fderiv ?_
  rw [ContinuousLinearMap.comp_id]
  module


/-- Distances from `y ∉ ball x₀ δ` to `x ∈ ball x₀ (δ/2)` and to `x₀` are comparable. -/
theorem norm_sub_bounds {x x₀ y : ℂ} {δ : ℝ} (hδ : 0 < δ) (hx : x ∈ ball x₀ (δ / 2))
    (hy : y ∉ ball x₀ δ) :
    δ ≤ ‖x₀ - y‖ ∧ δ / 2 ≤ ‖x - y‖ ∧ ‖x - y‖ ≤ 2 * ‖x₀ - y‖ ∧ ‖x₀ - y‖ ≤ 2 * ‖x - y‖ := by
  rw [mem_ball, dist_eq_norm] at hx
  rw [mem_ball, dist_eq_norm, not_lt, norm_sub_rev] at hy
  have h1 : ‖x - y‖ ≤ ‖x - x₀‖ + ‖x₀ - y‖ := norm_sub_le_norm_sub_add_norm_sub x x₀ y
  have h2 : ‖x₀ - y‖ ≤ ‖x₀ - x‖ + ‖x - y‖ := norm_sub_le_norm_sub_add_norm_sub x₀ x y
  rw [norm_sub_rev x₀ x] at h2
  refine ⟨hy, by linarith, by linarith, by linarith⟩

/-- `|log‖x - y‖ - log‖x₀ - y‖| ≤ log 2` for `x ∈ ball x₀ (δ/2)`, `y ∉ ball x₀ δ`. -/
theorem abs_log_norm_sub_sub_le {x x₀ y : ℂ} {δ : ℝ} (hδ : 0 < δ) (hx : x ∈ ball x₀ (δ / 2))
    (hy : y ∉ ball x₀ δ) :
    |Real.log ‖x - y‖ - Real.log ‖x₀ - y‖| ≤ Real.log 2 := by
  obtain ⟨h0, h1, h2, h3⟩ := norm_sub_bounds hδ hx hy
  have ha : 0 < ‖x - y‖ := by linarith
  have hb : 0 < ‖x₀ - y‖ := by linarith
  have e1 : Real.log ‖x - y‖ ≤ Real.log 2 + Real.log ‖x₀ - y‖ := by
    rw [← Real.log_mul (by norm_num) hb.ne']
    exact Real.log_le_log ha h2
  have e2 : Real.log ‖x₀ - y‖ ≤ Real.log 2 + Real.log ‖x - y‖ := by
    rw [← Real.log_mul (by norm_num) ha.ne']
    exact Real.log_le_log hb h3
  rw [abs_sub_le_iff]
  constructor <;> linarith

theorem aestronglyMeasurable_log_norm_sub_mul {g : ℂ → ℝ} (hg : Integrable g) (x : ℂ) :
    AEStronglyMeasurable (fun y => Real.log ‖x - y‖ * g y) volume :=
  ((measurable_const.sub measurable_id).norm.log.aestronglyMeasurable).mul hg.aestronglyMeasurable

/-- Local invariance of the integrability of `log‖x - ·‖ g` near a point where `g` vanishes. -/
theorem integrable_log_norm_sub_mul_iff {g : ℂ → ℝ} (hg : Integrable g) {x₀ x : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hsupp : ∀ᵐ w, w ∈ ball x₀ δ → g w = 0) (hx : x ∈ ball x₀ (δ / 2)) :
    Integrable (fun y => Real.log ‖x - y‖ * g y) ↔
      Integrable (fun y => Real.log ‖x₀ - y‖ * g y) := by
  have hD : Integrable (fun y => (Real.log ‖x - y‖ - Real.log ‖x₀ - y‖) * g y) := by
    refine Integrable.mono' (hg.norm.const_mul (Real.log 2)) ?_ ?_
    · exact (((measurable_const.sub measurable_id).norm.log.sub
        (measurable_const.sub measurable_id).norm.log).aestronglyMeasurable).mul
        hg.aestronglyMeasurable
    · filter_upwards [hsupp] with y hy
      by_cases hyb : y ∈ ball x₀ δ
      · simp [hy hyb]
      · rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (abs_log_norm_sub_sub_le hδ hx hyb) (norm_nonneg _)
  constructor
  · intro h
    refine (h.sub hD).congr (Eventually.of_forall fun y => ?_)
    simp only [Pi.sub_apply]
    ring
  · intro h
    refine (h.add hD).congr (Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply]
    ring

/-- The pointwise identity behind `∇ψ = -i (K ⋆ g)`: `-i K(w) c = (2π)⁻¹ c w/‖w‖²`. -/
theorem innerSL_neg_I_mul_biotSavartKernel (w : ℂ) (c : ℝ) :
    innerSL ℝ (-(Complex.I * (biotSavartKernel w * (c : ℂ)))) =
      (2 * π)⁻¹ • (c • ((‖w‖ ^ 2)⁻¹ • innerSL ℝ w)) := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hw : -(Complex.I * (biotSavartKernel w * (c : ℂ))) =
      ((2 * π)⁻¹ * (c * (‖w‖ ^ 2)⁻¹) : ℝ) • w := by
    rw [Complex.real_smul, biotSavartKernel]
    push_cast
    linear_combination (-(w * (2 * (π : ℂ) * (‖w‖ : ℂ) ^ 2)⁻¹ * (c : ℂ))) * hI
  rw [hw, map_smul, smul_smul, smul_smul, mul_assoc]


/-- The `x`-derivative of the integrand of the stream function. -/
def logKernelFDeriv (g : ℂ → ℝ) (x y : ℂ) : ℂ →L[ℝ] ℝ :=
  g y • ((‖x - y‖ ^ 2)⁻¹ • innerSL ℝ (x - y))

theorem norm_logKernelFDeriv_le {g : ℂ → ℝ} {x x₀ y : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hx : x ∈ ball x₀ (δ / 2)) (hy : y ∈ ball x₀ δ → g y = 0) :
    ‖logKernelFDeriv g x y‖ ≤ 2 / δ * |g y| := by
  by_cases hyb : y ∈ ball x₀ δ
  · simp [logKernelFDeriv, hy hyb]
  · obtain ⟨-, h1, -, -⟩ := norm_sub_bounds hδ hx hyb
    have ha : 0 < ‖x - y‖ := by linarith
    have hn : ‖logKernelFDeriv g x y‖ = |g y| * ‖x - y‖⁻¹ := by
      rw [logKernelFDeriv, norm_smul, norm_smul, innerSL_apply_norm, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg (a := (‖x - y‖ ^ 2)⁻¹) (by positivity)]
      field_simp
    rw [hn, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [show 2 / δ = (δ / 2)⁻¹ by field_simp]
    exact inv_anti₀ (by positivity) h1

theorem hasFDerivAt_log_norm_sub_mul {g : ℂ → ℝ} {x x₀ y : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hx : x ∈ ball x₀ (δ / 2)) (hy : y ∈ ball x₀ δ → g y = 0) :
    HasFDerivAt (fun x => Real.log ‖x - y‖ * g y) (logKernelFDeriv g x y) x := by
  by_cases hyb : y ∈ ball x₀ δ
  · have h0 : g y = 0 := hy hyb
    simp only [logKernelFDeriv, h0, mul_zero, zero_smul]
    exact hasFDerivAt_const 0 x
  · obtain ⟨-, h1, -, -⟩ := norm_sub_bounds hδ hx hyb
    have hxy : x ≠ y := by
      intro h
      rw [h, sub_self, norm_zero] at h1
      linarith
    exact (hasFDerivAt_log_norm_sub hxy).mul_const (g y)

theorem aestronglyMeasurable_logKernelFDeriv {g : ℂ → ℝ} (hg : Integrable g) (x : ℂ) :
    AEStronglyMeasurable (logKernelFDeriv g x) volume := by
  refine hg.aestronglyMeasurable.smul
    (AEStronglyMeasurable.smul (f := fun y => (‖x - y‖ ^ 2)⁻¹)
      (g := fun y => innerSL ℝ (x - y)) ?_ ?_)
  · exact ((measurable_const.sub measurable_id).norm.pow_const 2).inv.aestronglyMeasurable
  · exact ((innerSL ℝ).continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable

/-- `∇ψ = -i (K ⋆ g)` at a point near which `g` vanishes, provided the integral defining `ψ`
converges there. -/
theorem hasFDerivAt_logPotentialReal_of_integrable {g : ℂ → ℝ} (hg : Integrable g) {z : ℂ}
    {δ : ℝ} (hδ : 0 < δ) (hsupp : ∀ᵐ w, w ∈ ball z δ → g w = 0)
    (hint : Integrable fun y => Real.log ‖z - y‖ * g y) :
    HasFDerivAt (logPotentialReal g) (innerSL ℝ (-(Complex.I * velocity g z))) z := by
  have hbound : ∀ᵐ y, ∀ x ∈ ball z (δ / 2), ‖logKernelFDeriv g x y‖ ≤ 2 / δ * |g y| := by
    filter_upwards [hsupp] with y hy x hx
    exact norm_logKernelFDeriv_le hδ hx hy
  have hdiff : ∀ᵐ y, ∀ x ∈ ball z (δ / 2),
      HasFDerivAt (fun x => Real.log ‖x - y‖ * g y) (logKernelFDeriv g x y) x := by
    filter_upwards [hsupp] with y hy x hx
    exact hasFDerivAt_log_norm_sub_mul hδ hx hy
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (ball_mem_nhds z (half_pos hδ))
    (Eventually.of_forall fun x => aestronglyMeasurable_log_norm_sub_mul hg x) hint
    (aestronglyMeasurable_logKernelFDeriv hg z) hbound (hg.abs.const_mul (2 / δ)) hdiff
  have key2 := key.const_mul ((2 * π)⁻¹)
  show HasFDerivAt (fun x => (2 * π)⁻¹ * ∫ y, Real.log ‖x - y‖ * g y) _ z
  refine key2.congr_fderiv ?_
  -- identify the derivative
  have hφ : Integrable (fun y => biotSavartKernel (z - y) * (g y : ℂ)) :=
    integrable_biotSavart_of_vanishing hg hδ hsupp
  have hψ : Integrable (fun y => -(Complex.I * (biotSavartKernel (z - y) * (g y : ℂ)))) :=
    (hφ.const_mul Complex.I).neg
  rw [← integral_smul, velocity, ← integral_const_mul, ← integral_neg,
    ← ContinuousLinearMap.integral_comp_comm _ hψ]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [logKernelFDeriv]
  rw [innerSL_neg_I_mul_biotSavartKernel]


/-- Local dichotomy at a point `x₀ ∈ U`: either the integral defining `ψ` converges near `x₀`
and `∇ψ = -i (K ⋆ g)` there, or it diverges near `x₀` and `ψ = 0` (junk value) there. -/
theorem logPotentialReal_local_dichotomy {g : ℂ → ℝ} (hg : Integrable g) {U : Set ℂ}
    (hU : IsOpen U) (hsep : ∀ z ∈ U, ∃ δ > 0, ∀ᵐ w, w ∈ ball z δ → g w = 0) {x₀ : ℂ}
    (hx₀ : x₀ ∈ U) :
    (∃ V : Set ℂ, IsOpen V ∧ x₀ ∈ V ∧ V ⊆ U ∧ ∀ x ∈ V,
      HasFDerivAt (logPotentialReal g) (innerSL ℝ (-(Complex.I * velocity g x))) x) ∨
    (logPotentialReal g =ᶠ[𝓝 x₀] fun _ => 0) := by
  obtain ⟨δ, hδ, hsupp⟩ := hsep x₀ hx₀
  by_cases hint : Integrable fun y => Real.log ‖x₀ - y‖ * g y
  · refine Or.inl ⟨ball x₀ (δ / 2) ∩ U, isOpen_ball.inter hU,
      ⟨mem_ball_self (half_pos hδ), hx₀⟩, inter_subset_right, fun x hx => ?_⟩
    obtain ⟨δx, hδx, hsuppx⟩ := hsep x hx.2
    exact hasFDerivAt_logPotentialReal_of_integrable hg hδx hsuppx
      ((integrable_log_norm_sub_mul_iff hg hδ hsupp hx.1).mpr hint)
  · refine Or.inr ?_
    filter_upwards [ball_mem_nhds x₀ (half_pos hδ)] with x hx
    have hx' : ¬ Integrable fun y => Real.log ‖x - y‖ * g y := fun h =>
      hint ((integrable_log_norm_sub_mul_iff hg hδ hsupp hx).mp h)
    simp [logPotentialReal, integral_undef hx']

/-- Corrected form of `fderiv_logPotentialReal` (the interface statement lacks the
convergence hypothesis `hlog`). -/
theorem fderiv_logPotentialReal_of_integrable {g : ℂ → ℝ} (hg : Integrable g) {U : Set ℂ}
    (hU : IsOpen U) (hsep : ∀ z ∈ U, ∃ δ > 0, ∀ᵐ w, w ∈ ball z δ → g w = 0) {z : ℂ}
    (hz : z ∈ U) (hlog : Integrable fun y => Real.log ‖z - y‖ * g y) (v : ℂ) :
    fderiv ℝ (logPotentialReal g) z v = inner ℝ (-(Complex.I * velocity g z)) v := by
  obtain ⟨δ, hδ, hsupp⟩ := hsep z hz
  rw [(hasFDerivAt_logPotentialReal_of_integrable hg hδ hsupp hlog).fderiv, innerSL_apply_apply]

/-- The convergence hypothesis of `fderiv_logPotentialReal_of_integrable` holds when `g` has
bounded support and vanishes near `z`. -/
theorem integrable_log_norm_sub_mul_of_bounded_support {g : ℂ → ℝ} (hg : Integrable g)
    {R : ℝ} (hR : ∀ᵐ y, R < ‖y‖ → g y = 0) {z : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hsupp : ∀ᵐ w, w ∈ ball z δ → g w = 0) :
    Integrable fun y => Real.log ‖z - y‖ * g y := by
  refine Integrable.mono' (hg.norm.const_mul (|Real.log δ| + |Real.log (‖z‖ + |R| + δ)|))
    (aestronglyMeasurable_log_norm_sub_mul hg z) ?_
  filter_upwards [hR, hsupp] with y hyR hyz
  by_cases h0 : g y = 0
  · simp [h0]
  have hy1 : δ ≤ ‖z - y‖ := by
    by_contra h
    refine h0 (hyz ?_)
    rw [mem_ball, dist_eq_norm, norm_sub_rev]
    linarith
  have hy2 : ‖y‖ ≤ |R| := by
    by_contra h
    exact h0 (hyR (lt_of_le_of_lt (le_abs_self R) (not_le.mp h)))
  have hy3 : ‖z - y‖ ≤ ‖z‖ + |R| + δ := by
    have := norm_sub_le z y
    linarith
  have hpos : 0 < ‖z - y‖ := lt_of_lt_of_le hδ hy1
  rw [norm_mul, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rw [abs_le]
  constructor
  · have := Real.log_le_log hδ hy1
    have := neg_abs_le (Real.log δ)
    have := abs_nonneg (Real.log (‖z‖ + |R| + δ))
    linarith
  · have := Real.log_le_log hpos hy3
    have := le_abs_self (Real.log (‖z‖ + |R| + δ))
    have := abs_nonneg (Real.log δ)
    linarith

end NonUniqueEuler.Multipole
