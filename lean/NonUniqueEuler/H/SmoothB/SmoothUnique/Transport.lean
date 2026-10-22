import NonUniqueEuler.H.SmoothB.SmoothUnique.Velocity
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Helper for `P/SmoothB/SmoothUnique`: the energy estimate at a fixed time

* `integral_mul_fderiv_apply_eq_zero`: `∫ δ (v·∇δ) = -½ ∫ (div v) δ² = 0` for `δ ∈ C¹_c` and a
  divergence-free `v ∈ C¹` ("the transport term vanishes", `B_global_smooth.tex:502-503`);
* `abs_integral_le_of_transport`: if `A = -2 δ (v·∇δ) - 2 δ (D(K ∗ δ))` with `|D(x) w| ≤ L|w|`
  on `B_ρ` and `δ = 0` outside `B_ρ`, then `|∫ A| ≤ L (1 + 4ρ²) ∫ δ²` (`lem:BS-basic`(c) and
  `2|δ||w| ≤ δ² + |w|²`; `B_global_smooth.tex:503-507`, with the Cauchy–Schwarz step replaced
  by the pointwise AM–GM inequality, which gives the constant `L(1 + 4ρ²)` instead of `4ρL`).
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler.Smooth.UniqueAux

/-- A continuous function vanishing outside a compact set is integrable. -/
theorem integrable_of_vanish {g : ℂ → ℝ} (hg : Continuous g) {K : Set ℂ} (hK : IsCompact K)
    (h : ∀ x, x ∉ K → g x = 0) : Integrable g :=
  hg.integrable_of_hasCompactSupport (HasCompactSupport.intro hK h)

/-- **The transport term vanishes.** `∫ δ Dδ(v) = 0` for `δ ∈ C¹_c(ℝ²)` and `v ∈ C¹` with
`div v = 0`. -/
theorem integral_mul_fderiv_apply_eq_zero {f : ℂ → ℝ} {v : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (hv : ContDiff ℝ 1 v)
    (hdiv : ∀ x, Prelim.divergence v x = 0) :
    ∫ x, f x * fderiv ℝ f x (v x) = 0 := by
  have hK : IsCompact (tsupport f) := hfc
  have hvan : ∀ x, x ∉ tsupport f → f x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hcf : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  set φ : ℂ → ℝ := fun x => f x * f x with hφdef
  have hφ : ContDiff ℝ 1 φ := hf.mul hf
  have hφd : ∀ x w, fderiv ℝ φ x w = 2 * f x * fderiv ℝ f x w := by
    intro x w
    rw [hφdef, fderiv_fun_mul (hfd x) (hfd x)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hcφ : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  -- the components of `v`
  set v₁ : ℂ → ℝ := fun x => (v x).re with hv₁def
  set v₂ : ℂ → ℝ := fun x => (v x).im with hv₂def
  have hvd : Differentiable ℝ v := hv.differentiable one_ne_zero
  have hv₁ : ContDiff ℝ 1 v₁ := Complex.reCLM.contDiff.comp hv
  have hv₂ : ContDiff ℝ 1 v₂ := Complex.imCLM.contDiff.comp hv
  have hv₁d : ∀ x w, fderiv ℝ v₁ x w = (fderiv ℝ v x w).re := by
    intro x w
    have : HasFDerivAt v₁ (Complex.reCLM.comp (fderiv ℝ v x)) x :=
      Complex.reCLM.hasFDerivAt.comp x (hvd x).hasFDerivAt
    rw [this.fderiv]
    rfl
  have hv₂d : ∀ x w, fderiv ℝ v₂ x w = (fderiv ℝ v x w).im := by
    intro x w
    have : HasFDerivAt v₂ (Complex.imCLM.comp (fderiv ℝ v x)) x :=
      Complex.imCLM.hasFDerivAt.comp x (hvd x).hasFDerivAt
    rw [this.fderiv]
    rfl
  have hcv₁ : Continuous (fderiv ℝ v₁) := hv₁.continuous_fderiv one_ne_zero
  have hcv₂ : Continuous (fderiv ℝ v₂) := hv₂.continuous_fderiv one_ne_zero
  -- pointwise identity
  have hpt : ∀ x, f x * fderiv ℝ f x (v x) =
      (1 / 2) * (v₁ x * fderiv ℝ φ x 1) + (1 / 2) * (v₂ x * fderiv ℝ φ x Complex.I) := by
    intro x
    have hvx : v x = (v x).re • (1 : ℂ) + (v x).im • Complex.I := by
      apply Complex.ext <;> simp
    conv_lhs => rw [hvx]
    rw [map_add, map_smul, map_smul, hφd, hφd]
    simp only [smul_eq_mul, hv₁def, hv₂def]
    ring
  -- integrability
  have hI1 : Integrable (fun x => fderiv ℝ v₁ x 1 * φ x) := by
    refine integrable_of_vanish ((hcv₁.clm_apply continuous_const).mul (hf.continuous.mul
      hf.continuous)) hK (fun x hx => ?_)
    simp [hφdef, hvan x hx]
  have hI2 : Integrable (fun x => v₁ x * fderiv ℝ φ x 1) := by
    refine integrable_of_vanish (hv₁.continuous.mul (hcφ.clm_apply continuous_const)) hK
      (fun x hx => ?_)
    simp [hφd, hvan x hx]
  have hI3 : Integrable (fun x => v₁ x * φ x) := by
    refine integrable_of_vanish (hv₁.continuous.mul (hf.continuous.mul hf.continuous)) hK
      (fun x hx => ?_)
    simp [hφdef, hvan x hx]
  have hJ1 : Integrable (fun x => fderiv ℝ v₂ x Complex.I * φ x) := by
    refine integrable_of_vanish ((hcv₂.clm_apply continuous_const).mul (hf.continuous.mul
      hf.continuous)) hK (fun x hx => ?_)
    simp [hφdef, hvan x hx]
  have hJ2 : Integrable (fun x => v₂ x * fderiv ℝ φ x Complex.I) := by
    refine integrable_of_vanish (hv₂.continuous.mul (hcφ.clm_apply continuous_const)) hK
      (fun x hx => ?_)
    simp [hφd, hvan x hx]
  have hJ3 : Integrable (fun x => v₂ x * φ x) := by
    refine integrable_of_vanish (hv₂.continuous.mul (hf.continuous.mul hf.continuous)) hK
      (fun x hx => ?_)
    simp [hφdef, hvan x hx]
  have hφdiff : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hibp1 : ∫ x, v₁ x * fderiv ℝ φ x 1 = -∫ x, fderiv ℝ v₁ x 1 * φ x :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hI1 hI2 hI3
      (fun x _ => (hv₁.differentiable one_ne_zero) x) (fun x _ => hφdiff x)
  have hibp2 : ∫ x, v₂ x * fderiv ℝ φ x Complex.I = -∫ x, fderiv ℝ v₂ x Complex.I * φ x :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hJ1 hJ2 hJ3
      (fun x _ => (hv₂.differentiable one_ne_zero) x) (fun x _ => hφdiff x)
  have hsum : (∫ x, fderiv ℝ v₁ x 1 * φ x) + ∫ x, fderiv ℝ v₂ x Complex.I * φ x = 0 := by
    rw [← integral_add hI1 hJ1]
    have : ∀ x, fderiv ℝ v₁ x 1 * φ x + fderiv ℝ v₂ x Complex.I * φ x = 0 := by
      intro x
      rw [hv₁d, hv₂d, ← add_mul]
      have := hdiv x
      rw [Prelim.divergence_eq] at this
      rw [this, zero_mul]
    simp only [this, integral_zero]
  calc ∫ x, f x * fderiv ℝ f x (v x)
      = ∫ x, ((1 / 2) * (v₁ x * fderiv ℝ φ x 1) +
          (1 / 2) * (v₂ x * fderiv ℝ φ x Complex.I)) := integral_congr_ae
            (Filter.Eventually.of_forall hpt)
    _ = (1 / 2) * (∫ x, v₁ x * fderiv ℝ φ x 1) +
          (1 / 2) * ∫ x, v₂ x * fderiv ℝ φ x Complex.I := by
        rw [integral_add (hI2.const_mul _) (hJ2.const_mul _), integral_const_mul,
          integral_const_mul]
    _ = 0 := by
        rw [hibp1, hibp2]
        linear_combination (-(1 / 2 : ℝ)) * hsum

/-- **The energy estimate at a fixed time.** Let `δ ∈ C¹(ℝ²)` vanish outside `B_ρ`, let
`v ∈ C¹` be divergence free, and let `|D(x) w| ≤ L |w|` for `x ∈ B_ρ`. If an integrable `A`
equals `-2 δ Dδ(v) - 2 δ D(K ∗ δ)` pointwise, then `|∫ A| ≤ L (1 + 4ρ²) ∫ δ²`. -/
theorem abs_integral_le_of_transport {δ A : ℂ → ℝ} {v : ℂ → ℂ} {D : ℂ → ℂ →L[ℝ] ℝ}
    {ρ L : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L) (hδ : ContDiff ℝ 1 δ)
    (hδv : ∀ x, x ∉ ball (0 : ℂ) ρ → δ x = 0) (hv : ContDiff ℝ 1 v)
    (hdiv : ∀ x, Prelim.divergence v x = 0) (hD : ∀ x ∈ ball (0 : ℂ) ρ, ∀ w, |D x w| ≤ L * ‖w‖)
    (hA : Integrable A)
    (hAeq : ∀ x, A x = -2 * (δ x * fderiv ℝ δ x (v x)) - 2 * (δ x * D x (velocity δ x))) :
    |∫ x, A x| ≤ L * (1 + 4 * ρ ^ 2) * ∫ x, δ x ^ 2 := by
  have hcδ : Continuous δ := hδ.continuous
  have hδc : HasCompactSupport δ := hasCompactSupport_of_vanish hδv
  have hK : IsCompact (closedBall (0 : ℂ) ρ) := isCompact_closedBall 0 ρ
  have hvanK : ∀ x, x ∉ closedBall (0 : ℂ) ρ → δ x = 0 := fun x hx =>
    hδv x (fun h => hx (ball_subset_closedBall h))
  -- the transport term
  set B : ℂ → ℝ := fun x => δ x * fderiv ℝ δ x (v x) with hBdef
  have hB : Integrable B := by
    refine integrable_of_vanish (hcδ.mul ((hδ.continuous_fderiv one_ne_zero).clm_apply
      hv.continuous)) hK (fun x hx => ?_)
    simp [hBdef, hvanK x hx]
  have hB0 : ∫ x, B x = 0 := integral_mul_fderiv_apply_eq_zero hδ hδc hv hdiv
  -- the remaining term
  set w : ℂ → ℂ := velocity δ with hwdef
  set C : ℂ → ℝ := fun x => δ x * D x (w x) with hCdef
  have hCeq : C = fun x => -(1 / 2) * A x - B x := by
    funext x
    rw [hCdef, hBdef, hAeq x]
    ring
  have hC : Integrable C := by
    rw [hCeq]
    exact (hA.const_mul _).sub hB
  have hAint : ∫ x, A x = -2 * ∫ x, C x := by
    have : A = fun x => -2 * B x - 2 * C x := by
      funext x
      rw [hAeq x]
    rw [this, integral_sub (hB.const_mul _) (hC.const_mul _), integral_const_mul,
      integral_const_mul, hB0]
    ring
  -- `L²` bound on the velocity
  obtain ⟨hwmem, hwle⟩ := integral_sq_velocity_ball_le hcδ hρ hδv
  have hw2 : IntegrableOn (fun x => ‖w x‖ ^ 2) (ball (0 : ℂ) ρ) :=
    hwmem.integrable_norm_pow two_ne_zero
  have hδ2 : Integrable (fun x => δ x ^ 2) := (memLp_of_vanish hcδ hδv 2).integrable_sq
  set G : ℂ → ℝ := fun x => (L / 2) * (δ x ^ 2 + (ball (0 : ℂ) ρ).indicator
    (fun x => ‖w x‖ ^ 2) x) with hGdef
  have hG : Integrable G :=
    (hδ2.add (hw2.integrable_indicator measurableSet_ball)).const_mul _
  have hCG : ∀ x, ‖C x‖ ≤ G x := by
    intro x
    by_cases hx : x ∈ ball (0 : ℂ) ρ
    · simp only [hCdef, hGdef, indicator_of_mem hx, Real.norm_eq_abs, abs_mul]
      have h1 := hD x hx (w x)
      have h2 : 0 ≤ |δ x| := abs_nonneg _
      have h3 : 2 * (|δ x| * ‖w x‖) ≤ δ x ^ 2 + ‖w x‖ ^ 2 := by
        have := two_mul_le_add_sq (|δ x|) ‖w x‖
        rw [sq_abs] at this
        linarith
      calc |δ x| * |D x (w x)| ≤ |δ x| * (L * ‖w x‖) := mul_le_mul_of_nonneg_left h1 h2
        _ = (L / 2) * (2 * (|δ x| * ‖w x‖)) := by ring
        _ ≤ (L / 2) * (δ x ^ 2 + ‖w x‖ ^ 2) := mul_le_mul_of_nonneg_left h3 (by linarith)
    · simp only [hCdef, hGdef, indicator_of_notMem hx, hδv x hx]
      simp
  have hCint : |∫ x, C x| ≤ ∫ x, G x :=
    norm_integral_le_of_norm_le hG (Filter.Eventually.of_forall hCG)
  have hGint : ∫ x, G x = (L / 2) * ((∫ x, δ x ^ 2) + ∫ x in ball (0 : ℂ) ρ, ‖w x‖ ^ 2) := by
    rw [hGdef, integral_const_mul, integral_add hδ2 (hw2.integrable_indicator measurableSet_ball),
      integral_indicator measurableSet_ball]
  rw [hAint, abs_mul, abs_neg, abs_two]
  have hE : 0 ≤ ∫ x, δ x ^ 2 := integral_nonneg (fun x => sq_nonneg _)
  calc 2 * |∫ x, C x| ≤ 2 * ((L / 2) * ((∫ x, δ x ^ 2) + ∫ x in ball (0 : ℂ) ρ, ‖w x‖ ^ 2)) := by
        rw [← hGint]; linarith
    _ ≤ 2 * ((L / 2) * ((∫ x, δ x ^ 2) + (2 * ρ) ^ 2 * ∫ x, δ x ^ 2)) := by
        gcongr
    _ = L * (1 + 4 * ρ ^ 2) * ∫ x, δ x ^ 2 := by ring

end NonUniqueEuler.Smooth.UniqueAux
