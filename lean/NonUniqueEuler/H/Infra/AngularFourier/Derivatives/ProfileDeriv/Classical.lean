import NonUniqueEuler.H.Infra.AngularFourier.Derivatives.ProfileDeriv.Smooth
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Helpers for `P/Infra/AngularFourier/Derivatives/ProfileDeriv`: the classical identity

For a test function `η` on `(0, ∞)` and `f = fW ℓ η` (`= e^{-iℓθ} η(|x|)/|x|²`), with
`Φ₁ = x₁ f`, `Φ₂ = x₂ f`:
`∂₁Φ₁ + ∂₂Φ₂ = 2 f + Df(x)·x = e^{-iℓθ} η'(|x|)/|x| = W ℓ η' x` (`div_fW_eq`).

`Df(x)·x` is computed as `d/dt f(t x)|_{t=1}` with `f(t x) = e^{-iℓθ} η(t|x|)/(t|x|)²` for
`t > 0` (`fderiv_fW_apply_self`).
-/

noncomputable section

open MeasureTheory Set Real Filter Topology
open scoped ENNReal ContDiff

namespace NonUniqueEuler.Ang.ProfileDerivAux

theorem dirDeriv_re_mul' {f : ℂ → ℂ} {x : ℂ} (hf : DifferentiableAt ℝ f x) :
    Sob.dirDeriv 1 (fun y => (y.re : ℂ) * f y) x = (x.re : ℂ) * fderiv ℝ f x 1 + f x := by
  have h1 : HasFDerivAt (fun y : ℂ => (y.re : ℂ)) (Complex.ofRealCLM.comp Complex.reCLM) x :=
    (Complex.ofRealCLM.comp Complex.reCLM).hasFDerivAt
  have h3 : HasFDerivAt (fun y => (y.re : ℂ) * f y) _ x := h1.mul hf.hasFDerivAt
  simp only [Sob.dirDeriv]
  rw [h3.fderiv]
  simp

theorem dirDeriv_im_mul' {f : ℂ → ℂ} {x : ℂ} (hf : DifferentiableAt ℝ f x) :
    Sob.dirDeriv Complex.I (fun y => (y.im : ℂ) * f y) x =
      (x.im : ℂ) * fderiv ℝ f x Complex.I + f x := by
  have h1 : HasFDerivAt (fun y : ℂ => (y.im : ℂ)) (Complex.ofRealCLM.comp Complex.imCLM) x :=
    (Complex.ofRealCLM.comp Complex.imCLM).hasFDerivAt
  have h3 : HasFDerivAt (fun y => (y.im : ℂ) * f y) _ x := h1.mul hf.hasFDerivAt
  simp only [Sob.dirDeriv]
  rw [h3.fderiv]
  simp

/-- `∂₁(x₁ f) + ∂₂(x₂ f) = 2 f + Df(x)·x`. -/
theorem div_eq_two_add_fderiv {f : ℂ → ℂ} {x : ℂ} (hf : DifferentiableAt ℝ f x) :
    Sob.dirDeriv 1 (fun y => (y.re : ℂ) * f y) x +
        Sob.dirDeriv Complex.I (fun y => (y.im : ℂ) * f y) x =
      2 * f x + fderiv ℝ f x x := by
  rw [dirDeriv_re_mul' hf, dirDeriv_im_mul' hf]
  have key : x.re • (1 : ℂ) + x.im • Complex.I = x := by
    apply Complex.ext <;> simp
  have h := (fderiv ℝ f x).map_add (x.re • (1 : ℂ)) (x.im • Complex.I)
  rw [key, (fderiv ℝ f x).map_smul, (fderiv ℝ f x).map_smul, Complex.real_smul,
    Complex.real_smul] at h
  rw [h]
  ring

/-- `Df(x)·x = e^{-iℓθ} η'(|x|)/|x| - 2 f(x)` for `f = fW ℓ η`, `x ≠ 0`. -/
theorem fderiv_fW_apply_self (ℓ : ℤ) {η : ℝ → ℂ} (hη : Sob.IsTestFn (Ioi 0) η) {x : ℂ}
    (hx : x ≠ 0) :
    fderiv ℝ (fW ℓ η) x x = pW ℓ x * deriv η ‖x‖ - 2 * fW ℓ η x := by
  set r := ‖x‖ with hr_def
  have hr : 0 < r := norm_pos_iff.2 hx
  set c := angPhase (-ℓ) x with hc_def
  have hfd : Differentiable ℝ (fW ℓ η) := (isTestFn_fW ℓ hη).smooth.differentiable (by simp)
  have hηd : Differentiable ℝ η := hη.smooth.differentiable (by simp)
  -- chain rule along the ray
  have hray : HasDerivAt (fun t : ℝ => t • x) x 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const x
  have h1 : HasDerivAt (fun t : ℝ => fW ℓ η (t • x)) (fderiv ℝ (fW ℓ η) x x) 1 :=
    (hfd x).hasFDerivAt.comp_hasDerivAt_of_eq (1 : ℝ) hray (by simp)
  -- explicit derivative
  have hD : HasDerivAt (fun t : ℝ => ((t * r : ℝ) : ℂ)) (r : ℂ) 1 := by
    simpa using ((hasDerivAt_id (1 : ℝ)).mul_const r).ofReal_comp
  have hE : HasDerivAt (fun t : ℝ => η (t * r)) ((r : ℂ) * deriv η r) 1 := by
    have h0 : HasDerivAt η (deriv η r) ((fun t : ℝ => t * r) 1) := by
      simpa using (hηd r).hasDerivAt
    have := h0.scomp (1 : ℝ) ((hasDerivAt_id (1 : ℝ)).mul_const r)
    simpa [Function.comp_def, Complex.real_smul] using this
  have hD1 : ((1 * r : ℝ) : ℂ) ≠ 0 := by
    simpa using hr.ne'
  have hK := (((hasDerivAt_const (1 : ℝ) c).fun_div hD hD1).fun_div hD hD1).mul hE
  have h2 : HasDerivAt (fun t : ℝ => fW ℓ η (t • x))
      ((((0 * ((1 * r : ℝ) : ℂ) - c * r) / ((1 * r : ℝ) : ℂ) ^ 2) * ((1 * r : ℝ) : ℂ) -
          c / ((1 * r : ℝ) : ℂ) * r) / ((1 * r : ℝ) : ℂ) ^ 2 * η (1 * r) +
        c / ((1 * r : ℝ) : ℂ) / ((1 * r : ℝ) : ℂ) * ((r : ℂ) * deriv η r)) 1 := by
    refine hK.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds (zero_lt_one' ℝ)] with t ht
    exact fW_smul ℓ η ht x
  rw [h1.unique h2]
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  simp only [one_mul]
  rw [fW, pW]
  rw [← hc_def, ← hr_def]
  field_simp
  ring

/-- The classical identity `∂₁(x₁ f) + ∂₂(x₂ f) = W ℓ η'` for `f = fW ℓ η`. -/
theorem div_fW_eq (ℓ : ℤ) {η : ℝ → ℂ} (hη : Sob.IsTestFn (Ioi 0) η) (x : ℂ) :
    Sob.dirDeriv 1 (fun y => (y.re : ℂ) * fW ℓ η y) x +
        Sob.dirDeriv Complex.I (fun y => (y.im : ℂ) * fW ℓ η y) x =
      W ℓ (Sob.dirDeriv 1 η) x := by
  have hfd : Differentiable ℝ (fW ℓ η) := (isTestFn_fW ℓ hη).smooth.differentiable (by simp)
  rw [div_eq_two_add_fderiv (hfd x)]
  by_cases hx : x = 0
  · subst hx
    simp [fW, W, pW]
  · rw [fderiv_fW_apply_self ℓ hη hx, W]
    simp only [Sob.dirDeriv]
    rw [show deriv η ‖x‖ = fderiv ℝ η ‖x‖ 1 from rfl]
    ring

end NonUniqueEuler.Ang.ProfileDerivAux
