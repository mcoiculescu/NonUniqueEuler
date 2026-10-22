import NonUniqueEuler.Defs.Infra.Polar
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Proof: radial and angular derivatives on `ℂ` (I-POLAR)

Proves the declarations of `NonUniqueEuler/I/Infra/Polar/RadialDeriv.lean` (same names, same
statements).

* `hasFDerivAt_comp_norm`: the norm is `√(‖·‖²)`, so `hasStrictFDerivAt_norm_sq` and
  `HasFDerivAt.sqrt` give `D‖·‖(z) = ‖z‖⁻¹ ⟨z, ·⟩` for `z ≠ 0`; then the chain rule.
* `contDiffOn_comp_norm`: `contDiffAt_norm` away from `0` and `ContDiffAt.comp`
  (`Ioi 0` is a neighbourhood of `‖x‖ > 0`).
* `hasDerivAt_radial`, `hasDerivAt_angular`: the chain rule `HasFDerivAt.comp_hasDerivAt` with
  the explicit derivatives of `s ↦ s e^{iθ}` and `s ↦ e^{is} x`.
* `intervalIntegral_angular_deriv_eq_zero`: FTC for `θ ↦ φ(r e^{iθ})` and `2π`-periodicity of
  `circleMap`.
-/

noncomputable section

open Set Real

namespace NonUniqueEuler.Polar

/-- Derivative of the norm on `ℂ` away from `0`: `D‖·‖(z) = ‖z‖⁻¹ ⟨z, ·⟩`. -/
private theorem hasFDerivAt_norm_aux {z : ℂ} (hz : z ≠ 0) :
    HasFDerivAt (fun x : ℂ => ‖x‖) (‖z‖⁻¹ • innerSL ℝ z) z := by
  have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz
  have h1 := (hasStrictFDerivAt_norm_sq z).hasFDerivAt.sqrt (pow_pos hpos 2).ne'
  simp only [Real.sqrt_sq (norm_nonneg _)] at h1
  have e : (1 / (2 * ‖z‖)) • (2 • (innerSL ℝ) z) = ‖z‖⁻¹ • innerSL ℝ z := by
    rw [two_smul, ← two_smul ℝ, smul_smul]
    congr 1
    field_simp
  rw [e] at h1
  exact h1

/-- Derivative of a radial function at `z ≠ 0`: `D(f₀ ∘ ‖·‖)(z) = f₀'(|z|) ⟨z, ·⟩/|z|`. -/
theorem hasFDerivAt_comp_norm {f₀ : ℝ → ℝ} {f₀' : ℝ} {z : ℂ} (hz : z ≠ 0)
    (hf : HasDerivAt f₀ f₀' ‖z‖) :
    HasFDerivAt (fun x : ℂ => f₀ ‖x‖) ((f₀' / ‖z‖) • innerSL ℝ z) z := by
  have h := hf.comp_hasFDerivAt z (hasFDerivAt_norm_aux hz)
  rw [smul_smul, ← div_eq_mul_inv] at h
  exact h

/-- A radial function with a `C^n` profile on `(0,∞)` is `C^n` on `ℂ \ {0}`. -/
theorem contDiffOn_comp_norm {f₀ : ℝ → ℝ} {n : WithTop ℕ∞} (hf : ContDiffOn ℝ n f₀ (Ioi 0)) :
    ContDiffOn ℝ n (fun x : ℂ => f₀ ‖x‖) {0}ᶜ := by
  intro x hx
  have hx0 : x ≠ 0 := hx
  have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
  exact ((hf.contDiffAt (Ioi_mem_nhds hpos)).comp x (contDiffAt_norm ℝ hx0)).contDiffWithinAt

/-- The radial derivative: `d/dr φ(r e^{iθ}) = Dφ(r e^{iθ})(e^{iθ})`. -/
theorem hasDerivAt_radial {φ : ℂ → ℝ} {θ r : ℝ} (hφ : DifferentiableAt ℝ φ (circleMap 0 r θ)) :
    HasDerivAt (fun s : ℝ => φ (circleMap 0 s θ))
      (fderiv ℝ φ (circleMap 0 r θ) (Complex.exp (θ * Complex.I))) r := by
  have h : HasDerivAt (fun s : ℝ => circleMap 0 s θ) (Complex.exp (θ * Complex.I)) r := by
    have := (Complex.ofRealCLM.hasDerivAt (x := r)).mul_const (Complex.exp (θ * Complex.I))
    simpa [circleMap] using this
  exact hφ.hasFDerivAt.comp_hasDerivAt r h

/-- Derivative of a rotation orbit: `d/ds e^{is} x = i e^{is} x`. -/
private theorem hasDerivAt_rot_aux (x : ℂ) (θ : ℝ) :
    HasDerivAt (fun s : ℝ => rot s x) (Complex.I * rot θ x) θ := by
  have h := (((Complex.ofRealCLM.hasDerivAt (x := θ)).mul_const Complex.I).cexp).mul_const x
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] at h
  have e : Complex.exp (↑θ * Complex.I) * Complex.I * x = Complex.I * rot θ x := by
    simp only [rot]; ring
  rw [e] at h
  exact h

/-- The angular derivative: `d/dθ φ(e^{iθ} x) = Dφ(e^{iθ} x)(i e^{iθ} x)`; at `θ = 0` this is
`x^⊥ · ∇φ(x) = ∂_θ φ(x)`. -/
theorem hasDerivAt_angular {φ : ℂ → ℝ} {x : ℂ} {θ : ℝ} (hφ : DifferentiableAt ℝ φ (rot θ x)) :
    HasDerivAt (fun s : ℝ => φ (rot s x)) (fderiv ℝ φ (rot θ x) (Complex.I * rot θ x)) θ :=
  hφ.hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_rot_aux x θ)

/-- Derivative of `circleMap 0 r` in the form `i · circleMap 0 r θ`. -/
private theorem hasDerivAt_circleMap_aux (r θ : ℝ) :
    HasDerivAt (circleMap 0 r) (Complex.I * circleMap 0 r θ) θ := by
  have h := hasDerivAt_rot_aux (r : ℂ) θ
  have e : ∀ s : ℝ, rot s (r : ℂ) = circleMap 0 r s := fun s => by
    simp [rot, circleMap, mul_comm]
  simp only [e] at h
  exact h

/-- `∫₀^{2π} ∂_θ φ(r e^{iθ}) dθ = 0` for `φ ∈ C¹`. -/
theorem intervalIntegral_angular_deriv_eq_zero {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (r : ℝ) :
    ∫ θ in (0 : ℝ)..2 * π,
      fderiv ℝ φ (circleMap 0 r θ) (Complex.I * circleMap 0 r θ) = 0 := by
  have hd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hderiv : ∀ θ ∈ uIcc (0 : ℝ) (2 * π),
      HasDerivAt (fun s : ℝ => φ (circleMap 0 r s))
        (fderiv ℝ φ (circleMap 0 r θ) (Complex.I * circleMap 0 r θ)) θ := fun θ _ =>
    (hd _).hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_circleMap_aux r θ)
  have hcm : Continuous (circleMap 0 r) := continuous_circleMap 0 r
  have hcont : Continuous fun θ : ℝ =>
      fderiv ℝ φ (circleMap 0 r θ) (Complex.I * circleMap 0 r θ) :=
    ((hφ.continuous_fderiv one_ne_zero).comp hcm).clm_apply (continuous_const.mul hcm)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  have hp : circleMap 0 r (2 * π) = circleMap 0 r 0 := by
    simpa using periodic_circleMap 0 r 0
  simp [hp]

end NonUniqueEuler.Polar
