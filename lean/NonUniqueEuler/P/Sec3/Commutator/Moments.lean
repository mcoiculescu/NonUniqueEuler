import NonUniqueEuler.Defs.Sec3.Commutator
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Proof: the first moments of `∇ρ` (`∫ψ^{ij} = -δ_ij`)

Proof of `I/Sec3/Commutator/Moments.lean` (`03_compactness.tex:415-417`).

Integration by parts (`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`) with `f = ℓ`,
`g = ρ`: `∫ ℓ Dρ v = -∫ Dℓ v ρ = -ℓ(v) ∫ρ = -ℓ(v)`. All integrands are continuous with compact
support (`ρ` and `Dρ` have compact support). The ball form follows since `Dρ = 0` off
`tsupport ρ ⊆ B₁` (`support_fderiv_subset`).
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler.Weak

/-- `∫ ℓ(z) Dρ(z)v dz = -ℓ(v)` (`03_compactness.tex:415-417`, `∫ψ^{ij} = -δ_ij`). -/
theorem integral_mul_fderiv_mollifier_eq_neg {ρ : ℂ → ℝ} (hρ : IsMollifier ρ)
    (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ) :
    ∫ z, ℓ z * fderiv ℝ ρ z v = -ℓ v := by
  have hρc : Continuous ρ := hρ.contDiff.continuous
  have hρd : Differentiable ℝ ρ := hρ.contDiff.differentiable (by simp)
  have hDρc : Continuous fun z => fderiv ℝ ρ z v :=
    ((hρ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hDρs : HasCompactSupport fun z => fderiv ℝ ρ z v :=
    hρ.hasCompactSupport.fderiv (𝕜 := ℝ) |>.comp_left (g := fun L : ℂ →L[ℝ] ℝ => L v) (by simp)
  have hℓ : ∀ z, fderiv ℝ (fun x => ℓ x) z = ℓ := fun z => ℓ.fderiv
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun z => ℓ z) (g := ρ) (v := v)
    (by
      simp only [hℓ]
      exact (continuous_const.mul hρc).integrable_of_hasCompactSupport
        hρ.hasCompactSupport.mul_left)
    ((ℓ.continuous.mul hDρc).integrable_of_hasCompactSupport hDρs.mul_left)
    ((ℓ.continuous.mul hρc).integrable_of_hasCompactSupport hρ.hasCompactSupport.mul_left)
    (fun z _ => ℓ.differentiableAt) (fun z _ => hρd z)
  rw [key]
  simp only [hℓ]
  rw [integral_const_mul, hρ.integral_eq_one, mul_one]

/-- The same integral over `B₁`. -/
theorem setIntegral_ball_mul_fderiv_mollifier_eq_neg {ρ : ℂ → ℝ} (hρ : IsMollifier ρ)
    (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ) :
    ∫ z in ball (0 : ℂ) 1, ℓ z * fderiv ℝ ρ z v = -ℓ v := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero, integral_mul_fderiv_mollifier_eq_neg hρ]
  intro z hz
  have hz' : z ∉ tsupport ρ := fun h => hz (hρ.tsupport_subset h)
  have : fderiv ℝ ρ z = 0 := by
    by_contra h
    exact hz' (support_fderiv_subset (𝕜 := ℝ) h)
  simp [this]

end NonUniqueEuler.Weak
