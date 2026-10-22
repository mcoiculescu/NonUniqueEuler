import NonUniqueEuler.Defs.Infra.ODE
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Proof of the interface (I-ODE): smoothness of solutions of `ψ'' = V ψ + F`

Proves `IsInhomSolOn.contDiff` and `IsSolOn.contDiff` of `I/Infra/ODE/Smooth.lean`.

Proof. On `univ`, the derivatives within `univ` are ordinary derivatives, so `deriv ψ = ψ'`
and `deriv ψ' = V ψ + F`. By induction on `n : ℕ`, `ψ` and `ψ'` are `C^n`: the step uses
`contDiff_succ_iff_deriv` (the analyticity clause is vacuous since `n ≠ ω`) with
`deriv ψ = ψ' ∈ C^n` and `deriv ψ' = V ψ + F ∈ C^n`. Then `contDiff_infty` concludes.
The homogeneous case is the case `F = 0` (`IsSolOn.toInhom`).
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace NonUniqueEuler.LinODE

variable {V F : ℝ → ℂ} {s : Set ℝ} {ψ ψ' φ φ' : ℝ → ℂ}

/-- One bootstrap step: a differentiable function whose derivative is `C^n` is `C^{n+1}`. -/
private theorem contDiff_succ_of_deriv {f : ℝ → ℂ} {n : ℕ} (hf : Differentiable ℝ f)
    (hd : ContDiff ℝ n (deriv f)) : ContDiff ℝ (n + 1 : ℕ) f := by
  have h : ContDiff ℝ ((n : WithTop ℕ∞) + 1) f :=
    contDiff_succ_iff_deriv.2 ⟨hf, fun h => absurd h (by simp), hd⟩
  exact_mod_cast h

/-- Smooth coefficients give smooth solutions (inhomogeneous equation on `ℝ`). -/
theorem IsInhomSolOn.contDiff (hV : ContDiff ℝ ∞ V) (hF : ContDiff ℝ ∞ F)
    (h : IsInhomSolOn V F univ ψ ψ') :
    ContDiff ℝ ∞ ψ ∧ ContDiff ℝ ∞ ψ' ∧ deriv ψ = ψ' ∧
      ∀ ξ, deriv (deriv ψ) ξ = V ξ * ψ ξ + F ξ := by
  have h1 : ∀ ξ, HasDerivAt ψ (ψ' ξ) ξ := fun ξ =>
    (h.hasDerivWithinAt ξ (mem_univ ξ)).hasDerivAt Filter.univ_mem
  have h2 : ∀ ξ, HasDerivAt ψ' (V ξ * ψ ξ + F ξ) ξ := fun ξ =>
    (h.hasDerivWithinAt' ξ (mem_univ ξ)).hasDerivAt Filter.univ_mem
  have hd1 : deriv ψ = ψ' := funext fun ξ => (h1 ξ).deriv
  have hd2 : deriv ψ' = fun ξ => V ξ * ψ ξ + F ξ := funext fun ξ => (h2 ξ).deriv
  have hdiff1 : Differentiable ℝ ψ := fun ξ => (h1 ξ).differentiableAt
  have hdiff2 : Differentiable ℝ ψ' := fun ξ => (h2 ξ).differentiableAt
  have key : ∀ n : ℕ, ContDiff ℝ n ψ ∧ ContDiff ℝ n ψ' := by
    intro n
    induction n with
    | zero => exact ⟨contDiff_zero.2 hdiff1.continuous, contDiff_zero.2 hdiff2.continuous⟩
    | succ n ih =>
      refine ⟨contDiff_succ_of_deriv hdiff1 (hd1 ▸ ih.2), contDiff_succ_of_deriv hdiff2 ?_⟩
      rw [hd2]
      exact ((contDiff_infty.1 hV n).mul ih.1).add (contDiff_infty.1 hF n)
  refine ⟨contDiff_infty.2 fun n => (key n).1, contDiff_infty.2 fun n => (key n).2, hd1,
    fun ξ => ?_⟩
  rw [hd1, hd2]

/-- Smooth coefficients give smooth solutions (homogeneous equation on `ℝ`). -/
theorem IsSolOn.contDiff (hV : ContDiff ℝ ∞ V) (h : IsSolOn V univ ψ ψ') :
    ContDiff ℝ ∞ ψ ∧ ContDiff ℝ ∞ ψ' ∧ deriv ψ = ψ' ∧
      ∀ ξ, deriv (deriv ψ) ξ = V ξ * ψ ξ := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := IsInhomSolOn.contDiff (F := 0) hV contDiff_zero_fun h.toInhom
  refine ⟨h₁, h₂, h₃, fun ξ => ?_⟩
  have := h₄ ξ
  rwa [Pi.zero_apply, add_zero] at this

end NonUniqueEuler.LinODE
