import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Helper for `lem:adjoint`(2): a left eigenfunctional of `A` is one of `exp(tA)`

Helper of `P/Sec4/Adjoint.lean`. If `φ : X →L[ℂ] ℂ` satisfies `φ(A g) = z φ(g)` for all `g`, then
`φ(exp(tA) g) = e^{zt} φ(g)` (`04_ring.tex:616-618`). The manuscript differentiates
`t ↦ ℓ_*(e^{tL}g)`; here we use the exponential series directly (equivalent, shorter).
-/

noncomputable section

open Filter Topology
open scoped Nat

namespace NonUniqueEuler.AdjointAux

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem apply_pow_of_comp_eq (A : X →L[ℂ] X) (φ : X →L[ℂ] ℂ) (z : ℂ)
    (h : ∀ g, φ (A g) = z * φ g) (n : ℕ) (g : X) : φ ((A ^ n) g) = z ^ n * φ g := by
  induction n generalizing g with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_apply_eq_comp, ih, h, pow_succ]
    ring

variable [CompleteSpace X] in
/-- `φ ∘ A = z φ` implies `φ ∘ exp(tA) = e^{zt} φ`. -/
theorem apply_exp_smul_of_comp_eq (A : X →L[ℂ] X) (φ : X →L[ℂ] ℂ) (z : ℂ)
    (h : ∀ g, φ (A g) = z * φ g) (t : ℂ) (g : X) :
    φ (NormedSpace.exp (t • A) g) = Complex.exp (z * t) * φ g := by
  have hA : ∀ g, φ ((t • A) g) = (t * z) * φ g := by
    intro g
    rw [smul_apply, map_smul, h, smul_eq_mul]
    ring
  let Φ : (X →L[ℂ] X) →L[ℂ] ℂ := φ.comp (ContinuousLinearMap.apply ℂ X g)
  have h1 : HasSum (fun n : ℕ => (n !⁻¹ : ℂ) • (t • A) ^ n) (NormedSpace.exp (t • A)) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (t • A)
  have h2 := h1.mapL Φ
  have h3 : HasSum (fun n : ℕ => (n !⁻¹ : ℂ) • (z * t) ^ n) (NormedSpace.exp (z * t)) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (z * t)
  have h4 := h3.mul_right (φ g)
  have heq : (fun n : ℕ => Φ ((n !⁻¹ : ℂ) • (t • A) ^ n)) =
      fun n : ℕ => (n !⁻¹ : ℂ) • (z * t) ^ n * φ g := by
    funext n
    simp only [Φ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      map_smul, smul_eq_mul]
    rw [apply_pow_of_comp_eq (t • A) φ (t * z) hA n g]
    ring
  rw [heq] at h2
  rw [Complex.exp_eq_exp_ℂ]
  exact h2.unique h4

end NonUniqueEuler.AdjointAux
