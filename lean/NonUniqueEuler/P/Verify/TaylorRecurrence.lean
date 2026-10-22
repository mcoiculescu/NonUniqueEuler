import NonUniqueEuler.Defs.Verify.Taylor
import NonUniqueEuler.I.Verify.TaylorCoef
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Proof: the Taylor-coefficient recurrences of the enclosure procedure

Proof of the interface `NonUniqueEuler/I/Verify/TaylorRecurrence.lean` (same declarations,
statements copied verbatim).

**Manuscript.** Proof of Proposition A.3 (`prop:enclosure`, `A_verification.tex:346-362`,
`:380-400`, `:418-420`).

The recurrences follow from the Taylor-coefficient calculus of `I/Verify/TaylorCoef.lean`
(`taylorCoeff_deriv`, `taylorCoeff_mul`, `taylorCoeff_const_mul`, `taylorCoeff_add`,
`taylorCoeff_const`), used as a black box. The locality statement on a closed interval uses
`Set.EqOn.iteratedDeriv_of_isOpen` on `Ioo a b`, continuity of the iterated derivatives and
`closure_Ioo`.
-/

namespace NonUniqueEuler

namespace AppA

open Finset Set
open scoped ContDiff

/-- The logistic recurrence: if `A' = c · A Ā`, then
`A_{k+1} = (c/(k+1)) Σ_{r ≤ k} A_r Ā_{k-r}`. -/
theorem taylorCoeff_riccati {A Ā : ℝ → ℝ} {c : ℝ} (hA : ContDiff ℝ ∞ A)
    (hĀ : ContDiff ℝ ∞ Ā) (h : ∀ x, deriv A x = c * (A x * Ā x)) (k : ℕ) (x : ℝ) :
    taylorCoeff A (k + 1) x =
      c / ((k : ℝ) + 1) * ∑ r ∈ range (k + 1), taylorCoeff A r x * taylorCoeff Ā (k - r) x := by
  have hAA : ContDiff ℝ ∞ (fun y => A y * Ā y) := hA.mul hĀ
  have hd : deriv A = fun y => c * (A y * Ā y) := funext h
  have h1 := taylorCoeff_deriv A k x
  rw [hd, taylorCoeff_const_mul hAA c k x, taylorCoeff_mul hA hĀ k x, smul_eq_mul] at h1
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  rw [div_mul_eq_mul_div, h1, mul_div_cancel_left₀ _ hk]

/-- If `A + Ā` is constant, then `Ā_{k+1} = -A_{k+1}`. -/
theorem taylorCoeff_succ_eq_neg_of_add_eq_const {A Ā : ℝ → ℝ} {C : ℝ} (hA : ContDiff ℝ ∞ A)
    (hĀ : ContDiff ℝ ∞ Ā) (h : ∀ x, A x + Ā x = C) (k : ℕ) (x : ℝ) :
    taylorCoeff Ā (k + 1) x = -taylorCoeff A (k + 1) x := by
  have h1 := taylorCoeff_add hA hĀ (k + 1) x
  have hC : (fun y => A y + Ā y) = fun _ => C := funext h
  rw [hC, taylorCoeff_const C (Nat.succ_ne_zero k) x] at h1
  linarith

/-- The reciprocal recurrence: for a smooth nowhere vanishing `D`,
`(1/D)_{k+1} = -(1/D(x)) Σ_{r ≤ k} D_{r+1} (1/D)_{k-r}`
(that is, `R_k = -R_0 Σ_{r=1}^k D_r R_{k-r}`). -/
theorem taylorCoeff_inv {D : ℝ → ℂ} (hD : ContDiff ℝ ∞ D) (hne : ∀ x, D x ≠ 0) (k : ℕ)
    (x : ℝ) :
    taylorCoeff (fun y => (D y)⁻¹) (k + 1) x =
      -(D x)⁻¹ * ∑ r ∈ range (k + 1),
        taylorCoeff D (r + 1) x * taylorCoeff (fun y => (D y)⁻¹) (k - r) x := by
  have hDi : ContDiff ℝ ∞ (fun y => (D y)⁻¹) := hD.inv hne
  have h1 := taylorCoeff_mul hD hDi (k + 1) x
  have hone : (fun y => D y * (D y)⁻¹) = fun _ => (1 : ℂ) :=
    funext fun y => mul_inv_cancel₀ (hne y)
  rw [hone, taylorCoeff_const (1 : ℂ) (Nat.succ_ne_zero k) x, Finset.sum_range_succ'] at h1
  simp only [Nat.add_sub_add_right, Nat.sub_zero, taylorCoeff_zero D x] at h1
  -- `h1 : 0 = Σ_{r ≤ k} D_{r+1} R_{k-r} + D x * R_{k+1}`
  set S := ∑ r ∈ range (k + 1),
    taylorCoeff D (r + 1) x * taylorCoeff (fun y => (D y)⁻¹) (k - r) x with hS
  set R := taylorCoeff (fun y => (D y)⁻¹) (k + 1) x with hR
  have hx := hne x
  have e : D x * R = -S := by linear_combination -h1
  calc R = (D x)⁻¹ * (D x * R) := by rw [inv_mul_cancel_left₀ hx]
    _ = -(D x)⁻¹ * S := by rw [e]; ring

/-- The ODE recurrence: if `ψ'' = Vψ` on `ℝ`, then
`(k+1)(k+2) ψ_{k+2} = Σ_{r ≤ k} V_r ψ_{k-r}`. -/
theorem taylorCoeff_ode2 {ψ V : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hV : ContDiff ℝ ∞ V)
    (h : ∀ x, deriv (deriv ψ) x = V x * ψ x) (k : ℕ) (x : ℝ) :
    ((k : ℂ) + 1) * ((k : ℂ) + 2) * taylorCoeff ψ (k + 2) x =
      ∑ r ∈ range (k + 1), taylorCoeff V r x * taylorCoeff ψ (k - r) x := by
  have hd : deriv (deriv ψ) = fun y => V y * ψ y := funext h
  have h1 := taylorCoeff_deriv (deriv ψ) k x
  have h2 := taylorCoeff_deriv ψ (k + 1) x
  rw [show k + 1 + 1 = k + 2 from rfl] at h2
  rw [hd, taylorCoeff_mul hV hψ k x, h2] at h1
  rw [h1, Complex.real_smul, Complex.real_smul]
  push_cast
  ring

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Two smooth functions that agree on a nondegenerate closed interval have the same
derivatives of every order at every point of the closed interval (including the endpoints). -/
theorem iteratedDeriv_eq_of_eqOn_Icc {f g : ℝ → F} {a b : ℝ} (hab : a < b)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (h : EqOn f g (Icc a b)) {x : ℝ}
    (hx : x ∈ Icc a b) (k : ℕ) :
    iteratedDeriv k f x = iteratedDeriv k g x := by
  have hk : ((k : ℕ∞) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hcont : ∀ φ : ℝ → F, ContDiff ℝ ∞ φ → Continuous (iteratedDeriv k φ) :=
    fun φ hφ => hφ.continuous_iteratedDeriv k hk
  have hIoo : EqOn (iteratedDeriv k f) (iteratedDeriv k g) (Ioo a b) :=
    (h.mono Set.Ioo_subset_Icc_self).iteratedDeriv_of_isOpen isOpen_Ioo k
  have hIcc : EqOn (iteratedDeriv k f) (iteratedDeriv k g) (Icc a b) :=
    hIoo.of_subset_closure (hcont f hf).continuousOn (hcont g hg).continuousOn
      Set.Ioo_subset_Icc_self (by rw [closure_Ioo hab.ne])
  exact hIcc hx

theorem taylorCoeff_eq_of_eqOn_Icc {f g : ℝ → F} {a b : ℝ} (hab : a < b)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (h : EqOn f g (Icc a b)) {x : ℝ}
    (hx : x ∈ Icc a b) (k : ℕ) :
    taylorCoeff f k x = taylorCoeff g k x := by
  unfold taylorCoeff
  rw [iteratedDeriv_eq_of_eqOn_Icc hab hf hg h hx k]

end AppA

end NonUniqueEuler
