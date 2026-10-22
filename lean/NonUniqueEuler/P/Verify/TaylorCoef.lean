import NonUniqueEuler.Defs.Verify.Taylor
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Proof: the Taylor-coefficient calculus (linearity, Leibniz, derivative shift)

Proof of the interface `I/Verify/TaylorCoef.lean` (same declarations, statements verbatim).

**Manuscript.** Proof of Proposition A.3 (`prop:enclosure`), steps (i) and (iii)
(`A_verification.tex:346-362` and `:380-400`).

Each lemma is a direct consequence of the corresponding Mathlib lemma on `iteratedDeriv`
(`Mathlib/Analysis/Calculus/IteratedDeriv/Lemmas.lean`), after unfolding
`taylorCoeff f k x = (k!)⁻¹ • f^{(k)}(x)`:
* linearity: `iteratedDeriv_fun_add`, `iteratedDeriv_fun_sub`,
  `iteratedDeriv_fun_const_smul_field`, `iteratedDeriv_const_mul`;
* constants: `iteratedDeriv_const`;
* derivative shift: `iteratedDeriv_succ'` and `(k+1)! = (k+1) k!`;
* Leibniz: `iteratedDeriv_fun_mul` and `C(k,r) r! (k-r)! = k!`
  (`Nat.choose_mul_factorial_mul_factorial`);
* real-to-complex: `ContinuousLinearMap.iteratedFDeriv_comp_left` with `Complex.ofRealCLM`;
* exponentials: `iteratedDeriv_exp_const_mul`.
-/

namespace NonUniqueEuler

namespace AppA

open Finset
open scoped ContDiff

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem taylorCoeff_add {f g : ℝ → F} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (k : ℕ) (x : ℝ) :
    taylorCoeff (fun y => f y + g y) k x = taylorCoeff f k x + taylorCoeff g k x := by
  have h1 : ContDiffAt ℝ k f x := (contDiff_infty.mp hf k).contDiffAt
  have h2 : ContDiffAt ℝ k g x := (contDiff_infty.mp hg k).contDiffAt
  unfold taylorCoeff
  rw [iteratedDeriv_fun_add h1 h2, smul_add]

theorem taylorCoeff_sub {f g : ℝ → F} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (k : ℕ) (x : ℝ) :
    taylorCoeff (fun y => f y - g y) k x = taylorCoeff f k x - taylorCoeff g k x := by
  have h1 : ContDiffAt ℝ k f x := (contDiff_infty.mp hf k).contDiffAt
  have h2 : ContDiffAt ℝ k g x := (contDiff_infty.mp hg k).contDiffAt
  unfold taylorCoeff
  rw [iteratedDeriv_fun_sub h1 h2, smul_sub]

theorem taylorCoeff_const_smul {f : ℝ → F} (hf : ContDiff ℝ ∞ f) (c : ℝ) (k : ℕ) (x : ℝ) :
    taylorCoeff (fun y => c • f y) k x = c • taylorCoeff f k x := by
  unfold taylorCoeff
  rw [iteratedDeriv_fun_const_smul_field c f, smul_comm]

/-- The Taylor coefficients of order `k ≥ 1` of a constant vanish. -/
theorem taylorCoeff_const (c : F) {k : ℕ} (hk : k ≠ 0) (x : ℝ) :
    taylorCoeff (fun _ : ℝ => c) k x = 0 := by
  unfold taylorCoeff
  simp [iteratedDeriv_const, hk]

/-- The derivative shift `(f')_k = (k+1) f_{k+1}`. -/
theorem taylorCoeff_deriv (f : ℝ → F) (k : ℕ) (x : ℝ) :
    taylorCoeff (deriv f) k x = ((k : ℝ) + 1) • taylorCoeff f (k + 1) x := by
  unfold taylorCoeff
  rw [iteratedDeriv_succ', smul_smul]
  congr 1
  have hk : (Nat.factorial k : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  field_simp

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]

/-- **Leibniz rule** for Taylor coefficients (Cauchy product):
`(fg)_k = Σ_{r ≤ k} f_r g_{k-r}`. -/
theorem taylorCoeff_mul {f g : ℝ → 𝔸} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (k : ℕ) (x : ℝ) :
    taylorCoeff (fun y => f y * g y) k x =
      ∑ r ∈ range (k + 1), taylorCoeff f r x * taylorCoeff g (k - r) x := by
  have h1 : ContDiffAt ℝ k f x := (contDiff_infty.mp hf k).contDiffAt
  have h2 : ContDiffAt ℝ k g x := (contDiff_infty.mp hg k).contDiffAt
  unfold taylorCoeff
  rw [iteratedDeriv_fun_mul h1 h2, Finset.smul_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hrk : r ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
  rw [smul_mul_smul_comm, mul_assoc, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  have hc := Nat.choose_mul_factorial_mul_factorial hrk
  have hr0 : (Nat.factorial r : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos r).ne'
  have hkr0 : (Nat.factorial (k - r) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos (k - r)).ne'
  have hch : ((k.choose r : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hrk).ne'
  have hc' : ((k.choose r : ℕ) : ℝ) * (Nat.factorial r : ℝ) * (Nat.factorial (k - r) : ℝ) =
      (Nat.factorial k : ℝ) := by exact_mod_cast hc
  rw [← hc']
  field_simp

theorem taylorCoeff_const_mul {f : ℝ → 𝔸} (hf : ContDiff ℝ ∞ f) (c : 𝔸) (k : ℕ) (x : ℝ) :
    taylorCoeff (fun y => c * f y) k x = c * taylorCoeff f k x := by
  have h1 : ContDiffAt ℝ k f x := (contDiff_infty.mp hf k).contDiffAt
  unfold taylorCoeff
  rw [iteratedDeriv_const_mul c h1, mul_smul_comm]

/-- Real data in complex recurrences: the Taylor coefficients of `ξ ↦ (f ξ : ℂ)` are those of
`f`. -/
theorem taylorCoeff_ofReal {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (k : ℕ) (x : ℝ) :
    taylorCoeff (fun y => (f y : ℂ)) k x = ((taylorCoeff f k x : ℝ) : ℂ) := by
  have h1 : ContDiffAt ℝ k f x := (contDiff_infty.mp hf k).contDiffAt
  have hcomp : (fun y => (f y : ℂ)) = (Complex.ofRealCLM : ℝ →L[ℝ] ℂ) ∘ f := rfl
  have hD : iteratedDeriv k (fun y => (f y : ℂ)) x = ((iteratedDeriv k f x : ℝ) : ℂ) := by
    rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv, hcomp,
      Complex.ofRealCLM.iteratedFDeriv_comp_left h1 le_rfl]
    simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      Complex.ofRealCLM_apply]
  unfold taylorCoeff
  rw [hD, Complex.real_smul, smul_eq_mul, Complex.ofReal_mul]

/-- `(e^{cξ})_k = c^k e^{cξ}/k!` (for `c = ±2`: the coefficients `E^±_k`). -/
theorem taylorCoeff_exp_mul (c : ℝ) (k : ℕ) (x : ℝ) :
    taylorCoeff (fun y => Real.exp (c * y)) k x =
      c ^ k / (Nat.factorial k : ℝ) * Real.exp (c * x) := by
  unfold taylorCoeff
  rw [iteratedDeriv_exp_const_mul, smul_eq_mul]
  ring

end AppA

end NonUniqueEuler
