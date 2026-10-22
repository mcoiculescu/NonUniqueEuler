import NonUniqueEuler.Defs.Infra.CkNorm
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Complex.Basic

/-!
# Proof: the array norm of derivatives versus the operator norm (library I-CK)

Proof of `I/Infra/CkNorm/ArrayNorm.lean`. The manuscript's `|∇^q h(x)|` (`02_prelim.tex:72-75`)
is the Euclidean norm of the array of the `2^q` entries `D^q h x (e_{i 1}, …, e_{i q})`,
`e₀ = 1`, `e₁ = I`. We prove, for any continuous `q`-multilinear map `T` on `ℂ = ℝ²`,
`‖T‖ ≤ (∑_i ‖T e_i‖²)^{1/2} ≤ 2^{q/2} ‖T‖`, and apply it to `T = D^q h x`.

* First inequality: expand `v j = re (v j) • 1 + im (v j) • I` by multilinearity
  (`ContinuousMultilinearMap.map_sum`, `map_smul_univ`), then Cauchy–Schwarz
  (`Real.sum_mul_le_sqrt_mul_sqrt`) and `∑_r ∏_j c_{j,r j}² = ∏_j ‖v j‖²`
  (`Finset.prod_univ_sum`).
* Second inequality: each entry is at most `‖T‖` (`le_opNorm`, `‖1‖ = ‖I‖ = 1`), and there are
  `2^q` entries.
-/

noncomputable section

namespace NonUniqueEuler

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace ArrayNormAux

/-- The coordinates of `z` in the real basis `(1, I)`. -/
def coord (z : ℂ) : Fin 2 → ℝ := ![z.re, z.im]

/-- The real basis `(1, I)` of `ℂ`. -/
def basis2 : Fin 2 → ℂ := ![(1 : ℂ), Complex.I]

theorem eq_sum_coord (z : ℂ) : z = ∑ k : Fin 2, coord z k • basis2 k := by
  apply Complex.ext <;> simp [Fin.sum_univ_two, coord, basis2]

theorem sum_sq_coord (z : ℂ) : ∑ k : Fin 2, coord z k ^ 2 = ‖z‖ ^ 2 := by
  rw [Fin.sum_univ_two, Complex.sq_norm, Complex.normSq_apply]
  simp [coord]
  ring

theorem norm_basis2 (k : Fin 2) : ‖basis2 k‖ = 1 := by
  fin_cases k <;> simp [basis2]

/-- First inequality, for an arbitrary continuous multilinear map. -/
theorem opNorm_le_sqrt_sum {q : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin q => ℂ) F) :
    ‖T‖ ≤ Real.sqrt (∑ i : Fin q → Fin 2, ‖T (fun j => basis2 (i j))‖ ^ 2) := by
  classical
  refine ContinuousMultilinearMap.opNorm_le_bound (Real.sqrt_nonneg _) fun v => ?_
  set c : Fin q → Fin 2 → ℝ := fun j => coord (v j) with hc
  have hv : v = fun j => ∑ k : Fin 2, c j k • basis2 k := funext fun j => eq_sum_coord (v j)
  have hexp : T v = ∑ r : Fin q → Fin 2, (∏ j, c j (r j)) • T (fun j => basis2 (r j)) := by
    conv_lhs => rw [hv]
    rw [T.map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    exact T.map_smul_univ (fun j => c j (r j)) (fun j => basis2 (r j))
  have hprod : ∑ r : Fin q → Fin 2, (∏ j, c j (r j)) ^ 2 = (∏ j, ‖v j‖) ^ 2 := by
    rw [← Finset.prod_pow]
    have h1 : ∀ j, ‖v j‖ ^ 2 = ∑ k : Fin 2, c j k ^ 2 := fun j => (sum_sq_coord (v j)).symm
    simp_rw [h1]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    exact Finset.sum_congr rfl fun r _ => (Finset.prod_pow _ _ _).symm
  calc ‖T v‖ ≤ ∑ r : Fin q → Fin 2, ‖(∏ j, c j (r j)) • T (fun j => basis2 (r j))‖ := by
        rw [hexp]; exact norm_sum_le _ _
    _ = ∑ r : Fin q → Fin 2, |∏ j, c j (r j)| * ‖T (fun j => basis2 (r j))‖ := by
        simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ Real.sqrt (∑ r : Fin q → Fin 2, |∏ j, c j (r j)| ^ 2) *
          Real.sqrt (∑ r : Fin q → Fin 2, ‖T (fun j => basis2 (r j))‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = Real.sqrt (∑ i : Fin q → Fin 2, ‖T (fun j => basis2 (i j))‖ ^ 2) * ∏ j, ‖v j‖ := by
        simp_rw [sq_abs]
        rw [hprod, Real.sqrt_sq (Finset.prod_nonneg fun _ _ => norm_nonneg _), mul_comm]

/-- Second inequality, for an arbitrary continuous multilinear map. -/
theorem sqrt_sum_le_opNorm {q : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin q => ℂ) F) :
    Real.sqrt (∑ i : Fin q → Fin 2, ‖T (fun j => basis2 (i j))‖ ^ 2) ≤
      Real.sqrt (2 ^ q) * ‖T‖ := by
  have hentry : ∀ i : Fin q → Fin 2, ‖T (fun j => basis2 (i j))‖ ≤ ‖T‖ := fun i => by
    have := T.le_opNorm (fun j => basis2 (i j))
    simpa [norm_basis2] using this
  have hsum : ∑ i : Fin q → Fin 2, ‖T (fun j => basis2 (i j))‖ ^ 2 ≤ 2 ^ q * ‖T‖ ^ 2 := by
    calc ∑ i : Fin q → Fin 2, ‖T (fun j => basis2 (i j))‖ ^ 2
        ≤ ∑ _i : Fin q → Fin 2, ‖T‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hentry i) 2
      _ = 2 ^ q * ‖T‖ ^ 2 := by simp [Finset.sum_const, Finset.card_univ]
  calc Real.sqrt (∑ i : Fin q → Fin 2, ‖T (fun j => basis2 (i j))‖ ^ 2)
      ≤ Real.sqrt (2 ^ q * ‖T‖ ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (2 ^ q) * ‖T‖ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]

theorem iterDerivArrayNorm_eq (q : ℕ) (h : ℂ → F) (x : ℂ) :
    iterDerivArrayNorm q h x = Real.sqrt (∑ i : Fin q → Fin 2,
      ‖iteratedFDeriv ℝ q h x (fun j => basis2 (i j))‖ ^ 2) := rfl

end ArrayNormAux

open ArrayNormAux

theorem norm_iteratedFDeriv_le_arrayNorm (q : ℕ) (h : ℂ → F) (x : ℂ) :
    ‖iteratedFDeriv ℝ q h x‖ ≤ iterDerivArrayNorm q h x := by
  rw [iterDerivArrayNorm_eq]
  exact opNorm_le_sqrt_sum _

theorem arrayNorm_le_norm_iteratedFDeriv (q : ℕ) (h : ℂ → F) (x : ℂ) :
    iterDerivArrayNorm q h x ≤ Real.sqrt (2 ^ q) * ‖iteratedFDeriv ℝ q h x‖ := by
  rw [iterDerivArrayNorm_eq]
  exact sqrt_sum_le_opNorm _

end NonUniqueEuler
