import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Order.Antidiag.Prod
import Mathlib.Analysis.Complex.Basic
import NonUniqueEuler.Defs.Infra.Sobolev

/-!
# Helper for `P/Infra/Sobolev/DotGradSharp`: counting and a pointwise Cauchy–Schwarz bound

* `sum_choose_leIdx`: `∑_{β ≤ γ} C(γ₁,β₁) C(γ₂,β₂) = 2^{|γ|}`;
* `card_multiIdx`: `#multiIdx k = (k+1)(k+2)/2` (as real numbers);
* `norm_re_mul_add_im_mul_le`: `|Re z · A + Im z · B| ≤ |z| (|A|² + |B|²)^{1/2}`
  (Cauchy–Schwarz in `ℝ²`, `04_ring.tex:1561-1563`).

(`sum_choose_leIdx` follows the helper of the same name in `H/Infra/Sobolev/Leibniz/L2.lean`.)
-/

noncomputable section

open scoped ENNReal

namespace NonUniqueEuler.Sob.DotGradSharpAux

theorem sum_choose_leIdx (γ : ℕ × ℕ) :
    ∑ β ∈ leIdx γ, ((γ.1.choose β.1 * γ.2.choose β.2 : ℕ) : ℝ) = 2 ^ (γ.1 + γ.2) := by
  have : ∑ β ∈ leIdx γ, (γ.1.choose β.1 * γ.2.choose β.2 : ℕ) = 2 ^ (γ.1 + γ.2) := by
    rw [leIdx, Finset.sum_product, pow_add, ← Nat.sum_range_choose γ.1,
      ← Nat.sum_range_choose γ.2, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  exact_mod_cast this

theorem multiIdx_succ (k : ℕ) :
    multiIdx (k + 1) = multiIdx k ∪ Finset.antidiagonal (k + 1) := by
  ext γ
  simp only [Finset.mem_union, mem_multiIdx, Finset.mem_antidiagonal]
  omega

theorem card_multiIdx_two_mul (k : ℕ) : 2 * (multiIdx k).card = (k + 1) * (k + 2) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hdisj : Disjoint (multiIdx k) (Finset.antidiagonal (k + 1)) := by
      rw [Finset.disjoint_left]
      intro γ h1 h2
      rw [mem_multiIdx] at h1
      rw [Finset.mem_antidiagonal] at h2
      omega
    rw [multiIdx_succ, Finset.card_union_of_disjoint hdisj, Finset.Nat.card_antidiagonal,
      mul_add, ih]
    ring

theorem card_multiIdx (k : ℕ) :
    ((multiIdx k).card : ℝ) = ((k : ℝ) + 1) * ((k : ℝ) + 2) / 2 := by
  have h := card_multiIdx_two_mul k
  have h' : (2 : ℝ) * (multiIdx k).card = ((k : ℝ) + 1) * ((k : ℝ) + 2) := by
    exact_mod_cast h
  linarith

/-- Cauchy–Schwarz in `ℝ²`: `|a A + b B| ≤ (a² + b²)^{1/2} (|A|² + |B|²)^{1/2}` with `a + ib = z`. -/
theorem norm_re_mul_add_im_mul_le (z A B : ℂ) :
    ‖(z.re : ℂ) * A + (z.im : ℂ) * B‖ ≤ ‖z‖ * Real.sqrt (‖A‖ ^ 2 + ‖B‖ ^ 2) := by
  have h1 : ‖(z.re : ℂ) * A + (z.im : ℂ) * B‖ ≤ |z.re| * ‖A‖ + |z.im| * ‖B‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
  refine h1.trans ?_
  have hz : ‖z‖ = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply, sq, sq]
  rw [hz, ← Real.sqrt_mul (by positivity)]
  apply Real.le_sqrt_of_sq_le
  have ha : |z.re| ^ 2 = z.re ^ 2 := sq_abs _
  have hb : |z.im| ^ 2 = z.im ^ 2 := sq_abs _
  nlinarith [sq_nonneg (|z.re| * ‖B‖ - |z.im| * ‖A‖)]

end NonUniqueEuler.Sob.DotGradSharpAux
