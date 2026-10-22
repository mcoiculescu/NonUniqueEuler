import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import NonUniqueEuler.Defs.Infra.SobolevOneD

/-!
# Helper for `P/Infra/SobolevOneD/Multiplier`: pointwise and combinatorial bounds

* `norm_leibniz_sq_le`: if `‖A i‖ ≤ M` for `i ≤ j`, then
  `|∑_{i ≤ j} C(j,i) A_i G_{j-i}|² ≤ M² 2^j ∑_{i ≤ j} C(j,i) |G_{j-i}|²`
  (Cauchy–Schwarz with weights `C(j,i)`, `∑_i C(j,i) = 2^j`);
* `weighted_sum_le`: if `J_j ≤ M² 2^j ∑_{i ≤ j} C(j,i) I_{j-i}` with `I ≥ 0`, then
  `∑_{j ≤ k} (1+ℓ²)^{k-j} J_j ≤ 4^{k+1} M² ∑_{j ≤ k} (1+ℓ²)^{k-j} I_j`
  (weight monotonicity `(1+ℓ²)^{k-j} ≤ (1+ℓ²)^{k-(j-i)}`, `C(j,i) ≤ 2^j`, `∑_{j ≤ k} 4^j ≤ 4^{k+1}`).
-/

noncomputable section

namespace NonUniqueEuler.Sob.MultAux

/-- The pointwise Leibniz bound. -/
theorem norm_leibniz_sq_le {j : ℕ} {M : ℝ} (A G : ℕ → ℂ) (hA : ∀ i ≤ j, ‖A i‖ ≤ M) :
    ‖∑ i ∈ Finset.range (j + 1), (j.choose i : ℂ) * (A i * G (j - i))‖ ^ 2 ≤
      M ^ 2 * 2 ^ j * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖G (j - i)‖ ^ 2 := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hA 0 (Nat.zero_le _))
  set r : ℕ → ℝ := fun i => (j.choose i : ℝ) * (M * ‖G (j - i)‖) with hr
  have h1 : ‖∑ i ∈ Finset.range (j + 1), (j.choose i : ℂ) * (A i * G (j - i))‖ ≤
      ∑ i ∈ Finset.range (j + 1), r i := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    have hi' : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [norm_mul, norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hA i hi') (norm_nonneg _))
      (Nat.cast_nonneg _)
  have h2 : (∑ i ∈ Finset.range (j + 1), r i) ^ 2 ≤
      (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) *
        ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (M ^ 2 * ‖G (j - i)‖ ^ 2) :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun i _ => Nat.cast_nonneg _)
      (fun i _ => by positivity) (fun i _ => by simp only [hr]; nlinarith)
  have h3 : ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) = 2 ^ j := by
    exact_mod_cast Nat.sum_range_choose j
  have h0 : 0 ≤ ‖∑ i ∈ Finset.range (j + 1), (j.choose i : ℂ) * (A i * G (j - i))‖ :=
    norm_nonneg _
  calc ‖∑ i ∈ Finset.range (j + 1), (j.choose i : ℂ) * (A i * G (j - i))‖ ^ 2
      ≤ (∑ i ∈ Finset.range (j + 1), r i) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ ≤ _ := h2
    _ = M ^ 2 * 2 ^ j * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖G (j - i)‖ ^ 2 := by
        rw [h3, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring

theorem sum_four_pow_le (k : ℕ) : ∑ j ∈ Finset.range (k + 1), (4 : ℝ) ^ j ≤ 4 ^ (k + 1) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hp : (0 : ℝ) ≤ 4 ^ (k + 1) := by positivity
    calc ∑ j ∈ Finset.range (k + 1), (4 : ℝ) ^ j + 4 ^ (k + 1) ≤ 4 ^ (k + 1) + 4 ^ (k + 1) := by
          linarith
      _ ≤ 4 ^ (k + 1 + 1) := by rw [pow_succ (4 : ℝ) (k + 1)]; linarith

/-- The weighted sum bound. -/
theorem weighted_sum_le {k : ℕ} (ℓ : ℤ) {M : ℝ} {J I : ℕ → ℝ} (hI : ∀ m, 0 ≤ I m)
    (hJ : ∀ j ≤ k, J j ≤
      M ^ 2 * 2 ^ j * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * I (j - i)) :
    ∑ j ∈ Finset.range (k + 1), secWeight k j ℓ * J j ≤
      4 ^ (k + 1) * M ^ 2 * ∑ j ∈ Finset.range (k + 1), secWeight k j ℓ * I j := by
  set S := ∑ j ∈ Finset.range (k + 1), secWeight k j ℓ * I j with hSdef
  have hwI : ∀ m, 0 ≤ secWeight k m ℓ * I m := fun m => mul_nonneg (secWeight_nonneg _ _ _) (hI m)
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => hwI j
  have hterm : ∀ j ≤ k, secWeight k j ℓ * J j ≤ M ^ 2 * 4 ^ j * S := by
    intro j hj
    have hw : ∀ i ≤ j, secWeight k j ℓ ≤ secWeight k (j - i) ℓ := fun i hi =>
      pow_le_pow_right₀ (by nlinarith [sq_nonneg (ℓ : ℝ)]) (by omega)
    have hsub : ∑ i ∈ Finset.range (j + 1), secWeight k (j - i) ℓ * I (j - i) ≤ S := by
      have := Finset.sum_range_reflect (fun m => secWeight k m ℓ * I m) (j + 1)
      simp only [Nat.add_sub_cancel] at this
      rw [this]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
        fun m _ _ => hwI m
    have hC : ∀ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (secWeight k j ℓ * I (j - i)) ≤
        2 ^ j * (secWeight k (j - i) ℓ * I (j - i)) := by
      intro i hi
      have hi' : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      have hc : (j.choose i : ℝ) ≤ 2 ^ j := by exact_mod_cast Nat.choose_le_two_pow j i
      have hw' : secWeight k j ℓ * I (j - i) ≤ secWeight k (j - i) ℓ * I (j - i) :=
        mul_le_mul_of_nonneg_right (hw i hi') (hI _)
      exact mul_le_mul hc hw' (mul_nonneg (secWeight_nonneg _ _ _) (hI _)) (by positivity)
    have hM2 : 0 ≤ M ^ 2 * 2 ^ j := by positivity
    calc secWeight k j ℓ * J j
        ≤ secWeight k j ℓ *
            (M ^ 2 * 2 ^ j * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * I (j - i)) :=
          mul_le_mul_of_nonneg_left (hJ j hj) (secWeight_nonneg _ _ _)
      _ = M ^ 2 * 2 ^ j *
            ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (secWeight k j ℓ * I (j - i)) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
      _ ≤ M ^ 2 * 2 ^ j *
            ∑ i ∈ Finset.range (j + 1), 2 ^ j * (secWeight k (j - i) ℓ * I (j - i)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hC) hM2
      _ = M ^ 2 * 4 ^ j *
            ∑ i ∈ Finset.range (j + 1), secWeight k (j - i) ℓ * I (j - i) := by
          rw [← Finset.mul_sum]
          have : (4 : ℝ) ^ j = 2 ^ j * 2 ^ j := by
            rw [← mul_pow]; norm_num
          rw [this]
          ring
      _ ≤ M ^ 2 * 4 ^ j * S := mul_le_mul_of_nonneg_left hsub (by positivity)
  calc ∑ j ∈ Finset.range (k + 1), secWeight k j ℓ * J j
      ≤ ∑ j ∈ Finset.range (k + 1), M ^ 2 * 4 ^ j * S :=
        Finset.sum_le_sum fun j hj => hterm j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
    _ = M ^ 2 * S * ∑ j ∈ Finset.range (k + 1), (4 : ℝ) ^ j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ ≤ M ^ 2 * S * 4 ^ (k + 1) :=
        mul_le_mul_of_nonneg_left (sum_four_pow_le k) (by positivity)
    _ = 4 ^ (k + 1) * M ^ 2 * S := by ring

end NonUniqueEuler.Sob.MultAux
