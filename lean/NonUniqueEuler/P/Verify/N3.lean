import NonUniqueEuler.Statement.Evans
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Proof: (N3) holds

Proof of `NonUniqueEuler/I/Verify/N3.lean`: `prop:N3` (`A_verification.tex:654-683`,
Proposition A.8). We follow the manuscript proof.

* `εstar < 10⁻²¹`: `H x ≤ e^{2x}`, both arguments of `H` in `ε_*` are `< -49/2`, and
  `e^{49} > 2.7^{49} > 10^{21}` (`Real.exp_one_gt_d9`).
* `e^{a₀} < 0.66672`: `a₀ < -0.4054` and `∑_{k ≤ 5} 0.4054^k / k! > 1.49989`
  (`Real.sum_le_exp_of_nonneg`); hence `e^{6a₀} < 0.087834`, `e^{9a₀} < 0.026032`.
* `Θ_ℓ ≤ (1 - U²/6)⁻¹` whenever `π ℓ d ≤ U` and `U² < 6`, from `sin u ≥ u - u³/6`
  (`Real.sin_ge_sub_cube`); with `π < 3.1416` (`Real.pi_lt_d4`) and `d < 0.0200001` we take
  `U = 0.377` for `ℓ = 6` and `U = 0.5655` for `ℓ = 9`, giving `Θ_6 < 1.024264` and
  `Θ_9 < 1.0564`.

The helper lemmas live in the namespace `NonUniqueEuler.N3Proof`.
-/

namespace NonUniqueEuler

open RingData

namespace N3Proof

/-- `H(x) ≤ e^{2x}`. -/
lemma H_le_exp (x : ℝ) : H x ≤ Real.exp (2 * x) := by
  unfold H
  have h0 : 0 < Real.exp (-2 * x) := Real.exp_pos _
  calc (1 + Real.exp (-2 * x))⁻¹ ≤ (Real.exp (-2 * x))⁻¹ := inv_anti₀ h0 (by linarith)
    _ = Real.exp (2 * x) := by rw [← Real.exp_neg]; ring_nf

/-- `e^{-49} < 10⁻²¹`, from `e > 2.7` and `2.7^{49} > 10^{21}`. -/
lemma exp_neg_49_lt : Real.exp (-49) < 1 / 10 ^ 21 := by
  have he : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h49 : (2.7 : ℝ) ^ 49 < Real.exp 1 ^ 49 :=
    pow_lt_pow_left₀ he (by norm_num) (by norm_num)
  have hexp : Real.exp 49 = Real.exp 1 ^ 49 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hbig : (10 : ℝ) ^ 21 < Real.exp 49 := by
    rw [hexp]; exact lt_trans (by norm_num) h49
  rw [Real.exp_neg, one_div]
  exact (inv_lt_inv₀ (Real.exp_pos _) (by norm_num)).2 hbig

/-- `ε_* < 10⁻²¹` (first claim of `prop:N3`). -/
lemma εstar_lt : εstar < 1 / 10 ^ 21 := by
  have hxa : 2 * ((ξa - a₀) / d) ≤ -49 := by norm_num [ξa, a₀, d]
  have hyb : 2 * (-ξb / d) ≤ -49 := by norm_num [ξb, d]
  have h1 : H ((ξa - a₀) / d) ≤ Real.exp (-49) :=
    (H_le_exp _).trans (Real.exp_le_exp.2 hxa)
  have h2 : H (-ξb / d) ≤ Real.exp (-49) :=
    (H_le_exp _).trans (Real.exp_le_exp.2 hyb)
  exact lt_of_le_of_lt (max_le h1 h2) exp_neg_49_lt

/-- `e^{a₀} < 0.66672`. -/
lemma exp_a₀_lt : Real.exp a₀ < 0.66672 := by
  have hS : (1.49989 : ℝ) < Real.exp 0.4054 := by
    have h := Real.sum_le_exp_of_nonneg (x := (0.4054 : ℝ)) (by norm_num) 6
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith
  calc Real.exp a₀ < Real.exp (-0.4054) := Real.exp_lt_exp.2 (by norm_num [a₀])
    _ = (Real.exp 0.4054)⁻¹ := Real.exp_neg _
    _ < (1.49989 : ℝ)⁻¹ := (inv_lt_inv₀ (Real.exp_pos _) (by norm_num)).2 hS
    _ < 0.66672 := by norm_num

/-- `e^{6 a₀} < 0.087834`. -/
lemma exp_six_a₀_lt : Real.exp ((6 : ℕ) * a₀) < 0.087834 := by
  rw [Real.exp_nat_mul]
  calc Real.exp a₀ ^ 6 < (0.66672 : ℝ) ^ 6 :=
        pow_lt_pow_left₀ exp_a₀_lt (Real.exp_pos _).le (by norm_num)
    _ < 0.087834 := by norm_num

/-- `e^{9 a₀} < 0.026032`. -/
lemma exp_nine_a₀_lt : Real.exp ((9 : ℕ) * a₀) < 0.026032 := by
  rw [Real.exp_nat_mul]
  calc Real.exp a₀ ^ 9 < (0.66672 : ℝ) ^ 9 :=
        pow_lt_pow_left₀ exp_a₀_lt (Real.exp_pos _).le (by norm_num)
    _ < 0.026032 := by norm_num

/-- For `0 < u ≤ U` with `U² < 6`: `0 < u / sin u ≤ (1 - U²/6)⁻¹`, from
`sin u ≥ u - u³/6`. -/
lemma div_sin_le {u U : ℝ} (hu : 0 < u) (hU : u ≤ U) (hU6 : U ^ 2 < 6) :
    0 < u / Real.sin u ∧ u / Real.sin u ≤ (1 - U ^ 2 / 6)⁻¹ := by
  have hu2 : u ^ 2 ≤ U ^ 2 := pow_le_pow_left₀ hu.le hU 2
  have hpos : 0 < 1 - u ^ 2 / 6 := by linarith
  have hposU : 0 < 1 - U ^ 2 / 6 := by linarith
  have hs : u * (1 - u ^ 2 / 6) ≤ Real.sin u := by
    have h := Real.sin_ge_sub_cube hu.le
    have he : u * (1 - u ^ 2 / 6) = u - u ^ 3 / 6 := by ring
    rw [he]; exact h
  have hs0 : 0 < u * (1 - u ^ 2 / 6) := mul_pos hu hpos
  have hsin : 0 < Real.sin u := lt_of_lt_of_le hs0 hs
  refine ⟨div_pos hu hsin, ?_⟩
  calc u / Real.sin u ≤ u / (u * (1 - u ^ 2 / 6)) := div_le_div_of_nonneg_left hu.le hs0 hs
    _ = (1 - u ^ 2 / 6)⁻¹ := by field_simp
    _ ≤ (1 - U ^ 2 / 6)⁻¹ := inv_anti₀ hposU (by linarith)

lemma d_pos : (0 : ℝ) < d := by norm_num [d]

lemma d_lt : d < (0.0200001 : ℝ) := by norm_num [d]

/-- `0 < Θ_6 < 1.024264`. -/
lemma Θ_six : 0 < Θ 6 ∧ Θ 6 < 1.024264 := by
  have hu : 0 < Real.pi * ((6 : ℕ) : ℝ) * d := by
    have := d_pos; have := Real.pi_pos; push_cast; positivity
  have hU : Real.pi * ((6 : ℕ) : ℝ) * d ≤ 0.377 := by
    have hπ := Real.pi_lt_d4
    have hd := d_lt
    have hd0 := d_pos
    calc Real.pi * ((6 : ℕ) : ℝ) * d ≤ 3.1416 * 6 * 0.0200001 := by
          push_cast; gcongr
      _ ≤ 0.377 := by norm_num
  obtain ⟨h0, h1⟩ := div_sin_le hu hU (by norm_num)
  refine ⟨h0, lt_of_le_of_lt h1 (by norm_num)⟩

/-- `0 < Θ_9 < 1.0564`. -/
lemma Θ_nine : 0 < Θ 9 ∧ Θ 9 < 1.0564 := by
  have hu : 0 < Real.pi * ((9 : ℕ) : ℝ) * d := by
    have := d_pos; have := Real.pi_pos; push_cast; positivity
  have hU : Real.pi * ((9 : ℕ) : ℝ) * d ≤ 0.5655 := by
    have hπ := Real.pi_lt_d4
    have hd := d_lt
    have hd0 := d_pos
    calc Real.pi * ((9 : ℕ) : ℝ) * d ≤ 3.1416 * 9 * 0.0200001 := by
          push_cast; gcongr
      _ ≤ 0.5655 := by norm_num
  obtain ⟨h0, h1⟩ := div_sin_le hu hU (by norm_num)
  refine ⟨h0, lt_of_le_of_lt h1 (by norm_num)⟩

end N3Proof

open N3Proof in
theorem n3_holds : N3 := by
  intro ℓ hℓ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hℓ
  rcases hℓ with rfl | rfl
  · obtain ⟨hΘ0, hΘ⟩ := Θ_six
    have hE := exp_six_a₀_lt
    have hε := εstar_lt
    have hprod : Real.exp ((6 : ℕ) * a₀) * Θ 6 ≤ 0.087834 * 1.024264 :=
      mul_le_mul hE.le hΘ.le hΘ0.le (by norm_num)
    have : (0.087834 : ℝ) * 1.024264 + 1 / 10 ^ 21 < 9 / 100 := by norm_num
    linarith
  · obtain ⟨hΘ0, hΘ⟩ := Θ_nine
    have hE := exp_nine_a₀_lt
    have hε := εstar_lt
    have hprod : Real.exp ((9 : ℕ) * a₀) * Θ 9 ≤ 0.026032 * 1.0564 :=
      mul_le_mul hE.le hΘ.le hΘ0.le (by norm_num)
    have : (0.026032 : ℝ) * 1.0564 + 1 / 10 ^ 21 < 9 / 100 := by norm_num
    linarith

end NonUniqueEuler
