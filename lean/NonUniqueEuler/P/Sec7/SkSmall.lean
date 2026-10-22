import NonUniqueEuler.Defs.Sec7.All

/-!
# Proof: `eq:sk-small` (elementary bounds on the ratios `s_k` and radii `r_k`)

Proof of `I/Sec7/SkSmall.lean` (`07_several_rings.tex:17-25`). Uses only `a < 1` (proved
here from the explicit values of `ξL`, `ξR`; the same fact as the last conjunct of
`ringData_order`), the parameter ranges `DatumParams` (part of `P.Valid`) and the closed forms
`ratio`, `radius`. No interface file is used.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Rings

open RingData Datum

/-- `a = e^{ξL - ξR} < 1`, from the explicit values `ξL < 0 < ξR`. -/
private lemma a_lt_one' : a < 1 := by
  unfold a
  rw [Real.exp_lt_one_iff]
  norm_num [ξL, ξR]

/-- `s_j ≤ s̄` for every `j` (since `(2μ)^j ≥ 1`). -/
private lemma ratio_le_sbar {sbar μ : ℝ} (hs : 0 < sbar) (hμ : 1 < μ) (j : ℕ) :
    ratio sbar μ j ≤ sbar := by
  unfold ratio
  have h1 : (1 : ℝ) ≤ (2 * μ) ^ j := one_le_pow₀ (by linarith)
  exact div_le_self hs.le h1

/-- `s_k ≤ s̄/2` for `k ≥ 1` (since `(2μ)^k ≥ 2μ ≥ 2`). -/
private lemma ratio_le_half {sbar μ : ℝ} (hs : 0 < sbar) (hμ : 1 < μ) {k : ℕ} (hk : 1 ≤ k) :
    ratio sbar μ k ≤ sbar / 2 := by
  unfold ratio
  have h2μ : (1 : ℝ) ≤ 2 * μ := by linarith
  have h1 : 2 * μ ≤ (2 * μ) ^ k := by
    calc 2 * μ = (2 * μ) ^ 1 := (pow_one _).symm
      _ ≤ (2 * μ) ^ k := pow_le_pow_right₀ h2μ hk
  have h2 : (2 : ℝ) ≤ (2 * μ) ^ k := by linarith
  exact div_le_div_of_nonneg_left hs.le (by norm_num) h2

/-- `r_k / r_i = ∏_{j ∈ [i,k)} s_j` for `1 ≤ i ≤ k`. -/
private lemma radius_div {sbar μ : ℝ} (hs : 0 < sbar) (hμ : 0 < μ) {i k : ℕ} (hi : 1 ≤ i)
    (hik : i ≤ k) :
    radius sbar μ k / radius sbar μ i = ∏ j ∈ Finset.Ico i k, ratio sbar μ j := by
  have hpos : 0 < radius sbar μ i := radius_pos hs hμ i
  rw [div_eq_iff hpos.ne', radius, radius, ← Finset.prod_Ico_consecutive _ hi hik, mul_comm]

/-- **`eq:sk-small`** (`07_several_rings.tex:17-25`). For a valid approximation `P`
(`μ ∈ (1,2]`, `s̄ ∈ (0,a/16]`): `0 < s_k ≤ s̄/2 ≤ a/32` for `k ≥ 1`;
`r_k/r_i ≤ s_{k-1} s̄^{k-i-1}` for `1 ≤ i < k`; `μ⁴ s̄² < 1/8`; and `s̄^{m-2} < 1/2` (`m = 3`). -/
theorem sk_small (P : Approx) (hP : P.Valid) :
    (∀ k : ℕ, 1 ≤ k → 0 < P.s k ∧ P.s k ≤ P.sbar / 2 ∧ P.s k ≤ a / 32) ∧
    (∀ i k : ℕ, 1 ≤ i → i < k → P.r k / P.r i ≤ P.s (k - 1) * P.sbar ^ (k - i - 1)) ∧
    P.μ ^ 4 * P.sbar ^ 2 < 1 / 8 ∧
    P.sbar ^ (3 - 2) < 1 / 2 := by
  have hD := hP.datumParams
  have hs : 0 < P.sbar := hD.sbar_pos
  have hsle : P.sbar ≤ a / 16 := hD.sbar_le
  have hμ1 : 1 < P.μ := hD.one_lt_μ
  have hμ2 : P.μ ≤ 2 := hD.μ_le_two
  have hμ : 0 < P.μ := by linarith
  have ha1 : a < 1 := a_lt_one'
  have hs16 : P.sbar < 1 / 16 := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk
    refine ⟨ratio_pos hs hμ k, ratio_le_half hs hμ1 hk, ?_⟩
    have := ratio_le_half hs hμ1 hk
    rw [Approx.s_def]
    linarith
  · intro i k hi hik
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have him : i ≤ m := by omega
    rw [Approx.r_def, Approx.r_def, radius_div hs hμ hi (by omega),
      Finset.prod_Ico_succ_top him, Approx.s_def, Nat.add_sub_cancel, mul_comm]
    have hprod : ∏ j ∈ Finset.Ico i m, ratio P.sbar P.μ j ≤ P.sbar ^ (m + 1 - i - 1) := by
      have hcard : m + 1 - i - 1 = (Finset.Ico i m).card := by
        rw [Nat.card_Ico]; omega
      rw [hcard, ← Finset.prod_const]
      exact Finset.prod_le_prod (fun j _ => (ratio_pos hs hμ j).le)
        (fun j _ => ratio_le_sbar hs hμ1 j)
    exact mul_le_mul_of_nonneg_left hprod (ratio_pos hs hμ m).le
  · have hμ4 : P.μ ^ 4 ≤ 16 := by
      calc P.μ ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ hμ.le hμ2 4
        _ = 16 := by norm_num
    have hs2 : P.sbar ^ 2 < 1 / 256 := by
      calc P.sbar ^ 2 < (1 / 16) ^ 2 := pow_lt_pow_left₀ hs16 hs.le (by norm_num)
        _ = 1 / 256 := by norm_num
    have hs2nn : 0 ≤ P.sbar ^ 2 := by positivity
    calc P.μ ^ 4 * P.sbar ^ 2 ≤ 16 * P.sbar ^ 2 := mul_le_mul_of_nonneg_right hμ4 hs2nn
      _ < 16 * (1 / 256) := by linarith
      _ < 1 / 8 := by norm_num
  · norm_num
    linarith

end Rings

end NonUniqueEuler
