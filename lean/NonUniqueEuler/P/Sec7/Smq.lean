import NonUniqueEuler.Defs.Sec7.Transfer
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Proof: `eq:Smi` (the series `S_{m,q}` is finite)

Proof of `I/Sec7/Smq.lean` (`07_several_rings.tex:67-71`). Same declarations, statements copied
verbatim.

**Proof.** Write `x = 2^{-m} ∈ (0, 1)` and `a_p = ((p+1)m+q)^q`, so the `p`-th term is
`a_p x^p` (`2^{-pm} = (2^{-m})^p`). Since `(p+1)m + q ≤ (m+q)(p+1)`,
`a_p x^p ≤ (m+q)^q x⁻¹ (p+1)^q x^{p+1}`, and `Σ n^q x^n < ∞`
(`summable_pow_mul_geometric_of_norm_lt_one`), shifted by one (`summable_nat_add_iff`). The
`p = 0` term is `(m+q)^q > 0` and all terms are `≥ 0`, so `S_{m,q} > 0` (`Summable.tsum_pos`).
For `0 ≤ ρ ≤ 1/2`, `0 ≤ ρ^{pm} ≤ 2^{-pm}`; comparison (`Summable.of_nonneg_of_le`,
`Summable.tsum_le_tsum`).
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Rings

/-- The term bound `((p+1)m + q)^q ≤ (m+q)^q (p+1)^q`. -/
private lemma smq_term_le (m q p : ℕ) :
    ((((p + 1) * m + q : ℕ) : ℝ)) ^ q ≤ (((m + q : ℕ) : ℝ)) ^ q * (((p + 1 : ℕ) : ℝ)) ^ q := by
  rw [← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  have h : (p + 1) * m + q ≤ (m + q) * (p + 1) := by nlinarith
  exact_mod_cast h

/-- Summability of the base series `Σ_p ((p+1)m+q)^q 2^{-pm}`. -/
private lemma smq_summable_base {m : ℕ} (hm : 1 ≤ m) (q : ℕ) :
    Summable (fun p : ℕ => ((((p + 1) * m + q : ℕ) : ℝ)) ^ q * ((2 : ℝ)⁻¹) ^ (p * m)) := by
  set x : ℝ := ((2 : ℝ)⁻¹) ^ m with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hg : Summable (fun n : ℕ => ((n : ℝ)) ^ q * x ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one q (by rw [Real.norm_eq_abs, abs_of_pos hx0]; exact hx1)
  have hg1 : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ q * x ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr hg
  have hmaj : Summable (fun n : ℕ =>
      ((((m + q : ℕ) : ℝ)) ^ q * x⁻¹) * ((((n + 1 : ℕ) : ℝ)) ^ q * x ^ (n + 1))) :=
    hg1.mul_left _
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) hmaj
  have hpow : ((2 : ℝ)⁻¹) ^ (p * m) = x ^ p := by rw [hx, ← pow_mul, mul_comm]
  rw [hpow]
  have hxp : x⁻¹ * x ^ (p + 1) = x ^ p := by
    rw [pow_succ]; field_simp
  calc ((((p + 1) * m + q : ℕ) : ℝ)) ^ q * x ^ p
      ≤ ((((m + q : ℕ) : ℝ)) ^ q * (((p + 1 : ℕ) : ℝ)) ^ q) * x ^ p :=
        mul_le_mul_of_nonneg_right (smq_term_le m q p) (by positivity)
    _ = ((((m + q : ℕ) : ℝ)) ^ q * x⁻¹) * ((((p + 1 : ℕ) : ℝ)) ^ q * x ^ (p + 1)) := by
        rw [← hxp]; ring

/-- **`eq:Smi`** (`07_several_rings.tex:67-71`). For `m ≥ 1`, `q ≥ 0`: the series
`S_{m,q} = Σ_{p≥1} (pm+q)^q 2^{-(p-1)m}` converges, `S_{m,q} > 0`, and for `0 ≤ ρ ≤ 1/2`,
`Σ_{p≥1} (pm+q)^q ρ^{(p-1)m}` converges and is at most `S_{m,q}`. -/
theorem smq_summable {m : ℕ} (hm : 1 ≤ m) (q : ℕ) :
    Summable (fun p : ℕ => ((((p + 1) * m + q : ℕ) : ℝ)) ^ q * ((2 : ℝ)⁻¹) ^ (p * m)) ∧
    0 < Smq m q ∧
    ∀ ρ ∈ Icc (0 : ℝ) (1 / 2),
      Summable (fun p : ℕ => ((((p + 1) * m + q : ℕ) : ℝ)) ^ q * ρ ^ (p * m)) ∧
      ∑' p : ℕ, ((((p + 1) * m + q : ℕ) : ℝ)) ^ q * ρ ^ (p * m) ≤ Smq m q := by
  have hS := smq_summable_base hm q
  refine ⟨hS, ?_, ?_⟩
  · unfold Smq
    refine hS.tsum_pos (fun p => by positivity) 0 ?_
    have hmq : (0 : ℝ) < (((0 + 1) * m + q : ℕ) : ℝ) := by
      have : 0 < (0 + 1) * m + q := by omega
      exact_mod_cast this
    simpa using pow_pos hmq q
  · rintro ρ ⟨hρ0, hρ1⟩
    have hle : ∀ p : ℕ, ((((p + 1) * m + q : ℕ) : ℝ)) ^ q * ρ ^ (p * m) ≤
        ((((p + 1) * m + q : ℕ) : ℝ)) ^ q * ((2 : ℝ)⁻¹) ^ (p * m) := fun p =>
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ0 (by linarith) _) (by positivity)
    have hρS : Summable (fun p : ℕ => ((((p + 1) * m + q : ℕ) : ℝ)) ^ q * ρ ^ (p * m)) :=
      Summable.of_nonneg_of_le (fun p => by positivity) hle hS
    exact ⟨hρS, hρS.tsum_le_tsum hle hS⟩

end Rings

end NonUniqueEuler
