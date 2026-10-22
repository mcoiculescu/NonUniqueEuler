import Mathlib.Data.Real.ConjExponents
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Helpers for `lem:velocity`: the exponents `r_p`, `s_p`

Helper file of `P/Sec2/Velocity.lean` (namespace `NonUniqueEuler.BS.VelH`):
`02_prelim.tex:324-327`, `r_p = p'`, `s_p = p/(2p-2)` for `p ≤ 2`, `r_p = p`, `s_p = 1` for `p > 2`.
-/

namespace NonUniqueEuler.BS

namespace VelH

/-- The exponents of the proof of `lem:velocity`(a): `r = r_p`, `s = s_p` with
`1 ≤ s < 2`, `1/s + 1/p = 1 + 1/r`, `r ≥ max(2, p')`, and `r' ≤ p`. -/
theorem exists_exponents {p : ℝ} (hp : 4 / 3 < p) :
    ∃ r s : ℝ, 1 ≤ s ∧ s < 2 ∧ 1 / s + 1 / p = 1 + 1 / r ∧ 2 ≤ r ∧ p.conjExponent ≤ r ∧
      1 < r ∧ r.conjExponent ≤ p := by
  have hp1 : 0 < p - 1 := by linarith
  have hp0 : p ≠ 0 := by linarith
  rcases le_or_gt p 2 with h2 | h2
  · have h22 : 0 < 2 * p - 2 := by linarith
    refine ⟨p / (p - 1), p / (2 * p - 2), ?_, ?_, ?_, ?_, le_rfl, ?_, ?_⟩
    · rw [le_div_iff₀ h22]; linarith
    · rw [div_lt_iff₀ h22]; linarith
    · field_simp
      ring
    · rw [le_div_iff₀ hp1]; linarith
    · rw [lt_div_iff₀ hp1]; linarith
    · have h : p / (p - 1) - 1 = 1 / (p - 1) := by field_simp; ring
      unfold Real.conjExponent
      rw [h]
      field_simp
      rfl
  · refine ⟨p, 1, le_rfl, by norm_num, by ring, h2.le, ?_, by linarith, ?_⟩
    · unfold Real.conjExponent
      rw [div_le_iff₀ hp1]; nlinarith
    · unfold Real.conjExponent
      rw [div_le_iff₀ hp1]; nlinarith

theorem conjExponent_two : (2 : ℝ).conjExponent = 2 := by
  norm_num [Real.conjExponent]

theorem one_le_conjExponent {p : ℝ} (hp : 1 < p) : 1 ≤ p.conjExponent := by
  unfold Real.conjExponent
  rw [le_div_iff₀ (by linarith)]; linarith

end VelH

end NonUniqueEuler.BS
