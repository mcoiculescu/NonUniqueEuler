import NonUniqueEuler.Defs.Verify.SemOps
import NonUniqueEuler.Statement.Ring
import Mathlib.Analysis.Complex.Exponential

/-!
# Containment (CP) of the elementary functions `exp`, `H`, `UB.expUp`

Code: `NonUniqueEuler/Verify/Comp/Elem.lean`.

* `Ball.mem_expPoint : Real.exp x.toReal ∈ Ball.expPoint p x`;
* `Ball.mem_exp : x ∈ X → Real.exp x ∈ Ball.exp p X`;
* `Ball.mem_H : x ∈ X → RingData.H x ∈ Ball.H p X` (`H x = (1 + e^{-2x})⁻¹`);
* `UB.bounds_expUp : x ≤ᵤ U → Real.exp x ≤ᵤ U.expUp`.

The Taylor remainder is `Real.exp_bound` (`|e^r - Σ_{i<n} r^i/i!| ≤ |r|^n (n+1)/(n! n)` for
`|r| ≤ 1`), bounded by `2^(-10 n)` since `|r| < 2^(-10)` and `n ≥ 2`; the squaring step is
`Real.exp_nat_mul`.
-/

noncomputable section

namespace NonUniqueEuler.Verify

open Finset

namespace Ball

theorem mem_expTaylorAux (w : ℕ) (r : Dy) (k : ℕ) :
    ∀ (m : ℕ) (t s : Ball), r.toReal ^ m / m.factorial ∈ t →
      ∑ i ∈ range (m + 1), r.toReal ^ i / i.factorial ∈ s →
      ∑ i ∈ range (m + k + 1), r.toReal ^ i / i.factorial ∈ expTaylorAux w r k m t s := by
  induction k with
  | zero => intro m t s _ hs; simp only [expTaylorAux, add_zero]; exact hs
  | succ k ih =>
    intro m t s ht hs
    have ht' : r.toReal ^ (m + 1) / (m + 1).factorial ∈ divNat w (mulDy w r t) (m + 1) := by
      have h := mem_divNat (p := w) (mem_mulDy (p := w) (c := r) ht) (m + 1)
      convert h using 1
      rw [Nat.factorial_succ]; push_cast; field_simp; ring
    have hs' : ∑ i ∈ range (m + 1 + 1), r.toReal ^ i / i.factorial ∈
        add w s (divNat w (mulDy w r t) (m + 1)) := by
      rw [sum_range_succ]; exact mem_add hs ht'
    have h := ih (m + 1) _ _ ht' hs'
    rw [show m + (k + 1) + 1 = m + 1 + k + 1 by omega]
    exact h

theorem mem_expTaylor (w : ℕ) (r : Dy) (n : ℕ) :
    ∑ i ∈ range n, r.toReal ^ i / i.factorial ∈ expTaylor w r n := by
  cases n with
  | zero => simp [expTaylor]
  | succ n =>
    have h := mem_expTaylorAux w r n 0 one one (by simp) (by simp)
    simpa [expTaylor] using h

theorem mem_sqrIter (w : ℕ) : ∀ (j : ℕ) {b : Ball} {y : ℝ}, y ∈ b → y ^ (2 ^ j) ∈ sqrIter w j b
  | 0, b, y, hy => by simpa [sqrIter] using hy
  | j + 1, b, y, hy => by
    have h := mem_sqrIter w j (mem_sqr (p := w) hy)
    rw [show y ^ 2 ^ (j + 1) = (y * y) ^ 2 ^ j by rw [pow_succ', pow_mul, sq]]
    exact h

/-- `(n + 1) / (n! · n) ≤ 1` for `n ≥ 2`. -/
theorem exp_bound_coeff_le_one {n : ℕ} (hn : 2 ≤ n) :
    ((n.succ : ℝ) / (n.factorial * n)) ≤ 1 := by
  have h1 : n ≤ n.factorial := Nat.self_le_factorial n
  have h2 : n.succ ≤ n.factorial * n := by
    have : n * n ≤ n.factorial * n := Nat.mul_le_mul_right n h1
    simp only [Nat.succ_eq_add_one]; nlinarith
  have hpos : (0 : ℝ) < n.factorial * n := by positivity
  rw [div_le_one hpos]; exact_mod_cast h2

theorem mem_expPoint (p : ℕ) (x : Dy) : Real.exp x.toReal ∈ expPoint p x := by
  unfold expPoint
  dsimp only
  split
  · exact mem_top _
  · rename_i hj
    generalize hjdef : (x.exp + (bitLen x.man.natAbs : ℤ) + 10).toNat = j at hj
    -- the reduced argument `ρ = x / 2^j`
    set ρ : ℝ := (⟨x.man, x.exp - (j : ℤ)⟩ : Dy).toReal with hρ
    have hjge : x.exp + (bitLen x.man.natAbs : ℤ) + 10 ≤ j := by
      rw [← hjdef]; exact Int.self_le_toNat _
    have hρlt : |ρ| ≤ 2 ^ (-10 : ℤ) := by
      have hb : (x.man.natAbs : ℝ) < 2 ^ bitLen x.man.natAbs := by
        exact_mod_cast lt_two_pow_bitLen _
      have h1 : |ρ| = (x.man.natAbs : ℝ) * 2 ^ (x.exp - (j : ℤ)) := by
        rw [hρ, Dy.toReal_mk, abs_mul, abs_of_pos (two_zpow_pos _), Nat.cast_natAbs, Int.cast_abs]
      have h2 : (2 : ℝ) ^ bitLen x.man.natAbs * 2 ^ (x.exp - (j : ℤ)) ≤ 2 ^ (-10 : ℤ) := by
        rw [← two_zpow_natCast, ← two_zpow_add]
        exact zpow_le_zpow_right₀ (by norm_num) (by omega)
      rw [h1]
      nlinarith [two_zpow_pos (x.exp - (j : ℤ))]
    have hρ1 : |ρ| ≤ 1 := hρlt.trans (by norm_num)
    generalize hw : p + j + 10 = w
    generalize hn : w / 10 + 2 = n
    have hn2 : 2 ≤ n := by omega
    -- Taylor enclosure of `exp ρ`
    have hT := mem_expTaylor w ⟨x.man, x.exp - (j : ℤ)⟩ n
    rw [← hρ] at hT
    have hR : |Real.exp ρ - ∑ i ∈ range n, ρ ^ i / i.factorial| ≤ 2 ^ (-10 * (n : ℤ)) := by
      refine (Real.exp_bound hρ1 (by omega)).trans ?_
      have hpow : |ρ| ^ n ≤ 2 ^ (-10 * (n : ℤ)) := by
        calc |ρ| ^ n ≤ ((2 : ℝ) ^ (-10 : ℤ)) ^ n := pow_le_pow_left₀ (abs_nonneg _) hρlt n
          _ = 2 ^ (-10 * (n : ℤ)) := by rw [← zpow_natCast, ← zpow_mul]
      calc |ρ| ^ n * ((n.succ : ℝ) / (n.factorial * n)) ≤ |ρ| ^ n * 1 :=
            mul_le_mul_of_nonneg_left (exp_bound_coeff_le_one hn2) (by positivity)
        _ ≤ _ := by rw [mul_one]; exact hpow
    have hE : Real.exp ρ ∈ addErr (expTaylor w ⟨x.man, x.exp - (j : ℤ)⟩ n)
        (UB.pow2 (-10 * (n : ℤ))) := by
      exact mem_addErr hT (UB.bounds_pow2.2 hR)
    -- squaring `j` times
    have hS := mem_sqrIter w j hE
    have hexp : Real.exp ρ ^ (2 ^ j) = Real.exp x.toReal := by
      rw [← Real.exp_nat_mul]; congr 1
      rw [hρ, Dy.toReal_mk, Dy.toReal]; push_cast
      rw [show x.exp = (x.exp - (j : ℤ)) + (j : ℤ) by ring, two_zpow_add, two_zpow_natCast]
      ring_nf
    rw [hexp] at hS
    exact mem_round hS

theorem mem_exp (p : ℕ) {X : Ball} {x : ℝ} (hx : x ∈ X) : Real.exp x ∈ exp p X := by
  unfold exp
  split
  · exact mem_top _
  · rename_i m e hr
    have hx' : |x - X.mid.toReal| ≤ (m : ℝ) * 2 ^ e := by rw [mem_def, hr] at hx; exact hx
    split
    · rename_i hm
      subst hm
      have : x = X.mid.toReal := by
        have := abs_nonneg (x - X.mid.toReal); simp at hx'; linarith
      rw [this]; exact mem_expPoint p X.mid
    · dsimp only
      split
      · rename_i a b ha hb
        have h1 := neg_abs_le (x - X.mid.toReal)
        have h2 := le_abs_self (x - X.mid.toReal)
        have hlo : (X.mid.sub ⟨(m : ℤ), e⟩).toReal ≤ x := by
          simp only [Dy.toReal_sub, Dy.toReal_mk, Int.cast_natCast]; linarith
        have hhi : x ≤ (X.mid.add ⟨(m : ℤ), e⟩).toReal := by
          simp only [Dy.toReal_add, Dy.toReal_mk, Int.cast_natCast]; linarith
        apply mem_ofInterval
        · exact (lower?_le ha (mem_expPoint p _)).trans (Real.exp_le_exp.2 hlo)
        · exact (Real.exp_le_exp.2 hhi).trans (le_upper? hb (mem_expPoint p _))
      · exact mem_top _

theorem mem_H (p : ℕ) {X : Ball} {x : ℝ} (hx : x ∈ X) : RingData.H x ∈ H p X := by
  have h1 := mem_neg (mem_scale2 hx 1)
  have h2 := mem_exp p h1
  have h3 := mem_add (p := p) mem_one h2
  have h4 := mem_inv (p := p) h3
  unfold RingData.H
  rw [show -2 * x = -(x * 2 ^ (1 : ℤ)) by rw [zpow_one]; ring]
  exact h4

end Ball

namespace UB

theorem bounds_expUp {U : UB} {x : ℝ} (hx : x ≤ᵤ U) : Real.exp x ≤ᵤ U.expUp := by
  cases U with
  | inf => trivial
  | fin m e =>
    have h := Ball.le_upperUB (Ball.mem_expPoint (radPrec + 10) ⟨(m : ℤ), e⟩)
    refine Bounds.mono (Real.exp_le_exp.2 ?_) h
    simpa [Dy.toReal] using hx

end UB

end NonUniqueEuler.Verify
