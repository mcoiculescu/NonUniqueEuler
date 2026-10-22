import NonUniqueEuler.Defs.Sec2.Conventions
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Proof: `‖M‖_op ≤ 2 max_{i,l} |M_il|` for real `2 × 2` matrices

Proof of `I/SmoothB/OpNormEntry.lean` (the fact stated in the proofs of `lem:iter-lip`,
`B_global_smooth.tex:273-275`, and `lem:smooth-bounds`, `B_global_smooth.tex:518-520`).

For `v = v₁ + i v₂`, `L v = v₁ L(1) + v₂ L(i)`; each component of `L v` is `v₁ a + v₂ b` with
`|a|, |b| ≤ m`, so its square is at most `(a² + b²)(v₁² + v₂²) ≤ 2m²‖v‖²` (Cauchy–Schwarz,
`OpNormEntryAux.sq_lin_le`). Summing the two components, `‖L v‖² ≤ 4m²‖v‖²`.
-/

noncomputable section

namespace NonUniqueEuler.Smooth

namespace OpNormEntryAux

/-- Cauchy–Schwarz for one row: `(x a + y b)² ≤ 2 m² (x² + y²)` when `|a|, |b| ≤ m`. -/
theorem sq_lin_le {x y a b m : ℝ} (ha : |a| ≤ m) (hb : |b| ≤ m) :
    (x * a + y * b) ^ 2 ≤ 2 * m ^ 2 * (x ^ 2 + y ^ 2) := by
  have ha2 : a ^ 2 ≤ m ^ 2 := by
    rw [← sq_abs a]
    exact pow_le_pow_left₀ (abs_nonneg a) ha 2
  have hb2 : b ^ 2 ≤ m ^ 2 := by
    rw [← sq_abs b]
    exact pow_le_pow_left₀ (abs_nonneg b) hb 2
  have hid : (x * a + y * b) ^ 2 + (x * b - y * a) ^ 2 = (a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2) := by
    ring
  have h1 : (a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2) ≤ 2 * m ^ 2 * (x ^ 2 + y ^ 2) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith
  nlinarith [sq_nonneg (x * b - y * a)]

end OpNormEntryAux

/-- `‖M‖_op ≤ 2 max_{i,l} |M_il|` for a real `2 × 2` matrix `M` (`B_global_smooth.tex:273-275`,
`:518-520`), with any bound `m` of the moduli of the entries. -/
theorem opNorm_le_two_mul_of_entry_le {L : ℂ →L[ℝ] ℂ} {m : ℝ}
    (hL : ∀ i l : Fin 2, |Prelim.comp2 i (L (Prelim.e2 l))| ≤ m) :
    ‖L‖ ≤ 2 * m := by
  have hm : 0 ≤ m := le_trans (abs_nonneg _) (hL 0 0)
  have h00 : |(L 1).re| ≤ m := by simpa using hL 0 0
  have h10 : |(L 1).im| ≤ m := by simpa using hL 1 0
  have h01 : |(L Complex.I).re| ≤ m := by simpa using hL 0 1
  have h11 : |(L Complex.I).im| ≤ m := by simpa using hL 1 1
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
  have hv : v = (v.re : ℝ) • (1 : ℂ) + (v.im : ℝ) • Complex.I := by simp
  have hLv : L v = (v.re : ℝ) • L 1 + (v.im : ℝ) • L Complex.I := by
    conv_lhs => rw [hv]
    rw [map_add, map_smul, map_smul]
  have hre : (L v).re = v.re * (L 1).re + v.im * (L Complex.I).re := by
    rw [hLv]; simp
  have him : (L v).im = v.re * (L 1).im + v.im * (L Complex.I).im := by
    rw [hLv]; simp
  have hsqLv : ‖L v‖ ^ 2 = (L v).re ^ 2 + (L v).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hsqv : ‖v‖ ^ 2 = v.re ^ 2 + v.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hA := OpNormEntryAux.sq_lin_le (x := v.re) (y := v.im) h00 h01
  have hB := OpNormEntryAux.sq_lin_le (x := v.re) (y := v.im) h10 h11
  have hsq : ‖L v‖ ^ 2 ≤ (2 * m * ‖v‖) ^ 2 := by
    rw [hsqLv, hre, him, mul_pow, hsqv]
    nlinarith [hA, hB]
  have hc : 0 ≤ 2 * m * ‖v‖ := by positivity
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hc two_ne_zero).1 hsq

/-- The same bound for the derivative matrix `∇u(x) = (∂_l u_i(x))` of a real vector field:
`‖∇u(x)‖_op ≤ 2 max_{i,l} |∂_l u_i(x)|`. -/
theorem norm_fderiv_le_two_mul_of_gradEntry_le {u : ℂ → ℂ} {x : ℂ} {m : ℝ}
    (hu : ∀ i l : Fin 2, |Prelim.gradEntry u i l x| ≤ m) :
    ‖fderiv ℝ u x‖ ≤ 2 * m :=
  opNorm_le_two_mul_of_entry_le hu

end NonUniqueEuler.Smooth
