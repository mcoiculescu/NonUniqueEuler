import NonUniqueEuler.Defs.SmoothB.Iteration
import Mathlib.Data.Nat.Factorial.Basic
import NonUniqueEuler.H.SmoothB.IterCauchy.Induction

/-!
# Proof of `lem:iter-cauchy` (the iterates are Cauchy in `L²`)

Proof of `I/SmoothB/IterCauchy.lean` (`B_global_smooth.tex:353-379`). The steps are in the
helpers `H/SmoothB/IterCauchy/*`:
* `Basic`: support, smoothness and integrability of the iterates (`lem:iterates`), linearity of
  the Biot–Savart integral;
* `Calculus`: the transport term `∫ g (v·∇g) = 0` for `div v = 0`, differentiation of
  `∫ F(t,x)² dx`, `‖g‖²_{L²} = ∫ g²`;
* `Step`: `d/dt e_{j+1}² = -2 ∫ δ (K ∗ (ω^{[j]} - ω^{[j-1]}))·∇ω^{[j]}` and
  `|d/dt e_{j+1}²| ≤ 4RΨ e_j e_{j+1}` (`lem:iter-lip`, `lem:BS-basic`(c) with `ρ = R`);
* `Comparison`: the manuscript's `(e² + ε)^{1/2}`, `ε → 0` argument;
* `Induction`: the induction on `j`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace NonUniqueEuler.Smooth

variable {ω₀ : ℂ → ℝ} {R₀ : ℝ}

/-- `lem:iter-cauchy` (in `ℝ≥0∞`): for `T > 0`, `j ≥ 1` and `t ∈ [-T, T]`,
`‖ω^{[j]}(t) - ω^{[j-1]}(t)‖_{L²} ≤ 2‖ω₀‖_{L²} (2R(T)Ψ(T)|t|)^{j-1}/(j-1)!`. -/
theorem iter_cauchy (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) {T : ℝ} (hT : 0 < T) {j : ℕ}
    (hj : 1 ≤ j) {t : ℝ} (ht : t ∈ Icc (-T) T) :
    eLpNorm (iter ω₀ j t - iter ω₀ (j - 1) t) 2 volume ≤
      ENNReal.ofReal (2 * (eLpNorm ω₀ 2 volume).toReal *
        (2 * suppRadius ω₀ R₀ T * Psi ω₀ T * |t|) ^ (j - 1) / ((j - 1).factorial : ℝ)) := by
  have _hT := hT
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hm : MemLp (iter ω₀ (k + 1) t - iter ω₀ (k + 1 - 1) t) 2 volume :=
    (IterCauchyAux.iter_memLp h hne (k + 1) t 2).sub (IterCauchyAux.iter_memLp h hne k t 2)
  rw [← ENNReal.ofReal_toReal hm.eLpNorm_ne_top]
  exact ENNReal.ofReal_le_ofReal (IterCauchyAux.iterErr_succ_le h hne k t ht)

/-- `lem:iter-cauchy` as stated in the manuscript, with `e_j(t) = iterErr ω₀ j t`. -/
theorem iterErr_le (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) {T : ℝ} (hT : 0 < T) {j : ℕ}
    (hj : 1 ≤ j) {t : ℝ} (ht : t ∈ Icc (-T) T) :
    iterErr ω₀ j t ≤
      2 * (eLpNorm ω₀ 2 volume).toReal *
        (2 * suppRadius ω₀ R₀ T * Psi ω₀ T * |t|) ^ (j - 1) / ((j - 1).factorial : ℝ) := by
  have _hT := hT
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  exact IterCauchyAux.iterErr_succ_le h hne k t ht

end NonUniqueEuler.Smooth
