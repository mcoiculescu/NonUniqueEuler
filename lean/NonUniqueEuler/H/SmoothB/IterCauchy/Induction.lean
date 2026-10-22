import NonUniqueEuler.H.SmoothB.IterCauchy.Step
import NonUniqueEuler.H.SmoothB.IterCauchy.Comparison
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Helper for `lem:iter-cauchy`: the induction on `j`

`B_global_smooth.tex:362-379`. With `c = 2‖ω₀‖_{L²}` and `K = 2R(T)Ψ(T)`:
* `j = 1`: `e₁(t) ≤ ‖ω^{[1]}(t)‖₂ + ‖ω₀‖₂ = c` (`lem:iterates`(ii));
* `j → j + 1`: `e_{j+1}(0) = 0` and `|d/dt e_{j+1}²| ≤ 2 e_{j+1} · K e_j`; with the induction
  hypothesis `K e_j(τ) ≤ c K^j |τ|^{j-1}/(j-1)! = g'(|τ|)`, `g(s) = c K^j s^j / j!`, the comparison
  lemma (`IterCauchyAux.sqrt_le_sub_of_hasDerivAt`, the manuscript's `ε → 0` argument) gives
  `e_{j+1}(t) ≤ g(|t|)`; negative times by reflection `τ ↦ -τ`.

Fully proved (from the interfaces).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace NonUniqueEuler.Smooth.IterCauchyAux

variable {ω₀ : ℂ → ℝ} {R₀ : ℝ}

/-- `e₁(t) ≤ 2‖ω₀‖_{L²}` (`B_global_smooth.tex:363-364`). -/
theorem eLpNorm_iter_one_sub_le (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (t : ℝ) :
    eLpNorm (iter ω₀ 1 t - iter ω₀ 0 t) 2 volume ≤ 2 * eLpNorm ω₀ 2 volume := by
  have h1 := eLpNorm_sub_le (iter_memLp h hne 1 t 2).aestronglyMeasurable
    (iter_memLp h hne 0 t 2).aestronglyMeasurable (p := 2) (by norm_num)
  rw [iterates_eLpNorm h hne 1 t (by norm_num)] at h1
  have h0 : iter ω₀ 0 t = ω₀ := rfl
  rw [h0] at h1
  rw [two_mul]
  exact h1

/-- `e_{k+2}(0) = 0`, since `ω^{[j]}(0) = ω₀` for every `j ≥ 1` (`lem:iterates`(iv)). -/
theorem iterErr_zero_eq (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (k : ℕ) :
    iterErr ω₀ (k + 2) 0 = 0 := by
  have h2 : iter ω₀ (k + 2) 0 = ω₀ := (iterates_flow h hne (k + 1)).2.2.2.1
  have h1 : iter ω₀ (k + 1) 0 = ω₀ := (iterates_flow h hne k).2.2.2.1
  rw [iterErr_succ, h2, h1, sub_self, eLpNorm_zero, ENNReal.toReal_zero]

/-- The main induction: for `t ∈ [-T, T]`,
`e_{k+1}(t) ≤ 2‖ω₀‖_{L²} (2R(T)Ψ(T)|t|)^k / k!`. -/
theorem iterErr_succ_le (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) {T : ℝ} (k : ℕ) :
    ∀ t ∈ Icc (-T) T, iterErr ω₀ (k + 1) t ≤
      2 * (eLpNorm ω₀ 2 volume).toReal *
        (2 * suppRadius ω₀ R₀ T * Psi ω₀ T * |t|) ^ k / (k.factorial : ℝ) := by
  set c : ℝ := 2 * (eLpNorm ω₀ 2 volume).toReal with hc_def
  set K : ℝ := 2 * suppRadius ω₀ R₀ T * Psi ω₀ T with hK_def
  have hc : 0 ≤ c := mul_nonneg zero_le_two ENNReal.toReal_nonneg
  have hK : 0 ≤ K :=
    mul_nonneg (mul_nonneg zero_le_two (suppRadius_pos h hne T).le) (Psi_nonneg ω₀ T)
  have hfin : eLpNorm ω₀ 2 volume ≠ ∞ := (iter_memLp h hne 0 0 2).eLpNorm_ne_top
  induction k with
  | zero =>
    intro t _
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
    rw [iterErr_succ]
    have := ENNReal.toReal_mono (by finiteness) (eLpNorm_iter_one_sub_le h hne t)
    rw [ENNReal.toReal_mul] at this
    simpa using this
  | succ k ih =>
    -- the energy and its derivative
    set f : ℝ → ℝ := fun τ => iterErr ω₀ (k + 2) τ ^ 2 with hf_def
    set f' : ℝ → ℝ := fun τ => -2 * ∫ x, (iter ω₀ (k + 2) τ x - iter ω₀ (k + 1) τ x) *
        fderiv ℝ (iter ω₀ (k + 1) τ) x (iterVel ω₀ (k + 1) τ x - iterVel ω₀ k τ x)
      with hf'_def
    have hf : ∀ τ, HasDerivAt f (f' τ) τ := fun τ => hasDerivAt_iterErr_sq h hne k τ
    have hfb : ∀ τ ∈ Icc (-T) T, |f' τ| ≤ 2 * Real.sqrt (f τ) * (K * iterErr ω₀ (k + 1) τ) := by
      intro τ hτ
      obtain ⟨D, hD, hDb⟩ := iterErr_sq_deriv_bound h hne k hτ
      rw [← (hf τ).unique hD] at hDb
      simpa [hf_def, hK_def, mul_assoc] using hDb
    -- the comparison function
    set g : ℝ → ℝ := fun s => c * K ^ (k + 1) * s ^ (k + 1) / ((k + 1).factorial : ℝ)
      with hg_def
    set g' : ℝ → ℝ := fun s => c * K ^ (k + 1) * s ^ k / (k.factorial : ℝ) with hg'_def
    have hfact : ((k + 1).factorial : ℝ) = (k + 1 : ℝ) * (k.factorial : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hkpos : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
    have hg : ∀ s, HasDerivAt g (g' s) s := by
      intro s
      have := ((hasDerivAt_pow (k + 1) s).const_mul (c * K ^ (k + 1))).div_const
        ((k + 1).factorial : ℝ)
      refine this.congr_deriv ?_
      rw [hfact, Nat.add_sub_cancel]
      simp only [hg'_def]
      push_cast
      field_simp
    have hg0 : g 0 = 0 := by simp [hg_def]
    -- the comparison on `[0, T]` along `τ ↦ σ τ`, `σ = ±1`
    have key : ∀ σ : ℝ, |σ| = 1 → ∀ s ∈ Icc 0 T,
        iterErr ω₀ (k + 2) (σ * s) ≤ g s := by
      intro σ hσ
      have hσs : ∀ s ∈ Icc 0 T, σ * s ∈ Icc (-T) T := by
        intro s hs
        rw [mem_Icc, ← abs_le, abs_mul, hσ, one_mul, abs_of_nonneg hs.1]
        exact hs.2
      have habs : ∀ s ∈ Icc 0 T, |σ * s| = s := by
        intro s hs
        rw [abs_mul, hσ, one_mul, abs_of_nonneg hs.1]
      have hfσ : ∀ s ∈ Icc 0 T, HasDerivAt (fun s => f (σ * s)) (f' (σ * s) * σ) s := by
        intro s _
        have h1 : HasDerivAt (fun s : ℝ => σ * s) σ s := by
          simpa using (hasDerivAt_id s).const_mul σ
        exact (hf (σ * s)).comp s h1
      have hf0 : f (σ * 0) = 0 := by
        simp only [hf_def, mul_zero, iterErr_zero_eq h hne k]
        norm_num
      have hfnn : ∀ s ∈ Icc 0 T, 0 ≤ f (σ * s) := fun s _ => sq_nonneg _
      have hg'nn : ∀ s ∈ Icc 0 T, 0 ≤ g' s := by
        intro s hs
        have := hs.1
        simp only [hg'_def]
        positivity
      have hbound : ∀ s ∈ Icc 0 T, |f' (σ * s) * σ| ≤ 2 * Real.sqrt (f (σ * s)) * g' s := by
        intro s hs
        rw [abs_mul, hσ, mul_one]
        refine (hfb (σ * s) (hσs s hs)).trans ?_
        have hih := ih (σ * s) (hσs s hs)
        rw [habs s hs] at hih
        have hle : K * iterErr ω₀ (k + 1) (σ * s) ≤ g' s := by
          calc K * iterErr ω₀ (k + 1) (σ * s) ≤ K * (c * (K * s) ^ k / (k.factorial : ℝ)) :=
                mul_le_mul_of_nonneg_left hih hK
            _ = g' s := by
              simp only [hg'_def]
              rw [mul_pow]
              ring
        exact mul_le_mul_of_nonneg_left hle (by positivity)
      intro s hs
      have := sqrt_le_sub_of_hasDerivAt (f := fun s => f (σ * s)) hfσ hf0 hfnn
        (fun s _ => hg s) hg'nn hbound s hs
      rw [hg0, sub_zero] at this
      have hnn : 0 ≤ iterErr ω₀ (k + 2) (σ * s) := ENNReal.toReal_nonneg
      simpa [hf_def, Real.sqrt_sq hnn] using this
    -- conclusion
    intro t ht
    have hgt : g |t| = c * (K * |t|) ^ (k + 1) / ((k + 1).factorial : ℝ) := by
      simp only [hg_def]
      rw [mul_pow]
      ring
    have hat : |t| ∈ Icc 0 T := ⟨abs_nonneg t, abs_le.2 ht⟩
    rcases le_total 0 t with h0 | h0
    · have := key 1 (by norm_num) |t| hat
      rw [abs_of_nonneg h0, one_mul] at this
      rw [← hgt, abs_of_nonneg h0]
      exact this
    · have := key (-1) (by norm_num) |t| hat
      rw [abs_of_nonpos h0, neg_one_mul, neg_neg] at this
      rw [← hgt, abs_of_nonpos h0]
      exact this

end NonUniqueEuler.Smooth.IterCauchyAux
