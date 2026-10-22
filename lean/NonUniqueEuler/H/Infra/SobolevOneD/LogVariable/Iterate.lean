import NonUniqueEuler.H.Infra.SobolevOneD.LogVariable.Step

/-!
# Helpers for `P/Infra/SobolevOneD/LogVariable`: higher-order weak chain rules

Iterating the first-order rules of `Step.lean`:
* `exists_fwd`: if `G 0, G 1, …, G j` is a chain of first-order weak derivatives on `(0, ∞)`,
  then `∂_x^j (G 0 ∘ exp) = ∑_{p ≤ j} c_p e^{px} G_p(e^x)` weakly on `ℝ`, with coefficients `c`
  depending only on `j` (Stirling numbers of the second kind: `∂_x^j = ∑ S(j,p) r^p ∂_r^p`);
* `exists_rev`: if `U 0, …, U j` is a chain of first-order weak derivatives on `ℝ`, then
  `∂_r^j (U 0 ∘ log) = r^{-j} ∑_{p ≤ j} d_p U_p(log r)` weakly on `(0, ∞)`, with `d` depending
  only on `j` (Stirling numbers of the first kind: `r^j ∂_r^j = ∑ s(j,p) ∂_x^p`).

This is the manuscript's "`∂_r^j` is a combination of `∂_x^i`, `i ≤ j`, and conversely"
(`04_ring.tex:888-897`). All proofs are complete.
-/

noncomputable section

open MeasureTheory Set Filter

namespace NonUniqueEuler.Sob.LogVarH

/-- Index shift in the coefficient recursion. -/
theorem sum_shift (j : ℕ) (a b f : ℕ → ℂ) :
    ∑ p ∈ Finset.range (j + 2),
        ((if p < j + 1 then b p else 0) + (if p = 0 then 0 else a (p - 1))) * f p =
      ∑ p ∈ Finset.range (j + 1), b p * f p + ∑ p ∈ Finset.range (j + 1), a p * f (p + 1) := by
  simp only [add_mul, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_range_succ]
    simp only [lt_irrefl, ite_false, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun p hp => ?_
    simp [Finset.mem_range.1 hp]
  · rw [Finset.sum_range_succ']
    simp

theorem locallyIntegrable_const_mul {f : ℝ → ℂ} (hf : LocallyIntegrable f) (c : ℂ) :
    LocallyIntegrable (fun x => c * f x) :=
  hf.smul c

theorem locallyIntegrableOn_const_mul {V : Set ℝ} {f : ℝ → ℂ} (hf : LocallyIntegrableOn f V)
    (c : ℂ) : LocallyIntegrableOn (fun x => c * f x) V :=
  hf.smul c

/-- Forward iteration: `∂_x^j (G 0 ∘ exp) = ∑_{p ≤ j} c_p e^{px} G_p(e^x)`. -/
theorem exists_fwd (j : ℕ) : ∃ c : ℕ → ℂ, ∀ G : ℕ → ℝ → ℂ,
    (∀ p < j, HasWeakDerivOn (Ioi 0) (derivList 1) (G p) (G (p + 1))) →
    (∀ p ≤ j, LocallyIntegrableOn (G p) (Ioi 0)) →
    HasWeakDerivOn univ (derivList j) (fun x => G 0 (Real.exp x))
      (fun x => ∑ p ∈ Finset.range (j + 1),
        c p * ((Real.exp (p * x) : ℂ) * G p (Real.exp x))) := by
  induction j with
  | zero =>
    refine ⟨fun _ => 1, fun G _ _ => ?_⟩
    have e : (fun x => ∑ p ∈ Finset.range (0 + 1),
        (fun _ => (1 : ℂ)) p * ((Real.exp (p * x) : ℂ) * G p (Real.exp x))) =
        fun x => G 0 (Real.exp x) := by
      ext x; simp
    rw [e]
    exact hasWeakDerivOn_nil_self _
  | succ j ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨fun p => (if p < j + 1 then (p : ℂ) * c p else 0) + (if p = 0 then 0 else c (p - 1)),
      fun G hG hGli => ?_⟩
    have h1 := hc G (fun p hp => hG p (by omega)) (fun p hp => hGli p (by omega))
    set A : ℕ → ℝ → ℂ := fun p x => (Real.exp (p * x) : ℂ) * G p (Real.exp x) with hA
    have hAli : ∀ p ≤ j + 1, LocallyIntegrable (A p) := fun p hp =>
      locallyIntegrable_expMul_comp_exp (hGli p hp) p
    have hAd : ∀ p < j + 1, HasWeakDerivOn univ (derivList 1) (A p)
        (fun x => (p : ℂ) * A p x + A (p + 1) x) := fun p hp =>
      hasWeakDerivOn_expMul_comp_exp (hGli p (by omega)) (hGli (p + 1) (by omega)) (hG p hp) p
    have h2 := (hasWeakDerivOn_sum isOpen_univ (j + 1) (fun p x => c p * A p x)
      (fun p x => c p * ((p : ℂ) * A p x + A (p + 1) x))
      (fun p hp => locallyIntegrableOn_univ.2
        (locallyIntegrable_const_mul (hAli p (by omega)) (c p)))
      (fun p hp => locallyIntegrableOn_univ.2 (locallyIntegrable_const_mul
        (((hAli p (by omega)).smul (p : ℂ)).add (hAli (p + 1) (by omega))) (c p)))
      (fun p hp => (hAd p hp).const_mul (c p))).1
    have h3 := h1.trans h2
    rw [derivList_succ_eq]
    convert h3 using 1
    ext x
    rw [sum_shift j c (fun p => (p : ℂ) * c p) (fun p => A p x), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring

/-- Reverse iteration: `∂_r^j (U 0 ∘ log) = r^{-j} ∑_{p ≤ j} d_p U_p(log r)`. -/
theorem exists_rev (j : ℕ) : ∃ d : ℕ → ℂ, ∀ U : ℕ → ℝ → ℂ,
    (∀ p < j, HasWeakDerivOn univ (derivList 1) (U p) (U (p + 1))) →
    (∀ p ≤ j, LocallyIntegrable (U p)) →
    HasWeakDerivOn (Ioi 0) (derivList j) (fun r => U 0 (Real.log r))
      (fun r => ((r⁻¹ : ℝ) : ℂ) ^ j * ∑ p ∈ Finset.range (j + 1), d p * U p (Real.log r)) := by
  induction j with
  | zero =>
    refine ⟨fun _ => 1, fun U _ _ => ?_⟩
    have e : (fun r => ((r⁻¹ : ℝ) : ℂ) ^ 0 * ∑ p ∈ Finset.range (0 + 1),
        (fun _ => (1 : ℂ)) p * U p (Real.log r)) = fun r => U 0 (Real.log r) := by
      ext r; simp
    rw [e]
    exact hasWeakDerivOn_nil_self _
  | succ j ih =>
    obtain ⟨d, hd⟩ := ih
    refine ⟨fun p => (if p < j + 1 then -(j : ℂ) * d p else 0) + (if p = 0 then 0 else d (p - 1)),
      fun U hU hUli => ?_⟩
    have h1 := hd U (fun p hp => hU p (by omega)) (fun p hp => hUli p (by omega))
    obtain ⟨hV, hVli, hV'li⟩ := hasWeakDerivOn_sum isOpen_univ (j + 1)
      (fun p x => d p * U p x) (fun p x => d p * U (p + 1) x)
      (fun p hp => locallyIntegrableOn_univ.2
        (locallyIntegrable_const_mul (hUli p (by omega)) (d p)))
      (fun p hp => locallyIntegrableOn_univ.2
        (locallyIntegrable_const_mul (hUli (p + 1) (by omega)) (d p)))
      (fun p hp => (hU p (by omega)).const_mul (d p))
    have h2 := hasWeakDerivOn_expMul (locallyIntegrableOn_univ.1 hVli)
      (locallyIntegrableOn_univ.1 hV'li) hV (-(j : ℝ))
    have h3 := hasWeakDerivOn_comp_log h2
    have hexp : ∀ r : ℝ, 0 < r → Real.exp (-(j : ℝ) * Real.log r) = r⁻¹ ^ j := by
      intro r hr
      rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hr, inv_pow]
    have h4 : HasWeakDerivOn (Ioi 0) (derivList 1)
        (fun r => ((r⁻¹ : ℝ) : ℂ) ^ j * ∑ p ∈ Finset.range (j + 1), d p * U p (Real.log r))
        (fun r => ((r⁻¹ : ℝ) : ℂ) ^ (j + 1) * ∑ p ∈ Finset.range (j + 1 + 1),
          ((if p < j + 1 then -(j : ℂ) * d p else 0) + (if p = 0 then 0 else d (p - 1))) *
            U p (Real.log r)) := by
      refine h3.congr_ae (Eventually.of_forall fun r hr => ?_)
        (Eventually.of_forall fun r hr => ?_)
      · rw [hexp r hr]
        push_cast
        rfl
      · rw [hexp r hr, sum_shift j d (fun p => -(j : ℂ) * d p) (fun p => U p (Real.log r))]
        push_cast
        simp only [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun p _ => ?_
        ring
    rw [derivList_succ_eq]
    exact h1.trans h4

end NonUniqueEuler.Sob.LogVarH
