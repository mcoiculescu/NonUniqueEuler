import NonUniqueEuler.H.Infra.SobolevOneD.CompLog.Step

/-!
# Helpers for `P/Infra/SobolevOneD/CompLog`: the iterated chain rule for `u ∘ log`

Adapted from `H/Infra/SobolevOneD/LogVariable/Iterate.lean` and `.../Seq.lean` (restated in the
namespace `CompLogH` because the helpers of another proof may not be imported).

* `exists_rev`: if `U 0, …, U j` is a chain of first-order weak derivatives on `ℝ`, then
  `∂_r^j (U 0 ∘ log) = r^{-j} ∑_{p ≤ j} d_p U_p(log r)` weakly on `(0, ∞)`, with `d` depending
  only on `j` (Stirling numbers of the first kind: `r^j ∂_r^j = ∑ s(j,p) ∂_x^p`);
* `exists_seq`: for `g ∈ H^k(V)`, `V` open, a sequence `G 0 = g`, `G 1, …, G k` of weak
  derivatives of `g` in `L²(V)` forming a first-order chain.

This is the manuscript's "`∂_r^j` is a combination of `∂_x^i`, `i ≤ j`" (`04_ring.tex:888-897`).
All proofs are complete.
-/

noncomputable section

open MeasureTheory Set Filter

namespace NonUniqueEuler.Sob.CompLogH

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

/-- An `L²(V)` function on an open `V ⊆ ℝ` is locally integrable on `V`. -/
theorem locallyIntegrableOn_of_memLp {V : Set ℝ} (hV : IsOpen V) {h : ℝ → ℂ}
    (hL2 : MemLp h 2 (volume.restrict V)) : LocallyIntegrableOn h V := by
  have h1 : LocallyIntegrable h (volume.restrict V) := hL2.locallyIntegrable (by norm_num)
  rw [locallyIntegrableOn_iff hV.isLocallyClosed]
  intro K hK hKc
  have h2 : IntegrableOn h K (volume.restrict V) := h1.integrableOn_isCompact hKc
  rwa [IntegrableOn, Measure.restrict_restrict_of_subset hK] at h2

/-- The weak-derivative sequence of `g ∈ H^k(V)`: `L²(V)` weak derivatives of `g` forming a
first-order chain. -/
theorem exists_seq {k : ℕ} {V : Set ℝ} (hV : IsOpen V) {g : ℝ → ℂ} (hg : MemH1On k V g) :
    ∃ G : ℕ → ℝ → ℂ, G 0 = g ∧
      (∀ p ≤ k, MemLp (G p) 2 (volume.restrict V)) ∧
      (∀ p ≤ k, HasWeakDerivOn V (derivList p) g (G p)) ∧
      (∀ p < k, HasWeakDerivOn V (derivList 1) (G p) (G (p + 1))) := by
  have hD : ∀ p ≤ k, MemLp (weakDeriv1On V p g) 2 (volume.restrict V) ∧
      HasWeakDerivOn V (derivList p) g (weakDeriv1On V p g) := by
    intro p hp
    obtain ⟨h, hL2, hw⟩ := hg.deriv p hp
    have hli := locallyIntegrableOn_of_memLp hV hL2
    have hspec := weakDerivOn_spec hli hw
    have hae := weakDerivOn_ae_eq hV hli hw
    refine ⟨hL2.ae_eq ?_, hspec.2⟩
    rw [EventuallyEq, ae_restrict_iff' hV.measurableSet]
    filter_upwards [hae] with x hx hxV using (hx hxV).symm
  set G : ℕ → ℝ → ℂ := fun p => if p = 0 then g else weakDeriv1On V p g with hG
  have hG0 : G 0 = g := by simp [hG]
  have hGs : ∀ p, p ≠ 0 → G p = weakDeriv1On V p g := fun p hp => by simp [hG, hp]
  have hw : ∀ p ≤ k, HasWeakDerivOn V (derivList p) g (G p) := by
    intro p hp
    rcases Nat.eq_zero_or_pos p with rfl | hp0
    · rw [hG0]; exact hasWeakDerivOn_nil_self g
    · rw [hGs p hp0.ne']; exact (hD p hp).2
  refine ⟨G, hG0, fun p hp => ?_, hw, fun p hp => ?_⟩
  · rcases Nat.eq_zero_or_pos p with rfl | hp0
    · rw [hG0]; exact hg.memLp
    · rw [hGs p hp0.ne']; exact (hD p hp).1
  · exact hasWeakDerivOn_one_of_succ (hw p hp.le) (hw (p + 1) hp)

end NonUniqueEuler.Sob.CompLogH
