import NonUniqueEuler.H.Infra.SobolevOneD.LogVariable.Step
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Helpers for `P/Infra/SobolevOneD/LogVariable`: weak-derivative sequences and weights

* `locallyIntegrableOn_of_memLp`: `L²(V) ⊆ L¹_loc(V)` for open `V ⊆ ℝ`;
* `exists_seq`: for `g ∈ H^k(V)`, the sequence `G 0 = g`, `G p = weakDeriv1On V p g` (`p ≥ 1`)
  is in `L²(V)`, consists of weak derivatives of `g`, forms a first-order chain, and agrees a.e.
  on `V` with the chosen weak derivatives;
* `ae_eq_zero_of_hasWeakDerivOn`: a weak derivative vanishes a.e. on an open set where the
  function vanishes a.e.;
* `secWeight_anti`, `weighted_sum_le`: the weight bookkeeping
  `(1+ℓ²)^{k-j} ≤ (1+ℓ²)^{k-p}` for `p ≤ j` (manuscript `I/Infra/SobolevOneD/LogVariable`
  docstring).

All proofs are complete.
-/

noncomputable section

open MeasureTheory Set Filter

namespace NonUniqueEuler.Sob.LogVarH

/-- An `L²(V)` function on an open `V ⊆ ℝ` is locally integrable on `V`. -/
theorem locallyIntegrableOn_of_memLp {V : Set ℝ} (hV : IsOpen V) {h : ℝ → ℂ}
    (hL2 : MemLp h 2 (volume.restrict V)) : LocallyIntegrableOn h V := by
  have h1 : LocallyIntegrable h (volume.restrict V) := hL2.locallyIntegrable (by norm_num)
  rw [locallyIntegrableOn_iff hV.isLocallyClosed]
  intro K hK hKc
  have h2 : IntegrableOn h K (volume.restrict V) := h1.integrableOn_isCompact hKc
  rwa [IntegrableOn, Measure.restrict_restrict_of_subset hK] at h2

/-- The weak-derivative sequence of `g ∈ H^k(V)`. -/
theorem exists_seq {k : ℕ} {V : Set ℝ} (hV : IsOpen V) {g : ℝ → ℂ} (hg : MemH1On k V g) :
    ∃ G : ℕ → ℝ → ℂ, G 0 = g ∧
      (∀ p ≤ k, MemLp (G p) 2 (volume.restrict V)) ∧
      (∀ p ≤ k, HasWeakDerivOn V (derivList p) g (G p)) ∧
      (∀ p < k, HasWeakDerivOn V (derivList 1) (G p) (G (p + 1))) ∧
      (∀ p ≤ k, ∀ᵐ x, x ∈ V → weakDeriv1On V p g x = G p x) := by
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
  have hgli : LocallyIntegrableOn g V := locallyIntegrableOn_of_memLp hV hg.memLp
  set G : ℕ → ℝ → ℂ := fun p => if p = 0 then g else weakDeriv1On V p g with hG
  have hG0 : G 0 = g := by simp [hG]
  have hGs : ∀ p, p ≠ 0 → G p = weakDeriv1On V p g := fun p hp => by simp [hG, hp]
  have hw : ∀ p ≤ k, HasWeakDerivOn V (derivList p) g (G p) := by
    intro p hp
    rcases Nat.eq_zero_or_pos p with rfl | hp0
    · rw [hG0]; exact hasWeakDerivOn_nil_self g
    · rw [hGs p hp0.ne']; exact (hD p hp).2
  refine ⟨G, hG0, fun p hp => ?_, hw, fun p hp => ?_, fun p hp => ?_⟩
  · rcases Nat.eq_zero_or_pos p with rfl | hp0
    · rw [hG0]; exact hg.memLp
    · rw [hGs p hp0.ne']; exact (hD p hp).1
  · exact hasWeakDerivOn_one_of_succ (hw p hp.le) (hw (p + 1) hp)
  · rcases Nat.eq_zero_or_pos p with rfl | hp0
    · rw [hG0]
      exact weakDerivOn_ae_eq hV hgli (hasWeakDerivOn_nil_self g)
    · rw [hGs p hp0.ne']
      exact Eventually.of_forall fun _ _ => rfl

/-- A weak derivative vanishes a.e. on an open set where the function vanishes a.e. -/
theorem ae_eq_zero_of_hasWeakDerivOn {V W : Set ℝ} (hW : IsOpen W) (hWV : W ⊆ V)
    {vs : List ℝ} {f h : ℝ → ℂ} (hh : LocallyIntegrableOn h V) (hfh : HasWeakDerivOn V vs f h)
    (hf0 : ∀ᵐ x, x ∈ W → f x = 0) : ∀ᵐ x, x ∈ W → h x = 0 := by
  have h1 : HasWeakDerivOn W vs f h := hfh.mono hWV
  have h2 : HasWeakDerivOn W vs f (fun _ => 0) := by
    intro φ hφ
    have hφ' := hφ.iterDirDeriv vs
    simp only [zero_mul, integral_zero, mul_zero]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hf0] with x hx
    by_cases hxW : x ∈ W
    · simp [hx hxW]
    · simp [testFn_eq_zero hφ' hxW]
  exact HasWeakDerivOn.ae_eq hW (hh.mono_set hWV) locallyIntegrableOn_zero h1 h2

theorem secWeight_anti {k p j : ℕ} (hpj : p ≤ j) (ℓ : ℤ) :
    secWeight k j ℓ ≤ secWeight k p ℓ :=
  pow_le_pow_right₀ (by nlinarith [sq_nonneg (ℓ : ℝ)]) (Nat.sub_le_sub_left hpj k)

/-- Weight bookkeeping: if `a_j ≤ ∑_{p ≤ j} C_{jp} b_p` for `j ≤ k`, then
`∑_j (1+ℓ²)^{k-j} a_j ≤ (1 + ∑ C) ∑_p (1+ℓ²)^{k-p} b_p`. -/
theorem weighted_sum_le (k : ℕ) (ℓ : ℤ) (a b : ℕ → ℝ) (Cc : ℕ → ℕ → ℝ)
    (hC : ∀ j p, 0 ≤ Cc j p) (hb : ∀ p, 0 ≤ b p)
    (ha : ∀ j ≤ k, a j ≤ ∑ p ∈ Finset.range (j + 1), Cc j p * b p) :
    ∑ j ∈ Finset.range (k + 1), secWeight k j ℓ * a j ≤
      (1 + ∑ j ∈ Finset.range (k + 1), ∑ p ∈ Finset.range (j + 1), Cc j p) *
        ∑ p ∈ Finset.range (k + 1), secWeight k p ℓ * b p := by
  set S := ∑ p ∈ Finset.range (k + 1), secWeight k p ℓ * b p with hSdef
  have hS : 0 ≤ S := Finset.sum_nonneg fun p _ => mul_nonneg (secWeight_nonneg k p ℓ) (hb p)
  have hterm : ∀ j ∈ Finset.range (k + 1),
      secWeight k j ℓ * a j ≤ (∑ p ∈ Finset.range (j + 1), Cc j p) * S := by
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    calc secWeight k j ℓ * a j
        ≤ secWeight k j ℓ * ∑ p ∈ Finset.range (j + 1), Cc j p * b p :=
          mul_le_mul_of_nonneg_left (ha j hjk) (secWeight_nonneg k j ℓ)
      _ = ∑ p ∈ Finset.range (j + 1), Cc j p * (secWeight k j ℓ * b p) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun p _ => by ring
      _ ≤ ∑ p ∈ Finset.range (j + 1), Cc j p * S := by
          refine Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_left ?_ (hC j p)
          have hpj : p ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hp)
          calc secWeight k j ℓ * b p ≤ secWeight k p ℓ * b p :=
                mul_le_mul_of_nonneg_right (secWeight_anti hpj ℓ) (hb p)
            _ ≤ S := Finset.single_le_sum (f := fun p => secWeight k p ℓ * b p)
                  (fun i _ => mul_nonneg (secWeight_nonneg k i ℓ) (hb i))
                  (Finset.mem_range.2 (by omega))
      _ = (∑ p ∈ Finset.range (j + 1), Cc j p) * S := by rw [Finset.sum_mul]
  calc ∑ j ∈ Finset.range (k + 1), secWeight k j ℓ * a j
      ≤ ∑ j ∈ Finset.range (k + 1), (∑ p ∈ Finset.range (j + 1), Cc j p) * S :=
        Finset.sum_le_sum hterm
    _ = (∑ j ∈ Finset.range (k + 1), ∑ p ∈ Finset.range (j + 1), Cc j p) * S := by
        rw [Finset.sum_mul]
    _ ≤ (1 + ∑ j ∈ Finset.range (k + 1), ∑ p ∈ Finset.range (j + 1), Cc j p) * S :=
        mul_le_mul_of_nonneg_right (by linarith) hS

end NonUniqueEuler.Sob.LogVarH
