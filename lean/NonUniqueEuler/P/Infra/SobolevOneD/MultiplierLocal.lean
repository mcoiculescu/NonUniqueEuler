import NonUniqueEuler.Defs.Infra.SobolevOneD
import NonUniqueEuler.H.Infra.SobolevOneD.MultiplierLocal.General

/-!
# Proof: multipliers that vanish off a compact interval (library I-SOB1)

Proof of `NonUniqueEuler/I/Infra/SobolevOneD/MultiplierLocal.lean` (same declaration, same
statement).

* `a` vanishes on the open set `(0, ∞) \ [α, β]`, so its iterated derivatives vanish there and
  `|a^{(i)}| ≤ |M|` on all of `(0, ∞)` (`MultLocAux.norm_iteratedDeriv_le_of_vanish`).
* `MultLocAux.mul_bounded` (helper `General.lean`, a variant of `MultAux.mul_general` of
  `H/Infra/SobolevOneD/Multiplier/General.lean` without support condition on `g`): by the weak
  Leibniz rule on `(0, ∞)`, `a g ∈ H^k((0, ∞))` and, a.e. on `(0, ∞)`,
  `|∂^j(ag)|² ≤ M² 2^j ∑_{i ≤ j} C(j,i) |∂^{j-i} g|²`.
* Integrate against `r dr` on `[α, β] ⊂ (0, ∞)` and apply `MultLocAux.weighted_sum_le`
  (weight monotonicity, `C(j,i) ≤ 2^j`, `∑_{j ≤ k} 4^j ≤ 4^{k+1}`), exactly as in the proof of
  `secNormSq_mul_le` (`P/Infra/SobolevOneD/Multiplier.lean`).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace NonUniqueEuler.Sob

/-- Multipliers vanishing on `(0, ∞)` outside the compact `I = [α, β] ⊂ (0, ∞)` act on
`‖·‖_{k,ℓ;I}` for all `g ∈ H^k((0, ∞))`, with constant `4^{k+1} M²`, uniformly in `ℓ`. -/
theorem secNormSq_mul_le_of_vanish {k : ℕ} {α β : ℝ} (hα : 0 < α) {a g : ℝ → ℂ}
    (ha : ContDiffOn ℝ k a (Ioi 0)) (haI : ∀ r : ℝ, 0 < r → r ∉ Icc α β → a r = 0) {M : ℝ}
    (hM : ∀ i ≤ k, ∀ r ∈ Icc α β, ‖iteratedDeriv i a r‖ ≤ M) (hg : MemH1On k (Ioi 0) g)
    (ℓ : ℤ) :
    MemH1On k (Ioi 0) (fun r => a r * g r) ∧
      secNormSq k ℓ (Icc α β) (fun r => a r * g r) ≤
        4 ^ (k + 1) * M ^ 2 * secNormSq k ℓ (Icc α β) g := by
  have hMV := MultLocAux.norm_iteratedDeriv_le_of_vanish haI hM
  obtain ⟨hmem, hpt⟩ := MultLocAux.mul_bounded isOpen_Ioi ha hMV hg
  simp only [sq_abs] at hpt
  refine ⟨hmem, ?_⟩
  obtain ⟨hfam, -, -⟩ := MultLocAux.family_facts isOpen_Ioi hg
  have hsub : Icc α β ⊆ Ioi 0 := fun r hr => lt_of_lt_of_le hα hr.1
  have hint : ∀ m ≤ k,
      IntegrableOn (fun r => ‖weakDeriv1On (Ioi 0) m g r‖ ^ 2 * r) (Icc α β) := by
    intro m hm
    have h1 : MemLp (weakDeriv1On (Ioi 0) m g) 2 (volume.restrict (Icc α β)) :=
      (hfam m hm).2.2.mono_measure (Measure.restrict_mono hsub le_rfl)
    exact IntegrableOn.mul_continuousOn h1.norm.integrable_sq continuous_id.continuousOn
      isCompact_Icc
  unfold secNormSq
  refine MultLocAux.weighted_sum_le ℓ
    (J := fun j => ∫ r in Icc α β, ‖weakDeriv1On (Ioi 0) j (fun r => a r * g r) r‖ ^ 2 * r)
    (I := fun m => ∫ r in Icc α β, ‖weakDeriv1On (Ioi 0) m g r‖ ^ 2 * r)
    (fun m => setIntegral_nonneg measurableSet_Icc fun r hr =>
      mul_nonneg (sq_nonneg _) (hα.le.trans hr.1)) ?_
  intro j hj
  have hptj : ∀ᵐ r ∂(volume.restrict (Icc α β)),
      ‖weakDeriv1On (Ioi 0) j (fun r => a r * g r) r‖ ^ 2 * r ≤
        M ^ 2 * 2 ^ j * ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * (‖weakDeriv1On (Ioi 0) (j - i) g r‖ ^ 2 * r) := by
    have := ae_restrict_of_ae_restrict_of_subset hsub (hpt j hj)
    filter_upwards [this, ae_restrict_mem measurableSet_Icc] with r hr hrI
    have hr0 : 0 ≤ r := hα.le.trans hrI.1
    calc ‖weakDeriv1On (Ioi 0) j (fun r => a r * g r) r‖ ^ 2 * r
        ≤ (M ^ 2 * 2 ^ j * ∑ i ∈ Finset.range (j + 1),
            (j.choose i : ℝ) * ‖weakDeriv1On (Ioi 0) (j - i) g r‖ ^ 2) * r :=
          mul_le_mul_of_nonneg_right hr hr0
      _ = _ := by
          rw [mul_assoc, Finset.sum_mul]
          congr 1
          refine Finset.sum_congr rfl fun i _ => by ring
  have hintT : ∀ i ∈ Finset.range (j + 1), Integrable
      (fun r => (j.choose i : ℝ) * (‖weakDeriv1On (Ioi 0) (j - i) g r‖ ^ 2 * r))
      (volume.restrict (Icc α β)) := fun i _ => (hint (j - i) (by omega)).const_mul _
  have hintR : Integrable (fun r => M ^ 2 * 2 ^ j * ∑ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * (‖weakDeriv1On (Ioi 0) (j - i) g r‖ ^ 2 * r))
      (volume.restrict (Icc α β)) :=
    (integrable_finsetSum _ hintT).const_mul _
  have hnn : 0 ≤ᵐ[volume.restrict (Icc α β)]
      fun r => ‖weakDeriv1On (Ioi 0) j (fun r => a r * g r) r‖ ^ 2 * r := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hrI
    exact mul_nonneg (sq_nonneg _) (hα.le.trans hrI.1)
  calc ∫ r in Icc α β, ‖weakDeriv1On (Ioi 0) j (fun r => a r * g r) r‖ ^ 2 * r
      ≤ ∫ r in Icc α β, M ^ 2 * 2 ^ j * ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * (‖weakDeriv1On (Ioi 0) (j - i) g r‖ ^ 2 * r) :=
        integral_mono_of_nonneg hnn hintR hptj
    _ = M ^ 2 * 2 ^ j * ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * ∫ r in Icc α β, ‖weakDeriv1On (Ioi 0) (j - i) g r‖ ^ 2 * r := by
        rw [integral_const_mul, integral_finsetSum _ hintT]
        congr 1
        exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

end NonUniqueEuler.Sob
