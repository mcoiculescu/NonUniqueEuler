import NonUniqueEuler.Defs.Infra.SobolevOneD
import NonUniqueEuler.Defs.Infra.CkNorm
import NonUniqueEuler.H.Infra.SobolevOneD.Multiplier.General

/-!
# Proof: smooth multipliers on the weighted norms (library I-SOB1)

Proof of `NonUniqueEuler/I/Infra/SobolevOneD/Multiplier.lean` (same declarations, same
statements).

Both statements follow from `MultAux.mul_general` (helper `General.lean`), applied with
`V = (0, ∞)`, `K = [α, β]` and with `V = ℝ`, `K = [a₀, b₀]`:
* `a g ∈ H^k(V)`, by the weak Leibniz rule `∂^j(ag) = ∑_{i ≤ j} C(j,i) a^{(i)} ∂^{j-i} g` on the
  open set `V` (helper `Leibniz.lean`; the `C¹` test functions `a φ` are handled by mollification,
  helper `Mollify.lean`) and the vanishing of the weak derivatives of `g` outside `K`;
* pointwise a.e. on `V`, `|∂^j(ag)|² ≤ M² 2^j ∑_{i ≤ j} C(j,i) |∂^{j-i} g|²` (Cauchy–Schwarz with
  weights `C(j,i)`, helper `Bound.lean`).
Integrating (against `r dr` on `[α, β]`, resp. `dx` on `ℝ`) and `MultAux.weighted_sum_le`
(weight monotonicity `(1+ℓ²)^{k-j} ≤ (1+ℓ²)^{k-(j-i)}`, `C(j,i) ≤ 2^j`, `∑_{j ≤ k} 4^j ≤ 4^{k+1}`)
give the norm bounds.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace NonUniqueEuler.Sob

/-- Multipliers on `‖·‖_{k,ℓ;I}` for profiles on `(0, ∞)` supported in the compact
`I = [α, β] ⊂ (0, ∞)`. -/
theorem secNormSq_mul_le {k : ℕ} {α β : ℝ} (hα : 0 < α) {a g : ℝ → ℂ}
    (ha : ContDiffOn ℝ k a (Ioi 0)) {M : ℝ}
    (hM : ∀ i ≤ k, ∀ r ∈ Icc α β, ‖iteratedDeriv i a r‖ ≤ M) (hg : MemH1On k (Ioi 0) g)
    (hgI : ∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc α β → g r = 0) (ℓ : ℤ) :
    MemH1On k (Ioi 0) (fun r => a r * g r) ∧
      secNormSq k ℓ (Icc α β) (fun r => a r * g r) ≤ 4 ^ (k + 1) * M ^ 2 * secNormSq k ℓ (Icc α β) g := by
  obtain ⟨hmem, hpt⟩ := MultAux.mul_general isOpen_Ioi isClosed_Icc ha hM hg hgI
  refine ⟨hmem, ?_⟩
  obtain ⟨hfam, -, -⟩ := MultAux.family_facts isOpen_Ioi hg
  have hsub : Icc α β ⊆ Ioi 0 := fun r hr => lt_of_lt_of_le hα hr.1
  have hint : ∀ m ≤ k,
      IntegrableOn (fun r => ‖weakDeriv1On (Ioi 0) m g r‖ ^ 2 * r) (Icc α β) := by
    intro m hm
    have h1 : MemLp (weakDeriv1On (Ioi 0) m g) 2 (volume.restrict (Icc α β)) :=
      (hfam m hm).2.2.mono_measure (Measure.restrict_mono hsub le_rfl)
    exact IntegrableOn.mul_continuousOn h1.norm.integrable_sq continuous_id.continuousOn
      isCompact_Icc
  unfold secNormSq
  refine MultAux.weighted_sum_le ℓ
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

/-- Multipliers on `|·|_{k,ℓ}` on the line, for functions supported in `[a₀, b₀]`. -/
theorem logNormSq_mul_le {k : ℕ} {a₀ b₀ : ℝ} {a u : ℝ → ℂ} (ha : ContDiff ℝ k a) {M : ℝ}
    (hM : ∀ i ≤ k, ∀ x ∈ Icc a₀ b₀, ‖iteratedDeriv i a x‖ ≤ M) (hu : MemH1On k univ u)
    (huI : ∀ᵐ x, x ∉ Icc a₀ b₀ → u x = 0) (ℓ : ℤ) :
    MemH1On k univ (fun x => a x * u x) ∧
      logNormSq k ℓ (fun x => a x * u x) ≤ 4 ^ (k + 1) * M ^ 2 * logNormSq k ℓ u := by
  have huI' : ∀ᵐ x ∂(volume.restrict univ), x ∉ Icc a₀ b₀ → u x = 0 := by
    rwa [Measure.restrict_univ]
  obtain ⟨hmem, hpt⟩ := MultAux.mul_general isOpen_univ isClosed_Icc ha.contDiffOn hM hu huI'
  refine ⟨hmem, ?_⟩
  obtain ⟨hfam, -, -⟩ := MultAux.family_facts isOpen_univ hu
  have hint : ∀ m ≤ k,
      Integrable (fun x => ‖weakDeriv1On univ m u x‖ ^ 2) (volume.restrict univ) :=
    fun m hm => (hfam m hm).2.2.norm.integrable_sq
  unfold logNormSq logNormSqOn
  refine MultAux.weighted_sum_le ℓ
    (J := fun j => ∫ x in univ, ‖weakDeriv1On univ j (fun x => a x * u x) x‖ ^ 2)
    (I := fun m => ∫ x in univ, ‖weakDeriv1On univ m u x‖ ^ 2)
    (fun m => setIntegral_nonneg MeasurableSet.univ fun x _ => sq_nonneg _) ?_
  intro j hj
  have hintT : ∀ i ∈ Finset.range (j + 1), Integrable
      (fun x => (j.choose i : ℝ) * ‖weakDeriv1On univ (j - i) u x‖ ^ 2)
      (volume.restrict univ) := fun i _ => (hint (j - i) (by omega)).const_mul _
  have hintR : Integrable (fun x => M ^ 2 * 2 ^ j * ∑ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * ‖weakDeriv1On univ (j - i) u x‖ ^ 2) (volume.restrict univ) :=
    (integrable_finsetSum _ hintT).const_mul _
  have hnn : 0 ≤ᵐ[volume.restrict univ]
      fun x => ‖weakDeriv1On univ j (fun x => a x * u x) x‖ ^ 2 :=
    Filter.Eventually.of_forall fun x => sq_nonneg _
  calc ∫ x in univ, ‖weakDeriv1On univ j (fun x => a x * u x) x‖ ^ 2
      ≤ ∫ x in univ, M ^ 2 * 2 ^ j * ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * ‖weakDeriv1On univ (j - i) u x‖ ^ 2 :=
        integral_mono_of_nonneg hnn hintR (hpt j hj)
    _ = M ^ 2 * 2 ^ j * ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * ∫ x in univ, ‖weakDeriv1On univ (j - i) u x‖ ^ 2 := by
        rw [integral_const_mul, integral_finsetSum _ hintT]
        congr 1
        exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

end NonUniqueEuler.Sob
