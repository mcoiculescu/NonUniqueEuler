import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Complex.Basic
import NonUniqueEuler.Defs.Infra.Sobolev

/-!
# Helper for `P/Infra/Sobolev/Interp`: conjugation, the `L²` pairing, and `#multiIdx k`

Manuscript `02_prelim.tex:632-643` (proof of (E3)), restructured as in restructuring R3
(integration by parts instead of Plancherel). Generic, `I`-independent facts:

* `iterDirDeriv_conj`, `isTestFn_conj`: complex conjugation commutes with (real) directional
  derivatives, so `conj ∘ φ` is a test function whenever `φ` is;
* `integral_conj_mul_eq_inner`: `∫ conj(a) b = ⟪a, b⟫_{L²}` for `a, b ∈ L²`;
* `norm_integral_conj_mul_le`: Cauchy–Schwarz `|∫ conj(a) b| ≤ ‖a‖₂ ‖b‖₂`;
* `card_multiIdx_le`: `#multiIdx k = (k+1)(k+2)/2 ≤ 3^k`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff ComplexConjugate InnerProductSpace

namespace NonUniqueEuler.Sob.InterpH

/-- Directional derivatives commute with complex conjugation. -/
theorem dirDeriv_conj (v : ℂ) (φ : ℂ → ℂ) :
    dirDeriv v (fun x => conj (φ x)) = fun x => conj (dirDeriv v φ x) := by
  funext x
  have h : (fun x => conj (φ x)) = (Complex.conjCLE : ℂ ≃L[ℝ] ℂ) ∘ φ := by
    funext y; simp
  simp only [dirDeriv]
  rw [h, ContinuousLinearEquiv.comp_fderiv]
  simp

/-- Iterated directional derivatives commute with complex conjugation. -/
theorem iterDirDeriv_conj (vs : List ℂ) (φ : ℂ → ℂ) :
    iterDirDeriv vs (fun x => conj (φ x)) = fun x => conj (iterDirDeriv vs φ x) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => rw [iterDirDeriv_cons, ih, dirDeriv_conj]; rfl

/-- The conjugate of a test function is a test function. -/
theorem isTestFn_conj {V : Set ℂ} {φ : ℂ → ℂ} (h : IsTestFn V φ) :
    IsTestFn V (fun x => conj (φ x)) := by
  have hsupp : Function.support (fun x => conj (φ x)) = Function.support φ := by
    ext x; simp
  refine ⟨?_, ?_, ?_⟩
  · have := (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).contDiff.comp h.smooth (n := ∞)
    simpa [Function.comp_def] using this
  · exact h.compact.comp_left (g := fun z : ℂ => conj z) (by simp)
  · simpa [tsupport, hsupp] using h.subset

/-- The `L²` pairing as an integral: `∫ conj(a) b = ⟪a, b⟫_{L²}`. -/
theorem integral_conj_mul_eq_inner {a b : ℂ → ℂ} (ha : MemLp a 2 volume)
    (hb : MemLp b 2 volume) :
    ∫ x, conj (a x) * b x = ⟪ha.toLp a, hb.toLp b⟫_ℂ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with x hxa hxb
  rw [hxa, hxb, RCLike.inner_apply']

/-- Cauchy–Schwarz in `L²`: `|∫ conj(a) b| ≤ ‖a‖₂ ‖b‖₂`. -/
theorem norm_integral_conj_mul_le {a b : ℂ → ℂ} (ha : MemLp a 2 volume)
    (hb : MemLp b 2 volume) :
    ‖∫ x, conj (a x) * b x‖ ≤ l2 a * l2 b := by
  rw [integral_conj_mul_eq_inner ha hb]
  calc _ ≤ ‖ha.toLp a‖ * ‖hb.toLp b‖ := norm_inner_le_norm _ _
    _ = l2 a * l2 b := by rw [Lp.norm_toLp, Lp.norm_toLp]; rfl

theorem two_add_le_two_mul_three_pow (k : ℕ) : k + 2 ≤ 2 * 3 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih => rw [pow_succ]; omega

/-- `#multiIdx k ≤ 3^k` (the exact value is `(k+1)(k+2)/2`). -/
theorem card_multiIdx_le (k : ℕ) : (multiIdx k).card ≤ 3 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hsub : multiIdx (k + 1) ⊆
        multiIdx k ∪ (Finset.range (k + 2)).image (fun i => (i, k + 1 - i)) := by
      intro γ hγ
      rw [mem_multiIdx] at hγ
      rw [Finset.mem_union, mem_multiIdx, Finset.mem_image]
      by_cases h : γ.1 + γ.2 ≤ k
      · exact Or.inl h
      · right
        refine ⟨γ.1, Finset.mem_range.2 (by omega), ?_⟩
        ext
        · rfl
        · simp only; omega
    have h2 := two_add_le_two_mul_three_pow k
    calc (multiIdx (k + 1)).card
        ≤ (multiIdx k ∪ (Finset.range (k + 2)).image (fun i => (i, k + 1 - i))).card :=
          Finset.card_le_card hsub
      _ ≤ (multiIdx k).card + ((Finset.range (k + 2)).image (fun i => (i, k + 1 - i))).card :=
          Finset.card_union_le _ _
      _ ≤ 3 ^ k + (k + 2) := by
          refine add_le_add ih (Finset.card_image_le.trans ?_)
          simp
      _ ≤ 3 ^ (k + 1) := by rw [pow_succ]; omega

end NonUniqueEuler.Sob.InterpH
