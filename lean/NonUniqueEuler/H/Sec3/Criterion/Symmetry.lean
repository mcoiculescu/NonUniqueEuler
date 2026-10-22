import NonUniqueEuler.H.Sec3.Criterion.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Helper for `P/Sec3/Criterion`: item (vi) of `thm:criterion`

Manuscript: proof of `thm:criterion`, last paragraph, `03_compactness.tex:1066-1077`.

If `gₙ ⇀ g` weakly in `L²` (tested against all of `L²`) and `gₙ ∘ Q = ι gₙ` a.e. for a linear
isometry `Q` of `ℝ² = ℂ`, then `g ∘ Q = ι g` a.e.: change of variables `y = Qx` (`Q` preserves
Lebesgue measure), the pairing against `ψ ∘ Q⁻¹ ∈ L²`, and `ae_eq_of_forall_integral_mul_eq`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.Compact.CriterionAux

/-- (vi): symmetries pass to weak `L²` limits. -/
theorem isSymmetricUnder_of_weakTendsto {gs : ℕ → ℂ → ℝ} {g : ℂ → ℝ} (hg : MemLp g 2 volume)
    (hw : ∀ ψ : ℂ → ℝ, MemLp ψ 2 volume →
      Tendsto (fun n => ∫ x, gs n x * ψ x) atTop (𝓝 (∫ x, g x * ψ x)))
    (Q : ℂ ≃ₗᵢ[ℝ] ℂ) (ι : ℝ) (hsym : ∀ n, IsSymmetricUnder Q ι (gs n)) :
    IsSymmetricUnder Q ι g := by
  have hQ : MeasurePreserving Q volume volume := Q.measurePreserving
  have hQs : MeasurePreserving Q.symm volume volume := Q.symm.measurePreserving
  have key : ∀ ψ : ℂ → ℝ, MemLp ψ 2 volume →
      ∫ x, g (Q x) * ψ x = ∫ x, (ι * g x) * ψ x := by
    intro ψ hψ
    have hψQ : MemLp (fun y => ψ (Q.symm y)) 2 volume := hψ.comp_measurePreserving hQs
    have hch : ∀ G : ℂ → ℝ, ∫ x, G (Q x) * ψ x = ∫ y, G y * ψ (Q.symm y) := fun G => by
      have := hQ.integral_comp Q.toHomeomorph.measurableEmbedding
        (fun y => G y * ψ (Q.symm y))
      simpa using this
    have h1 : Tendsto (fun n => ∫ x, gs n x * ψ (Q.symm x)) atTop
        (𝓝 (∫ x, g (Q x) * ψ x)) := by
      rw [hch g]; exact hw _ hψQ
    have h2 : Tendsto (fun n => ∫ x, gs n x * ψ (Q.symm x)) atTop
        (𝓝 (ι * ∫ x, g x * ψ x)) := by
      have e : (fun n => ∫ x, gs n x * ψ (Q.symm x)) = fun n => ι * ∫ x, gs n x * ψ x := by
        funext n
        rw [← hch (gs n), ← integral_const_mul]
        refine integral_congr_ae ((hsym n).mono fun x hx => ?_)
        simp only at hx ⊢
        rw [hx, mul_assoc]
      rw [e]
      exact (hw ψ hψ).const_mul ι
    rw [tendsto_nhds_unique h1 h2, ← integral_const_mul]
    congr 1
    funext x
    ring
  exact ae_eq_of_forall_integral_mul_eq (hg.comp_measurePreserving hQ) (hg.const_mul ι) key

end NonUniqueEuler.Compact.CriterionAux
