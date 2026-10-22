import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Helpers for `P/Sec4/Edge`: generic integral lemmas

Manuscript-independent facts used in the proof of `lem:edge` (`04_ring.tex:730-769`):

* `integral_kernel_conj_symm`: a real symmetric kernel gives a Hermitian form,
  `∫∫ K(x,y) f(y) conj(g(x)) = conj ∫∫ K(x,y) g(y) conj(f(x))` (Fubini);
* `sq_integral_mul_le`: the weighted Cauchy–Schwarz inequality
  `(∫ A B w)² ≤ (∫ A² w)(∫ B² w)` for `w ≥ 0` (discriminant argument);
* `integrable_prod_Icc`: continuous functions on `[a,b]²` are integrable for the product of the
  restricted Lebesgue measures.
-/

noncomputable section

open MeasureTheory Set ComplexConjugate

namespace NonUniqueEuler.EdgeH

/-- A real symmetric kernel defines a Hermitian form (Fubini). -/
theorem integral_kernel_conj_symm {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    (K : α → α → ℝ) (hK : ∀ x y, K x y = K y x) (f g : α → ℂ)
    (hint : Integrable (fun p : α × α => (K p.1 p.2 : ℂ) * f p.2 * conj (g p.1)) (μ.prod μ)) :
    ∫ x, (∫ y, (K x y : ℂ) * f y ∂μ) * conj (g x) ∂μ =
      conj (∫ x, (∫ y, (K x y : ℂ) * g y ∂μ) * conj (f x) ∂μ) := by
  rw [← integral_conj]
  have h1 : ∀ x, conj ((∫ y, (K x y : ℂ) * g y ∂μ) * conj (f x)) =
      ∫ y, (K x y : ℂ) * conj (g y) * f x ∂μ := by
    intro x
    rw [map_mul, Complex.conj_conj, ← integral_conj, ← integral_mul_const]
    congr 1
    funext y
    rw [map_mul, Complex.conj_ofReal]
  have h2 : ∀ x, (∫ y, (K x y : ℂ) * f y ∂μ) * conj (g x) =
      ∫ y, (K x y : ℂ) * f y * conj (g x) ∂μ := fun x => (integral_mul_const _ _).symm
  simp_rw [h1, h2]
  rw [integral_integral_swap]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [hK x y]
    ring
  · exact hint

/-- The weighted Cauchy–Schwarz inequality `(∫ A B w)² ≤ (∫ A² w)(∫ B² w)` for `w ≥ 0`. -/
theorem sq_integral_mul_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {A B w : α → ℝ}
    (hw : ∀ᵐ x ∂μ, 0 ≤ w x) (hAA : Integrable (fun x => A x ^ 2 * w x) μ)
    (hBB : Integrable (fun x => B x ^ 2 * w x) μ)
    (hAB : Integrable (fun x => A x * B x * w x) μ) :
    (∫ x, A x * B x * w x ∂μ) ^ 2 ≤ (∫ x, A x ^ 2 * w x ∂μ) * (∫ x, B x ^ 2 * w x ∂μ) := by
  set a := ∫ x, A x ^ 2 * w x ∂μ
  set b := ∫ x, A x * B x * w x ∂μ
  set c := ∫ x, B x ^ 2 * w x ∂μ
  have key : ∀ t : ℝ, 0 ≤ a * (t * t) + (-2 * b) * t + c := by
    intro t
    have hexp : ∀ x, (t * A x - B x) ^ 2 * w x =
        (t * t) * (A x ^ 2 * w x) + (-2 * t) * (A x * B x * w x) + B x ^ 2 * w x := by
      intro x; ring
    have hint : ∫ x, (t * A x - B x) ^ 2 * w x ∂μ =
        a * (t * t) + (-2 * b) * t + c := by
      have i1 : Integrable (fun x => (t * t) * (A x ^ 2 * w x)) μ := hAA.const_mul _
      have i2 : Integrable (fun x => (-2 * t) * (A x * B x * w x)) μ := hAB.const_mul _
      have i12 : Integrable
          (fun x => (t * t) * (A x ^ 2 * w x) + (-2 * t) * (A x * B x * w x)) μ := i1.add i2
      simp_rw [hexp]
      rw [integral_add i12 hBB, integral_add i1 i2, integral_const_mul,
        integral_const_mul]
      ring
    rw [← hint]
    exact integral_nonneg_of_ae (hw.mono fun x hx => mul_nonneg (sq_nonneg _) hx)
  have hd := discrim_le_zero key
  rw [discrim] at hd
  nlinarith [hd]

/-- Continuous functions on `[a,b]²` are integrable for the product of the restricted measures. -/
theorem integrable_prod_Icc {a b : ℝ} {F : ℝ × ℝ → ℂ} (hF : ContinuousOn F (Icc a b ×ˢ Icc a b)) :
    Integrable F ((volume.restrict (Icc a b)).prod (volume.restrict (Icc a b))) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact hF.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

end NonUniqueEuler.EdgeH
