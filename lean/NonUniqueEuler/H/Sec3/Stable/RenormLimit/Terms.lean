import NonUniqueEuler.H.Sec3.Stable.RenormLimit.Basic
import NonUniqueEuler.Defs.Sec2.Spaces

/-!
# Helpers for `prop:stable`, step 3 (the limit is renormalized): the three error terms

Helper file of `P/Sec3/Stable/RenormLimit.lean` (`03_compactness.tex:802-815`).

* `integrable_renorm_mul`: if `a S ∈ L¹` and `|Υ(s)| ≤ L|s|`, `Υ(0) = 0`, then `Υ(a) S ∈ L¹`
  (measurability through `Υ(a) S = (Υ(a)/a)(a S)`).
* `lintegral_transport_sub_le`: the difference of two renormalized transport integrands over the
  slab is bounded by `LD (∫_{(0,T)×B_R}|a - b| + ∫|a||w - w'| + ∫|a - b||w'|)` when
  `supp φ ⊂ ℝ × B_R` (`03_compactness.tex:808-813`).
* `lintegral_prodSet_mul_le`: `∫_{I×s}|u||w| ≤ K ∫_I ‖w(t)‖_{L²(s)} dt` when
  `‖u(t)‖_{L²(s)} ≤ K` (Tonelli and Cauchy–Schwarz on slices; the first error term of the
  manuscript).
* `tendsto_lintegral_sub_mul`: `∫_{I×s}|uₙ - f||w| → 0` if `uₙ → f` in `L¹(I×s)`, with uniform
  `L²` bounds on the slices of `uₙ - f` and `w` (the second error term: weak `L²` convergence).
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace NonUniqueEuler.Compact.RenormLimitAux

open Weak

/-- `|x| ≤ c|y|` in `ℝ≥0∞` form. -/
theorem enorm_le_ofReal_mul_enorm {x y c : ℝ} (hc : 0 ≤ c) (h : |x| ≤ c * |y|) :
    ‖x‖ₑ ≤ ENNReal.ofReal c * ‖y‖ₑ := by
  rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul hc]
  exact ENNReal.ofReal_le_ofReal h

/-- If `a S` is integrable, `a` is a.e. strongly measurable, `Υ` is continuous, `Υ(0) = 0` and
`|Υ(s)| ≤ L|s|`, then `Υ(a) S` is integrable. -/
theorem integrable_renorm_mul {α : Type*} [MeasurableSpace α] {μ : Measure α} {Υ : ℝ → ℝ}
    (hΥc : Continuous Υ) (hΥ0 : Υ 0 = 0) {L : ℝ} (hlin : ∀ s, |Υ s| ≤ L * |s|) {a S : α → ℝ}
    (ha : AEStronglyMeasurable a μ) (h : Integrable (fun x => a x * S x) μ) :
    Integrable (fun x => Υ (a x) * S x) μ := by
  have heq : (fun x => Υ (a x) / a x * (a x * S x)) = fun x => Υ (a x) * S x := by
    funext x
    by_cases hx : a x = 0
    · simp [hx, hΥ0]
    · field_simp
  have hm : AEStronglyMeasurable (fun x => Υ (a x) / a x * (a x * S x)) μ :=
    (((hΥc.comp_aestronglyMeasurable ha).aemeasurable.div ha.aemeasurable).aestronglyMeasurable).mul
      h.aestronglyMeasurable
  rw [heq] at hm
  refine Integrable.mono' (h.norm.const_mul L) hm (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs, abs_mul]
  calc |Υ (a x)| * |S x| ≤ (L * |a x|) * |S x| :=
        mul_le_mul_of_nonneg_right (hlin _) (abs_nonneg _)
    _ = L * (|a x| * |S x|) := by ring

/-- **The pointwise estimate, integrated.** For `φ ∈ 𝒟_T` with `supp φ ⊂ ℝ × B_R` and
`‖Dφ‖ ≤ D`, the difference of the renormalized transport integrands of `(a, w)` and `(b, w')`
is bounded on the slab by
`LD (∫_{(0,T)×B_R}|a - b| + ∫_{(0,T)×B_R}|a||w - w'| + ∫_{(0,T)×B_R}|a - b||w'|)`. -/
theorem lintegral_transport_sub_le {T R L D : ℝ} {Υ : ℝ → ℝ} (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hlip : ∀ a b, |Υ a - Υ b| ≤ L * |a - b|) (hlin : ∀ s, |Υ s| ≤ L * |s|)
    {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) (hDφ : ∀ p, ‖fderiv ℝ φ p‖ ≤ D)
    (hR : ∀ p ∈ tsupport φ, p.2 ∈ ball (0 : ℂ) R)
    {a b : ℝ → ℂ → ℝ} {w w' : ℝ → ℂ → ℂ}
    (ha : AEStronglyMeasurable (Function.uncurry a)
      (volume.restrict (Ioo (0 : ℝ) T ×ˢ ball (0 : ℂ) R)))
    (hb : AEStronglyMeasurable (Function.uncurry b)
      (volume.restrict (Ioo (0 : ℝ) T ×ˢ ball (0 : ℂ) R)))
    (hw' : AEStronglyMeasurable (Function.uncurry w')
      (volume.restrict (Ioo (0 : ℝ) T ×ˢ ball (0 : ℂ) R))) :
    ∫⁻ p in slab T, ‖transportIntegrand (fun t x => Υ (a t x)) w φ p -
        transportIntegrand (fun t x => Υ (b t x)) w' φ p‖ₑ ≤
      ENNReal.ofReal (L * D) *
        ((∫⁻ p in Ioo (0 : ℝ) T ×ˢ ball (0 : ℂ) R, ‖a p.1 p.2 - b p.1 p.2‖ₑ) +
          (∫⁻ p in Ioo (0 : ℝ) T ×ˢ ball (0 : ℂ) R, ‖a p.1 p.2‖ₑ * ‖w p.1 p.2 - w' p.1 p.2‖ₑ) +
          ∫⁻ p in Ioo (0 : ℝ) T ×ˢ ball (0 : ℂ) R, ‖a p.1 p.2 - b p.1 p.2‖ₑ * ‖w' p.1 p.2‖ₑ) := by
  set S : Set (ℝ × ℂ) := Ioo (0 : ℝ) T ×ˢ ball (0 : ℂ) R with hS_def
  have hS : MeasurableSet S := measurableSet_Ioo.prod measurableSet_ball
  have hslab : MeasurableSet (slab T) := measurableSet_Ioo.prod MeasurableSet.univ
  set G : ℝ × ℂ → ℝ≥0∞ := fun p => ‖a p.1 p.2 - b p.1 p.2‖ₑ +
    ‖a p.1 p.2‖ₑ * ‖w p.1 p.2 - w' p.1 p.2‖ₑ + ‖a p.1 p.2 - b p.1 p.2‖ₑ * ‖w' p.1 p.2‖ₑ
    with hG_def
  have hpt : ∀ p ∈ slab T, ‖transportIntegrand (fun t x => Υ (a t x)) w φ p -
      transportIntegrand (fun t x => Υ (b t x)) w' φ p‖ₑ ≤
        S.indicator (fun p => ENNReal.ofReal (L * D) * G p) p := by
    intro p hp
    by_cases hps : p ∈ tsupport φ
    · have hpS : p ∈ S := ⟨hp.1, hR p hps⟩
      rw [indicator_of_mem hpS]
      exact enorm_renorm_integrand_sub_le hL hD hlip hlin (abs_timeDeriv_le hφ hDφ p.1 p.2)
        (fderiv ℝ (fun y => φ (p.1, y)) p.2) (norm_fderiv_slice_le hφ hD hDφ p.1 p.2) _ _ _ _
    · have hps' : (p.1, p.2) ∉ tsupport φ := by rwa [Prod.mk.eta]
      have h0 : ∀ v, timeDeriv φ p.1 p.2 + spaceDeriv φ p.1 p.2 v = 0 := fun v =>
        timeDeriv_add_spaceDeriv_eq_zero hφ hps' v
      simp only [transportIntegrand, h0, mul_zero, sub_self, enorm_zero]
      exact zero_le
  have hA : AEMeasurable (fun p : ℝ × ℂ => ‖a p.1 p.2 - b p.1 p.2‖ₑ) (volume.restrict S) :=
    (ha.sub hb).enorm
  have hC : AEMeasurable (fun p : ℝ × ℂ => ‖a p.1 p.2 - b p.1 p.2‖ₑ * ‖w' p.1 p.2‖ₑ)
      (volume.restrict S) :=
    (ha.sub hb).enorm.mul hw'.enorm
  calc _ ≤ ∫⁻ p in slab T, S.indicator (fun p => ENNReal.ofReal (L * D) * G p) p :=
        setLIntegral_mono' hslab hpt
    _ ≤ ∫⁻ p, S.indicator (fun p => ENNReal.ofReal (L * D) * G p) p :=
        setLIntegral_le_lintegral _ _
    _ = ∫⁻ p in S, ENNReal.ofReal (L * D) * G p := lintegral_indicator hS _
    _ = ENNReal.ofReal (L * D) * ∫⁻ p in S, G p :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := by
        congr 1
        rw [hG_def, lintegral_add_right' _ hC, lintegral_add_left' hA]

/-- **Cauchy–Schwarz on slices.** If `‖u(t)‖_{L²(s)} ≤ K` for a.e. `t ∈ I`, then
`∫_{I×s}|u||w| ≤ K ‖w‖_{L¹(I;L²(s))}`. -/
theorem lintegral_prodSet_mul_le {I : Set ℝ} {s : Set ℂ} {u : ℝ → ℂ → ℝ} {w : ℝ → ℂ → ℂ}
    {K : ℝ≥0∞} (hK : K ≠ ∞)
    (hu : ∀ᵐ t ∂(volume.restrict I), AEStronglyMeasurable (u t) (volume.restrict s) ∧
        eLpNorm (u t) 2 (volume.restrict s) ≤ K)
    (hw : ∀ᵐ t ∂(volume.restrict I), AEStronglyMeasurable (w t) (volume.restrict s)) :
    ∫⁻ p in I ×ˢ s, ‖u p.1 p.2‖ₑ * ‖w p.1 p.2‖ₑ ≤ K * bochnerNorm 1 2 I s w := by
  refine (lintegral_prodSet_le I s (fun p => ‖u p.1 p.2‖ₑ * ‖w p.1 p.2‖ₑ)).trans ?_
  rw [bochnerNorm, eLpNorm_one_eq_lintegral_enorm, ← lintegral_const_mul' K _ hK]
  refine lintegral_mono_ae ?_
  filter_upwards [hu, hw] with t ⟨hut, hKt⟩ hwt
  rw [enorm_eq_self]
  calc ∫⁻ x in s, ‖u t x‖ₑ * ‖w t x‖ₑ ≤
        eLpNorm (u t) 2 (volume.restrict s) * eLpNorm (w t) 2 (volume.restrict s) :=
        lintegral_enorm_mul_le hut hwt
    _ ≤ K * eLpNorm (w t) 2 (volume.restrict s) := by gcongr

/-- **`L²` bound on a product set.** If `‖u(t)‖_{L²(s)} ≤ K` for a.e. `t ∈ I`, then
`∫_{I×s}|u|² ≤ |I| K²`. -/
theorem lintegral_prodSet_sq_le {E : Type*} [NormedAddCommGroup E] {I : Set ℝ} {s : Set ℂ}
    {u : ℝ → ℂ → E} {K : ℝ≥0∞}
    (hu : ∀ᵐ t ∂(volume.restrict I), eLpNorm (u t) 2 (volume.restrict s) ≤ K) :
    ∫⁻ p in I ×ˢ s, ‖u p.1 p.2‖ₑ ^ (2 : ℝ) ≤ volume I * K ^ (2 : ℝ) := by
  refine (lintegral_prodSet_le I s (fun p => ‖u p.1 p.2‖ₑ ^ (2 : ℝ))).trans ?_
  calc ∫⁻ t in I, ∫⁻ x in s, ‖u t x‖ₑ ^ (2 : ℝ) =
        ∫⁻ t in I, eLpNorm (u t) 2 (volume.restrict s) ^ (2 : ℝ) :=
        lintegral_congr fun t => lintegral_enorm_rpow_two (u t)
    _ ≤ ∫⁻ _ in I, K ^ (2 : ℝ) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hu] with t ht
        gcongr
    _ = volume I * K ^ (2 : ℝ) := by rw [setLIntegral_const, mul_comm]

/-- **Weak `L²` convergence on a product set.** If `uₙ → f` in `L¹(I × s)`, `|I| < ∞`,
`‖uₙ(t) - f(t)‖_{L²(s)} ≤ K` and `‖w(t)‖_{L²(s)} ≤ K_w` for a.e. `t ∈ I`, then
`∫_{I×s}|uₙ - f||w| → 0`. -/
theorem tendsto_lintegral_sub_mul {I : Set ℝ} {s : Set ℂ} (hI : volume I ≠ ∞)
    {u : ℕ → ℝ → ℂ → ℝ} {f : ℝ → ℂ → ℝ} {w : ℝ → ℂ → ℂ} {K Kw : ℝ≥0∞} (hK : K ≠ ∞)
    (hKw : Kw ≠ ∞)
    (hu : ∀ n, AEStronglyMeasurable (Function.uncurry (u n)) (volume.restrict (I ×ˢ s)))
    (hf : AEStronglyMeasurable (Function.uncurry f) (volume.restrict (I ×ˢ s)))
    (hw : AEStronglyMeasurable (Function.uncurry w) (volume.restrict (I ×ˢ s)))
    (hL1 : Tendsto (fun n => ∫⁻ p in I ×ˢ s, ‖u n p.1 p.2 - f p.1 p.2‖ₑ) atTop (𝓝 0))
    (hu2 : ∀ n, ∀ᵐ t ∂(volume.restrict I),
      eLpNorm (fun x => u n t x - f t x) 2 (volume.restrict s) ≤ K)
    (hw2 : ∀ᵐ t ∂(volume.restrict I), eLpNorm (w t) 2 (volume.restrict s) ≤ Kw) :
    Tendsto (fun n => ∫⁻ p in I ×ˢ s, ‖u n p.1 p.2 - f p.1 p.2‖ₑ * ‖w p.1 p.2‖ₑ) atTop
      (𝓝 0) := by
  have hC : volume I * K ^ (2 : ℝ) ≠ ∞ :=
    ENNReal.mul_ne_top hI (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hK)
  refine tendsto_lintegral_mul_of_L1_L2 (C := volume I * K ^ (2 : ℝ)) hC
    (fun n => ((hu n).sub hf).enorm) hw.enorm hL1 (fun n => ?_) ?_
  · exact lintegral_prodSet_sq_le (u := fun t x => u n t x - f t x) (hu2 n)
  · refine ne_top_of_le_ne_top ?_ (lintegral_prodSet_sq_le (u := w) hw2)
    exact ENNReal.mul_ne_top hI (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hKw)

end NonUniqueEuler.Compact.RenormLimitAux
