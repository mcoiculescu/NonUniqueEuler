import NonUniqueEuler.H.Sec3.Transport.Mollified.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Helper for `P/Sec3/Transport/Mollified`: measurability and bounds of the mollified objects

With `U(t,x) = u(t) ⋆ ρ_ε (x)` (`mollify`), `D = (div(wu)) ⋆ ρ_ε` (`mollifyDiv`) and
`G = w·∇(u ⋆ ρ_ε)` (`dotGradMollify`):

* `exists_stronglyMeasurable_param_integral`: a parametric integral
  `(t,x) ↦ ∫ B(x - y, f(t,y)) dy` with `B` continuous and `f` a.e. strongly measurable on
  `μ ⊗ volume` agrees, for `μ`-a.e. `t` and every `x`, with a strongly measurable function
  (the same integral of a strongly measurable representative of `f`).
* Joint (`μ ⊗ volume`) and slice-wise (`t ↦ ·` for each fixed `x`) a.e. strong measurability of
  `U`, `D` and of the `ℂ →L[ℝ] ℝ`-valued `A(t,x) = ∫ u(t,y) Dρ_ε(x-y) dy`; joint measurability of
  `G(t,x) = A(t,x)(w(t,x))` (`dotGradMollify_eq_clm`).
* Pointwise bounds: `|U| ≤ C_ρ ‖u(t)‖₁`, `|D| ≤ C_D ‖u(t)w(t)‖₁`, `|G| ≤ C_D ‖u(t)‖₁ |w(t,x)|`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace NonUniqueEuler.Weak.MollifiedH

/-! ### Parametric integrals -/

section Param

variable {F E : Type*} [NormedAddCommGroup F] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A parametric convolution-type integral of an a.e. strongly measurable function agrees with a
strongly measurable function for a.e. time and every point. -/
theorem exists_stronglyMeasurable_param_integral {μ : Measure ℝ} [SFinite μ] {f : ℝ → ℂ → F}
    (hf : AEStronglyMeasurable (Function.uncurry f) (μ.prod volume)) {B : ℂ × F → E}
    (hB : Continuous B) :
    ∃ g : ℝ × ℂ → E, StronglyMeasurable g ∧
      ∀ᵐ t ∂μ, ∀ x, g (t, x) = ∫ y, B (x - y, f t y) := by
  set f' := hf.mk (Function.uncurry f)
  have hf' : StronglyMeasurable f' := hf.stronglyMeasurable_mk
  have hae : ∀ᵐ t ∂μ, f t =ᵐ[volume] fun y => f' (t, y) :=
    Measure.ae_ae_eq_curry_of_prod hf.ae_eq_mk
  refine ⟨fun p => ∫ y, B (p.2 - y, f' (p.1, y)), ?_, ?_⟩
  · refine StronglyMeasurable.integral_prod_right'
      (f := fun q : (ℝ × ℂ) × ℂ => B (q.1.2 - q.2, f' (q.1.1, q.2))) ?_
    refine hB.comp_stronglyMeasurable (StronglyMeasurable.prodMk ?_ ?_)
    · exact (continuous_snd.comp continuous_fst |>.sub continuous_snd).stronglyMeasurable
    · exact hf'.comp_measurable ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  · filter_upwards [hae] with t ht x
    refine integral_congr_ae ?_
    filter_upwards [ht] with y hy
    simp only [hy]

/-- Joint a.e. strong measurability of a parametric integral. -/
theorem aestronglyMeasurable_param_integral {μ : Measure ℝ} [SFinite μ] {f : ℝ → ℂ → F}
    (hf : AEStronglyMeasurable (Function.uncurry f) (μ.prod volume)) {B : ℂ × F → E}
    (hB : Continuous B) :
    AEStronglyMeasurable (fun p : ℝ × ℂ => ∫ y, B (p.2 - y, f p.1 y)) (μ.prod volume) := by
  obtain ⟨g, hg, hae⟩ := exists_stronglyMeasurable_param_integral hf hB
  refine hg.aestronglyMeasurable.congr ?_
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hae] with p hp
  exact hp p.2

/-- Slice-wise a.e. strong measurability of a parametric integral, at every point. -/
theorem aestronglyMeasurable_param_integral_slice {μ : Measure ℝ} [SFinite μ] {f : ℝ → ℂ → F}
    (hf : AEStronglyMeasurable (Function.uncurry f) (μ.prod volume)) {B : ℂ × F → E}
    (hB : Continuous B) (x : ℂ) :
    AEStronglyMeasurable (fun t => ∫ y, B (x - y, f t y)) μ := by
  obtain ⟨g, hg, hae⟩ := exists_stronglyMeasurable_param_integral hf hB
  have hm : Measurable fun t : ℝ => (t, x) := measurable_id.prodMk measurable_const
  refine (hg.comp_measurable hm).aestronglyMeasurable.congr ?_
  filter_upwards [hae] with t ht
  exact ht x

end Param

/-! ### The mollified objects -/

section Objects

variable {ρ : ℂ → ℝ} {ε : ℝ} {μ : Measure ℝ} [SFinite μ]

theorem continuous_mollify_kernel (hρ : IsMollifier ρ) (ε : ℝ) :
    Continuous (fun q : ℂ × ℝ => q.2 * scaled ρ ε q.1) :=
  continuous_snd.mul ((continuous_scaled hρ ε).comp continuous_fst)

theorem continuous_div_kernel (hρ : IsMollifier ρ) (ε : ℝ) :
    Continuous (fun q : ℂ × ℂ => fderiv ℝ (scaled ρ ε) q.1 q.2) :=
  ((continuous_fderiv_scaled hρ ε).comp continuous_fst).clm_apply continuous_snd

theorem continuous_clm_kernel (hρ : IsMollifier ρ) (ε : ℝ) :
    Continuous (fun q : ℂ × ℝ => q.2 • fderiv ℝ (scaled ρ ε) q.1) :=
  continuous_snd.smul ((continuous_fderiv_scaled hρ ε).comp continuous_fst)

/-- `(div(wu)) ⋆ ρ_ε` as the integral of `Dρ_ε(x-y)` applied to `u(t,y) w(t,y)`. -/
theorem mollifyDiv_eq (u : ℝ → ℂ → ℝ) (w : ℝ → ℂ → ℂ) (t : ℝ) (x : ℂ) :
    mollifyDiv ρ ε u w t x = ∫ y, fderiv ℝ (scaled ρ ε) (x - y) (u t y • w t y) := by
  unfold mollifyDiv
  congr 1
  funext y
  rw [map_smul, smul_eq_mul]

theorem aestronglyMeasurable_mollify (hρ : IsMollifier ρ) {u : ℝ → ℂ → ℝ}
    (hu : AEStronglyMeasurable (Function.uncurry u) (μ.prod volume)) :
    AEStronglyMeasurable (fun p : ℝ × ℂ => mollify ρ ε (u p.1) p.2) (μ.prod volume) :=
  aestronglyMeasurable_param_integral hu (continuous_mollify_kernel hρ ε)

theorem aestronglyMeasurable_mollify_slice (hρ : IsMollifier ρ) {u : ℝ → ℂ → ℝ}
    (hu : AEStronglyMeasurable (Function.uncurry u) (μ.prod volume)) (x : ℂ) :
    AEStronglyMeasurable (fun t => mollify ρ ε (u t) x) μ :=
  aestronglyMeasurable_param_integral_slice hu (continuous_mollify_kernel hρ ε) x

theorem aestronglyMeasurable_mollifyDiv (hρ : IsMollifier ρ) {u : ℝ → ℂ → ℝ}
    {w : ℝ → ℂ → ℂ}
    (huw : AEStronglyMeasurable (fun p : ℝ × ℂ => u p.1 p.2 • w p.1 p.2) (μ.prod volume)) :
    AEStronglyMeasurable (fun p : ℝ × ℂ => mollifyDiv ρ ε u w p.1 p.2) (μ.prod volume) := by
  simp only [mollifyDiv_eq]
  exact aestronglyMeasurable_param_integral (f := fun t y => u t y • w t y) huw
    (continuous_div_kernel hρ ε)

theorem aestronglyMeasurable_mollifyDiv_slice (hρ : IsMollifier ρ) {u : ℝ → ℂ → ℝ}
    {w : ℝ → ℂ → ℂ}
    (huw : AEStronglyMeasurable (fun p : ℝ × ℂ => u p.1 p.2 • w p.1 p.2) (μ.prod volume))
    (x : ℂ) : AEStronglyMeasurable (fun t => mollifyDiv ρ ε u w t x) μ := by
  simp only [mollifyDiv_eq]
  exact aestronglyMeasurable_param_integral_slice (f := fun t y => u t y • w t y) huw
    (continuous_div_kernel hρ ε) x

/-- The `ℂ →L[ℝ] ℝ`-valued integral `A(t,x) = ∫ u(t,y) Dρ_ε(x-y) dy` is jointly measurable. -/
theorem aestronglyMeasurable_clm (hρ : IsMollifier ρ) {u : ℝ → ℂ → ℝ}
    (hu : AEStronglyMeasurable (Function.uncurry u) (μ.prod volume)) :
    AEStronglyMeasurable (fun p : ℝ × ℂ => ∫ y, u p.1 y • fderiv ℝ (scaled ρ ε) (p.2 - y))
      (μ.prod volume) :=
  aestronglyMeasurable_param_integral hu (continuous_clm_kernel hρ ε)

end Objects

/-! ### Pointwise bounds -/

section Bounds

variable {ρ : ℂ → ℝ} {ε : ℝ}

/-- `|g ⋆ ρ_ε (x)| ≤ C_ρ ‖g‖₁`. -/
theorem abs_mollify_le {g : ℂ → ℝ} (hg : Integrable g) {C : ℝ}
    (hC : ∀ z, |scaled ρ ε z| ≤ C) (x : ℂ) :
    |mollify ρ ε g x| ≤ C * ∫ y, |g y| := by
  rw [← integral_const_mul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le ((hg.norm.const_mul C).congr (ae_of_all _ fun y => ?_))
    (ae_of_all _ fun y => ?_)
  · simp [Real.norm_eq_abs]
  · rw [Real.norm_eq_abs, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hC _) (abs_nonneg _)

/-- `|∫ Dρ_ε(x-y)(h(y)) dy| ≤ C_D ‖h‖₁`. -/
theorem abs_integral_fderiv_le {h : ℂ → ℂ} (hh : Integrable h) {C : ℝ}
    (hC : ∀ z, ‖fderiv ℝ (scaled ρ ε) z‖ ≤ C) (x : ℂ) :
    |∫ y, fderiv ℝ (scaled ρ ε) (x - y) (h y)| ≤ C * ∫ y, ‖h y‖ := by
  rw [← integral_const_mul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (hh.norm.const_mul C) (ae_of_all _ fun y => ?_)
  exact ((fderiv ℝ (scaled ρ ε) (x - y)).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))

/-- `|(div(wu)) ⋆ ρ_ε (t,x)| ≤ C_D ‖u(t)w(t)‖₁`. -/
theorem abs_mollifyDiv_le {u : ℝ → ℂ → ℝ} {w : ℝ → ℂ → ℂ} {t : ℝ}
    (huw : Integrable (fun y => u t y • w t y)) {C : ℝ}
    (hC : ∀ z, ‖fderiv ℝ (scaled ρ ε) z‖ ≤ C) (x : ℂ) :
    |mollifyDiv ρ ε u w t x| ≤ C * ∫ y, ‖u t y • w t y‖ := by
  rw [mollifyDiv_eq]
  exact abs_integral_fderiv_le huw hC x

/-- `|w·∇(u ⋆ ρ_ε)(t,x)| ≤ C_D ‖u(t)‖₁ |w(t,x)|`. -/
theorem abs_dotGradMollify_le {u : ℝ → ℂ → ℝ} {w : ℝ → ℂ → ℂ} {t : ℝ}
    (hu : Integrable (u t)) {C : ℝ} (hC : ∀ z, ‖fderiv ℝ (scaled ρ ε) z‖ ≤ C) (x : ℂ) :
    |dotGradMollify ρ ε u w t x| ≤ C * (∫ y, |u t y|) * ‖w t x‖ := by
  unfold dotGradMollify
  rw [mul_assoc, mul_comm (∫ y, |u t y|), ← mul_assoc, ← integral_const_mul,
    ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (hu.norm.const_mul _) (ae_of_all _ fun y => ?_)
  simp only [Real.norm_eq_abs]
  rw [abs_mul]
  have h1 : |fderiv ℝ (scaled ρ ε) (x - y) (w t x)| ≤ C * ‖w t x‖ := by
    rw [← Real.norm_eq_abs]
    exact ((fderiv ℝ (scaled ρ ε) (x - y)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))
  calc |u t y| * |fderiv ℝ (scaled ρ ε) (x - y) (w t x)| ≤ |u t y| * (C * ‖w t x‖) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = C * ‖w t x‖ * |u t y| := by ring

/-- For `u(t) ∈ L¹`, `w·∇(u ⋆ ρ_ε)(t,x) = A(t,x)(w(t,x))` with the `ℂ →L[ℝ] ℝ`-valued integral
`A(t,x) = ∫ u(t,y) Dρ_ε(x-y) dy`. -/
theorem dotGradMollify_eq_clm (hρ : IsMollifier ρ) {u : ℝ → ℂ → ℝ} {w : ℝ → ℂ → ℂ} {t : ℝ}
    (hε : ε ≠ 0) (hu : Integrable (u t)) (x : ℂ) :
    dotGradMollify ρ ε u w t x =
      (∫ y, u t y • fderiv ℝ (scaled ρ ε) (x - y)) (w t x) := by
  obtain ⟨C, -, hC⟩ := exists_bound_fderiv_scaled hρ hε
  have hint : Integrable (fun y => u t y • fderiv ℝ (scaled ρ ε) (x - y)) := by
    refine (hu.norm.const_mul C).mono' ?_ (ae_of_all _ fun y => ?_)
    · exact hu.aestronglyMeasurable.smul
        ((continuous_fderiv_scaled hρ ε).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    · rw [norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
  rw [ContinuousLinearMap.integral_apply hint]
  unfold dotGradMollify
  congr 1

end Bounds

end NonUniqueEuler.Weak.MollifiedH
