import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Prod
import NonUniqueEuler.Defs.Infra.Sobolev

/-!
# Helper for `P/Infra/Sobolev/EmbedL4`: the Ladyzhenskaya inequality for `C¹_c` functions

Manuscript `02_prelim.tex:613-620`, proof of (E1), first part ("Let first `g ∈ C_c^∞`").

* `sq_enorm_le_lintegral`: the one-dimensional bound `|f(s)|² ≤ ∫_ℝ 2 |f| |f'|`
  (fundamental theorem of calculus on `(-∞, s]` for `|f|²`, and `|(|f|²)'| ≤ 2 |f| |f'|`);
* `lintegral_enorm_pow_four_le`: `∫ |φ|⁴ ≤ (2 ∫ |φ||∂₂φ|) (2 ∫ |φ||∂₁φ|)` (Tonelli on
  `ℂ ≃ ℝ × ℝ`);
* `lintegral_enorm_pow_four_le_ofReal`: with Cauchy–Schwarz,
  `∫ |φ|⁴ ≤ 4 ‖φ‖₂² ‖∂₁φ‖₂ ‖∂₂φ‖₂ ≤ 2 ‖φ‖₂² (‖∂₁φ‖₂² + ‖∂₂φ‖₂²)`.
-/

noncomputable section

open MeasureTheory Set Filter Complex
open scoped ENNReal Topology ContDiff

namespace NonUniqueEuler.Sob.EmbedL4H

/-- `‖2 ⟪a, b⟫‖ₑ ≤ 2 ‖a‖ₑ ‖b‖ₑ`. -/
theorem enorm_two_inner_le (a b : ℂ) :
    ‖(2 : ℝ) * inner ℝ a b‖ₑ ≤ 2 * ‖a‖ₑ * ‖b‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm]
  have h1 : ‖(2 : ℝ) * inner ℝ a b‖ ≤ 2 * ‖a‖ * ‖b‖ := by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_two, mul_assoc]
    exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm a b) (by norm_num)
  calc ENNReal.ofReal ‖(2 : ℝ) * inner ℝ a b‖ ≤ ENNReal.ofReal (2 * ‖a‖ * ‖b‖) :=
        ENNReal.ofReal_le_ofReal h1
    _ = 2 * ENNReal.ofReal ‖a‖ * ENNReal.ofReal ‖b‖ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
        simp

/-- One-dimensional bound: for `f : ℝ → ℂ` with continuous derivative `f'`, vanishing for
`|r| > R`, `|f(s)|² ≤ ∫_ℝ 2 |f| |f'|`. -/
theorem sq_enorm_le_lintegral {f f' : ℝ → ℂ} (hd : ∀ r, HasDerivAt f (f' r) r)
    (hf' : Continuous f') {R : ℝ} (hR : ∀ r, R < |r| → f r = 0) (s : ℝ) :
    ‖f s‖ₑ ^ 2 ≤ ∫⁻ r, 2 * ‖f r‖ₑ * ‖f' r‖ₑ := by
  set u' : ℝ → ℝ := fun r => 2 * inner ℝ (f r) (f' r) with hu'_def
  have hu : ∀ r, HasDerivAt (fun r => ‖f r‖ ^ 2) (u' r) r := fun r => (hd r).norm_sq
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun r => (hd r).continuousAt
  have hu'c : Continuous u' := continuous_const.mul (hfc.inner hf')
  have hu'supp : HasCompactSupport u' := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) fun r hr => ?_
    have hr' : R < |r| := by
      simp only [mem_Icc, not_and_or, not_le] at hr
      rcases hr with h | h
      · exact lt_abs.2 (Or.inr (by linarith))
      · exact lt_abs.2 (Or.inl h)
    simp [u', hR r hr']
  have hint : Integrable u' := hu'c.integrable_of_hasCompactSupport hu'supp
  have htend : Tendsto (fun r => ‖f r‖ ^ 2) atBot (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_lt_atBot (-|R| - 1)] with r hr
    have : R < |r| := by
      have h1 : R ≤ |R| := le_abs_self R
      have h2 : -r ≤ |r| := neg_le_abs r
      linarith
    simp [hR r this]
  have hFTC := integral_Iic_of_hasDerivAt_of_tendsto (hu s).continuousAt.continuousWithinAt
    (fun r _ => hu r) hint.integrableOn htend
  calc ‖f s‖ₑ ^ 2 = ‖(‖f s‖ ^ 2 : ℝ)‖ₑ := by rw [enorm_pow, enorm_norm]
    _ = ‖∫ r in Iic s, u' r‖ₑ := by rw [hFTC, sub_zero]
    _ ≤ ∫⁻ r in Iic s, ‖u' r‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ r, ‖u' r‖ₑ := setLIntegral_le_lintegral _ _
    _ ≤ ∫⁻ r, 2 * ‖f r‖ₑ * ‖f' r‖ₑ := lintegral_mono fun r => enorm_two_inner_le _ _


/-- A compactly supported function vanishes outside some ball. -/
theorem exists_eq_zero_of_lt_norm {φ : ℂ → ℂ} (hc : HasCompactSupport φ) :
    ∃ R : ℝ, ∀ z : ℂ, R < ‖z‖ → φ z = 0 := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
  refine ⟨R, fun z hz => image_eq_zero_of_notMem_tsupport fun hmem => ?_⟩
  have := hR hmem
  rw [Metric.mem_closedBall, dist_zero_right] at this
  linarith

/-- Transport of lower integrals along `ℂ ≃ ℝ × ℝ`. -/
theorem lintegral_complex_eq_prod (G : ℂ → ℝ≥0∞) :
    ∫⁻ z, G z = ∫⁻ p : ℝ × ℝ, G (p.1 + p.2 * I) := by
  have h := (MeasurePreserving.symm _ Complex.volume_preserving_equiv_real_prod).lintegral_comp_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding G
  rw [← h]
  refine lintegral_congr fun p => ?_
  simp [Complex.mk_eq_add_mul_I]

theorem partialD_one_zero (φ : ℂ → ℂ) (z : ℂ) : partialD (1, 0) φ z = fderiv ℝ φ z 1 := by
  simp [partialD, pdList, iterDirDeriv, dirDeriv]

theorem partialD_zero_one (φ : ℂ → ℂ) (z : ℂ) : partialD (0, 1) φ z = fderiv ℝ φ z I := by
  simp [partialD, pdList, iterDirDeriv, dirDeriv]

/-- Tonelli step of (E1): `∫ |φ|⁴ ≤ (∫ 2 |φ||∂₂φ|) (∫ 2 |φ||∂₁φ|)` for `φ ∈ C¹_c`. -/
theorem lintegral_enorm_pow_four_le {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    ∫⁻ z, ‖φ z‖ₑ ^ 4 ≤ (∫⁻ z, 2 * ‖φ z‖ₑ * ‖partialD (0, 1) φ z‖ₑ) *
      (∫⁻ z, 2 * ‖φ z‖ₑ * ‖partialD (1, 0) φ z‖ₑ) := by
  obtain ⟨R, hR⟩ := exists_eq_zero_of_lt_norm hc
  have hdiff : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hcd : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  set F : ℝ × ℝ → ℝ≥0∞ := fun p => ‖φ (p.1 + p.2 * I)‖ₑ with hF
  set D₁ : ℝ × ℝ → ℝ≥0∞ := fun p => ‖fderiv ℝ φ (p.1 + p.2 * I) 1‖ₑ with hD₁
  set D₂ : ℝ × ℝ → ℝ≥0∞ := fun p => ‖fderiv ℝ φ (p.1 + p.2 * I) I‖ₑ with hD₂
  have hemb : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) + p.2 * I := by fun_prop
  have hFm : Measurable F := (hφ.continuous.comp hemb).enorm.measurable
  have hD₁m : Measurable D₁ :=
    ((hcd.comp hemb).clm_apply continuous_const).enorm.measurable
  have hD₂m : Measurable D₂ :=
    ((hcd.comp hemb).clm_apply continuous_const).enorm.measurable
  set G₁ : ℝ × ℝ → ℝ≥0∞ := fun p => 2 * F p * D₁ p with hG₁
  set G₂ : ℝ × ℝ → ℝ≥0∞ := fun p => 2 * F p * D₂ p with hG₂
  have hG₁m : Measurable G₁ := (measurable_const.mul hFm).mul hD₁m
  have hG₂m : Measurable G₂ := (measurable_const.mul hFm).mul hD₂m
  set A : ℝ → ℝ≥0∞ := fun t => ∫⁻ r, G₁ (r, t) with hA
  set B : ℝ → ℝ≥0∞ := fun s => ∫⁻ r, G₂ (s, r) with hB
  have hAm : Measurable A := hG₁m.lintegral_prod_left'
  have hBm : Measurable B := hG₂m.lintegral_prod_right'
  -- the two one-dimensional bounds
  have hA_le : ∀ s t : ℝ, F (s, t) ^ 2 ≤ A t := by
    intro s t
    have hd : ∀ r : ℝ, HasDerivAt (fun r : ℝ => φ (r + t * I)) (fderiv ℝ φ (r + t * I) 1) r := by
      intro r
      have h1 : HasDerivAt (fun r : ℝ => (r : ℂ) + t * I) 1 r := by
        simpa using ((hasDerivAt_id r).ofReal_comp).add_const ((t : ℂ) * I)
      exact (hdiff _).hasFDerivAt.comp_hasDerivAt r h1
    have hf' : Continuous fun r : ℝ => fderiv ℝ φ (r + t * I) 1 :=
      (hcd.comp (by fun_prop)).clm_apply continuous_const
    have hR' : ∀ r : ℝ, R < |r| → φ (r + t * I) = 0 := by
      intro r hr
      apply hR
      have := Complex.abs_re_le_norm ((r : ℂ) + t * I)
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero] at this
      linarith
    exact sq_enorm_le_lintegral hd hf' hR' s
  have hB_le : ∀ s t : ℝ, F (s, t) ^ 2 ≤ B s := by
    intro s t
    have hd : ∀ r : ℝ, HasDerivAt (fun r : ℝ => φ (s + r * I)) (fderiv ℝ φ (s + r * I) I) r := by
      intro r
      have h1 : HasDerivAt (fun r : ℝ => (s : ℂ) + r * I) I r := by
        simpa using (((hasDerivAt_id r).ofReal_comp).mul_const I).const_add (s : ℂ)
      exact (hdiff _).hasFDerivAt.comp_hasDerivAt r h1
    have hf' : Continuous fun r : ℝ => fderiv ℝ φ (s + r * I) I :=
      (hcd.comp (by fun_prop)).clm_apply continuous_const
    have hR' : ∀ r : ℝ, R < |r| → φ (s + r * I) = 0 := by
      intro r hr
      apply hR
      have := Complex.abs_im_le_norm ((s : ℂ) + r * I)
      simp only [add_im, ofReal_im, mul_im, I_re, mul_zero, ofReal_re, I_im, mul_one,
        zero_add, add_zero] at this
      linarith
    exact sq_enorm_le_lintegral hd hf' hR' t
  have hpt : ∀ s t : ℝ, F (s, t) ^ 4 ≤ B s * A t := by
    intro s t
    calc F (s, t) ^ 4 = F (s, t) ^ 2 * F (s, t) ^ 2 := by ring
      _ ≤ B s * A t := mul_le_mul' (hB_le s t) (hA_le s t)
  have h4 : ∫⁻ z, ‖φ z‖ₑ ^ 4 = ∫⁻ p : ℝ × ℝ, F p ^ 4 := lintegral_complex_eq_prod _
  have hI₁ : ∫⁻ z, 2 * ‖φ z‖ₑ * ‖partialD (1, 0) φ z‖ₑ = ∫⁻ t, A t := by
    have : ∫⁻ z, 2 * ‖φ z‖ₑ * ‖partialD (1, 0) φ z‖ₑ = ∫⁻ p, G₁ p := by
      rw [lintegral_complex_eq_prod]
      simp only [partialD_one_zero]
      rfl
    rw [this, Measure.volume_eq_prod, lintegral_prod_symm _ hG₁m.aemeasurable]
  have hI₂ : ∫⁻ z, 2 * ‖φ z‖ₑ * ‖partialD (0, 1) φ z‖ₑ = ∫⁻ s, B s := by
    have : ∫⁻ z, 2 * ‖φ z‖ₑ * ‖partialD (0, 1) φ z‖ₑ = ∫⁻ p, G₂ p := by
      rw [lintegral_complex_eq_prod]
      simp only [partialD_zero_one]
      rfl
    rw [this, Measure.volume_eq_prod, lintegral_prod _ hG₂m.aemeasurable]
  rw [h4, hI₁, hI₂, Measure.volume_eq_prod, lintegral_prod _ (hFm.pow_const 4).aemeasurable]
  calc ∫⁻ s, ∫⁻ t, F (s, t) ^ 4 ≤ ∫⁻ s, ∫⁻ t, B s * A t :=
        lintegral_mono fun s => lintegral_mono fun t => hpt s t
    _ = ∫⁻ s, B s * ∫⁻ t, A t := by
        refine lintegral_congr fun s => ?_
        exact lintegral_const_mul _ hAm
    _ = (∫⁻ s, B s) * ∫⁻ t, A t := lintegral_mul_const _ hBm


/-- Cauchy–Schwarz: `∫ |φ| |ψ| ≤ ‖φ‖₂ ‖ψ‖₂`. -/
theorem lintegral_enorm_mul_le {φ ψ : ℂ → ℂ} (hφ : AEStronglyMeasurable φ volume)
    (hψ : AEStronglyMeasurable ψ volume) :
    ∫⁻ z, ‖φ z‖ₑ * ‖ψ z‖ₑ ≤ eLpNorm φ 2 volume * eLpNorm ψ 2 volume := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two
    hφ.enorm hψ.enorm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simpa using h

/-- The Ladyzhenskaya inequality for `φ ∈ C¹_c`:
`∫ |φ|⁴ ≤ 2 ‖φ‖₂² (‖∂₁φ‖₂² + ‖∂₂φ‖₂²)` (`02_prelim.tex:613-620`). -/
theorem lintegral_enorm_pow_four_le_ofReal {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) :
    ∫⁻ z, ‖φ z‖ₑ ^ 4 ≤ ENNReal.ofReal (2 * l2 φ ^ 2 *
      (l2 (partialD (1, 0) φ) ^ 2 + l2 (partialD (0, 1) φ) ^ 2)) := by
  have hcd : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  have hc₁ : Continuous (partialD (1, 0) φ) := by
    have : partialD (1, 0) φ = fun z => fderiv ℝ φ z 1 := funext (partialD_one_zero φ)
    rw [this]; exact hcd.clm_apply continuous_const
  have hc₂ : Continuous (partialD (0, 1) φ) := by
    have : partialD (0, 1) φ = fun z => fderiv ℝ φ z I := funext (partialD_zero_one φ)
    rw [this]; exact hcd.clm_apply continuous_const
  have hs₁ : HasCompactSupport (partialD (1, 0) φ) := by
    have : partialD (1, 0) φ = fun z => fderiv ℝ φ z 1 := funext (partialD_one_zero φ)
    rw [this]; exact (hc.fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] ℂ => L 1) (by simp)
  have hs₂ : HasCompactSupport (partialD (0, 1) φ) := by
    have : partialD (0, 1) φ = fun z => fderiv ℝ φ z I := funext (partialD_zero_one φ)
    rw [this]; exact (hc.fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] ℂ => L I) (by simp)
  have hL : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hc
  have hL₁ : MemLp (partialD (1, 0) φ) 2 volume := hc₁.memLp_of_hasCompactSupport hs₁
  have hL₂ : MemLp (partialD (0, 1) φ) 2 volume := hc₂.memLp_of_hasCompactSupport hs₂
  set a := l2 φ with ha
  set b := l2 (partialD (1, 0) φ) with hb
  set c := l2 (partialD (0, 1) φ) with hc'
  have ha0 : 0 ≤ a := l2_nonneg _
  have hb0 : 0 ≤ b := l2_nonneg _
  have hc0 : 0 ≤ c := l2_nonneg _
  have ea : eLpNorm φ 2 volume = ENNReal.ofReal a := (ENNReal.ofReal_toReal hL.eLpNorm_ne_top).symm
  have eb : eLpNorm (partialD (1, 0) φ) 2 volume = ENNReal.ofReal b :=
    (ENNReal.ofReal_toReal hL₁.eLpNorm_ne_top).symm
  have ec : eLpNorm (partialD (0, 1) φ) 2 volume = ENNReal.ofReal c :=
    (ENNReal.ofReal_toReal hL₂.eLpNorm_ne_top).symm
  have h₁ : ∫⁻ z, 2 * ‖φ z‖ₑ * ‖partialD (1, 0) φ z‖ₑ ≤ ENNReal.ofReal (2 * (a * b)) := by
    simp_rw [mul_assoc]
    rw [lintegral_const_mul' _ _ (by simp), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_mul ha0, ← ea, ← eb]
    rw [ENNReal.ofReal_ofNat]
    gcongr
    exact lintegral_enorm_mul_le hL.1 hL₁.1
  have h₂ : ∫⁻ z, 2 * ‖φ z‖ₑ * ‖partialD (0, 1) φ z‖ₑ ≤ ENNReal.ofReal (2 * (a * c)) := by
    simp_rw [mul_assoc]
    rw [lintegral_const_mul' _ _ (by simp), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_mul ha0, ← ea, ← ec]
    rw [ENNReal.ofReal_ofNat]
    gcongr
    exact lintegral_enorm_mul_le hL.1 hL₂.1
  calc ∫⁻ z, ‖φ z‖ₑ ^ 4
      ≤ (∫⁻ z, 2 * ‖φ z‖ₑ * ‖partialD (0, 1) φ z‖ₑ) *
          (∫⁻ z, 2 * ‖φ z‖ₑ * ‖partialD (1, 0) φ z‖ₑ) := lintegral_enorm_pow_four_le hφ hc
    _ ≤ ENNReal.ofReal (2 * (a * c)) * ENNReal.ofReal (2 * (a * b)) := mul_le_mul' h₂ h₁
    _ = ENNReal.ofReal (2 * (a * c) * (2 * (a * b))) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ ENNReal.ofReal (2 * a ^ 2 * (b ^ 2 + c ^ 2)) := by
        apply ENNReal.ofReal_le_ofReal
        nlinarith [mul_nonneg (sq_nonneg a) (sq_nonneg (b - c))]

end NonUniqueEuler.Sob.EmbedL4H
