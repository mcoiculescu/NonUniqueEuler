import NonUniqueEuler.Defs.Infra.Polar
import NonUniqueEuler.I.Infra.Polar.Power
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.Isometry

/-!
# Helpers for `P/Infra/Polar/LogLaplacian`: the weak derivative of `log‖·‖`

For `φ ∈ C¹_c(ℂ; ℝ)`:
* `integral_eq_integral_integral_horizontal`: Fubini on `ℂ ≅ ℝ × ℝ`, integrating first along
  horizontal lines;
* `integral_line`: on each horizontal line `{Im z = y}`, `y ≠ 0`, the function `log‖·‖` is smooth
  with `∂_x log‖z‖ = x/(x²+y²)`, and one-dimensional integration by parts gives
  `∫ log‖x+iy‖ ∂_xφ(x+iy) dx = -∫ x/(x²+y²) φ(x+iy) dx`;
* `integral_log_norm_mul_fderiv_one`: the direction `v = 1` (the line `y = 0` is a null set);
* `integral_log_norm_mul_fderiv_aux`: every direction `v`, by the rotation `z = e^{i arg v} w`
  (measure preserving) and `v = ‖v‖ e^{i arg v}`.

This is the manuscript's integration by parts of `lem:BS-basic`(d) (`02_prelim.tex:216-221`), done
on lines instead of on `{|z| > ε}` (restructuring R6); no boundary term arises since the line
`y = 0` is null. All proofs are complete.
-/

noncomputable section

open MeasureTheory Set Metric Real Filter Topology

namespace NonUniqueEuler.Polar.LogLaplacianH

/-- Fubini on `ℂ ≅ ℝ × ℝ`, integrating first along horizontal lines. -/
theorem integral_eq_integral_integral_horizontal {F : ℂ → ℝ} (hF : Integrable F) :
    ∫ z, F z = ∫ y : ℝ, ∫ x : ℝ, F ((x : ℂ) + y * Complex.I) := by
  have hmp : MeasurePreserving Complex.measurableEquivRealProd.symm volume volume :=
    Complex.volume_preserving_equiv_real_prod.symm
  rw [← hmp.integral_comp' F]
  have hint : Integrable (fun p : ℝ × ℝ => F (Complex.measurableEquivRealProd.symm p))
      ((volume : Measure ℝ).prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (hmp.integrable_comp_emb Complex.measurableEquivRealProd.symm.measurableEmbedding).2 hF
  rw [Measure.volume_eq_prod]
  rw [integral_prod_symm _ hint]
  refine congrArg _ (funext fun y => congrArg _ (funext fun x => ?_))
  simp [Complex.measurableEquivRealProd_symm_apply, Complex.mk_eq_add_mul_I]

theorem norm_add_mul_I_sq (x y : ℝ) : ‖(x : ℂ) + y * Complex.I‖ ^ 2 = x ^ 2 + y ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_add_mul_I]

theorem sq_add_sq_pos {y : ℝ} (hy : y ≠ 0) (x : ℝ) : 0 < x ^ 2 + y ^ 2 := by
  have := pow_pos (abs_pos.2 hy) 2
  rw [sq_abs] at this
  nlinarith [sq_nonneg x]

theorem hasDerivAt_log_norm_line {y : ℝ} (hy : y ≠ 0) (x : ℝ) :
    HasDerivAt (fun x : ℝ => Real.log ‖(x : ℂ) + y * Complex.I‖) (x / (x ^ 2 + y ^ 2)) x := by
  have heq : (fun x : ℝ => Real.log ‖(x : ℂ) + y * Complex.I‖)
      = fun x => Real.log (x ^ 2 + y ^ 2) / 2 := by
    funext x
    rw [Complex.norm_add_mul_I, Real.log_sqrt (sq_add_sq_pos hy x).le]
  rw [heq]
  have h1 : HasDerivAt (fun x : ℝ => x ^ 2 + y ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).add_const (y ^ 2)
  refine ((h1.log (sq_add_sq_pos hy x).ne').div_const 2).congr_deriv ?_
  field_simp

theorem hasDerivAt_line {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 1 ψ) (y x : ℝ) :
    HasDerivAt (fun x : ℝ => ψ ((x : ℂ) + y * Complex.I))
      (fderiv ℝ ψ ((x : ℂ) + y * Complex.I) 1) x := by
  have hγ : HasDerivAt (fun x : ℝ => (x : ℂ) + y * Complex.I) 1 x := by
    simpa using (hasDerivAt_id x).ofReal_comp.add_const ((y : ℂ) * Complex.I)
  exact ((hψ.differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt x hγ

/-- Integration by parts on a horizontal line `{Im z = y}`, `y ≠ 0`. -/
theorem integral_line {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) {y : ℝ}
    (hy : y ≠ 0) :
    ∫ x : ℝ, Real.log ‖(x : ℂ) + y * Complex.I‖ * fderiv ℝ ψ ((x : ℂ) + y * Complex.I) 1
      = -∫ x : ℝ, ((((x : ℂ) + y * Complex.I).re) / ‖(x : ℂ) + y * Complex.I‖ ^ 2)
          * ψ ((x : ℂ) + y * Complex.I) := by
  obtain ⟨M, hM⟩ : ∃ M, tsupport ψ ⊆ closedBall 0 M :=
    hc.isCompact.isBounded.subset_closedBall 0
  set b : ℝ := |M| + 1 with hb
  set a : ℝ := -b with ha
  have hab : a ≤ b := by rw [ha]; linarith [abs_nonneg M]
  have hvan : ∀ x : ℝ, b ≤ |x| → ((x : ℂ) + y * Complex.I) ∉ tsupport ψ := by
    intro x hx hmem
    have h1 := hM hmem
    rw [mem_closedBall, dist_zero_right] at h1
    have h2 : |x| ≤ ‖(x : ℂ) + y * Complex.I‖ := by
      simpa using Complex.abs_re_le_norm ((x : ℂ) + y * Complex.I)
    linarith [le_abs_self M]
  have hout : ∀ x : ℝ, x ∉ Ioc a b → b ≤ |x| := by
    intro x hx
    simp only [mem_Ioc, not_and_or, not_lt, not_le] at hx
    rcases hx with hx | hx
    · rw [ha] at hx
      rw [abs_of_neg (by linarith [abs_nonneg M])]
      linarith
    · rw [abs_of_pos (by linarith [abs_nonneg M])]
      linarith
  have hv0 : ∀ x : ℝ, b ≤ |x| → ψ ((x : ℂ) + y * Complex.I) = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (hvan x hx)
  have hdv0 : ∀ x : ℝ, b ≤ |x| → fderiv ℝ ψ ((x : ℂ) + y * Complex.I) = 0 := fun x hx =>
    fderiv_of_notMem_tsupport ℝ (hvan x hx)
  have eL : ∫ x : ℝ, Real.log ‖(x : ℂ) + y * Complex.I‖ * fderiv ℝ ψ ((x : ℂ) + y * Complex.I) 1
      = ∫ x in a..b, Real.log ‖(x : ℂ) + y * Complex.I‖
          * fderiv ℝ ψ ((x : ℂ) + y * Complex.I) 1 := by
    rw [intervalIntegral.integral_of_le hab, setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    rw [hdv0 x (hout x hx), _root_.zero_apply, mul_zero]
  have eR : ∫ x : ℝ, ((((x : ℂ) + y * Complex.I).re) / ‖(x : ℂ) + y * Complex.I‖ ^ 2)
          * ψ ((x : ℂ) + y * Complex.I)
      = ∫ x in a..b, ((((x : ℂ) + y * Complex.I).re) / ‖(x : ℂ) + y * Complex.I‖ ^ 2)
          * ψ ((x : ℂ) + y * Complex.I) := by
    rw [intervalIntegral.integral_of_le hab, setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    rw [hv0 x (hout x hx), mul_zero]
  rw [eL, eR]
  have hu' : Continuous fun x : ℝ => x / (x ^ 2 + y ^ 2) :=
    continuous_id.div (by fun_prop) fun x => (sq_add_sq_pos hy x).ne'
  have hv' : Continuous fun x : ℝ => fderiv ℝ ψ ((x : ℂ) + y * Complex.I) 1 :=
    ((hψ.continuous_fderiv one_ne_zero).comp (by fun_prop)).clm_apply continuous_const
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ => hasDerivAt_log_norm_line hy x) (fun x _ => hasDerivAt_line hψ y x)
    (hu'.intervalIntegrable _ _) (hv'.intervalIntegrable _ _)]
  have hba : b ≤ |a| := by rw [ha, abs_neg, abs_of_pos (by linarith [abs_nonneg M])]
  have hbb : b ≤ |b| := le_abs_self b
  rw [hv0 a hba, hv0 b hbb, mul_zero, mul_zero, sub_zero, zero_sub]
  congr 1
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [norm_add_mul_I_sq]
  simp

/-- `∫ (z.re/‖z‖²) ψ(z)` is absolutely convergent for continuous compactly supported `ψ`. -/
theorem integrable_re_div_mul {ψ : ℂ → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    Integrable (fun z : ℂ => (z.re / ‖z‖ ^ 2) * ψ z) := by
  have hI : Integrable (fun z : ℂ => ‖z‖ ^ (-1 : ℝ) * ψ z) := by
    have := (locallyIntegrable_norm_rpow (by norm_num : (-2 : ℝ) < -1)
      ).integrable_smul_right_of_hasCompactSupport hψ hc
    simpa only [smul_eq_mul] using this
  refine hI.mono ?_ ?_
  · exact ((Complex.continuous_re.measurable.div
      (continuous_norm.measurable.pow_const 2)).mul hψ.measurable).aestronglyMeasurable
  · refine Eventually.of_forall fun z => ?_
    have h1 : ‖z.re / ‖z‖ ^ 2‖ ≤ ‖z‖⁻¹ := by
      rcases eq_or_ne z 0 with rfl | hz
      · simp
      · have hz' : 0 < ‖z‖ := norm_pos_iff.2 hz
        rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖z‖ ^ 2),
          div_le_iff₀ (by positivity)]
        calc |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
          _ = ‖z‖⁻¹ * ‖z‖ ^ 2 := by field_simp
    have h2 : ‖‖z‖ ^ (-1 : ℝ)‖ = ‖z‖⁻¹ := by
      rw [Real.rpow_neg_one, Real.norm_eq_abs, abs_inv, abs_norm]
    rw [norm_mul, norm_mul, h2]
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)

/-- The weak derivative of `log‖·‖` in the direction `1`. -/
theorem integral_log_norm_mul_fderiv_one {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hc : HasCompactSupport ψ) :
    ∫ z, Real.log ‖z‖ * fderiv ℝ ψ z 1 = -∫ z, (z.re / ‖z‖ ^ 2) * ψ z := by
  have hint1 : Integrable (fun z => Real.log ‖z‖ * fderiv ℝ ψ z 1) := by
    have := locallyIntegrable_log_norm.integrable_smul_right_of_hasCompactSupport
      ((hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const) (hc.fderiv_apply (𝕜 := ℝ) 1)
    simpa only [smul_eq_mul] using this
  have hint2 := integrable_re_div_mul hψ.continuous hc
  rw [integral_eq_integral_integral_horizontal hint1,
    integral_eq_integral_integral_horizontal hint2, ← integral_neg]
  refine integral_congr_ae ?_
  have hae : ∀ᵐ y : ℝ, y ≠ 0 := by
    refine ae_iff.2 ?_
    simp
  filter_upwards [hae] with y hy
  exact integral_line hψ hc hy

/-- The weak derivative of `log‖·‖` in every direction `v`. -/
theorem integral_log_norm_mul_fderiv_aux {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) (v : ℂ) :
    ∫ z, Real.log ‖z‖ * fderiv ℝ φ z v = -∫ z, (inner ℝ z v / ‖z‖ ^ 2) * φ z := by
  set L : ℂ ≃ₗᵢ[ℝ] ℂ := rotation (Circle.exp (Complex.arg v)) with hL
  have hL1 : L 1 = Complex.exp (Complex.arg v * Complex.I) := by
    simp [hL, rotation_apply, Circle.coe_exp]
  have hv : v = ‖v‖ • L 1 := by
    rw [hL1, Complex.real_smul, Complex.norm_mul_exp_arg_mul_I]
  have hψ : ContDiff ℝ 1 (fun w => φ (L w)) := hφ.comp L.contDiff
  have hψc : HasCompactSupport (fun w => φ (L w)) :=
    hc.comp_isClosedEmbedding L.toHomeomorph.isClosedEmbedding
  have hfd : ∀ w, fderiv ℝ (fun w => φ (L w)) w 1 = fderiv ℝ φ (L w) (L 1) := by
    intro w
    have : HasFDerivAt (fun w => φ (L w))
        ((fderiv ℝ φ (L w)).comp (L.toContinuousLinearEquiv : ℂ →L[ℝ] ℂ)) w :=
      ((hφ.differentiable one_ne_zero) (L w)).hasFDerivAt.comp w
        L.toContinuousLinearEquiv.hasFDerivAt
    rw [this.fderiv]
    rfl
  have core := integral_log_norm_mul_fderiv_one hψ hψc
  have hmp : MeasurePreserving L volume volume := L.measurePreserving
  have hemb : MeasurableEmbedding L := L.toHomeomorph.measurableEmbedding
  have e1 : ∫ z, Real.log ‖z‖ * fderiv ℝ φ z v
      = ∫ w, Real.log ‖L w‖ * fderiv ℝ φ (L w) v :=
    (hmp.integral_comp hemb (fun z => Real.log ‖z‖ * fderiv ℝ φ z v)).symm
  have e2 : ∫ z, (inner ℝ z v / ‖z‖ ^ 2) * φ z
      = ∫ w, (inner ℝ (L w) v / ‖L w‖ ^ 2) * φ (L w) :=
    (hmp.integral_comp hemb (fun z => (inner ℝ z v / ‖z‖ ^ 2) * φ z)).symm
  have hDv : ∀ x, fderiv ℝ φ x v = ‖v‖ * fderiv ℝ φ x (L 1) := fun x => by
    calc fderiv ℝ φ x v = fderiv ℝ φ x (‖v‖ • L 1) := by rw [← hv]
      _ = ‖v‖ * fderiv ℝ φ x (L 1) := by rw [map_smul, smul_eq_mul]
  have hinner : ∀ w, inner ℝ (L w) v = ‖v‖ * w.re := fun w => by
    calc inner ℝ (L w) v = inner ℝ (L w) (‖v‖ • L 1) := by rw [← hv]
      _ = ‖v‖ * inner ℝ w 1 := by
          rw [real_inner_smul_right, LinearIsometryEquiv.inner_map_map]
      _ = ‖v‖ * w.re := by simp [Complex.inner]
  have h1 : ∀ w, Real.log ‖L w‖ * fderiv ℝ φ (L w) v
      = ‖v‖ * (Real.log ‖w‖ * fderiv ℝ (fun w => φ (L w)) w 1) := by
    intro w
    rw [hfd, LinearIsometryEquiv.norm_map, hDv]
    ring
  have h2 : ∀ w, (inner ℝ (L w) v / ‖L w‖ ^ 2) * φ (L w)
      = ‖v‖ * ((w.re / ‖w‖ ^ 2) * φ (L w)) := by
    intro w
    rw [LinearIsometryEquiv.norm_map, hinner]
    ring
  rw [e1, e2]
  simp_rw [h1, h2]
  rw [integral_const_mul, integral_const_mul, core, mul_neg]

end NonUniqueEuler.Polar.LogLaplacianH
