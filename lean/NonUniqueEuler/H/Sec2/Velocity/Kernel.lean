import NonUniqueEuler.Defs.Sec2.BiotSavart
import NonUniqueEuler.I.Infra.ConvMinkowski.Young
import NonUniqueEuler.I.Infra.ConvMinkowski.Measurable
import NonUniqueEuler.I.Sec2.BSBasic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Helpers for `lem:velocity`: kernel pieces, convolutions, Hölder, dominated convergence

Helper file of `P/Sec2/Velocity.lean` (namespace `NonUniqueEuler.BS.VelH`).

* the kernel pieces `kBall ε = 1_{B_ε} K`, `kOut L = 1_{ℝ²∖B_L} K`, `kAnn ε L = 1_{B_L ∖ B_ε} K`
  and their bounds;
* the convolution `cv k f x = ∫ k(x - y) f(y) dy` (so `velocity f = cv K f`): measurability,
  linearity at points of absolute convergence;
* Hölder's inequality `∫⁻ |f| g ≤ ‖f‖_a ‖g‖_b` for an `ℝ≥0∞`-valued `g`;
* dominated convergence for `eLpNorm` on a finite measure.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.BS.VelH

/-! ### The kernel -/

theorem measurable_K : Measurable biotSavartKernel := by
  unfold biotSavartKernel
  fun_prop

theorem norm_K (z : ℂ) : ‖biotSavartKernel z‖ = (2 * Real.pi * ‖z‖)⁻¹ := by
  have hpi : 0 < 2 * Real.pi := by positivity
  rcases eq_or_ne z 0 with rfl | hz
  · simp [biotSavartKernel]
  have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [biotSavartKernel, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity)]
  field_simp

theorem norm_K_le_of_le {z : ℂ} {r : ℝ} (hr : 0 < r) (hz : r ≤ ‖z‖) :
    ‖biotSavartKernel z‖ ≤ (2 * Real.pi * r)⁻¹ := by
  rw [norm_K]
  have hpi : 0 < 2 * Real.pi := by positivity
  exact inv_anti₀ (by positivity) (by nlinarith)

/-- `1_{B_ε} K`. -/
def kBall (ε : ℝ) (z : ℂ) : ℂ := (ball (0 : ℂ) ε).indicator biotSavartKernel z

/-- `1_{ℝ² ∖ B_L} K`. -/
def kOut (L : ℝ) (z : ℂ) : ℂ := (ball (0 : ℂ) L)ᶜ.indicator biotSavartKernel z

/-- `1_{B_L ∖ B_ε} K`. -/
def kAnn (ε L : ℝ) (z : ℂ) : ℂ := (ball (0 : ℂ) L \ ball (0 : ℂ) ε).indicator biotSavartKernel z

theorem measurable_kBall (ε : ℝ) : Measurable (kBall ε) :=
  measurable_K.indicator measurableSet_ball

theorem measurable_kOut (L : ℝ) : Measurable (kOut L) :=
  measurable_K.indicator measurableSet_ball.compl

theorem measurable_kAnn (ε L : ℝ) : Measurable (kAnn ε L) :=
  measurable_K.indicator (measurableSet_ball.diff measurableSet_ball)

theorem norm_kBall_le (ε : ℝ) (z : ℂ) : ‖kBall ε z‖ ≤ ‖biotSavartKernel z‖ := by
  unfold kBall
  exact norm_indicator_le_norm_self _ _

theorem norm_kOut_le (L : ℝ) (z : ℂ) : ‖kOut L z‖ ≤ ‖biotSavartKernel z‖ := by
  unfold kOut
  exact norm_indicator_le_norm_self _ _

theorem norm_kAnn_le (ε L : ℝ) (z : ℂ) : ‖kAnn ε L z‖ ≤ ‖biotSavartKernel z‖ := by
  unfold kAnn
  exact norm_indicator_le_norm_self _ _

/-- `‖K - 1_{B_L∖B_ε}K‖ ≤ ‖1_{B_ε}K‖ + ‖1_{ℝ²∖B_L}K‖` pointwise. -/
theorem norm_sub_kAnn_le (ε L : ℝ) (z : ℂ) :
    ‖biotSavartKernel z - kAnn ε L z‖ ≤ ‖kBall ε z‖ + ‖kOut L z‖ := by
  unfold kAnn kBall kOut
  by_cases h1 : z ∈ ball (0 : ℂ) L \ ball (0 : ℂ) ε
  · rw [indicator_of_mem h1, sub_self, norm_zero]
    positivity
  · rw [indicator_of_notMem h1, sub_zero]
    rw [Set.mem_sdiff, not_and_or, not_not] at h1
    rcases h1 with h1 | h1
    · rw [indicator_of_mem (show z ∈ (ball (0 : ℂ) L)ᶜ from h1)]
      exact le_add_of_nonneg_left (norm_nonneg _)
    · rw [indicator_of_mem h1]
      exact le_add_of_nonneg_right (norm_nonneg _)

theorem norm_kOut_le_const {L : ℝ} (hL : 0 < L) (z : ℂ) :
    ‖kOut L z‖ ≤ (2 * Real.pi * L)⁻¹ := by
  unfold kOut
  by_cases hz : z ∈ (ball (0 : ℂ) L)ᶜ
  · rw [indicator_of_mem hz]
    refine norm_K_le_of_le hL ?_
    simpa [mem_ball_zero_iff] using hz
  · rw [indicator_of_notMem hz, norm_zero]
    positivity

theorem norm_kAnn_le_const {ε : ℝ} (hε : 0 < ε) (L : ℝ) (z : ℂ) :
    ‖kAnn ε L z‖ ≤ (2 * Real.pi * ε)⁻¹ := by
  unfold kAnn
  by_cases hz : z ∈ ball (0 : ℂ) L \ ball (0 : ℂ) ε
  · rw [indicator_of_mem hz]
    refine norm_K_le_of_le hε ?_
    have := hz.2
    simpa [mem_ball_zero_iff] using this
  · rw [indicator_of_notMem hz, norm_zero]
    positivity

theorem eLpNorm_kOut_top_le {L : ℝ} (hL : 0 < L) :
    eLpNorm (kOut L) ⊤ volume ≤ ENNReal.ofReal (2 * Real.pi * L)⁻¹ := by
  rw [eLpNorm_exponent_top]
  exact eLpNormEssSup_le_of_ae_bound (Eventually.of_forall (norm_kOut_le_const hL))

theorem memLp_kAnn {ε : ℝ} (hε : 0 < ε) (L : ℝ) (q : ℝ≥0∞) : MemLp (kAnn ε L) q volume := by
  have hfin : volume (ball (0 : ℂ) L \ ball (0 : ℂ) ε) ≠ ∞ :=
    ((measure_mono sdiff_subset).trans_lt measure_ball_lt_top).ne
  have hb : MemLp biotSavartKernel q (volume.restrict (ball (0 : ℂ) L \ ball (0 : ℂ) ε)) := by
    have : IsFiniteMeasure (volume.restrict (ball (0 : ℂ) L \ ball (0 : ℂ) ε)) :=
      isFiniteMeasure_restrict.mpr hfin
    refine MemLp.of_bound measurable_K.aestronglyMeasurable (2 * Real.pi * ε)⁻¹ ?_
    refine (ae_restrict_iff' (measurableSet_ball.diff measurableSet_ball)).mpr
      (Eventually.of_forall fun z hz => ?_)
    refine norm_K_le_of_le hε ?_
    have := hz.2
    simpa [mem_ball_zero_iff] using this
  unfold kAnn
  exact (memLp_indicator_iff_restrict (measurableSet_ball.diff measurableSet_ball)).mpr hb

theorem lintegral_kBall {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ z, ‖kBall ε z‖ₑ = ENNReal.ofReal ε := by
  unfold kBall
  simp_rw [enorm_indicator_eq_indicator_enorm]
  rw [lintegral_indicator measurableSet_ball]
  exact (integral_norm_biotSavartKernel_ball hε).2.2

theorem memLp_kBall_one {ε : ℝ} (hε : 0 < ε) : MemLp (kBall ε) 1 volume := by
  refine ⟨(measurable_kBall ε).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_one_eq_lintegral_enorm, lintegral_kBall hε]
  exact ENNReal.ofReal_lt_top

/-! ### Convolutions -/

/-- The convolution `(k ∗ f)(x) = ∫ k(x - y) f(y) dy` of a complex kernel and a real function. -/
def cv (k : ℂ → ℂ) (f : ℂ → ℝ) (x : ℂ) : ℂ := ∫ y, k (x - y) * (f y : ℂ)

theorem velocity_eq_cv (f : ℂ → ℝ) : velocity f = cv biotSavartKernel f := rfl

theorem aestronglyMeasurable_cv {k : ℂ → ℂ} (hk : AEStronglyMeasurable k volume) {f : ℂ → ℝ}
    (hf : AEStronglyMeasurable f volume) : AEStronglyMeasurable (cv k f) volume := by
  have hf' : AEStronglyMeasurable (fun y => (f y : ℂ)) volume :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hf
  have h := (hf'.convolution_integrand (ContinuousLinearMap.mul ℝ ℂ) hk
    (μ := volume) (ν := volume)).integral_prod_right'
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [cv, ContinuousLinearMap.mul_apply']
  congr 1
  funext y
  ring

theorem enorm_cv_le (k : ℂ → ℂ) (f : ℂ → ℝ) (x : ℂ) : ‖cv k f x‖ₑ ≤ Conv.convAbs k f x :=
  Conv.enorm_integral_conv_le k f x

/-- Integrability of `y ↦ k(x - y) f(y)` from a finite majorant. -/
theorem integrable_of_convAbs {k : ℂ → ℂ} (hk : AEStronglyMeasurable k volume) {f : ℂ → ℝ}
    (hf : AEStronglyMeasurable f volume) {x : ℂ} (hx : Conv.convAbs k f x ≠ ∞) :
    Integrable (fun y => k (x - y) * (f y : ℂ)) :=
  Conv.integrable_conv_of_convAbs_ne_top hk hf hx

theorem cv_sub_right {k : ℂ → ℂ} {f g : ℂ → ℝ} {x : ℂ}
    (hf : Integrable (fun y => k (x - y) * (f y : ℂ)))
    (hg : Integrable (fun y => k (x - y) * (g y : ℂ))) :
    cv k (f - g) x = cv k f x - cv k g x := by
  unfold cv
  rw [← integral_sub hf hg]
  congr 1
  funext y
  simp only [Pi.sub_apply, Complex.ofReal_sub]
  ring

theorem cv_sub_left {k₁ k₂ : ℂ → ℂ} {f : ℂ → ℝ} {x : ℂ}
    (h₁ : Integrable (fun y => k₁ (x - y) * (f y : ℂ)))
    (h₂ : Integrable (fun y => k₂ (x - y) * (f y : ℂ))) :
    cv (fun z => k₁ z - k₂ z) f x = cv k₁ f x - cv k₂ f x := by
  unfold cv
  rw [← integral_sub h₁ h₂]
  congr 1
  funext y
  ring

/-- Majorant subadditivity: if `‖k z‖ ≤ ‖k₁ z‖ + ‖k₂ z‖`, then
`|k| ⋆ |f| ≤ |k₁| ⋆ |f| + |k₂| ⋆ |f|`. -/
theorem convAbs_le_add {E₁ E₂ F : Type*} [NormedAddCommGroup E₁] [NormedAddCommGroup E₂]
    [NormedAddCommGroup F] {k : ℂ → ℂ} {k₁ : ℂ → E₁} {k₂ : ℂ → E₂}
    (hk₁ : AEStronglyMeasurable k₁ volume) {f : ℂ → F} (hf : AEStronglyMeasurable f volume)
    (hsplit : ∀ z, ‖k z‖ ≤ ‖k₁ z‖ + ‖k₂ z‖) (x : ℂ) :
    Conv.convAbs k f x ≤ Conv.convAbs k₁ f x + Conv.convAbs k₂ f x := by
  have hmp := Measure.measurePreserving_sub_left (volume : Measure ℂ) x
  have hk₁' : AEMeasurable (fun y => ‖k₁ (x - y)‖ₑ) volume :=
    (hk₁.comp_measurePreserving hmp).enorm
  unfold Conv.convAbs
  have hadd := lintegral_add_left' (hk₁'.mul hf.enorm) (fun y => ‖k₂ (x - y)‖ₑ * ‖f y‖ₑ)
  simp only [Pi.mul_apply] at hadd
  rw [← hadd]
  refine lintegral_mono fun y => ?_
  rw [← add_mul]
  gcongr
  have h := hsplit (x - y)
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal h

/-! ### Hölder and dominated convergence -/

/-- Hölder's inequality `∫⁻ |f| g ≤ ‖f‖_a ‖g‖_b` with a `[0,∞]`-valued `g`. -/
theorem lintegral_enorm_mul_le {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {f : α → E} {g : α → ℝ≥0∞} (hf : AEStronglyMeasurable f μ)
    (hg : AEMeasurable g μ) {a b : ℝ} (hab : a.HolderConjugate b) :
    ∫⁻ x, ‖f x‖ₑ * g x ∂μ ≤
      eLpNorm f (ENNReal.ofReal a) μ * eLpNorm g (ENNReal.ofReal b) μ := by
  have ha : 0 < a := hab.pos
  have hb : 0 < b := hab.symm.pos
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hab hf.enorm hg
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using ha) ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hb) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal ha.le, ENNReal.toReal_ofReal hb.le]
  simpa only [Pi.mul_apply, enorm_eq_self] using h

/-- Dominated convergence for `eLpNorm` (`0 < q < ∞`) on a finite measure: uniformly bounded
functions converging to `0` a.e. converge to `0` in `L^q`. -/
theorem tendsto_eLpNorm_zero_of_bound {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] [NormedAddCommGroup E] {F : ℕ → α → E}
    (hF : ∀ n, AEStronglyMeasurable (F n) μ) {C : ℝ} (hC : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 0)) {q : ℝ≥0∞} (hq0 : q ≠ 0)
    (hq : q ≠ ∞) : Tendsto (fun n => eLpNorm (F n) q μ) atTop (𝓝 0) := by
  have hqpos : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hq]
  have hint : Tendsto (fun n => ∫⁻ x, ‖F n x‖ₑ ^ q.toReal ∂μ) atTop (𝓝 0) := by
    have h0 : (∫⁻ _x, (0 : ℝ≥0∞) ∂μ) = 0 := lintegral_zero
    rw [← h0]
    refine tendsto_lintegral_of_dominated_convergence' (fun _ => ENNReal.ofReal C ^ q.toReal)
      (fun n => ((hF n).enorm.pow_const _)) (fun n => ?_) ?_ ?_
    · filter_upwards [hC n] with x hx
      gcongr
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hx
    · rw [lintegral_const]
      exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hqpos.le ENNReal.ofReal_ne_top)
        (measure_ne_top _ _)
    · filter_upwards [hlim] with x hx
      have h1 : Tendsto (fun n => ‖F n x‖ₑ) atTop (𝓝 0) := by
        have := (continuous_enorm.tendsto (0 : E)).comp hx
        rw [enorm_zero] at this
        exact this
      have h2 := (ENNReal.continuous_rpow_const (y := q.toReal)).tendsto 0
      rw [ENNReal.zero_rpow_of_pos hqpos] at h2
      exact h2.comp h1
  have h2 := (ENNReal.continuous_rpow_const (y := 1 / q.toReal)).tendsto 0
  rw [ENNReal.zero_rpow_of_pos (by positivity)] at h2
  exact h2.comp hint

/-- An `L^q(B_R)` bound for a function bounded by `c` on the ball. -/
theorem eLpNorm_ball_le_of_bound {f : ℂ → ℝ≥0∞} {c : ℝ≥0∞} (hf : ∀ x, f x ≤ c) (R : ℝ)
    (q : ℝ≥0∞) :
    eLpNorm f q (volume.restrict (ball (0 : ℂ) R)) ≤
      c * volume (ball (0 : ℂ) R) ^ q.toReal⁻¹ := by
  have h := eLpNorm_le_of_ae_enorm_bound (μ := volume.restrict (ball (0 : ℂ) R)) (p := q)
    (f := f) (C := c) (Eventually.of_forall fun x => by rw [enorm_eq_self]; exact hf x)
  rwa [Measure.restrict_apply_univ, smul_eq_mul] at h

end NonUniqueEuler.BS.VelH
