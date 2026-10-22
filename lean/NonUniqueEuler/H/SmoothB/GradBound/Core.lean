import NonUniqueEuler.H.SmoothB.GradBound.Velocity
import NonUniqueEuler.H.SmoothB.GradBound.Cutoff
import NonUniqueEuler.H.SmoothB.GradBound.Norms
import NonUniqueEuler.I.Infra.Polar.Power
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Helper for `lem:grad-bound`: the estimate for a fixed cutoff

Helper of `P/SmoothB/GradBound.lean` (`B_global_smooth.tex:125-147`). Fix `0 < a < b ≤ 1` and the
radial cutoff `χ = cut a b` (`0` on `|z| ≤ a`, `1` on `|z| ≥ b`). For real `g ∈ C¹_c` we split
`∫ (K_BS)_i(z) ∂_l g(x - z) dz = ∫ (1 - χ)(K_BS)_i ∂_l g(x - ·) + ∫ χ (K_BS)_i ∂_l g(x - ·)`:
* near part (`abs_integral_near_le`): at most `b ‖∇g‖_∞`, by `∫_{B_b} |K_BS| = b`;
* far part: integration by parts on the whole plane (R6; Mathlib
  `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`) moves `∂_l` to `F = χ (K_BS)_i`
  (`integral_cutKernel_mul_eq`); then `|∂_l F(z) g(x - z)|` is bounded by
  `‖g‖_∞ ψ'(|z|)/(2π|z|) + ‖g‖_∞ 1_{a<|z|<1}/(2π|z|²) + |g(x - z)|/(2π)`
  (`abs_fderiv_cutKernel_mul_le`), whose integral is `‖g‖_∞ + ‖g‖_∞ log(1/a) + ‖g‖₁/(2π)`
  (`integral_ibpMajorant`).

Result (`abs_integral_kernelComp_le`):
`|∂_l u_i(x)| ≤ b ‖∇g‖_∞ + ‖g‖_∞ + ‖g‖_∞ log(1/a) + ‖g‖₁/(2π)`. The manuscript's bound with
`δ` is the limit `a, b → δ` (taken in the P file).
-/

noncomputable section

open MeasureTheory Set Metric Real Filter Topology
open scoped ContDiff

namespace NonUniqueEuler.GradBoundH

/-! ### The kernel components off the origin -/

theorem kernelComp_eq_comp (i : Fin 2) : BS.kernelComp i = comp2CLM i ∘ biotSavartKernel := by
  funext z
  simp [comp2CLM_apply, BS.kernelComp]

theorem contDiffAt_biotSavartKernel {z : ℂ} (hz : z ≠ 0) : ContDiffAt ℝ ∞ biotSavartKernel z :=
  BS.contDiffOn_biotSavartKernel.contDiffAt (isOpen_compl_singleton.mem_nhds hz)

theorem contDiffAt_kernelComp (i : Fin 2) {z : ℂ} (hz : z ≠ 0) :
    ContDiffAt ℝ ∞ (BS.kernelComp i) z := by
  rw [kernelComp_eq_comp]
  exact (comp2CLM i).contDiff.contDiffAt.comp z (contDiffAt_biotSavartKernel hz)

theorem fderiv_kernelComp_apply (i : Fin 2) {z : ℂ} (hz : z ≠ 0) (v : ℂ) :
    fderiv ℝ (BS.kernelComp i) z v = Prelim.comp2 i (fderiv ℝ biotSavartKernel z v) := by
  have hK := ((contDiffAt_biotSavartKernel hz).differentiableAt (by simp)).hasFDerivAt
  have h := (comp2CLM i).hasFDerivAt.comp z hK
  rw [kernelComp_eq_comp, h.fderiv]
  simp [comp2CLM_apply]

/-- `|∂_l (K_BS)_i(z)| ≤ (2π|z|²)⁻¹` (`lem:BS-basic`(a)). -/
theorem abs_fderiv_kernelComp_le (i l : Fin 2) {z : ℂ} (hz : z ≠ 0) :
    |fderiv ℝ (BS.kernelComp i) z (Prelim.e2 l)| ≤ (2 * π * ‖z‖ ^ 2)⁻¹ := by
  rw [fderiv_kernelComp_apply i hz]
  exact BS.abs_gradEntry_biotSavartKernel_le hz i l

/-! ### The cut-off kernel `F = χ (K_BS)_i` -/

/-- The cut-off kernel component `F = χ (K_BS)_i`, `χ = cut a b`. -/
def cutKernel (a b : ℝ) (i : Fin 2) (z : ℂ) : ℝ :=
  cut a b z * BS.kernelComp i z

variable {a b : ℝ}

theorem cutKernel_eventuallyEq_zero (ha : 0 < a) (hab : a < b) (i : Fin 2) :
    cutKernel a b i =ᶠ[𝓝 (0 : ℂ)] fun _ => (0 : ℝ) := by
  filter_upwards [cut_eventuallyEq_zero ha hab] with z hz
  simp [cutKernel, hz]

theorem contDiff_cutKernel (ha : 0 < a) (hab : a < b) (i : Fin 2) :
    ContDiff ℝ 1 (cutKernel a b i) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  rcases eq_or_ne z 0 with rfl | hz
  · exact contDiffAt_const.congr_of_eventuallyEq (cutKernel_eventuallyEq_zero ha hab i)
  · exact ((contDiff_cut ha hab).contDiffAt.of_le (by simp)).mul
      ((contDiffAt_kernelComp i hz).of_le (by simp))

theorem fderiv_cutKernel_apply (ha : 0 < a) (hab : a < b) (i : Fin 2) {z : ℂ} (hz : z ≠ 0)
    (v : ℂ) :
    fderiv ℝ (cutKernel a b i) z v =
      cut a b z * fderiv ℝ (BS.kernelComp i) z v + BS.kernelComp i z * fderiv ℝ (cut a b) z v := by
  have h1 : DifferentiableAt ℝ (cut a b) z := (contDiff_cut ha hab).differentiable (by simp) z
  have h2 : DifferentiableAt ℝ (BS.kernelComp i) z :=
    (contDiffAt_kernelComp i hz).differentiableAt (by simp)
  have : cutKernel a b i = fun y => cut a b y * BS.kernelComp i y := rfl
  rw [this, fderiv_fun_mul h1 h2]
  simp [smul_eq_mul]

/-! ### The majorant after integration by parts -/

/-- The majorant of `|∂_l F(z) g(x - z)|`:
`A ψ'(|z|)/(2π|z|) + A 1_{a<|z|<1}(z) |z|⁻²/(2π) + |g(x - z)|/(2π)`. -/
def ibpMajorant (a b A : ℝ) (g : ℂ → ℝ) (x z : ℂ) : ℝ :=
  A * (deriv (cutProfile a b) ‖z‖ / (2 * π * ‖z‖)) +
    A * ((Polar.annulus a 1).indicator (fun w : ℂ => (‖w‖ ^ 2)⁻¹) z / (2 * π)) +
      |g (x - z)| / (2 * π)

theorem abs_fderiv_cutKernel_mul_le (ha : 0 < a) (hab : a < b) (i l : Fin 2) {g : ℂ → ℝ}
    {A : ℝ} (hA : ∀ y, |g y| ≤ A) (x z : ℂ) :
    |fderiv ℝ (cutKernel a b i) z (Prelim.e2 l) * g (x - z)| ≤ ibpMajorant a b A g x z := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  have hd0 : 0 ≤ deriv (cutProfile a b) ‖z‖ := deriv_cutProfile_nonneg hab _
  have hM1 : 0 ≤ A * (deriv (cutProfile a b) ‖z‖ / (2 * π * ‖z‖)) := by positivity
  have hind : 0 ≤ (Polar.annulus a 1).indicator (fun w : ℂ => (‖w‖ ^ 2)⁻¹) z :=
    indicator_nonneg (fun w _ => by positivity) z
  have hM2 : 0 ≤ A * ((Polar.annulus a 1).indicator (fun w : ℂ => (‖w‖ ^ 2)⁻¹) z / (2 * π)) :=
    mul_nonneg hA0 (div_nonneg hind (by positivity))
  have hM3 : 0 ≤ |g (x - z)| / (2 * π) := by positivity
  rcases eq_or_ne z 0 with rfl | hz
  · rw [(cutKernel_eventuallyEq_zero ha hab i).fderiv_eq]
    simp only [fderiv_fun_const, Pi.zero_apply, zero_apply, zero_mul, abs_zero]
    unfold ibpMajorant
    linarith
  · rw [fderiv_cutKernel_apply ha hab i hz, abs_mul]
    have hc0 : 0 ≤ cut a b z := cut_nonneg z
    have hc1 : cut a b z ≤ 1 := cut_le_one z
    have hp := abs_fderiv_kernelComp_le i l hz
    have hq := abs_kernelComp_le i z
    have he : |fderiv ℝ (cut a b) z (Prelim.e2 l)| ≤ deriv (cutProfile a b) ‖z‖ := by
      simpa [norm_e2] using abs_fderiv_cut_le ha hab z (Prelim.e2 l)
    have hG : |g (x - z)| ≤ A := hA _
    have hG0 : 0 ≤ |g (x - z)| := abs_nonneg _
    have hz0 : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hpi : 0 < 2 * π := by positivity
    -- the boundary term
    have t1 : |BS.kernelComp i z| * |fderiv ℝ (cut a b) z (Prelim.e2 l)| * |g (x - z)| ≤
        A * (deriv (cutProfile a b) ‖z‖ / (2 * π * ‖z‖)) := by
      calc |BS.kernelComp i z| * |fderiv ℝ (cut a b) z (Prelim.e2 l)| * |g (x - z)|
          ≤ (2 * π * ‖z‖)⁻¹ * deriv (cutProfile a b) ‖z‖ * A := by gcongr
        _ = A * (deriv (cutProfile a b) ‖z‖ / (2 * π * ‖z‖)) := by
          rw [div_eq_mul_inv]; ring
    -- the volume term
    have t2 : cut a b z * |fderiv ℝ (BS.kernelComp i) z (Prelim.e2 l)| * |g (x - z)| ≤
        A * ((Polar.annulus a 1).indicator (fun w : ℂ => (‖w‖ ^ 2)⁻¹) z / (2 * π)) +
          |g (x - z)| / (2 * π) := by
      by_cases h1 : ‖z‖ ≤ a
      · rw [cut_eq_zero hab h1, zero_mul, zero_mul]
        exact add_nonneg hM2 hM3
      · push Not at h1
        by_cases h2 : ‖z‖ < 1
        · have hmem : z ∈ Polar.annulus a 1 := ⟨h1, h2⟩
          rw [indicator_of_mem hmem]
          calc cut a b z * |fderiv ℝ (BS.kernelComp i) z (Prelim.e2 l)| * |g (x - z)|
              ≤ 1 * (2 * π * ‖z‖ ^ 2)⁻¹ * A := by gcongr
            _ = A * ((‖z‖ ^ 2)⁻¹ / (2 * π)) := by
              rw [mul_inv, div_eq_mul_inv]; ring
            _ ≤ _ := le_add_of_nonneg_right hM3
        · push Not at h2
          have hz1 : (2 * π * ‖z‖ ^ 2)⁻¹ ≤ (2 * π)⁻¹ := by
            apply inv_anti₀ hpi
            have : 1 ≤ ‖z‖ ^ 2 := one_le_pow₀ h2
            nlinarith
          calc cut a b z * |fderiv ℝ (BS.kernelComp i) z (Prelim.e2 l)| * |g (x - z)|
              ≤ 1 * (2 * π)⁻¹ * |g (x - z)| := by gcongr; exact hp.trans hz1
            _ = |g (x - z)| / (2 * π) := by rw [div_eq_mul_inv]; ring
            _ ≤ _ := le_add_of_nonneg_left hM2
    have habs : |cut a b z * fderiv ℝ (BS.kernelComp i) z (Prelim.e2 l) +
        BS.kernelComp i z * fderiv ℝ (cut a b) z (Prelim.e2 l)| ≤
        cut a b z * |fderiv ℝ (BS.kernelComp i) z (Prelim.e2 l)| +
          |BS.kernelComp i z| * |fderiv ℝ (cut a b) z (Prelim.e2 l)| := by
      refine (abs_add_le _ _).trans (le_of_eq ?_)
      rw [abs_mul, abs_mul, abs_of_nonneg hc0]
    calc |cut a b z * fderiv ℝ (BS.kernelComp i) z (Prelim.e2 l) +
          BS.kernelComp i z * fderiv ℝ (cut a b) z (Prelim.e2 l)| * |g (x - z)|
        ≤ (cut a b z * |fderiv ℝ (BS.kernelComp i) z (Prelim.e2 l)| +
          |BS.kernelComp i z| * |fderiv ℝ (cut a b) z (Prelim.e2 l)|) * |g (x - z)| := by
          gcongr
      _ = cut a b z * |fderiv ℝ (BS.kernelComp i) z (Prelim.e2 l)| * |g (x - z)| +
          |BS.kernelComp i z| * |fderiv ℝ (cut a b) z (Prelim.e2 l)| * |g (x - z)| := by ring
      _ ≤ ibpMajorant a b A g x z := by
          unfold ibpMajorant
          linarith

theorem integrableOn_annulus_inv_sq (ha : 0 < a) :
    IntegrableOn (fun w : ℂ => (‖w‖ ^ 2)⁻¹) (Polar.annulus a 1) := by
  refine Measure.integrableOn_of_bounded (M := (a ^ 2)⁻¹) ?_ ?_ ?_
  · have hsub : Polar.annulus a 1 ⊆ ball (0 : ℂ) 1 := fun w hw => by
      rw [mem_ball_zero_iff]
      exact hw.2
    exact ((measure_mono hsub).trans_lt measure_ball_lt_top).ne
  · exact ((measurable_norm.pow_const 2).inv).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem (Polar.measurableSet_annulus a 1) fun w hw => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ ha.le hw.1.le 2)

theorem integrable_ibpMajorant (ha : 0 < a) (hab : a < b) {g : ℂ → ℝ} (hg : Continuous g)
    (hc : HasCompactSupport g) (A : ℝ) (x : ℂ) : Integrable (ibpMajorant a b A g x) := by
  have i1 := (integrable_cutBoundary hab).const_mul A
  have i2 := (((integrableOn_annulus_inv_sq ha).integrable_indicator
    (Polar.measurableSet_annulus a 1)).div_const (2 * π)).const_mul A
  have i3 := (integrable_abs_comp_sub hg hc x).div_const (2 * π)
  exact (i1.add i2).add i3

theorem integral_ibpMajorant (ha : 0 < a) (ha1 : a ≤ 1) (hab : a < b) {g : ℂ → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) (A : ℝ) (x : ℂ) :
    ∫ z, ibpMajorant a b A g x z = A + A * Real.log (1 / a) + Smooth.l1 g / (2 * π) := by
  have i1 := (integrable_cutBoundary hab).const_mul A
  have i2 := (((integrableOn_annulus_inv_sq ha).integrable_indicator
    (Polar.measurableSet_annulus a 1)).div_const (2 * π)).const_mul A
  have i3 := (integrable_abs_comp_sub hg hc x).div_const (2 * π)
  have i12 : Integrable (fun z : ℂ => A * (deriv (cutProfile a b) ‖z‖ / (2 * π * ‖z‖)) +
      A * ((Polar.annulus a 1).indicator (fun w : ℂ => (‖w‖ ^ 2)⁻¹) z / (2 * π))) :=
    i1.add i2
  unfold ibpMajorant
  rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
    integral_div, integral_div, integral_indicator (Polar.measurableSet_annulus a 1),
    Polar.setIntegral_annulus_norm_sq_inv ha ha1, integral_cutBoundary ha.le hab,
    integral_abs_comp_sub_eq_l1 hg x]
  have : (2 * π) ≠ 0 := by positivity
  field_simp

/-! ### Integration by parts -/

/-- `∫ F(z) ∂_l g(x - z) dz = ∫ ∂_l F(z) g(x - z) dz` (whole-plane integration by parts, R6). -/
theorem integral_cutKernel_mul_eq (ha : 0 < a) (hab : a < b) (i l : Fin 2) {g : ℂ → ℝ}
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (x : ℂ) :
    ∫ z, cutKernel a b i z * fderiv ℝ g (x - z) (Prelim.e2 l) =
      ∫ z, fderiv ℝ (cutKernel a b i) z (Prelim.e2 l) * g (x - z) := by
  set G : ℂ → ℝ := fun z => g (x - z) with hGdef
  have hGd : ∀ z, HasFDerivAt G ((fderiv ℝ g (x - z)).comp (-ContinuousLinearMap.id ℝ ℂ)) z := by
    intro z
    have h1 : HasFDerivAt (fun z : ℂ => x - z) (-ContinuousLinearMap.id ℝ ℂ) z := by
      simpa using (hasFDerivAt_id z).const_sub x
    exact ((hg.differentiable one_ne_zero) (x - z)).hasFDerivAt.comp z h1
  have hGfd : ∀ z v, fderiv ℝ G z v = -(fderiv ℝ g (x - z) v) := fun z v => by
    rw [(hGd z).fderiv]
    simp
  have hGc : ContDiff ℝ 1 G := hg.comp (contDiff_const.sub contDiff_id)
  have hGcs : HasCompactSupport G := hc.comp_homeomorph (Homeomorph.subLeft x)
  have hF := contDiff_cutKernel ha hab i
  have hFc : Continuous (cutKernel a b i) := hF.continuous
  have hF'c : Continuous fun z => fderiv ℝ (cutKernel a b i) z (Prelim.e2 l) :=
    (hF.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hG'c : Continuous fun z => fderiv ℝ G z (Prelim.e2 l) :=
    (hGc.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hG'cs : HasCompactSupport fun z => fderiv ℝ G z (Prelim.e2 l) := by
    have : (fun z => fderiv ℝ G z (Prelim.e2 l)) =
        (fun L : ℂ →L[ℝ] ℝ => L (Prelim.e2 l)) ∘ fderiv ℝ G := rfl
    rw [this]
    exact (hGcs.fderiv ℝ).comp_left (by simp)
  have i1 : Integrable fun z => fderiv ℝ (cutKernel a b i) z (Prelim.e2 l) * G z :=
    (hF'c.mul hGc.continuous).integrable_of_hasCompactSupport hGcs.mul_left
  have i2 : Integrable fun z => cutKernel a b i z * fderiv ℝ G z (Prelim.e2 l) :=
    (hFc.mul hG'c).integrable_of_hasCompactSupport hG'cs.mul_left
  have i3 : Integrable fun z => cutKernel a b i z * G z :=
    (hFc.mul hGc.continuous).integrable_of_hasCompactSupport hGcs.mul_left
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable i1 i2 i3
    (fun z _ => hF.differentiable one_ne_zero z) (fun z _ => hGc.differentiable one_ne_zero z)
  simp only [hGfd, mul_neg, integral_neg] at hibp
  exact neg_inj.1 hibp

/-! ### The near part -/

theorem abs_integral_near_le (ha : 0 < a) (hab : a < b) (i : Fin 2) {φ : ℂ → ℝ} {N : ℝ}
    (hφ : ∀ y, |φ y| ≤ N) (x : ℂ) :
    |∫ z, (1 - cut a b z) * BS.kernelComp i z * φ (x - z)| ≤ b * N := by
  have hb : 0 < b := ha.trans hab
  have hN : 0 ≤ N := (abs_nonneg _).trans (hφ 0)
  obtain ⟨hKint, hKval, -⟩ := BS.integral_norm_biotSavartKernel_ball hb
  have hmaj : Integrable
      (fun z => N * (ball (0 : ℂ) b).indicator (fun w => ‖biotSavartKernel w‖) z) :=
    (IntegrableOn.integrable_indicator hKint.norm measurableSet_ball).const_mul N
  have hpt : ∀ z, ‖(1 - cut a b z) * BS.kernelComp i z * φ (x - z)‖ ≤
      N * (ball (0 : ℂ) b).indicator (fun w => ‖biotSavartKernel w‖) z := by
    intro z
    rw [Real.norm_eq_abs]
    by_cases hz : z ∈ ball (0 : ℂ) b
    · rw [indicator_of_mem hz, abs_mul, abs_mul]
      have h1 : |1 - cut a b z| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [cut_nonneg (a := a) (b := b) z, cut_le_one (a := a) (b := b) z]
      have h2 : |BS.kernelComp i z| ≤ ‖biotSavartKernel z‖ := abs_comp2_le i _
      calc |1 - cut a b z| * |BS.kernelComp i z| * |φ (x - z)|
          ≤ 1 * ‖biotSavartKernel z‖ * N := by gcongr; exact hφ _
        _ = N * ‖biotSavartKernel z‖ := by ring
    · rw [indicator_of_notMem hz, mul_zero]
      have : cut a b z = 1 := cut_eq_one hab (by simpa [mem_ball_zero_iff] using hz)
      simp [this]
  have h := norm_integral_le_of_norm_le hmaj (Eventually.of_forall hpt)
  rw [Real.norm_eq_abs, integral_const_mul, integral_indicator measurableSet_ball, hKval] at h
  linarith

/-! ### The estimate for a fixed cutoff -/

/-- `|∫ (K_BS)_i(z) ∂_l g(x - z) dz| ≤ b ‖∇g‖_∞ + ‖g‖_∞ + ‖g‖_∞ log(1/a) + ‖g‖₁/(2π)` for
`0 < a < b ≤ 1` (`B_global_smooth.tex:128-144`, with the cutoff between `a` and `b` in place of
the sharp cut at `δ`). -/
theorem abs_integral_kernelComp_le (ha : 0 < a) (hab : a < b) (hb1 : b ≤ 1) (i l : Fin 2)
    {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (x : ℂ) :
    |∫ z, BS.kernelComp i z * fderiv ℝ g (x - z) (Prelim.e2 l)| ≤
      b * Smooth.gradSup g + Smooth.Amax g + Smooth.Amax g * Real.log (1 / a) +
        Smooth.l1 g / (2 * π) := by
  set φ : ℂ → ℝ := fun y => fderiv ℝ g y (Prelim.e2 l) with hφdef
  have hφ : Continuous φ := (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hφc : HasCompactSupport φ := by
    have : φ = (fun L : ℂ →L[ℝ] ℝ => L (Prelim.e2 l)) ∘ fderiv ℝ g := rfl
    rw [this]
    exact (hc.fderiv ℝ).comp_left (by simp)
  have hφx : Continuous fun z => φ (x - z) := hφ.comp (continuous_const.sub continuous_id)
  have hφxc : HasCompactSupport fun z => φ (x - z) := hφc.comp_homeomorph (Homeomorph.subLeft x)
  have hT := integrable_kernelComp_mul i hφ hφc x
  have h2 : Integrable (fun z => cutKernel a b i z * φ (x - z)) :=
    ((contDiff_cutKernel ha hab i).continuous.mul hφx).integrable_of_hasCompactSupport
      hφxc.mul_left
  have h1 : Integrable (fun z => (1 - cut a b z) * BS.kernelComp i z * φ (x - z)) :=
    (hT.sub h2).congr (Eventually.of_forall fun z => by simp only [Pi.sub_apply, cutKernel]; ring)
  have hsplit : ∫ z, BS.kernelComp i z * φ (x - z) =
      (∫ z, (1 - cut a b z) * BS.kernelComp i z * φ (x - z)) +
        ∫ z, cutKernel a b i z * φ (x - z) := by
    rw [← integral_add h1 h2]
    congr 1
    funext z
    simp only [cutKernel]
    ring
  rw [hsplit]
  have hnear := abs_integral_near_le ha hab i (N := Smooth.gradSup g)
    (abs_fderiv_e2_le_gradSup hg hc l) x
  have hfar : |∫ z, cutKernel a b i z * φ (x - z)| ≤
      Smooth.Amax g + Smooth.Amax g * Real.log (1 / a) + Smooth.l1 g / (2 * π) := by
    rw [hφdef, integral_cutKernel_mul_eq ha hab i l hg hc x]
    have h := norm_integral_le_of_norm_le (integrable_ibpMajorant ha hab hg.continuous hc
      (Smooth.Amax g) x) (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]
        exact abs_fderiv_cutKernel_mul_le ha hab i l (abs_le_Amax hg.continuous hc) x z)
    rw [integral_ibpMajorant ha (hab.le.trans hb1) hab hg.continuous hc, Real.norm_eq_abs] at h
    exact h
  calc |(∫ z, (1 - cut a b z) * BS.kernelComp i z * φ (x - z)) +
        ∫ z, cutKernel a b i z * φ (x - z)|
      ≤ |∫ z, (1 - cut a b z) * BS.kernelComp i z * φ (x - z)| +
        |∫ z, cutKernel a b i z * φ (x - z)| := abs_add_le _ _
    _ ≤ _ := by linarith

end NonUniqueEuler.GradBoundH
