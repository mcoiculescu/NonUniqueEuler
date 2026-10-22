import NonUniqueEuler.Defs.Sec2.BiotSavart
import NonUniqueEuler.I.Sec2.BSBasic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Helper for `lem:grad-bound`: differentiation under the integral sign

Helper of `P/SmoothB/GradBound.lean` (`B_global_smooth.tex:125-127`, first sentence of the
proof). For real `g ∈ C¹_c`, the velocity `u = K ∗ g` is a Mathlib convolution of the locally
integrable kernel with a compactly supported `C¹` function, so `u ∈ C¹` and
`∂_l u_i(x) = ∫ (K_BS)_i(z) ∂_l g(x - z) dz`:
* `contDiff_velocity_one`: `velocity g` is `C¹`;
* `gradEntry_velocity_eq`: `∂_l u_i(x) = ∫ z, kernelComp i z * fderiv ℝ g (x - z) (e2 l)`;
* `integrable_kernelComp_mul`: the integrand is integrable for any continuous compactly
  supported `φ` in place of `∂_l g`.

The convolution lemmas (`locallyIntegrable_biotSavartKernel`, `velocity_eq_conv`,
`fderiv_conv_apply`, `fderiv_velocity_apply`) follow the proved helper
`H/Sec2/BSSmooth/Differentiate.lean` of the proof `Sec2/BSSmooth` (copied here, under a different
namespace, because a P file may import only its own helpers).
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ContDiff Convolution

namespace NonUniqueEuler.GradBoundH

/-- The Biot–Savart kernel is locally integrable (`lem:BS-basic`(a)). -/
theorem locallyIntegrable_biotSavartKernel : LocallyIntegrable biotSavartKernel volume := by
  rw [locallyIntegrable_iff]
  intro k hk
  obtain ⟨r, hr, hkr⟩ := hk.isBounded.subset_ball_lt 0 0
  exact (BS.integral_norm_biotSavartKernel_ball hr).1.mono_set hkr

/-- The velocity as a convolution with the kernel on the left. -/
theorem velocity_eq_conv (g : ℂ → ℝ) :
    velocity g = biotSavartKernel ⋆[(ContinuousLinearMap.mul ℝ ℂ).flip, volume]
      (fun y => (g y : ℂ)) := by
  rw [convolution_flip]
  exact Conv.velocity_eq_convolution g

/-- Generic: the derivative of `k ⋆ h` in direction `v` is `k ⋆ ∂_v h`. -/
theorem fderiv_conv_apply {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] E' →L[ℝ] F) {k : ℂ → E} (hk : LocallyIntegrable k volume) {h : ℂ → E'}
    (hh : ContDiff ℝ 1 h) (hc : HasCompactSupport h) (x v : ℂ) :
    fderiv ℝ (k ⋆[L, volume] h) x v = (k ⋆[L, volume] fun y => fderiv ℝ h y v) x := by
  rw [(hc.hasFDerivAt_convolution_right L hk hh x).fderiv]
  exact convolution_precompR_apply L hk (hc.fderiv ℝ) (hh.continuous_fderiv one_ne_zero) x v

/-- The derivative of the complexification of a real function. -/
theorem fderiv_ofReal_apply {h : ℂ → ℝ} {y : ℂ} (hh : DifferentiableAt ℝ h y) (v : ℂ) :
    fderiv ℝ (fun y => (h y : ℂ)) y v = (fderiv ℝ h y v : ℂ) := by
  have := (Complex.ofRealCLM.hasFDerivAt.comp y hh.hasFDerivAt).fderiv
  simp only [Function.comp_def, Complex.ofRealCLM_apply] at this
  rw [this]
  rfl

theorem contDiff_ofReal_comp {h : ℂ → ℝ} {n : WithTop ℕ∞} (hh : ContDiff ℝ n h) :
    ContDiff ℝ n (fun y => (h y : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp hh

theorem hasCompactSupport_ofReal_comp {h : ℂ → ℝ} (hc : HasCompactSupport h) :
    HasCompactSupport (fun y => (h y : ℂ)) :=
  hc.comp_left Complex.ofReal_zero

/-- `∂_v (K ∗ h) = K ∗ ∂_v h` for real `h ∈ C¹_c`. -/
theorem fderiv_velocity_apply {h : ℂ → ℝ} (hh : ContDiff ℝ 1 h) (hc : HasCompactSupport h)
    (x v : ℂ) : fderiv ℝ (velocity h) x v = velocity (fun y => fderiv ℝ h y v) x := by
  rw [velocity_eq_conv, velocity_eq_conv,
    fderiv_conv_apply _ locallyIntegrable_biotSavartKernel (contDiff_ofReal_comp hh)
      (hasCompactSupport_ofReal_comp hc)]
  congr 1
  funext y
  exact fderiv_ofReal_apply (hh.differentiable one_ne_zero y) v

/-- `u = K ∗ g ∈ C¹` for real `g ∈ C¹_c`. -/
theorem contDiff_velocity_one {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) :
    ContDiff ℝ 1 (velocity g) := by
  rw [velocity_eq_conv]
  exact (hasCompactSupport_ofReal_comp hc).contDiff_convolution_right (n := 1) _
    locallyIntegrable_biotSavartKernel (contDiff_ofReal_comp hg)

/-! ### Components -/

/-- `comp2 i` as a continuous real-linear map. -/
def comp2CLM : Fin 2 → ℂ →L[ℝ] ℝ := ![Complex.reCLM, Complex.imCLM]

theorem comp2CLM_apply (i : Fin 2) (z : ℂ) : comp2CLM i z = Prelim.comp2 i z := by
  fin_cases i <;> rfl

theorem comp2_mul_ofReal (i : Fin 2) (z : ℂ) (r : ℝ) :
    Prelim.comp2 i (z * (r : ℂ)) = Prelim.comp2 i z * r := by
  fin_cases i <;> simp

theorem abs_comp2_le (i : Fin 2) (z : ℂ) : |Prelim.comp2 i z| ≤ ‖z‖ := by
  fin_cases i
  · simpa using Complex.abs_re_le_norm z
  · simpa using Complex.abs_im_le_norm z

/-- `|(K_BS)_i(z)| ≤ (2π|z|)⁻¹` for every `z` (both sides vanish at `z = 0`). -/
theorem abs_kernelComp_le (i : Fin 2) (z : ℂ) :
    |BS.kernelComp i z| ≤ (2 * Real.pi * ‖z‖)⁻¹ := by
  rcases eq_or_ne z 0 with rfl | hz
  · have : BS.kernelComp i 0 = 0 := by fin_cases i <;> simp [BS.kernelComp, biotSavartKernel]
    simp [this]
  · exact (abs_comp2_le i _).trans (BS.norm_biotSavartKernel_eq hz).le

/-- `z ↦ (K_BS)_i(z) φ(x - z)` is integrable for continuous compactly supported `φ`, and so is
`z ↦ K_BS(z) φ(x - z)`. -/
theorem integrable_kernel_mul {φ : ℂ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (x : ℂ) : Integrable (fun z => biotSavartKernel z * (φ (x - z) : ℂ)) volume := by
  have hc : Continuous fun z => (φ (x - z) : ℂ) :=
    Complex.continuous_ofReal.comp (hφ.comp (continuous_const.sub continuous_id))
  have hcs : HasCompactSupport fun z => (φ (x - z) : ℂ) := by
    have h1 : HasCompactSupport fun z => φ (x - z) :=
      hφc.comp_homeomorph (Homeomorph.subLeft x)
    exact hasCompactSupport_ofReal_comp h1
  have := locallyIntegrable_biotSavartKernel.integrable_smul_left_of_hasCompactSupport hc hcs
  refine this.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [smul_eq_mul]
  ring

theorem integrable_kernelComp_mul (i : Fin 2) {φ : ℂ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (x : ℂ) :
    Integrable (fun z => BS.kernelComp i z * φ (x - z)) volume := by
  have := (comp2CLM i).integrable_comp (integrable_kernel_mul hφ hφc x)
  refine this.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [comp2CLM_apply, comp2_mul_ofReal, BS.kernelComp]

/-- `∂_l u_i(x) = ∫ (K_BS)_i(z) ∂_l g(x - z) dz` for real `g ∈ C¹_c`
(`B_global_smooth.tex:126-127`). -/
theorem gradEntry_velocity_eq {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (i l : Fin 2) (x : ℂ) :
    Prelim.gradEntry (velocity g) i l x =
      ∫ z, BS.kernelComp i z * fderiv ℝ g (x - z) (Prelim.e2 l) := by
  set φ : ℂ → ℝ := fun y => fderiv ℝ g y (Prelim.e2 l) with hφdef
  have hφ : Continuous φ := (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hφc : HasCompactSupport φ := by
    have : φ = (fun L : ℂ →L[ℝ] ℝ => L (Prelim.e2 l)) ∘ fderiv ℝ g := rfl
    rw [this]
    exact (hc.fderiv ℝ).comp_left (by simp)
  have h1 : Prelim.gradEntry (velocity g) i l x = Prelim.comp2 i (velocity φ x) := by
    simp only [Prelim.gradEntry, Prelim.pd]
    rw [fderiv_velocity_apply hg hc]
  have h2 : velocity φ x = ∫ z, biotSavartKernel z * (φ (x - z) : ℂ) := by
    simp only [velocity]
    rw [← integral_sub_left_eq_self _ volume x]
    simp only [sub_sub_cancel]
  rw [h1, h2, ← comp2CLM_apply, ← (comp2CLM i).integral_comp_comm (integrable_kernel_mul hφ hφc x)]
  congr 1
  funext z
  simp only [comp2CLM_apply, comp2_mul_ofReal, BS.kernelComp, hφdef]

end NonUniqueEuler.GradBoundH
