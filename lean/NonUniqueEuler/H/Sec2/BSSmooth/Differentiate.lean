import NonUniqueEuler.Defs.Sec2.BiotSavart
import NonUniqueEuler.I.Sec2.BSBasic
import NonUniqueEuler.I.Infra.Polar.Power
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Helper for `lem:BS-basic`(d): differentiation under the integral sign

Helper of `P/Sec2/BSSmooth.lean` (`02_prelim.tex:208-212`). For real `g ∈ C_c^∞`, the velocity
`u = K ∗ g` and the stream function `ψ = (2π)⁻¹ log|·| ∗ g` are Mathlib convolutions of a locally
integrable kernel with a compactly supported smooth function, so they are smooth and every
derivative falls on `g`:
* `fderiv_velocity_apply`: `∂_v (K ∗ g) = K ∗ ∂_v g`;
* `fderiv_logPotentialReal_apply`: `∂_v ψ(x) = (2π)⁻¹ ∫ log|t| ∂_v g(x - t) dt`;
* `iterDirDeriv_velocity`: `∂_{vs} (K ∗ g) = K ∗ ∂_{vs} g` for every list of directions.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ContDiff Convolution

namespace NonUniqueEuler.BSSmoothH

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

theorem velocity_apply_eq_integral (g : ℂ → ℝ) (x : ℂ) :
    velocity g x = ∫ t, (g (x - t) : ℂ) * biotSavartKernel t := by
  rw [velocity_eq_conv, convolution_def]
  rfl

/-- The stream function as a convolution with the kernel `log‖·‖` on the left. -/
theorem logPotentialReal_eq_conv (g : ℂ → ℝ) :
    Multipole.logPotentialReal g = fun x => (2 * Real.pi)⁻¹ *
      ((fun t : ℂ => Real.log ‖t‖) ⋆[(ContinuousLinearMap.mul ℝ ℝ).flip, volume] g) x := by
  funext x
  rw [convolution_flip, Multipole.logPotentialReal, convolution_def]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [mul_comm]

theorem logPotentialReal_apply_eq_integral (g : ℂ → ℝ) (x : ℂ) :
    Multipole.logPotentialReal g x =
      (2 * Real.pi)⁻¹ * ∫ t, g (x - t) * Real.log ‖t‖ := by
  simp only [logPotentialReal_eq_conv, convolution_def]
  rfl

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

/-- `D_v h = ∂_v h` of a real function. -/
def dR (v : ℂ) (h : ℂ → ℝ) (y : ℂ) : ℝ := fderiv ℝ h y v

theorem contDiff_dR {h : ℂ → ℝ} (hh : ContDiff ℝ ∞ h) (v : ℂ) : ContDiff ℝ ∞ (dR v h) := by
  have : ContDiff ℝ ∞ (fderiv ℝ h) := hh.fderiv_right (m := ∞) le_rfl
  exact this.clm_apply contDiff_const

theorem hasCompactSupport_dR {h : ℂ → ℝ} (hc : HasCompactSupport h) (v : ℂ) :
    HasCompactSupport (dR v h) := by
  have : dR v h = (fun L : ℂ →L[ℝ] ℝ => L v) ∘ fderiv ℝ h := rfl
  rw [this]
  exact (hc.fderiv ℝ).comp_left (by simp)

/-- `lem:BS-basic`(d): `∂_v (K ∗ h) = K ∗ ∂_v h` for real `h ∈ C¹_c`. -/
theorem fderiv_velocity_apply {h : ℂ → ℝ} (hh : ContDiff ℝ 1 h) (hc : HasCompactSupport h)
    (x v : ℂ) : fderiv ℝ (velocity h) x v = velocity (dR v h) x := by
  rw [velocity_eq_conv, velocity_eq_conv,
    fderiv_conv_apply _ locallyIntegrable_biotSavartKernel (contDiff_ofReal_comp hh)
      (hasCompactSupport_ofReal_comp hc)]
  congr 1
  funext y
  exact fderiv_ofReal_apply (hh.differentiable one_ne_zero y) v

theorem contDiff_velocity {h : ℂ → ℝ} (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) :
    ContDiff ℝ ∞ (velocity h) := by
  rw [velocity_eq_conv]
  exact (hasCompactSupport_ofReal_comp hc).contDiff_convolution_right _
    locallyIntegrable_biotSavartKernel (contDiff_ofReal_comp hh)

theorem contDiff_logPotentialReal {h : ℂ → ℝ} (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) :
    ContDiff ℝ ∞ (Multipole.logPotentialReal h) := by
  rw [logPotentialReal_eq_conv]
  exact contDiff_const.mul (hc.contDiff_convolution_right _ Polar.locallyIntegrable_log_norm hh)

/-- `∂_v ψ = (2π)⁻¹ log‖·‖ ⋆ ∂_v h`. -/
theorem fderiv_logPotentialReal_apply {h : ℂ → ℝ} (hh : ContDiff ℝ 1 h)
    (hc : HasCompactSupport h) (x v : ℂ) :
    fderiv ℝ (Multipole.logPotentialReal h) x v = Multipole.logPotentialReal (dR v h) x := by
  have hd : DifferentiableAt ℝ ((fun t : ℂ => Real.log ‖t‖) ⋆[(ContinuousLinearMap.mul ℝ ℝ).flip,
      volume] h) x :=
    (hc.hasFDerivAt_convolution_right _ Polar.locallyIntegrable_log_norm hh x).differentiableAt
  rw [logPotentialReal_eq_conv, logPotentialReal_eq_conv, fderiv_const_mul hd]
  simp only [smul_apply, smul_eq_mul]
  rw [fderiv_conv_apply _ Polar.locallyIntegrable_log_norm hh hc]
  rfl

/-- The function `y ↦ ∂_v ψ(y)` is the stream function of `∂_v h`. -/
theorem fderiv_logPotentialReal_apply' {h : ℂ → ℝ} (hh : ContDiff ℝ 1 h)
    (hc : HasCompactSupport h) (v : ℂ) :
    (fun y => fderiv ℝ (Multipole.logPotentialReal h) y v) =
      Multipole.logPotentialReal (dR v h) :=
  funext fun y => fderiv_logPotentialReal_apply hh hc y v

/-- `iterDirDeriv` of a complexified real function stays real. -/
theorem dirDeriv_ofReal {h : ℂ → ℝ} (hh : ContDiff ℝ 1 h) (v : ℂ) :
    Sob.dirDeriv v (fun y => (h y : ℂ)) = fun y => (dR v h y : ℂ) :=
  funext fun y => fderiv_ofReal_apply (hh.differentiable one_ne_zero y) v

/-- `lem:BS-basic`(d): `∂_{vs} (K ∗ g) = K ∗ ∂_{vs} g` for every list of directions, with
`∂_{vs} g` real, smooth and compactly supported. -/
theorem iterDirDeriv_velocity (vs : List ℂ) {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) :
    ∃ h : ℂ → ℝ, ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧
      Sob.iterDirDeriv vs (velocity g) = velocity h ∧
      Sob.iterDirDeriv vs (fun y => (g y : ℂ)) = fun y => (h y : ℂ) := by
  induction vs with
  | nil => exact ⟨g, hg, hgc, rfl, rfl⟩
  | cons v vs ih =>
    obtain ⟨h, hh, hhc, h1, h2⟩ := ih
    refine ⟨dR v h, contDiff_dR hh v, hasCompactSupport_dR hhc v, ?_, ?_⟩
    · rw [Sob.iterDirDeriv_cons, h1]
      funext x
      exact fderiv_velocity_apply (hh.of_le (by simp)) hhc x v
    · rw [Sob.iterDirDeriv_cons, h2]
      exact dirDeriv_ofReal (hh.of_le (by simp)) v

end NonUniqueEuler.BSSmoothH
