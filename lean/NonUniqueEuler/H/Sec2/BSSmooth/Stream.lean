import NonUniqueEuler.H.Sec2.BSSmooth.Differentiate
import NonUniqueEuler.I.Infra.Polar.LogLaplacian
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Helper for `lem:BS-basic`(d): the stream function

Helper of `P/Sec2/BSSmooth.lean` (`02_prelim.tex:212-240`). For real `h ∈ C_c^∞` and
`ψ = Multipole.logPotentialReal h`:
* `velocity_eq_perpGrad`: `K ∗ h = ∇^⊥ψ` (the weak derivative of `log|·|`,
  `Polar.integral_log_norm_mul_fderiv`, replaces the integration by parts on `{|z| > ε}`, R6);
* `laplacian_logPotentialReal`: `Δψ = h` (`Polar.integral_log_norm_mul_laplacian`, R6);
* `divergence_velocity`, `curl_velocity`: `div u = 0`, `∂₁u₂ - ∂₂u₁ = h`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ContDiff Convolution Laplacian

namespace NonUniqueEuler.BSSmoothH

/-- `D²f(x)(v, w) = ∂_v (∂_w f)(x)`. -/
theorem fderiv_fderiv_apply_eq {f : ℂ → ℝ} {x : ℂ} (hf : DifferentiableAt ℝ (fderiv ℝ f) x)
    (v w : ℂ) : fderiv ℝ (fderiv ℝ f) x v w = dR v (dR w f) x := by
  show _ = fderiv ℝ (fun y => fderiv ℝ f y w) x v
  rw [fderiv_clm_apply hf (differentiableAt_const w)]
  simp

/-- `Δf = ∂₁∂₁f + ∂₂∂₂f` (classical). -/
theorem laplacian_eq_dR {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f) (x : ℂ) :
    Δ f x = dR 1 (dR 1 f) x + dR Complex.I (dR Complex.I f) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) x
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [fderiv_fderiv_apply_eq hd, fderiv_fderiv_apply_eq hd]

/-- Symmetry of second derivatives. -/
theorem dR_dR_comm {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (x v w : ℂ) :
    dR v (dR w f) x = dR w (dR v f) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := 1) (by simp)).differentiable one_ne_zero) x
  rw [← fderiv_fderiv_apply_eq hd, ← fderiv_fderiv_apply_eq hd]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)) v w

/-- `∂_v [k(x - ·)](t) = -∂_v k(x - t)`. -/
theorem dR_comp_sub {k : ℂ → ℝ} (hk : Differentiable ℝ k) (x v : ℂ) :
    dR v (fun t => k (x - t)) = fun t => -dR v k (x - t) := by
  funext t
  have h := ((hk (x - t)).hasFDerivAt.comp t ((hasFDerivAt_id t).const_sub x)).fderiv
  simp only [Function.comp_def] at h
  simp only [dR, h]
  simp

/-- `Δ [k(x - ·)](t) = Δk(x - t)`. -/
theorem laplacian_comp_sub {k : ℂ → ℝ} (hk : ContDiff ℝ ∞ k) (x t : ℂ) :
    Δ (fun t => k (x - t)) t = Δ k (x - t) := by
  have hk1 : Differentiable ℝ k := hk.differentiable (by simp)
  have hk2 : ∀ v, Differentiable ℝ (dR v k) := fun v => (contDiff_dR hk v).differentiable (by simp)
  have hc : ContDiff ℝ 2 (fun t => k (x - t)) :=
    (hk.of_le (by simp)).comp (contDiff_const.sub contDiff_id)
  rw [laplacian_eq_dR hc, laplacian_eq_dR (hk.of_le (by simp))]
  have e : ∀ v, dR v (dR v (fun t => k (x - t))) t = dR v (dR v k) (x - t) := by
    intro v
    rw [dR_comp_sub hk1]
    have : (fun t => -dR v k (x - t)) = fun t => (-dR v k) (x - t) := rfl
    rw [this, dR_comp_sub ((hk2 v).neg)]
    simp only [dR]
    rw [fderiv_neg]
    simp
  rw [e, e]

/-- Integrability of the convolution integrand `t ↦ k(x - t) log‖t‖`. -/
theorem integrable_comp_sub_mul_log {k : ℂ → ℝ} (hk : Continuous k) (hc : HasCompactSupport k)
    (x : ℂ) : Integrable (fun t => k (x - t) * Real.log ‖t‖) volume :=
  hc.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ).flip
    Polar.locallyIntegrable_log_norm hk x

/-- Integrability of the convolution integrand `t ↦ k(x - t) K(t)`. -/
theorem integrable_comp_sub_mul_kernel {k : ℂ → ℝ} (hk : Continuous k) (hc : HasCompactSupport k)
    (x : ℂ) : Integrable (fun t => (k (x - t) : ℂ) * biotSavartKernel t) volume :=
  (hasCompactSupport_ofReal_comp hc).convolutionExists_right (ContinuousLinearMap.mul ℝ ℂ).flip
    locallyIntegrable_biotSavartKernel (Complex.continuous_ofReal.comp hk) x

/-- `lem:BS-basic`(d): `Δψ = h`. -/
theorem laplacian_logPotentialReal {h : ℂ → ℝ} (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) :
    Δ (Multipole.logPotentialReal h) = h := by
  funext x
  have h1 : ∀ v, ContDiff ℝ ∞ (dR v h) := fun v => contDiff_dR hh v
  have h1c : ∀ v, HasCompactSupport (dR v h) := fun v => hasCompactSupport_dR hc v
  have hψ : ∀ v w, dR v (dR w (Multipole.logPotentialReal h)) =
      Multipole.logPotentialReal (dR v (dR w h)) := by
    intro v w
    have e1 : dR w (Multipole.logPotentialReal h) = Multipole.logPotentialReal (dR w h) :=
      fderiv_logPotentialReal_apply' (hh.of_le (by simp)) hc w
    rw [e1]
    exact fderiv_logPotentialReal_apply' ((h1 w).of_le (by simp)) (h1c w) v
  rw [laplacian_eq_dR ((contDiff_logPotentialReal hh hc).of_le (by simp)), hψ, hψ,
    logPotentialReal_apply_eq_integral, logPotentialReal_apply_eq_integral, ← mul_add,
    ← integral_add]
  rotate_left
  · exact integrable_comp_sub_mul_log (contDiff_dR (h1 1) 1).continuous
      (hasCompactSupport_dR (h1c 1) 1) x
  · exact integrable_comp_sub_mul_log (contDiff_dR (h1 _) _).continuous
      (hasCompactSupport_dR (h1c _) _) x
  have e : ∀ t, dR 1 (dR 1 h) (x - t) * Real.log ‖t‖ +
      dR Complex.I (dR Complex.I h) (x - t) * Real.log ‖t‖ =
      Real.log ‖t‖ * Δ (fun s => h (x - s)) t := by
    intro t
    rw [laplacian_comp_sub hh, laplacian_eq_dR (hh.of_le (by simp))]
    ring
  simp_rw [e]
  have hcs : HasCompactSupport (fun s => h (x - s)) :=
    hc.comp_homeomorph (Homeomorph.subLeft x)
  rw [Polar.integral_log_norm_mul_laplacian (h := fun s => h (x - s))
    ((hh.of_le (by simp)).comp (contDiff_const.sub contDiff_id)) hcs]
  simp only [sub_zero]
  field_simp

/-- `∫ ∂_v h(x - t) log‖t‖ dt = ∫ ⟨t, v⟩/‖t‖² h(x - t) dt` (the weak derivative of `log‖·‖`). -/
theorem integral_dR_comp_sub_mul_log {h : ℂ → ℝ} (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h)
    (x v : ℂ) :
    ∫ t, dR v h (x - t) * Real.log ‖t‖ = ∫ t, (inner ℝ t v / ‖t‖ ^ 2) * h (x - t) := by
  have hcs : HasCompactSupport (fun s => h (x - s)) :=
    hc.comp_homeomorph (Homeomorph.subLeft x)
  have hc1 : ContDiff ℝ 1 (fun s => h (x - s)) :=
    (hh.of_le (by simp)).comp (contDiff_const.sub contDiff_id)
  have := Polar.integral_log_norm_mul_fderiv hc1 hcs v
  have e : ∀ t, fderiv ℝ (fun s => h (x - s)) t v = -dR v h (x - t) := by
    intro t
    have := congrFun (dR_comp_sub (hh.differentiable (by simp)) x v) t
    exact this
  simp_rw [e] at this
  rw [← neg_neg (∫ t, (inner ℝ t v / ‖t‖ ^ 2) * h (x - t)), ← this, ← integral_neg]
  congr 1
  funext t
  ring

/-- `lem:BS-basic`(d): `u = ∇^⊥ψ`. -/
theorem velocity_eq_perpGrad {h : ℂ → ℝ} (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) :
    velocity h = Prelim.perpGrad (Multipole.logPotentialReal h) := by
  funext x
  have hpd : ∀ l : Fin 2, Prelim.pd l (Multipole.logPotentialReal h) x =
      (2 * Real.pi)⁻¹ * ∫ t, (inner ℝ t (Prelim.e2 l) / ‖t‖ ^ 2) * h (x - t) := by
    intro l
    rw [Prelim.pd, fderiv_logPotentialReal_apply (hh.of_le (by simp)) hc,
      logPotentialReal_apply_eq_integral, integral_dR_comp_sub_mul_log hh hc]
  have hint := integrable_comp_sub_mul_kernel hh.continuous hc x
  rw [Prelim.perpGrad_eq, velocity_apply_eq_integral]
  apply Complex.ext
  · have hre := integral_re hint
    simp only [RCLike.re_to_complex] at hre
    rw [← hre]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    rw [hpd 1, ← integral_const_mul, ← integral_neg]
    congr 1
    funext t
    have hk := BS.kernelComp_zero t
    simp only [BS.kernelComp, Prelim.comp2_zero] at hk
    rw [hk]
    simp [Complex.inner]
    ring
  · have him := integral_im hint
    simp only [RCLike.im_to_complex] at him
    rw [← him]
    simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero, mul_one, zero_add]
    rw [hpd 0, ← integral_const_mul]
    congr 1
    funext t
    have hk := BS.kernelComp_one t
    simp only [BS.kernelComp, Prelim.comp2_one] at hk
    rw [hk]
    simp [Complex.inner]
    ring

/-- The real part of the derivative is the derivative of the real part. -/
theorem re_fderiv_apply {u : ℂ → ℂ} {x : ℂ} (hu : DifferentiableAt ℝ u x) (v : ℂ) :
    (fderiv ℝ u x v).re = fderiv ℝ (fun y => (u y).re) x v := by
  have := (Complex.reCLM.hasFDerivAt.comp x hu.hasFDerivAt).fderiv
  simp only [Function.comp_def, Complex.reCLM_apply] at this
  rw [this]
  rfl

theorem im_fderiv_apply {u : ℂ → ℂ} {x : ℂ} (hu : DifferentiableAt ℝ u x) (v : ℂ) :
    (fderiv ℝ u x v).im = fderiv ℝ (fun y => (u y).im) x v := by
  have := (Complex.imCLM.hasFDerivAt.comp x hu.hasFDerivAt).fderiv
  simp only [Function.comp_def, Complex.imCLM_apply] at this
  rw [this]
  rfl

theorem re_velocity_eq {h : ℂ → ℝ} (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) :
    (fun y => (velocity h y).re) = fun y => -dR Complex.I (Multipole.logPotentialReal h) y := by
  rw [velocity_eq_perpGrad hh hc]
  funext y
  simp [Prelim.perpGrad_eq, Prelim.pd, dR]

theorem im_velocity_eq {h : ℂ → ℝ} (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) :
    (fun y => (velocity h y).im) = dR 1 (Multipole.logPotentialReal h) := by
  rw [velocity_eq_perpGrad hh hc]
  funext y
  simp [Prelim.perpGrad_eq, Prelim.pd, dR]

/-- `lem:BS-basic`(d): `div u = 0`. -/
theorem divergence_velocity {h : ℂ → ℝ} (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) (x : ℂ) :
    Prelim.divergence (velocity h) x = 0 := by
  have hu : DifferentiableAt ℝ (velocity h) x :=
    (contDiff_velocity hh hc).differentiable (by simp) x
  have hψ := contDiff_logPotentialReal hh hc
  rw [Prelim.divergence_eq, re_fderiv_apply hu, im_fderiv_apply hu, re_velocity_eq hh hc,
    im_velocity_eq hh hc]
  have hd : DifferentiableAt ℝ (dR Complex.I (Multipole.logPotentialReal h)) x :=
    (contDiff_dR hψ _).differentiable (by simp) x
  rw [fderiv_fun_neg]
  simp only [neg_apply]
  have := dR_dR_comm hψ x 1 Complex.I
  simp only [dR] at this ⊢
  rw [this]
  ring

/-- `lem:BS-basic`(d): `∂₁u₂ - ∂₂u₁ = h`. -/
theorem curl_velocity {h : ℂ → ℝ} (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) (x : ℂ) :
    Prelim.curl (velocity h) x = h x := by
  have hu : DifferentiableAt ℝ (velocity h) x :=
    (contDiff_velocity hh hc).differentiable (by simp) x
  have hψ := contDiff_logPotentialReal hh hc
  rw [Prelim.curl_eq, re_fderiv_apply hu, im_fderiv_apply hu, re_velocity_eq hh hc,
    im_velocity_eq hh hc]
  rw [fderiv_fun_neg]
  simp only [neg_apply, sub_neg_eq_add]
  have := laplacian_eq_dR (hψ.of_le (by simp)) x
  rw [laplacian_logPotentialReal hh hc] at this
  rw [this]
  rfl

end NonUniqueEuler.BSSmoothH
