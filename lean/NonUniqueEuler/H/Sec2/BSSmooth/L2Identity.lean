import NonUniqueEuler.H.Sec2.BSSmooth.Stream
import NonUniqueEuler.H.Sec2.BSSmooth.Decay
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Helper for `lem:BS-basic`(d): the `L²` identity `Σ_{i,l} ‖∂_l u_i‖² = ‖h‖²`

Helper of `P/Sec2/BSSmooth.lean` (`02_prelim.tex:250-261`). For real `h ∈ C_c^∞` and `u = K ∗ h`:
pointwise, with `div u = 0` and `curl u = h`,
`|∂₁u|² + |∂₂u|² = (div u)² + (curl u)² - 2 det ∇u = h² - 2 Im(conj(∂₁u) ∂₂u)`,
and `∫ conj(∂₁u) ∂₂u` is real: two whole-plane integrations by parts
(`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`, with the decay `u = O(|x|^{-1})`,
`∇u = O(|x|^{-2})`, `∇²u = O(|x|^{-3})`) and `∂₁∂₂u = ∂₂∂₁u` give
`∫ conj(∂₁u) ∂₂u = -∫ conj(u) ∂₁∂₂u = ∫ conj(∂₂u) ∂₁u = conj ∫ conj(∂₁u) ∂₂u`.

Deviation (restructuring, in the spirit of R6): the manuscript integrates by parts twice on
`B_r` the second derivatives of `ψ` and lets `r → ∞`; here the null-Lagrangian form of the same
computation (`det ∇u` integrates to zero) is used on the whole plane.
-/

noncomputable section

open MeasureTheory Set Metric Filter ComplexConjugate
open scoped ContDiff ENNReal

namespace NonUniqueEuler.BSSmoothH

/-- `‖F‖²_{L²} = ∫ |F|²` for `F ∈ L²`. -/
theorem l2_sq_eq_integral {F : ℂ → ℂ} (hF : MemLp F 2 volume) :
    Sob.l2 F ^ 2 = ∫ x, ‖F x‖ ^ 2 := by
  have hnn : 0 ≤ ∫ x, ‖F x‖ ^ (2 : ℝ) := integral_nonneg fun x => by positivity
  rw [Sob.l2, hF.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  rw [ENNReal.toReal_ofReal (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hnn]
  norm_num

/-- `D²u(x)(v, w) = ∂_v(∂_w u)(x)` for complex-valued `u`. -/
theorem fderiv_fderiv_apply_eq_C {u : ℂ → ℂ} {x : ℂ} (hu : DifferentiableAt ℝ (fderiv ℝ u) x)
    (v w : ℂ) : fderiv ℝ (fderiv ℝ u) x v w = fderiv ℝ (fun y => fderiv ℝ u y w) x v := by
  rw [fderiv_clm_apply hu (differentiableAt_const w)]
  simp

theorem fderiv_conj_apply {u : ℂ → ℂ} {x : ℂ} (hu : DifferentiableAt ℝ u x) (v : ℂ) :
    fderiv ℝ (fun y => conj (u y)) x v = conj (fderiv ℝ u x v) := by
  have := (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp x hu.hasFDerivAt).fderiv
  simp only [Function.comp_def, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply] at this
  rw [this]
  rfl

theorem differentiable_conj_comp {u : ℂ → ℂ} (hu : Differentiable ℝ u) :
    Differentiable ℝ fun y => conj (u y) :=
  fun x => (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp x
    (hu x).hasFDerivAt).differentiableAt

/-- The pointwise identity `|∂₁u|² + |∂₂u|² = (curl u)² - 2 Im(conj(∂₁u) ∂₂u)` when
`div u = 0`. -/
theorem norm_sq_add_norm_sq_eq (a b : ℂ) (hdiv : a.re + b.im = 0) :
    ‖a‖ ^ 2 + ‖b‖ ^ 2 = (a.im - b.re) ^ 2 - 2 * (conj a * b).im := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
  have hd : b.im = -a.re := by linarith
  rw [hd]
  ring

section Velocity

variable {h : ℂ → ℝ}

theorem contDiff_fderiv_velocity_apply (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) (w : ℂ) :
    ContDiff ℝ ∞ fun y => fderiv ℝ (velocity h) y w :=
  ((contDiff_velocity hh hc).fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

theorem continuous_fderiv_fderiv_velocity_apply (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h)
    (v w : ℂ) : Continuous fun x => fderiv ℝ (fderiv ℝ (velocity h)) x v w := by
  have hDDu : Continuous fun x => fderiv ℝ (fderiv ℝ (velocity h)) x :=
    ((contDiff_velocity hh hc).fderiv_right (m := 1) (by simp)).continuous_fderiv (by simp)
  exact (hDDu.clm_apply continuous_const).clm_apply continuous_const

theorem differentiable_fderiv_velocity (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) :
    Differentiable ℝ (fderiv ℝ (velocity h)) :=
  ((contDiff_velocity hh hc).fderiv_right (m := ∞) le_rfl).differentiable (by simp)

theorem decaysLike_conj_velocity (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) :
    DecaysLike (fun y => conj (velocity h y)) 1 :=
  (decaysLike_velocity hh.continuous hc).mono_norm fun x => by simp

theorem decaysLike_conj_fderiv_velocity (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h)
    (v : ℂ) : DecaysLike (fun y => conj (fderiv ℝ (velocity h) y v)) 2 :=
  (decaysLike_fderiv_velocity hh.continuous hc v).mono_norm fun x => by simp

/-- `∫ conj(∂_v u) ∂_w u` converges. -/
theorem integrable_conj_fderiv_mul_fderiv (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h)
    (v w : ℂ) :
    Integrable (fun x => conj (fderiv ℝ (velocity h) x v) * fderiv ℝ (velocity h) x w) volume :=
  ((decaysLike_conj_fderiv_velocity hh hc v).mul
    (decaysLike_fderiv_velocity hh.continuous hc w)).integrable
    ((Complex.continuous_conj.comp (contDiff_fderiv_velocity_apply hh hc v).continuous).mul
      (contDiff_fderiv_velocity_apply hh hc w).continuous) (by norm_num)

/-- One whole-plane integration by parts: `∫ conj(u) ∂_v∂_w u = -∫ conj(∂_v u) ∂_w u`. -/
theorem integral_conj_mul_fderiv_fderiv (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h)
    (v w : ℂ) :
    ∫ x, conj (velocity h x) * fderiv ℝ (fun y => fderiv ℝ (velocity h) y w) x v =
      -∫ x, conj (fderiv ℝ (velocity h) x v) * fderiv ℝ (velocity h) x w := by
  have hud : Differentiable ℝ (velocity h) := (contDiff_velocity hh hc).differentiable (by simp)
  have e1 : ∀ x, fderiv ℝ (fun y => conj (velocity h y)) x v =
      conj (fderiv ℝ (velocity h) x v) :=
    fun x => fderiv_conj_apply (hud x) v
  have e2 : ∀ x, fderiv ℝ (fun y => fderiv ℝ (velocity h) y w) x v =
      fderiv ℝ (fderiv ℝ (velocity h)) x v w :=
    fun x => (fderiv_fderiv_apply_eq_C (differentiable_fderiv_velocity hh hc x) v w).symm
  have huc : Continuous fun y => conj (velocity h y) :=
    Complex.continuous_conj.comp (contDiff_velocity hh hc).continuous
  have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun y => conj (velocity h y)) (g := fun y => fderiv ℝ (velocity h) y w) (v := v) ?_ ?_ ?_
    (fun x _ => differentiable_conj_comp hud x)
    (fun x _ => (contDiff_fderiv_velocity_apply hh hc w).differentiable (by simp) x)
  · simpa only [e1] using this
  · simp only [e1]
    exact integrable_conj_fderiv_mul_fderiv hh hc v w
  · simp only [e2]
    exact ((decaysLike_conj_velocity hh hc).mul
      (decaysLike_fderiv_fderiv_velocity hh.continuous hc v w)).integrable
      (huc.mul (continuous_fderiv_fderiv_velocity_apply hh hc v w)) (by norm_num)
  · exact ((decaysLike_conj_velocity hh hc).mul
      (decaysLike_fderiv_velocity hh.continuous hc w)).integrable
      (huc.mul (contDiff_fderiv_velocity_apply hh hc w).continuous) (by norm_num)

/-- `∫ conj(∂₁u) ∂₂u` is real (`det ∇u` integrates to zero). -/
theorem im_integral_conj_pd_mul_pd (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) :
    (∫ x, conj (fderiv ℝ (velocity h) x 1) * fderiv ℝ (velocity h) x Complex.I).im = 0 := by
  have hu := contDiff_velocity hh hc
  have hsym : ∀ x, fderiv ℝ (fun y => fderiv ℝ (velocity h) y Complex.I) x 1 =
      fderiv ℝ (fun y => fderiv ℝ (velocity h) y 1) x Complex.I := by
    intro x
    rw [← fderiv_fderiv_apply_eq_C (differentiable_fderiv_velocity hh hc x),
      ← fderiv_fderiv_apply_eq_C (differentiable_fderiv_velocity hh hc x)]
    exact (hu.contDiffAt.isSymmSndFDerivAt (by simp)) 1 Complex.I
  have hreal : ∫ x, conj (fderiv ℝ (velocity h) x 1) * fderiv ℝ (velocity h) x Complex.I =
      ∫ x, conj (fderiv ℝ (velocity h) x Complex.I) * fderiv ℝ (velocity h) x 1 := by
    have h1 := integral_conj_mul_fderiv_fderiv hh hc 1 Complex.I
    have h2 := integral_conj_mul_fderiv_fderiv hh hc Complex.I 1
    simp_rw [hsym] at h1
    rw [h1] at h2
    exact neg_injective h2
  have : ∫ x, conj (fderiv ℝ (velocity h) x Complex.I) * fderiv ℝ (velocity h) x 1 =
      conj (∫ x, conj (fderiv ℝ (velocity h) x 1) * fderiv ℝ (velocity h) x Complex.I) := by
    rw [← integral_conj]
    congr 1
    funext x
    simp [mul_comm]
  rw [this] at hreal
  exact Complex.conj_eq_iff_im.mp hreal.symm

/-- `lem:BS-basic`(d), `γ = 0`: `‖∂₁u‖²_{L²} + ‖∂₂u‖²_{L²} = ‖h‖²_{L²}` for `u = K ∗ h`. -/
theorem sum_l2_pd_velocity (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) :
    ∑ l : Fin 2, Sob.l2 (Prelim.pd l (velocity h)) ^ 2 = Sob.l2 (fun y => (h y : ℂ)) ^ 2 := by
  have hL2 : ∀ v, MemLp (fun x => fderiv ℝ (velocity h) x v) 2 volume :=
    fun v => (memLp_fderiv_velocity hh hc v).1
  have hL2h : MemLp (fun y => (h y : ℂ)) 2 volume :=
    (Complex.continuous_ofReal.comp hh.continuous).memLp_of_hasCompactSupport
      (hasCompactSupport_ofReal_comp hc)
  have hpw : ∀ x, ‖fderiv ℝ (velocity h) x 1‖ ^ 2 + ‖fderiv ℝ (velocity h) x Complex.I‖ ^ 2 =
      (h x) ^ 2 - 2 * (conj (fderiv ℝ (velocity h) x 1) * fderiv ℝ (velocity h) x Complex.I).im := by
    intro x
    have hdiv := divergence_velocity hh hc x
    have hcurl := curl_velocity hh hc x
    rw [Prelim.divergence_eq] at hdiv
    rw [Prelim.curl_eq] at hcurl
    rw [norm_sq_add_norm_sq_eq _ _ hdiv, ← hcurl]
  have hsq : ∀ F : ℂ → ℂ, MemLp F 2 volume → Integrable (fun x => ‖F x‖ ^ 2) volume :=
    fun F hF => (memLp_two_iff_integrable_sq_norm hF.1).mp hF
  rw [Fin.sum_univ_two]
  change Sob.l2 (fun x => fderiv ℝ (velocity h) x 1) ^ 2 +
    Sob.l2 (fun x => fderiv ℝ (velocity h) x Complex.I) ^ 2 = _
  rw [l2_sq_eq_integral (hL2 1), l2_sq_eq_integral (hL2 Complex.I), l2_sq_eq_integral hL2h,
    ← integral_add (hsq _ (hL2 1)) (hsq _ (hL2 Complex.I))]
  simp_rw [hpw]
  have hhsq : Integrable (fun x => (h x) ^ 2) volume := by
    have : HasCompactSupport (fun x => (h x) ^ 2) :=
      hc.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
    exact (hh.continuous.pow 2).integrable_of_hasCompactSupport this
  have hI1 := integrable_conj_fderiv_mul_fderiv hh hc 1 Complex.I
  have himI : Integrable (fun x => 2 * (conj (fderiv ℝ (velocity h) x 1) *
      fderiv ℝ (velocity h) x Complex.I).im) volume := by
    have := hI1.im
    exact this.const_mul 2
  have him := integral_im hI1
  simp only [RCLike.im_to_complex] at him
  rw [integral_sub hhsq himI, integral_const_mul, him, im_integral_conj_pd_mul_pd hh hc]
  simp only [mul_zero, sub_zero]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [Complex.norm_real, sq_abs]

end Velocity

end NonUniqueEuler.BSSmoothH
