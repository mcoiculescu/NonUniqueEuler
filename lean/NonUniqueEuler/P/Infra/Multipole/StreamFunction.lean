import NonUniqueEuler.Defs.Infra.Multipole
import NonUniqueEuler.I.Infra.Multipole.CauchySmooth
import NonUniqueEuler.I.Infra.Multipole.Holomorphic
import NonUniqueEuler.H.Infra.Multipole.StreamFunction.Gradient
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Proof of `I/Infra/Multipole/StreamFunction.lean` (I-MULT, R11)

* `hasFDerivAt_log_norm`, `harmonicOnNhd_log_norm`: the point vortex (`y = 0` case of
  `hasFDerivAt_log_norm_sub`; Mathlib's `AnalyticAt.harmonicAt_log_norm` for `f = id`).
* The stream function `ψ = logPotentialReal g` near a point `x₀ ∈ U`
  (`logPotentialReal_local_dichotomy`, in the helper file): either the integral defining `ψ`
  converges near `x₀`, and then `∇ψ = -i (K ⋆ g)` there by differentiation under the integral
  sign, or it diverges near `x₀`, and then `ψ = 0` (the junk value) there.
* Smoothness: in the first case `Dψ = innerSL ∘ (-i (K ⋆ g))`, which is `C^∞` because the velocity
  is (`contDiffOn_velocity`); in the second case `ψ` is locally constant.
* Harmonicity: `K ⋆ g = conj F` with `F = (2πi)⁻¹ C[g]` holomorphic on `U`, so
  `D²ψ(y)(a, a) = ⟨-i conj (F'(y) a), a⟩`, and `Δψ = ⟨-i conj F', 1⟩ + ⟨-i conj (F' i), i⟩ = 0`.
  This avoids differentiating twice under the integral sign.
* `fderiv_logPotentialReal`: differentiation under the integral sign, under the convergence
  hypothesis `hlog` (`fderiv_logPotentialReal_of_integrable` in the helper file); `hlog` holds
  for `g` vanishing outside a ball (`integrable_log_norm_sub_mul_of_vanishing_outside`).
-/

noncomputable section

open MeasureTheory Set Metric Real Filter Topology ComplexConjugate Laplacian
open scoped ContDiff

namespace NonUniqueEuler.Multipole

/-- `log‖·‖` has gradient `z/‖z‖²` at `z ≠ 0`. -/
theorem hasFDerivAt_log_norm {z : ℂ} (hz : z ≠ 0) :
    HasFDerivAt (fun x : ℂ => Real.log ‖x‖) ((‖z‖ ^ 2)⁻¹ • innerSL ℝ z) z := by
  simpa using hasFDerivAt_log_norm_sub (y := 0) hz

/-- `log‖·‖` is harmonic on `ℂ \ {0}`. -/
theorem harmonicOnNhd_log_norm :
    InnerProductSpace.HarmonicOnNhd (fun x : ℂ => Real.log ‖x‖) {0}ᶜ := by
  intro x hx
  exact AnalyticAt.harmonicAt_log_norm (f := id) analyticAt_id hx

/-- The stream function is smooth where `g` vanishes nearby. -/
theorem contDiffOn_logPotentialReal {g : ℂ → ℝ} (hg : Integrable g) {U : Set ℂ}
    (hU : IsOpen U) (hsep : ∀ z ∈ U, ∃ δ > 0, ∀ᵐ w, w ∈ ball z δ → g w = 0) :
    ContDiffOn ℝ ∞ (logPotentialReal g) U := by
  intro x₀ hx₀
  rcases logPotentialReal_local_dichotomy hg hU hsep hx₀ with ⟨V, hVo, hx₀V, hVU, hV⟩ | h0
  · have hG : ContDiffOn ℝ ∞ (fun x => innerSL ℝ (-(Complex.I * velocity g x))) V :=
      (innerSL ℝ).contDiff.comp_contDiffOn
        ((contDiffOn_const.mul ((contDiffOn_velocity hg hU hsep).mono hVU)).neg)
    have hsmooth : ContDiffOn ℝ ∞ (logPotentialReal g) V := by
      rw [contDiffOn_infty_iff_fderiv_of_isOpen hVo]
      exact ⟨fun x hx => (hV x hx).differentiableAt.differentiableWithinAt,
        hG.congr fun x hx => (hV x hx).fderiv⟩
    exact (hsmooth.contDiffAt (hVo.mem_nhds hx₀V)).contDiffWithinAt
  · exact (contDiffAt_const.congr_of_eventuallyEq h0).contDiffWithinAt

/-- The integral defining the stream function `ψ(z)` converges when `g ∈ L¹` vanishes a.e.
outside a ball and a.e. near `z`. Supplies `hlog` of `fderiv_logPotentialReal` for compactly
supported vorticities (all consumers). -/
theorem integrable_log_norm_sub_mul_of_vanishing_outside {g : ℂ → ℝ} (hg : Integrable g)
    {R : ℝ} (hR : ∀ᵐ y, R < ‖y‖ → g y = 0) {z : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hsupp : ∀ᵐ w, w ∈ ball z δ → g w = 0) :
    Integrable fun y => Real.log ‖z - y‖ * g y :=
  integrable_log_norm_sub_mul_of_bounded_support hg hR hδ hsupp

/-- `∇ψ = -i (K ⋆ g)`, i.e. `K ⋆ g = ∇^⊥ψ`, where `g` vanishes nearby and the integral defining
`ψ(z)` converges (`hlog`; without it the statement is false, see the module docstring). -/
theorem fderiv_logPotentialReal {g : ℂ → ℝ} (hg : Integrable g) {U : Set ℂ} (hU : IsOpen U)
    (hsep : ∀ z ∈ U, ∃ δ > 0, ∀ᵐ w, w ∈ ball z δ → g w = 0) {z : ℂ} (hz : z ∈ U)
    (hlog : Integrable fun y => Real.log ‖z - y‖ * g y) (v : ℂ) :
    fderiv ℝ (logPotentialReal g) z v = inner ℝ (-(Complex.I * velocity g z)) v :=
  fderiv_logPotentialReal_of_integrable hg hU hsep hz hlog v

/-- The algebraic identity behind `Δψ = 0`: `⟨-i conj d, 1⟩ + ⟨-i conj (d i), i⟩ = 0`. -/
private theorem inner_neg_I_conj_add_inner_neg_I_conj (d : ℂ) :
    inner ℝ (-(Complex.I * conj (d * 1))) (1 : ℂ) +
      inner ℝ (-(Complex.I * conj (d * Complex.I))) Complex.I = 0 := by
  simp only [Complex.inner, mul_one, map_mul, Complex.conj_I, map_neg, Complex.mul_re,
    Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.conj_re, Complex.conj_im,
    Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im]
  ring

/-- The stream function is harmonic where `g` vanishes nearby. -/
theorem harmonicOnNhd_logPotentialReal {g : ℂ → ℝ} (hg : Integrable g) {U : Set ℂ}
    (hU : IsOpen U) (hsep : ∀ z ∈ U, ∃ δ > 0, ∀ᵐ w, w ∈ ball z δ → g w = 0) :
    InnerProductSpace.HarmonicOnNhd (logPotentialReal g) U := by
  intro x₀ hx₀
  have hsm := contDiffOn_logPotentialReal hg hU hsep
  have hvsm := contDiffOn_velocity hg hU hsep
  rcases logPotentialReal_local_dichotomy hg hU hsep hx₀ with ⟨V, hVo, hx₀V, hVU, hV⟩ | h0
  · refine ⟨(hsm.contDiffAt (hU.mem_nhds hx₀)).of_le (by simp), ?_⟩
    -- the holomorphic function `F = (2πi)⁻¹ C[g]` with `K ⋆ g = conj F`
    set F : ℂ → ℂ := fun x => (2 * π * Complex.I)⁻¹ * cauchyTransform (fun w => (g w : ℂ)) x
      with hFdef
    have hsepc : ∀ z ∈ U, ∃ δ > 0, ∀ᵐ w, w ∈ ball z δ → (g w : ℂ) = 0 := by
      intro z hz
      obtain ⟨δ, hδ, h⟩ := hsep z hz
      exact ⟨δ, hδ, h.mono fun w hw hb => by simp [hw hb]⟩
    have hF : DifferentiableOn ℂ F U :=
      (differentiableOn_cauchyTransform hg.ofReal hU hsepc).const_mul _
    have hvel : velocity g = fun x => conj (F x) :=
      funext (velocity_eq_conj_cauchyTransform g)
    filter_upwards [hVo.mem_nhds hx₀V] with y hy
    have hyU : y ∈ U := hVU hy
    have hDv : ∀ a, fderiv ℝ (velocity g) y a = conj (iteratedDeriv 1 F y * a) := by
      intro a
      have h := iteratedFDeriv_real_conj_apply_eq hU hF hyU 1 ![a]
      rw [iteratedFDeriv_one_apply, ← hvel] at h
      simpa using h
    have hvd : DifferentiableAt ℝ (velocity g) y :=
      (hvsm.contDiffAt (hU.mem_nhds hyU)).differentiableAt (by simp)
    have hGd : HasFDerivAt (fun x => -(Complex.I * velocity g x))
        (-(Complex.I • fderiv ℝ (velocity g) y)) y :=
      (hvd.hasFDerivAt.const_mul Complex.I).neg
    have hfd : fderiv ℝ (logPotentialReal g) =ᶠ[𝓝 y]
        fun x => innerSL ℝ (-(Complex.I * velocity g x)) := by
      filter_upwards [hVo.mem_nhds hy] with x hx using (hV x hx).fderiv
    have h2 : fderiv ℝ (fderiv ℝ (logPotentialReal g)) y =
        (innerSL ℝ).comp (-(Complex.I • fderiv ℝ (velocity g) y)) := by
      rw [hfd.fderiv_eq]
      exact ((innerSL ℝ).hasFDerivAt.comp y hGd).fderiv
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
    simp only [iteratedFDeriv_two_apply, h2, Matrix.cons_val_zero, Matrix.cons_val_one,
      ContinuousLinearMap.comp_apply, neg_apply,
      smul_apply, innerSL_apply_apply, smul_eq_mul, hDv, Pi.zero_apply]
    exact inner_neg_I_conj_add_inner_neg_I_conj _
  · exact (InnerProductSpace.harmonicAt_congr_nhds h0).2 (InnerProductSpace.harmonicAt_const 0)

end NonUniqueEuler.Multipole
