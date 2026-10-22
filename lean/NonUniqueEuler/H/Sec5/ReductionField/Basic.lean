import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Infra.Multipole.StreamFunction
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.Isometry
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Helper for `lem:reduction`(1): calculus of `∇^⊥`, the point vortex, rotations

Helper of `P/Sec5/ReductionField.lean` (`05_single_ring.tex:146-184`). Configuration-free facts:
* `divergence_perpGrad`, `curl_perpGrad`: for `ψ` of class `C²` at `x`,
  `div ∇^⊥ψ (x) = 0` (symmetry of second derivatives) and `curl ∇^⊥ψ (x) = Δψ(x)`;
* `perpGrad_sub_const_mul`: `∇^⊥(f₁ - G f₂) = ∇^⊥f₁ - G ∇^⊥f₂` at a point where both are
  differentiable;
* the point vortex `vortex G x = G x^⊥/|x|²` (`h = K * (ω_i + ω_o) - vortex G`): it is
  `∇^⊥(G log|x|)` off `0` (`vortex_eq_perpGrad`), smooth off `0`, and `O`-equivariant;
* `biotSavartKernel_rot`, `velocity_rot`: `K(Ox) = O K(x)`, hence `(K * g)(Ox) = O (K * g)(x)` for
  every `g` with `g ∘ O = g` (`05_single_ring.tex:141-143`).
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology ComplexConjugate
open scoped ContDiff Laplacian

namespace NonUniqueEuler

namespace OneRing

namespace RedFieldH

/-! ### `div` and `curl` of `∇^⊥ψ` -/

/-- The real part of a derivative is the derivative of the real part. -/
theorem re_fderiv_apply {u : ℂ → ℂ} {x : ℂ} (hu : DifferentiableAt ℝ u x) (v : ℂ) :
    (fderiv ℝ u x v).re = fderiv ℝ (fun y => (u y).re) x v := by
  have := (Complex.reCLM.hasFDerivAt.comp x hu.hasFDerivAt).fderiv
  simp only [Function.comp_def, Complex.reCLM_apply] at this
  rw [this]
  rfl

/-- The imaginary part of a derivative is the derivative of the imaginary part. -/
theorem im_fderiv_apply {u : ℂ → ℂ} {x : ℂ} (hu : DifferentiableAt ℝ u x) (v : ℂ) :
    (fderiv ℝ u x v).im = fderiv ℝ (fun y => (u y).im) x v := by
  have := (Complex.imCLM.hasFDerivAt.comp x hu.hasFDerivAt).fderiv
  simp only [Function.comp_def, Complex.imCLM_apply] at this
  rw [this]
  rfl

theorem perpGrad_re (ψ : ℂ → ℝ) (y : ℂ) :
    (Prelim.perpGrad ψ y).re = -fderiv ℝ ψ y Complex.I := by
  simp [Prelim.perpGrad_eq, Prelim.pd]

theorem perpGrad_im (ψ : ℂ → ℝ) (y : ℂ) :
    (Prelim.perpGrad ψ y).im = fderiv ℝ ψ y 1 := by
  simp [Prelim.perpGrad_eq, Prelim.pd]

/-- `∂_w (∂_v ψ)(x) = D²ψ(x) w v`. -/
theorem fderiv_fderiv_apply {ψ : ℂ → ℝ} {x : ℂ} (hd : DifferentiableAt ℝ (fderiv ℝ ψ) x)
    (v w : ℂ) : fderiv ℝ (fun y => fderiv ℝ ψ y v) x w = fderiv ℝ (fderiv ℝ ψ) x w v := by
  rw [fderiv_clm_apply hd (differentiableAt_const v)]
  simp

theorem differentiableAt_fderiv_of_contDiffAt {ψ : ℂ → ℝ} {x : ℂ}
    (hψ : ContDiffAt ℝ 2 ψ x) : DifferentiableAt ℝ (fderiv ℝ ψ) x :=
  (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero

theorem differentiableAt_perpGrad {ψ : ℂ → ℝ} {x : ℂ} (hψ : ContDiffAt ℝ 2 ψ x) :
    DifferentiableAt ℝ (Prelim.perpGrad ψ) x := by
  have hd := differentiableAt_fderiv_of_contDiffAt hψ
  have h1 : DifferentiableAt ℝ (fun y => fderiv ℝ ψ y 1) x :=
    hd.clm_apply (differentiableAt_const _)
  have h2 : DifferentiableAt ℝ (fun y => fderiv ℝ ψ y Complex.I) x :=
    hd.clm_apply (differentiableAt_const _)
  have heq : Prelim.perpGrad ψ = fun y =>
      ((-(fderiv ℝ ψ y Complex.I) : ℝ) : ℂ) + ((fderiv ℝ ψ y 1 : ℝ) : ℂ) * Complex.I := by
    funext y
    simp [Prelim.perpGrad_eq, Prelim.pd]
  rw [heq]
  have hc := Complex.ofRealCLM.differentiableAt (x := (0 : ℝ))
  exact ((Complex.ofRealCLM.differentiable.differentiableAt.comp x h2.neg).add
    ((Complex.ofRealCLM.differentiable.differentiableAt.comp x h1).mul_const _))

/-- `div ∇^⊥ψ = 0` at a point where `ψ` is `C²`. -/
theorem divergence_perpGrad {ψ : ℂ → ℝ} {x : ℂ} (hψ : ContDiffAt ℝ 2 ψ x) :
    Prelim.divergence (Prelim.perpGrad ψ) x = 0 := by
  have hd := differentiableAt_fderiv_of_contDiffAt hψ
  have hu := differentiableAt_perpGrad hψ
  rw [Prelim.divergence_eq, re_fderiv_apply hu, im_fderiv_apply hu]
  have hre : (fun y => (Prelim.perpGrad ψ y).re) = fun y => -fderiv ℝ ψ y Complex.I :=
    funext (perpGrad_re ψ)
  have him : (fun y => (Prelim.perpGrad ψ y).im) = fun y => fderiv ℝ ψ y 1 :=
    funext (perpGrad_im ψ)
  rw [hre, him, fderiv_fun_neg, neg_apply, fderiv_fderiv_apply hd,
    fderiv_fderiv_apply hd]
  have hsymm := hψ.isSymmSndFDerivAt (by simp) 1 Complex.I
  rw [hsymm]
  ring

/-- `curl ∇^⊥ψ = Δψ` at a point where `ψ` is `C²`. -/
theorem curl_perpGrad {ψ : ℂ → ℝ} {x : ℂ} (hψ : ContDiffAt ℝ 2 ψ x) :
    Prelim.curl (Prelim.perpGrad ψ) x = Δ ψ x := by
  have hd := differentiableAt_fderiv_of_contDiffAt hψ
  have hu := differentiableAt_perpGrad hψ
  rw [Prelim.curl_eq, re_fderiv_apply hu, im_fderiv_apply hu]
  have hre : (fun y => (Prelim.perpGrad ψ y).re) = fun y => -fderiv ℝ ψ y Complex.I :=
    funext (perpGrad_re ψ)
  have him : (fun y => (Prelim.perpGrad ψ y).im) = fun y => fderiv ℝ ψ y 1 :=
    funext (perpGrad_im ψ)
  rw [hre, him, fderiv_fun_neg, neg_apply, fderiv_fderiv_apply hd,
    fderiv_fderiv_apply hd, InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- `∇^⊥(f₁ - G f₂) = ∇^⊥f₁ - G ∇^⊥f₂` at a point where `f₁`, `f₂` are differentiable. -/
theorem perpGrad_sub_const_mul {f₁ f₂ : ℂ → ℝ} {x : ℂ} (h₁ : DifferentiableAt ℝ f₁ x)
    (h₂ : DifferentiableAt ℝ f₂ x) (G : ℝ) :
    Prelim.perpGrad (fun y => f₁ y - G * f₂ y) x =
      Prelim.perpGrad f₁ x - (G : ℂ) * Prelim.perpGrad f₂ x := by
  have hfd : fderiv ℝ (fun y => f₁ y - G * f₂ y) x = fderiv ℝ f₁ x - G • fderiv ℝ f₂ x := by
    rw [fderiv_fun_sub h₁ (h₂.const_mul G), fderiv_const_mul h₂]
  simp only [Prelim.perpGrad_eq, Prelim.pd, hfd, sub_apply,
    smul_apply, smul_eq_mul, Prelim.e2_zero, Prelim.e2_one]
  apply Complex.ext <;> simp; ring

/-! ### The point vortex `G x^⊥/|x|²` -/

/-- The point vortex `G x^⊥/|x|²` (`05_single_ring.tex:98-101`), in the form used by
`RingConfig.h`. -/
def vortex (G : ℝ) (x : ℂ) : ℂ :=
  (G : ℂ) * (Complex.I * x) / (((‖x‖ ^ 2 : ℝ)) : ℂ)

theorem h_eq_velocity_sub_vortex (c : RingConfig) (t : ℝ) (x : ℂ) :
    c.h t x = velocity (fun y => c.innerPart t y + c.outerPart t y) x - vortex c.G x := rfl

/-- `∇^⊥ log|x| = x^⊥/|x|²` off `0`. -/
theorem perpGrad_log_norm {x : ℂ} (hx : x ≠ 0) :
    Prelim.perpGrad (fun y : ℂ => Real.log ‖y‖) x =
      Complex.I * x / (((‖x‖ ^ 2 : ℝ)) : ℂ) := by
  have hfd := (Multipole.hasFDerivAt_log_norm hx).fderiv
  have hn : (‖x‖ ^ 2 : ℝ) ≠ 0 := by positivity
  simp only [Prelim.perpGrad_eq, Prelim.pd, hfd, smul_apply,
    innerSL_apply_apply, smul_eq_mul, Prelim.e2_zero, Prelim.e2_one]
  rw [div_eq_inv_mul, ← Complex.ofReal_inv]
  apply Complex.ext
  · simp [Complex.inner]
    ring
  · simp [Complex.inner]
    ring

/-- The point vortex is `∇^⊥(G log|x|)` off `0`. -/
theorem vortex_eq_perpGrad (G : ℝ) {x : ℂ} (hx : x ≠ 0) :
    vortex G x = (G : ℂ) * Prelim.perpGrad (fun y : ℂ => Real.log ‖y‖) x := by
  rw [perpGrad_log_norm hx, vortex]
  ring

/-- The point vortex is smooth off `0`. -/
theorem contDiffOn_vortex (G : ℝ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (vortex G) {0}ᶜ := by
  intro x hx
  have hx0 : x ≠ 0 := hx
  have hn : ((‖x‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have : (‖x‖ ^ 2 : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℂ => (G : ℂ) * (Complex.I * y)) x :=
    contDiffAt_const.mul (contDiffAt_const.mul contDiffAt_id)
  have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℂ => (((‖y‖ ^ 2 : ℝ)) : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x (contDiff_norm_sq ℝ).contDiffAt
  have h3 := h1.mul (h2.inv hn)
  have heq : vortex G = (fun y : ℂ => (G : ℂ) * (Complex.I * y)) *
      (fun y : ℂ => (((‖y‖ ^ 2 : ℝ)) : ℂ))⁻¹ := by
    funext y
    simp [vortex, div_eq_mul_inv]
  rw [heq]
  exact h3.contDiffWithinAt

theorem norm_exp_mul_I (θ : ℝ) : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I θ

theorem norm_rot (θ : ℝ) (x : ℂ) : ‖rot θ x‖ = ‖x‖ := by
  rw [rot, norm_mul, norm_exp_mul_I, one_mul]

/-- The point vortex is `O`-equivariant. -/
theorem vortex_rot (G θ : ℝ) (x : ℂ) : vortex G (rot θ x) = rot θ (vortex G x) := by
  rw [vortex, vortex, norm_rot, rot, rot]
  ring

/-! ### Rotation equivariance of the Biot–Savart law -/

theorem biotSavartKernel_rot (θ : ℝ) (z : ℂ) :
    biotSavartKernel (rot θ z) = rot θ (biotSavartKernel z) := by
  rw [biotSavartKernel, biotSavartKernel, norm_rot, rot, rot]
  ring

theorem rot_sub (θ : ℝ) (x y : ℂ) : rot θ x - rot θ y = rot θ (x - y) := by
  simp only [rot]
  ring

theorem rot_eq_rotation (θ : ℝ) (x : ℂ) : rot θ x = rotation (Circle.exp θ) x := by
  rw [rotation_apply, Circle.coe_exp, rot]

/-- `(K * g)(Ox) = O (K * g)(x)` for every `g` with `g ∘ O = g` (`05_single_ring.tex:141-143`). -/
theorem velocity_rot {g : ℂ → ℝ} {θ : ℝ} (hg : ∀ y, g (rot θ y) = g y) (x : ℂ) :
    velocity g (rot θ x) = rot θ (velocity g x) := by
  let R : ℂ ≃ₗᵢ[ℝ] ℂ := rotation (Circle.exp θ)
  have hmp : MeasurePreserving R volume volume := R.measurePreserving
  have hme : MeasurableEmbedding R := R.toHomeomorph.measurableEmbedding
  rw [velocity, ← hmp.integral_comp hme]
  have hfun : (fun z => biotSavartKernel (rot θ x - R z) * (g (R z) : ℂ)) =
      fun z => Complex.exp ((θ : ℂ) * Complex.I) * (biotSavartKernel (x - z) * (g z : ℂ)) := by
    funext z
    have hRz : R z = rot θ z := (rot_eq_rotation θ z).symm
    rw [hRz, hg, rot_sub, biotSavartKernel_rot, rot]
    ring
  rw [hfun, integral_const_mul, velocity, rot]

end RedFieldH

end OneRing

end NonUniqueEuler
