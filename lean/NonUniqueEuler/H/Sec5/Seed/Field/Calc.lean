import NonUniqueEuler.Defs.Sec2.Conventions
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Helpers for the seed field (`lem:seed`, step 1): calculus of `∇^⊥ψ` and radial cutoffs

Helper of `P/Sec5/Seed/Field.lean` (`05_single_ring.tex:1152-1191`). Configuration-free facts:
* `divergence_perpGrad`: `div ∇^⊥ψ = 0` where `ψ` is `C²` (symmetry of second derivatives;
  copied, namespace renamed, from `H/Sec5/ReductionField/Basic.lean` of the proof
  `Sec5/ReductionField`, which this proof may not import (import rules, `README.md`));
* `contDiff_perpGrad`: `∇^⊥ψ` is `C^∞` if `ψ` is;
* `perpGrad_eq_zero_of_eventuallyEq`: `∇^⊥ψ(y) = 0` if `ψ = 0` near `y`;
* `perpGrad_rot`: `ψ ∘ O_θ = ψ` implies `∇^⊥ψ ∘ O_θ = O_θ ∘ ∇^⊥ψ`;
* `contDiff_cutoff_radial`: `x ↦ c(|x|) f(|x|)` is `C^∞` on `ℂ` if `c ∈ C^∞(ℝ)` vanishes near
  `(-∞, ε)` (`ε > 0`) and `f` is `C^∞` on `(0, ∞)`;
* `exists_cutoff`: for `0 < a < 1` a cutoff `c ∈ C^∞(ℝ)`, `c = 1` on `[a,1]`,
  `tsupport c ⊆ [3a/4, 1 + a/4]` (`ContDiffBump`).
-/

noncomputable section

open Set Filter Topology Metric
open scoped ContDiff

namespace NonUniqueEuler

namespace OneRing

namespace SeedFieldH

/-! ### `div ∇^⊥ψ = 0` -/

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

/-- `∇^⊥ψ = -∂₂ψ + i ∂₁ψ` as a function. -/
theorem perpGrad_fun_eq (ψ : ℂ → ℝ) :
    Prelim.perpGrad ψ = fun y =>
      ((-(fderiv ℝ ψ y Complex.I) : ℝ) : ℂ) + ((fderiv ℝ ψ y 1 : ℝ) : ℂ) * Complex.I := by
  funext y
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
  rw [perpGrad_fun_eq]
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

/-! ### Smoothness and support of `∇^⊥ψ` -/

/-- `∇^⊥ψ` is `C^∞` if `ψ` is. -/
theorem contDiff_perpGrad {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (Prelim.perpGrad ψ) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ ψ) := (contDiff_infty_iff_fderiv.1 hψ).2
  have h1 : ContDiff ℝ ∞ (fun y => fderiv ℝ ψ y 1) := hd.clm_apply contDiff_const
  have h2 : ContDiff ℝ ∞ (fun y => fderiv ℝ ψ y Complex.I) := hd.clm_apply contDiff_const
  rw [perpGrad_fun_eq]
  exact (Complex.ofRealCLM.contDiff.comp h2.neg).add
    ((Complex.ofRealCLM.contDiff.comp h1).mul contDiff_const)

/-- `∇^⊥ψ(y) = 0` if `ψ` vanishes near `y`. -/
theorem perpGrad_eq_zero_of_eventuallyEq {ψ : ℂ → ℝ} {y : ℂ}
    (h : ψ =ᶠ[𝓝 y] fun _ => (0 : ℝ)) : Prelim.perpGrad ψ y = 0 := by
  have hf : fderiv ℝ ψ y = 0 := by
    rw [h.fderiv_eq]
    exact fderiv_const_apply _
  simp [Prelim.perpGrad_eq, Prelim.pd, hf]

/-! ### Rotations -/

theorem rot_re (θ : ℝ) (w : ℂ) :
    (rot θ w).re = Real.cos θ * w.re - Real.sin θ * w.im := by
  simp [rot, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

theorem rot_im (θ : ℝ) (w : ℂ) :
    (rot θ w).im = Real.sin θ * w.re + Real.cos θ * w.im := by
  simp [rot, Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ring

theorem rot_rot_neg (θ : ℝ) (w : ℂ) : rot θ (rot (-θ) w) = w := by
  simp only [rot, ← mul_assoc, ← Complex.exp_add]
  push_cast
  ring_nf
  simp

/-- If `ψ ∘ O_θ = ψ`, then `Dψ(O_θ y)(O_θ w) = Dψ(y)(w)`. -/
theorem fderiv_rot_apply {ψ : ℂ → ℝ} (hψ : Differentiable ℝ ψ) {θ : ℝ}
    (hrot : ∀ x, ψ (rot θ x) = ψ x) (y w : ℂ) :
    fderiv ℝ ψ (rot θ y) (rot θ w) = fderiv ℝ ψ y w := by
  set u : ℂ := Complex.exp ((θ : ℂ) * Complex.I)
  have hL : HasFDerivAt (fun z : ℂ => rot θ z) (ContinuousLinearMap.mul ℝ ℂ u) y := by
    have := (ContinuousLinearMap.mul ℝ ℂ u).hasFDerivAt (x := y)
    have hfun : (fun z : ℂ => rot θ z) = ⇑(ContinuousLinearMap.mul ℝ ℂ u) := by
      funext z
      simp [rot, u]
    rw [hfun]
    exact this
  have hc := (hψ (rot θ y)).hasFDerivAt.comp y hL
  have heq : (ψ ∘ fun z => rot θ z) = ψ := funext hrot
  rw [heq] at hc
  rw [hc.fderiv]
  simp [rot, u]

/-- `ψ ∘ O_θ = ψ` implies `∇^⊥ψ(O_θ x) = O_θ ∇^⊥ψ(x)`. -/
theorem perpGrad_rot {ψ : ℂ → ℝ} (hψ : Differentiable ℝ ψ) {θ : ℝ}
    (hrot : ∀ x, ψ (rot θ x) = ψ x) (x : ℂ) :
    Prelim.perpGrad ψ (rot θ x) = rot θ (Prelim.perpGrad ψ x) := by
  have h1 : fderiv ℝ ψ (rot θ x) 1 = fderiv ℝ ψ x (rot (-θ) 1) := by
    rw [← fderiv_rot_apply hψ hrot x (rot (-θ) 1), rot_rot_neg]
  have h2 : fderiv ℝ ψ (rot θ x) Complex.I = fderiv ℝ ψ x (rot (-θ) Complex.I) := by
    rw [← fderiv_rot_apply hψ hrot x (rot (-θ) Complex.I), rot_rot_neg]
  apply Complex.ext
  · rw [rot_re, perpGrad_re, perpGrad_re, perpGrad_im, h2,
      Prelim.fderiv_apply_eq_inner_grad, Prelim.fderiv_apply_eq_inner_grad,
      Prelim.fderiv_apply_eq_inner_grad, rot_re, rot_im]
    simp only [Real.cos_neg, Real.sin_neg, Complex.I_re, Complex.I_im, Complex.one_re,
      Complex.one_im]
    ring
  · rw [rot_im, perpGrad_im, perpGrad_re, perpGrad_im, h1,
      Prelim.fderiv_apply_eq_inner_grad, Prelim.fderiv_apply_eq_inner_grad,
      Prelim.fderiv_apply_eq_inner_grad, rot_re, rot_im]
    simp only [Real.cos_neg, Real.sin_neg, Complex.I_re, Complex.I_im, Complex.one_re,
      Complex.one_im]
    ring

/-! ### Radial cutoffs -/

/-- `x ↦ c(|x|) f(|x|)` is `C^∞` on `ℂ` if `c ∈ C^∞(ℝ)` vanishes on `(-∞, ε)`, `ε > 0`, and `f`
is `C^∞` on `(0, ∞)`. -/
theorem contDiff_cutoff_radial {c : ℝ → ℝ} (hc : ContDiff ℝ ∞ c) {ε : ℝ} (hε : 0 < ε)
    (hc0 : ∀ r, r < ε → c r = 0) {f : ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f (Ioi 0)) :
    ContDiff ℝ ∞ (fun x : ℂ => (c ‖x‖ : ℂ) * f ‖x‖) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    have hev : (fun x : ℂ => (c ‖x‖ : ℂ) * f ‖x‖) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
      filter_upwards [ball_mem_nhds (0 : ℂ) hε] with y hy
      rw [mem_ball_zero_iff] at hy
      simp [hc0 _ hy]
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hn : ContDiffAt ℝ ∞ (fun x : ℂ => ‖x‖) x := contDiffAt_norm ℝ hx
    have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hfa : ContDiffAt ℝ ∞ f ‖x‖ := hf.contDiffAt (Ioi_mem_nhds hpos)
    have h1 : ContDiffAt ℝ ∞ (fun x : ℂ => (c ‖x‖ : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x (hc.contDiffAt.comp x hn)
    exact h1.mul (hfa.comp x hn)

/-- A cutoff for the seed: for `0 < a < 1` there is `c ∈ C^∞(ℝ)` with `c = 1` on `[a,1]` and
`tsupport c ⊆ [3a/4, 1 + a/4]`. -/
theorem exists_cutoff {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∃ c : ℝ → ℝ, ContDiff ℝ ∞ c ∧ (∀ r ∈ Icc a 1, c r = 1) ∧
      tsupport c ⊆ Icc (3 * a / 4) (1 + a / 4) := by
  let β : ContDiffBump ((a + 1) / 2) :=
    { rIn := (1 - a) / 2
      rOut := (1 - a) / 2 + a / 4
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  refine ⟨β, β.contDiff, ?_, ?_⟩
  · intro r hr
    apply β.one_of_mem_closedBall
    rw [Real.closedBall_eq_Icc]
    constructor
    · show (a + 1) / 2 - (1 - a) / 2 ≤ r
      linarith [hr.1]
    · show r ≤ (a + 1) / 2 + (1 - a) / 2
      linarith [hr.2]
  · rw [β.tsupport_eq, Real.closedBall_eq_Icc]
    intro r hr
    have h1 : (a + 1) / 2 - ((1 - a) / 2 + a / 4) ≤ r := hr.1
    have h2 : r ≤ (a + 1) / 2 + ((1 - a) / 2 + a / 4) := hr.2
    constructor <;> linarith

end SeedFieldH

end OneRing

end NonUniqueEuler
