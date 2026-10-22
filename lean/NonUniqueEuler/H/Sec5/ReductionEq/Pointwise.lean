import NonUniqueEuler.Defs.Sec5.All
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Helpers for `lem:reduction`(3): the right side of `eq:ring` at a point

Helper of `P/Sec5/ReductionEq.lean`. For a real perturbation `w_R` (complexified to
`W = (w_R : ℂ)`) at a point `x` where the weak first derivatives of `W` and of `Φ` are the
classical ones, the right side of `eq:ring`,
`ringRHS χ G h W x = L(G)W + B(W,W) - h·∇W - h·∇Φ`, is the classical expression
`-(Ω(|x|;G) ∂_θ w_R + (K_BS*w_R)·∇Φ + (K_BS*w_R)·∇w_R + h·∇w_R + h·∇Φ)(x)`
(`ringRHS_eq_classical`; `05_single_ring.tex:211-215`). Also: `x^⊥·∇Φ = ∂_θ Φ = 0` for a radial
`Φ` (`fderiv_mul_I_eq_zero_of_radial`), and real-valued functions have real directional
derivatives (`fderiv_ofReal_apply`).
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace NonUniqueEuler.OneRing.RedEqH

open RingData

/-- The directional derivative of a complexified real function is the complexified directional
derivative. -/
theorem fderiv_ofReal_apply {f : ℂ → ℝ} {x : ℂ} (hf : DifferentiableAt ℝ f x) (v : ℂ) :
    fderiv ℝ (fun y => ((f y : ℝ) : ℂ)) x v = ((fderiv ℝ f x v : ℝ) : ℂ) := by
  have h : HasFDerivAt (fun y => ((f y : ℝ) : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ f x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x hf.hasFDerivAt
  rw [h.fderiv]
  rfl

/-- `U₁ ∂₁f + U₂ ∂₂f = Df(x)U`. -/
theorem re_mul_add_im_mul (L : ℂ →L[ℝ] ℝ) (U : ℂ) :
    ((U.re : ℝ) : ℂ) * ((L 1 : ℝ) : ℂ) + ((U.im : ℝ) : ℂ) * ((L Complex.I : ℝ) : ℂ) =
      ((L U : ℝ) : ℂ) := by
  have hU : U = U.re • (1 : ℂ) + U.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_rhs => rw [hU]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  push_cast
  ring

/-- `x₁ ∂₂f - x₂ ∂₁f = Df(x)(x^⊥)` with `x^⊥ = i x`. -/
theorem re_mul_sub_im_mul (L : ℂ →L[ℝ] ℝ) (x : ℂ) :
    ((x.re : ℝ) : ℂ) * ((L Complex.I : ℝ) : ℂ) - ((x.im : ℝ) : ℂ) * ((L 1 : ℝ) : ℂ) =
      ((L (Complex.I * x) : ℝ) : ℂ) := by
  have hU : Complex.I * x = (-x.im) • (1 : ℂ) + x.re • Complex.I := by
    apply Complex.ext <;> simp
  rw [hU, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  push_cast
  ring

/-- `x^⊥ · ∇Φ = ∂_θ Φ = 0` for a pointwise radial `Φ`. -/
theorem fderiv_mul_I_eq_zero_of_radial {P : ℂ → ℝ} (hrad : IsRadialPointwise P) {x : ℂ}
    (hP : DifferentiableAt ℝ P x) : fderiv ℝ P x (Complex.I * x) = 0 := by
  have hrotd : HasDerivAt (fun θ : ℝ => rot θ x) (Complex.I * x) 0 := by
    have h1 : HasDerivAt (fun θ : ℝ => (θ : ℂ) * Complex.I) Complex.I 0 := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const Complex.I
    have h2 := (h1.cexp).mul_const x
    simpa [rot] using h2
  have hcomp : HasDerivAt (fun θ : ℝ => P (rot θ x)) (fderiv ℝ P x (Complex.I * x)) 0 := by
    have hP' : HasFDerivAt P (fderiv ℝ P x) (rot 0 x) := by
      simpa [rot] using hP.hasFDerivAt
    exact hP'.comp_hasDerivAt (0 : ℝ) hrotd
  have hconst : (fun θ : ℝ => P (rot θ x)) = fun _ => P x := by
    funext θ
    exact hrad θ x
  rw [hconst] at hcomp
  exact hcomp.unique (hasDerivAt_const 0 (P x))

/-- The coupling term `𝒦w = -(K_BS * w)·∇Φ` of a complexified real `w`, when the Biot–Savart
integral converges absolutely at `x`. -/
theorem couplingFn_ofReal (χ : ℝ → ℝ) (wR : ℂ → ℝ) (x : ℂ)
    (hint : Integrable (fun y => biotSavartKernel (x - y) * (wR y : ℂ))) :
    (ringPhiSetting χ).couplingFn (fun y => ((wR y : ℝ) : ℂ)) x =
      -((fderiv ℝ (ringPhi χ) x (velocity wR x) : ℝ) : ℂ) := by
  have hpt : ∀ y, ((fderiv ℝ (ringPhi χ) x (biotSavartKernel (x - y)) : ℝ) : ℂ) *
      ((wR y : ℝ) : ℂ) =
      ((fderiv ℝ (ringPhi χ) x (biotSavartKernel (x - y) * (wR y : ℂ)) : ℝ) : ℂ) := by
    intro y
    have : biotSavartKernel (x - y) * (wR y : ℂ) = wR y • biotSavartKernel (x - y) := by
      rw [Complex.real_smul, mul_comm]
    rw [this, map_smul, smul_eq_mul]
    push_cast
    ring
  have hL : ∫ y, fderiv ℝ (ringPhi χ) x (biotSavartKernel (x - y) * (wR y : ℂ)) =
      fderiv ℝ (ringPhi χ) x (∫ y, biotSavartKernel (x - y) * (wR y : ℂ)) :=
    (fderiv ℝ (ringPhi χ) x).integral_comp_comm hint
  simp only [SectorSetting.couplingFn, ringPhiSetting_om]
  rw [neg_inj]
  simp_rw [hpt]
  rw [integral_complex_ofReal, hL]
  rfl

/-- `partialD (1,0) f x = Df(x)1`. -/
theorem partialD_one_zero (f : ℂ → ℂ) (x : ℂ) : Sob.partialD (1, 0) f x = fderiv ℝ f x 1 := by
  simp [Sob.partialD, Sob.iterDirDeriv, Sob.pdList, Sob.dirDeriv]

/-- `partialD (0,1) f x = Df(x)i`. -/
theorem partialD_zero_one (f : ℂ → ℂ) (x : ℂ) :
    Sob.partialD (0, 1) f x = fderiv ℝ f x Complex.I := by
  simp [Sob.partialD, Sob.iterDirDeriv, Sob.pdList, Sob.dirDeriv]

/-- **The right side of `eq:ring` at a point, classically** (`05_single_ring.tex:211-215`). For
a real `w_R` and a point `x` at which the weak first derivatives of `W = (w_R : ℂ)` and of `Φ`
are the classical ones and the Biot–Savart integral of `w_R` converges absolutely,
`L(G)W + B(W,W) - h·∇W - h·∇Φ = -(Ω ∂_θ w_R + (K_BS*w_R)·∇Φ + (K_BS*w_R)·∇w_R + h·∇w_R + h·∇Φ)`. -/
theorem ringRHS_eq_classical (χ : ℝ → ℝ) (G : ℝ) (hv : ℂ → ℂ) (wR : ℂ → ℝ) (x : ℂ)
    (hint : Integrable (fun y => biotSavartKernel (x - y) * (wR y : ℂ)))
    (h1 : Sob.weakPartial (1, 0) (fun y => ((wR y : ℝ) : ℂ)) x =
      ((fderiv ℝ wR x 1 : ℝ) : ℂ))
    (h2 : Sob.weakPartial (0, 1) (fun y => ((wR y : ℝ) : ℂ)) x =
      ((fderiv ℝ wR x Complex.I : ℝ) : ℂ))
    (h3 : Sob.weakPartial (1, 0) (PhiC χ) x = ((fderiv ℝ (ringPhi χ) x 1 : ℝ) : ℂ))
    (h4 : Sob.weakPartial (0, 1) (PhiC χ) x =
      ((fderiv ℝ (ringPhi χ) x Complex.I : ℝ) : ℂ)) :
    ringRHS χ G hv (fun y => ((wR y : ℝ) : ℂ)) x =
      -((Lin.Omega χ G ‖x‖ * fderiv ℝ wR x (Complex.I * x) +
          fderiv ℝ (ringPhi χ) x (velocity wR x) + fderiv ℝ wR x (velocity wR x) +
          fderiv ℝ wR x (hv x) + fderiv ℝ (ringPhi χ) x (hv x) : ℝ) : ℂ) := by
  have hvRe : BS.velocityRe (fun y => ((wR y : ℝ) : ℂ)) = velocity wR := by
    funext z
    simp [BS.velocityRe]
  have hvIm : BS.velocityIm (fun y => ((wR y : ℝ) : ℂ)) = fun _ => 0 := by
    funext z
    simp [BS.velocityIm, velocity]
  have hcoup := couplingFn_ofReal χ wR x hint
  simp only [ringRHS, Lin.Lfn, SectorSetting.linFn, SectorSetting.transportPartFn, Bfn, bsGrad,
    hGrad, Sob.dotGrad, Ang.thetaDeriv, hvRe, hvIm, h1, h2, h3, h4, hcoup]
  rw [re_mul_sub_im_mul, re_mul_add_im_mul, re_mul_add_im_mul, re_mul_add_im_mul,
    re_mul_add_im_mul, map_zero]
  have hO : (ringPhiSetting χ).Omega G ‖x‖ = Lin.Omega χ G ‖x‖ := rfl
  rw [hO]
  push_cast
  ring

end NonUniqueEuler.OneRing.RedEqH
