import NonUniqueEuler.H.Infra.AngularFourier.NormEquiv.ProfileDeriv.ParamInt
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Helpers for `P/Infra/AngularFourier/NormEquiv/ProfileDeriv`: angular coefficients

For a smooth `φ : ℂ → ℂ` and a smooth weight `c : ℝ → ℂ`, the angular coefficient
`angCoef c φ r = ∫₀^{2π} c(θ) φ(r e^{iθ}) dθ` is smooth in `r` (`contDiff_angCoef`), with
derivative `∫₀^{2π} c(θ) Dφ(r e^{iθ})(e^{iθ}) dθ` (`hasDerivAt_angCoef`).

With `cC ℓ θ = e^{iℓθ} cos θ`, `cS ℓ θ = e^{iℓθ} sin θ`, `C = angCoef (cC ℓ) φ`,
`S = angCoef (cS ℓ) φ`, the polar form of `∂₁ = cos θ ∂_r - (sin θ / r) ∂_θ`,
`∂₂ = sin θ ∂_r + (cos θ / r) ∂_θ`, after an integration by parts in `θ`, reads
* `r ∫ e^{iℓθ} ∂₁φ(r e^{iθ}) dθ = C + r C' + iℓ S` (`key_one`),
* `r ∫ e^{iℓθ} ∂₂φ(r e^{iθ}) dθ = S + r S' - iℓ C` (`key_two`),
for every `r ∈ ℝ`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff

namespace NonUniqueEuler.Ang.NEProfileDerivAux

/-- `e^{iℓθ}`. -/
def eA (ℓ : ℤ) (θ : ℝ) : ℂ :=
  Complex.exp ((ℓ : ℂ) * θ * Complex.I)

/-- `e^{iℓθ} cos θ`. -/
def cC (ℓ : ℤ) (θ : ℝ) : ℂ :=
  eA ℓ θ * (Real.cos θ : ℂ)

/-- `e^{iℓθ} sin θ`. -/
def cS (ℓ : ℤ) (θ : ℝ) : ℂ :=
  eA ℓ θ * (Real.sin θ : ℂ)

/-- The polar integrand `c(θ) φ(r e^{iθ})` as a function of `(r, θ)`. -/
def polF (c : ℝ → ℂ) (φ : ℂ → ℂ) (p : ℝ × ℝ) : ℂ :=
  c p.2 * φ (circleMap 0 p.1 p.2)

/-- The angular coefficient `∫₀^{2π} c(θ) φ(r e^{iθ}) dθ`. -/
def angCoef (c : ℝ → ℂ) (φ : ℂ → ℂ) (r : ℝ) : ℂ :=
  ∫ θ in (0 : ℝ)..2 * π, c θ * φ (circleMap 0 r θ)

/-! ### Smoothness of the weights -/

theorem hasDerivAt_eA (ℓ : ℤ) (θ : ℝ) :
    HasDerivAt (eA ℓ) ((ℓ : ℂ) * Complex.I * eA ℓ θ) θ := by
  have h1 : HasDerivAt (fun t : ℝ => (ℓ : ℂ) * (t : ℂ) * Complex.I) ((ℓ : ℂ) * 1 * Complex.I) θ :=
    ((hasDerivAt_id θ).ofReal_comp.const_mul (ℓ : ℂ)).mul_const Complex.I
  have h2 := h1.cexp
  have e : Complex.exp ((ℓ : ℂ) * θ * Complex.I) * ((ℓ : ℂ) * 1 * Complex.I) =
      (ℓ : ℂ) * Complex.I * eA ℓ θ := by
    rw [eA]; ring
  rw [← e]
  exact h2

theorem contDiff_eA (ℓ : ℤ) : ContDiff ℝ ∞ (eA ℓ) := by
  have h : ContDiff ℝ ∞ (fun t : ℝ => (ℓ : ℂ) * (t : ℂ) * Complex.I) :=
    (contDiff_const.mul Complex.ofRealCLM.contDiff).mul contDiff_const
  exact Complex.contDiff_exp.comp h

theorem contDiff_ofReal_cos : ContDiff ℝ ∞ (fun θ : ℝ => (Real.cos θ : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp Real.contDiff_cos

theorem contDiff_ofReal_sin : ContDiff ℝ ∞ (fun θ : ℝ => (Real.sin θ : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp Real.contDiff_sin

theorem contDiff_cC (ℓ : ℤ) : ContDiff ℝ ∞ (cC ℓ) :=
  (contDiff_eA ℓ).mul contDiff_ofReal_cos

theorem contDiff_cS (ℓ : ℤ) : ContDiff ℝ ∞ (cS ℓ) :=
  (contDiff_eA ℓ).mul contDiff_ofReal_sin

theorem hasDerivAt_cC (ℓ : ℤ) (θ : ℝ) :
    HasDerivAt (cC ℓ) ((ℓ : ℂ) * Complex.I * cC ℓ θ - cS ℓ θ) θ := by
  have h := (hasDerivAt_eA ℓ θ).mul (Real.hasDerivAt_cos θ).ofReal_comp
  have e : (ℓ : ℂ) * Complex.I * eA ℓ θ * (Real.cos θ : ℂ) + eA ℓ θ * ((-Real.sin θ : ℝ) : ℂ) =
      (ℓ : ℂ) * Complex.I * cC ℓ θ - cS ℓ θ := by
    rw [cC, cS]; push_cast; ring
  rw [← e]
  exact h

theorem hasDerivAt_cS (ℓ : ℤ) (θ : ℝ) :
    HasDerivAt (cS ℓ) ((ℓ : ℂ) * Complex.I * cS ℓ θ + cC ℓ θ) θ := by
  have h := (hasDerivAt_eA ℓ θ).mul (Real.hasDerivAt_sin θ).ofReal_comp
  have e : (ℓ : ℂ) * Complex.I * eA ℓ θ * (Real.sin θ : ℂ) + eA ℓ θ * ((Real.cos θ : ℝ) : ℂ) =
      (ℓ : ℂ) * Complex.I * cS ℓ θ + cC ℓ θ := by
    rw [cC, cS]; ring
  rw [← e]
  exact h

/-! ### Smoothness of the angular coefficients -/

theorem contDiff_circleMap_prod : ContDiff ℝ ∞ (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by
  have h1 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => ((p.1 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp contDiff_fst
  have h2 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => Complex.exp (((p.2 : ℝ) : ℂ) * Complex.I)) :=
    Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp contDiff_snd).mul contDiff_const)
  have e : (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) =
      fun p : ℝ × ℝ => ((p.1 : ℝ) : ℂ) * Complex.exp (((p.2 : ℝ) : ℂ) * Complex.I) := by
    funext p; rw [circleMap_zero]
  rw [e]
  exact h1.mul h2

theorem contDiff_polF {c : ℝ → ℂ} {φ : ℂ → ℂ} (hc : ContDiff ℝ ∞ c) (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (polF c φ) :=
  (hc.comp contDiff_snd).mul (hφ.comp contDiff_circleMap_prod)

theorem angCoef_eq (c : ℝ → ℂ) (φ : ℂ → ℂ) :
    angCoef c φ = fun r => ∫ θ in (0 : ℝ)..2 * π, polF c φ (r, θ) := rfl

theorem contDiff_angCoef {c : ℝ → ℂ} {φ : ℂ → ℂ} (hc : ContDiff ℝ ∞ c) (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (angCoef c φ) := by
  rw [angCoef_eq]
  exact paramInt_contDiff (contDiff_polF hc hφ) 0 (2 * π)

theorem hasDerivAt_circleMap_radius (r θ : ℝ) :
    HasDerivAt (fun s : ℝ => circleMap 0 s θ) (Complex.exp ((θ : ℂ) * Complex.I)) r := by
  have h := (hasDerivAt_id r).ofReal_comp.mul_const (Complex.exp ((θ : ℂ) * Complex.I))
  simp only [id, Complex.ofReal_one, one_mul] at h
  have e : (fun s : ℝ => circleMap 0 s θ) =
      fun s : ℝ => (s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    funext s; rw [circleMap_zero]
  rw [e]
  exact h

theorem d1_polF {c : ℝ → ℂ} {φ : ℂ → ℂ} (hc : ContDiff ℝ ∞ c) (hφ : ContDiff ℝ ∞ φ)
    (r θ : ℝ) :
    d1 (polF c φ) (r, θ) =
      c θ * fderiv ℝ φ (circleMap 0 r θ) (Complex.exp ((θ : ℂ) * Complex.I)) := by
  have hF := hasDerivAt_d1 ((contDiff_polF hc hφ).differentiable (by simp)) r θ
  have hφd : DifferentiableAt ℝ φ (circleMap 0 r θ) :=
    (hφ.differentiable (by simp)) _
  have h2 : HasDerivAt (fun s : ℝ => c θ * φ (circleMap 0 s θ))
      (c θ * fderiv ℝ φ (circleMap 0 r θ) (Complex.exp ((θ : ℂ) * Complex.I))) r :=
    (hφd.hasFDerivAt.comp_hasDerivAt r (hasDerivAt_circleMap_radius r θ)).const_mul (c θ)
  exact hF.unique h2

/-- The radial derivative of the angular coefficient. -/
theorem hasDerivAt_angCoef {c : ℝ → ℂ} {φ : ℂ → ℂ} (hc : ContDiff ℝ ∞ c) (hφ : ContDiff ℝ ∞ φ)
    (r : ℝ) :
    HasDerivAt (angCoef c φ)
      (∫ θ in (0 : ℝ)..2 * π,
        c θ * fderiv ℝ φ (circleMap 0 r θ) (Complex.exp ((θ : ℂ) * Complex.I))) r := by
  have h := paramInt_hasDerivAt ((contDiff_polF hc hφ).of_le (by simp)) 0 (2 * π) r
  simp only [d1_polF hc hφ] at h
  exact h

/-! ### The polar decomposition of `∂₁`, `∂₂` -/

theorem ofReal_eq_cos_smul (r θ : ℝ) :
    (r : ℂ) = Real.cos θ • circleMap 0 r θ - Real.sin θ • (circleMap 0 r θ * Complex.I) := by
  rw [circleMap_zero, Complex.exp_mul_I, Complex.real_smul, Complex.real_smul,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have e1 : ((Real.cos θ : ℝ) : ℂ) ^ 2 + ((Real.sin θ : ℝ) : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq θ
  linear_combination (-(r : ℂ)) * e1 + ((r : ℂ) * ((Real.sin θ : ℝ) : ℂ) ^ 2) * Complex.I_sq

theorem ofReal_mul_I_eq (r θ : ℝ) :
    (r : ℂ) * Complex.I =
      Real.sin θ • circleMap 0 r θ + Real.cos θ • (circleMap 0 r θ * Complex.I) := by
  rw [circleMap_zero, Complex.exp_mul_I, Complex.real_smul, Complex.real_smul,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have e1 : ((Real.cos θ : ℝ) : ℂ) ^ 2 + ((Real.sin θ : ℝ) : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq θ
  linear_combination (-(r : ℂ) * Complex.I) * e1 +
    (-(r : ℂ) * ((Real.sin θ : ℝ) : ℂ) * ((Real.cos θ : ℝ) : ℂ)) * Complex.I_sq

theorem clm_one_decomp (L : ℂ →L[ℝ] ℂ) (r θ : ℝ) :
    (r : ℂ) * L 1 = (Real.cos θ : ℂ) * L (circleMap 0 r θ) -
      (Real.sin θ : ℂ) * L (circleMap 0 r θ * Complex.I) := by
  have h1 : (r : ℂ) * L 1 = L (r : ℂ) := by
    rw [← Complex.real_smul, ← map_smul, Complex.real_smul, mul_one]
  rw [h1, ofReal_eq_cos_smul r θ, map_sub, map_smul, map_smul, Complex.real_smul,
    Complex.real_smul]

theorem clm_I_decomp (L : ℂ →L[ℝ] ℂ) (r θ : ℝ) :
    (r : ℂ) * L Complex.I = (Real.sin θ : ℂ) * L (circleMap 0 r θ) +
      (Real.cos θ : ℂ) * L (circleMap 0 r θ * Complex.I) := by
  have h1 : (r : ℂ) * L Complex.I = L ((r : ℂ) * Complex.I) := by
    rw [← Complex.real_smul, ← map_smul, Complex.real_smul]
  rw [h1, ofReal_mul_I_eq r θ, map_add, map_smul, map_smul, Complex.real_smul,
    Complex.real_smul]

theorem clm_circleMap (L : ℂ →L[ℝ] ℂ) (r θ : ℝ) :
    L (circleMap 0 r θ) = (r : ℂ) * L (Complex.exp ((θ : ℂ) * Complex.I)) := by
  rw [circleMap_zero, ← Complex.real_smul, map_smul, Complex.real_smul]

end NonUniqueEuler.Ang.NEProfileDerivAux
