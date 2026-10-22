import NonUniqueEuler.H.Infra.AngularFourier.NormEquiv.ProfileDeriv.Key
import NonUniqueEuler.H.Infra.AngularFourier.NormEquiv.ProfileDeriv.OneD
import NonUniqueEuler.H.Infra.AngularFourier.NormEquiv.ProfileDeriv.PlanePolar

/-!
# Helpers for `P/Infra/AngularFourier/NormEquiv/ProfileDeriv`: both sides in radial form

* `eA_add`, `eA_sub`, `angCoef_add`, `angCoef_sub`: `e^{i(ℓ∓1)θ}` in terms of
  `e^{iℓθ} cos θ`, `e^{iℓθ} sin θ`;
* `good_deriv`, `good_profile`: `h' g` and `h g` are integrable on `(0,∞)` for continuous `g`;
* `lhs_eq`: `∫ h(|x|) e^{iℓθ} ∂_vφ = ∫₀^∞ h(r) · r ∫₀^{2π} e^{iℓθ} ∂_vφ(r e^{iθ}) dθ dr`;
* `rhs_eq`: for a profile `A` with `r A(r) = (r h'(r) + σ h(r))/2` on `(0,∞)`,
  `∫ A(|x|) e^{imθ} φ = (1/2)(∫ h' · r Q + σ ∫ h Q)`, `Q = angCoef (eA m) φ`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff

namespace NonUniqueEuler.Ang.NEProfileDerivAux

variable {ρm ρp : ℝ} {h : ℝ → ℂ} {φ : ℂ → ℂ}

theorem eA_sub_one (ℓ : ℤ) (θ : ℝ) :
    eA (ℓ - 1) θ = eA ℓ θ * ((Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I) := by
  have e : ((ℓ - 1 : ℤ) : ℂ) * (θ : ℂ) * Complex.I =
      (ℓ : ℂ) * θ * Complex.I + ((-θ : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [eA, e, Complex.exp_add, Complex.exp_mul_I ((-θ : ℝ) : ℂ), ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg, eA]
  push_cast
  ring

theorem eA_add_one (ℓ : ℤ) (θ : ℝ) :
    eA (ℓ + 1) θ = eA ℓ θ * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) := by
  have e : ((ℓ + 1 : ℤ) : ℂ) * (θ : ℂ) * Complex.I =
      (ℓ : ℂ) * θ * Complex.I + (θ : ℂ) * Complex.I := by
    push_cast; ring
  rw [eA, e, Complex.exp_add, Complex.exp_mul_I (θ : ℂ), ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, eA]

theorem eA_add (ℓ : ℤ) (θ : ℝ) : eA (ℓ - 1) θ + eA (ℓ + 1) θ = 2 * cC ℓ θ := by
  rw [eA_sub_one, eA_add_one, cC]; ring

theorem eA_sub (ℓ : ℤ) (θ : ℝ) :
    eA (ℓ - 1) θ - eA (ℓ + 1) θ = -2 * Complex.I * cS ℓ θ := by
  rw [eA_sub_one, eA_add_one, cS]; ring

theorem intervalIntegrable_angCoef_integrand {c : ℝ → ℂ} (hc : Continuous c)
    (hφ : ContDiff ℝ ∞ φ) (r : ℝ) :
    IntervalIntegrable (fun θ => c θ * φ (circleMap 0 r θ)) volume 0 (2 * π) :=
  (hc.mul (continuous_comp_circleMap hφ r)).intervalIntegrable _ _

theorem angCoef_add (hφ : ContDiff ℝ ∞ φ) (ℓ : ℤ) (r : ℝ) :
    angCoef (eA (ℓ - 1)) φ r + angCoef (eA (ℓ + 1)) φ r = 2 * angCoef (cC ℓ) φ r := by
  rw [angCoef, angCoef, ← intervalIntegral.integral_add
    (intervalIntegrable_angCoef_integrand (contDiff_eA _).continuous hφ r)
    (intervalIntegrable_angCoef_integrand (contDiff_eA _).continuous hφ r),
    angCoef, ← intervalIntegral.integral_const_mul]
  congr 1
  funext θ
  linear_combination (φ (circleMap 0 r θ)) * eA_add ℓ θ

theorem angCoef_sub (hφ : ContDiff ℝ ∞ φ) (ℓ : ℤ) (r : ℝ) :
    angCoef (eA (ℓ - 1)) φ r - angCoef (eA (ℓ + 1)) φ r =
      -2 * Complex.I * angCoef (cS ℓ) φ r := by
  rw [angCoef, angCoef, ← intervalIntegral.integral_sub
    (intervalIntegrable_angCoef_integrand (contDiff_eA _).continuous hφ r)
    (intervalIntegrable_angCoef_integrand (contDiff_eA _).continuous hφ r),
    angCoef, ← intervalIntegral.integral_const_mul]
  congr 1
  funext θ
  linear_combination (φ (circleMap 0 r θ)) * eA_sub ℓ θ

/-! ### Integrability on `(0, ∞)` -/

theorem good_deriv (hρm : 0 < ρm) (hh : Sob.MemH1On 1 (Ioi 0) h)
    (hhI : ∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc ρm ρp → h r = 0)
    {g : ℝ → ℂ} (hg : Continuous g) :
    IntegrableOn (fun r => Sob.weakDeriv1On (Ioi 0) 1 h r * g r) (Ioi 0) :=
  integrableOn_of_eq hρm hh hhI hg (continuous_const (y := (0 : ℂ))) (fun r _ => by simp)

theorem good_profile (hρm : 0 < ρm) (hh : Sob.MemH1On 1 (Ioi 0) h)
    (hhI : ∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc ρm ρp → h r = 0)
    {g : ℝ → ℂ} (hg : Continuous g) :
    IntegrableOn (fun r => h r * g r) (Ioi 0) :=
  integrableOn_of_eq hρm hh hhI (continuous_const (y := (0 : ℂ))) hg (fun r _ => by simp)

/-! ### The two sides -/

theorem lhs_eq (hρm : 0 < ρm) (hh : Sob.MemH1On 1 (Ioi 0) h)
    (hhI : ∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc ρm ρp → h r = 0) (ℓ : ℤ)
    (hφ : Sob.IsTestFn univ φ) (v : ℂ) :
    ∫ x, ofProfile ℓ h x * fderiv ℝ φ x v =
      ∫ r in Ioi (0 : ℝ), h r * ((r : ℂ) *
        ∫ θ in (0 : ℝ)..2 * π, eA ℓ θ * fderiv ℝ φ (circleMap 0 r θ) v) := by
  have hψ := hφ.dirDeriv v
  have hf : IntegrableOn (fun r : ℝ => (r : ℂ) * h r) (Ioi 0) :=
    integrableOn_of_eq hρm hh hhI (g₁ := fun _ => 0) (g₂ := fun r : ℝ => (r : ℂ))
      continuous_const Complex.continuous_ofReal (fun r _ => by ring)
  have hp := (ofProfile_polar hf ℓ (ψ := Sob.dirDeriv v φ) hψ.continuous hψ.compact).2
  simp only [Sob.dirDeriv] at hp
  rw [hp]
  refine setIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
  simp only [angCoef, Sob.dirDeriv]
  ring

theorem rhs_eq (hρm : 0 < ρm) (hh : Sob.MemH1On 1 (Ioi 0) h)
    (hhI : ∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc ρm ρp → h r = 0)
    (hφ : Sob.IsTestFn univ φ) {A : ℝ → ℂ} (σ : ℂ)
    (hA : ∀ r ∈ Ioi (0 : ℝ),
      (r : ℂ) * A r = (2 : ℂ)⁻¹ * ((r : ℂ) * Sob.weakDeriv1On (Ioi 0) 1 h r + σ * h r))
    (m : ℤ) :
    Integrable (fun x => ofProfile m A x * φ x) ∧
      ∫ x, ofProfile m A x * φ x =
        (2 : ℂ)⁻¹ * ((∫ r in Ioi (0 : ℝ),
          Sob.weakDeriv1On (Ioi 0) 1 h r * ((r : ℂ) * angCoef (eA m) φ r)) +
          σ * ∫ r in Ioi (0 : ℝ), h r * angCoef (eA m) φ r) := by
  have hf : IntegrableOn (fun r : ℝ => (r : ℂ) * A r) (Ioi 0) :=
    integrableOn_of_eq hρm hh hhI (g₁ := fun r : ℝ => (2 : ℂ)⁻¹ * (r : ℂ))
      (g₂ := fun _ => (2 : ℂ)⁻¹ * σ) (continuous_const.mul Complex.continuous_ofReal)
      continuous_const (fun r hr => by rw [hA r hr]; ring)
  have hp := ofProfile_polar hf m hφ.continuous hφ.compact
  refine ⟨hp.1, ?_⟩
  have hQ : Continuous (angCoef (eA m) φ) := (contDiff_angCoef (contDiff_eA m) hφ.smooth).continuous
  have hi1 := good_deriv hρm hh hhI (g := fun r : ℝ => (r : ℂ) * angCoef (eA m) φ r)
    (Complex.continuous_ofReal.mul hQ)
  have hi2 := good_profile hρm hh hhI hQ
  have hsum : (∫ r in Ioi (0 : ℝ),
        Sob.weakDeriv1On (Ioi 0) 1 h r * ((r : ℂ) * angCoef (eA m) φ r)) +
      σ * ∫ r in Ioi (0 : ℝ), h r * angCoef (eA m) φ r =
      ∫ r in Ioi (0 : ℝ), (Sob.weakDeriv1On (Ioi 0) 1 h r * ((r : ℂ) * angCoef (eA m) φ r) +
        σ * (h r * angCoef (eA m) φ r)) := by
    rw [integral_add hi1 (Integrable.const_mul hi2 σ), integral_const_mul]
  rw [hp.2, hsum, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
  have h1 := hA r hr
  show (r : ℂ) * (A r * angCoef (eA m) φ r) = (2 : ℂ)⁻¹ *
    (Sob.weakDeriv1On (Ioi 0) 1 h r * ((r : ℂ) * angCoef (eA m) φ r) +
      σ * (h r * angCoef (eA m) φ r))
  linear_combination (angCoef (eA m) φ r) * h1

end NonUniqueEuler.Ang.NEProfileDerivAux
