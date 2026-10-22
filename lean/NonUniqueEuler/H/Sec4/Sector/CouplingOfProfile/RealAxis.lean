import NonUniqueEuler.H.Sec4.Sector.CouplingOfProfile.Basic
import NonUniqueEuler.I.Infra.Polar.Fubini
import NonUniqueEuler.I.Infra.Polar.RadialDeriv
import NonUniqueEuler.I.Infra.Multipole.CircleKernel

/-!
# Helper for `couplingFn_ofProfile`: the coupling term at a point `r > 0` of the real axis

Helper file of `P/Sec4/Sector/CouplingOfProfile.lean` (fully proved). Manuscript
`04_ring.tex:257-263`, computed directly in polar coordinates.

* `fderiv_om_ofReal`: `Dω̄(r)v = ω̄'(r) Re v` for `r > 0` (`ω̄ = ω̄(|x|)`,
  `Polar.hasFDerivAt_comp_norm`).
* `bsKernel_sub_re`: `Re K_BS(r - y) = Im y/(2π|r - y|²)`.
* `couplingFn_ofReal`: if `(|K_BS| ⋆ |W|)(r) < ∞` then `(𝒦W)(r) = k_ℓ(r)(𝒢_ℓ g)(r)`, by polar
  coordinates (`Polar.integral_eq_integral_Ioi_intervalIntegral`) and the circle integral
  `Multipole.intervalIntegral_sin_div_norm_sub_circleMap_sq_mul_exp`.
-/

noncomputable section

open MeasureTheory Set Real Filter
open scoped ENNReal

namespace NonUniqueEuler.CouplingOfProfileH

open Ang SectorSetting

theorem om_eq_omR_norm {S : SectorSetting} (hS : S.Valid) (x : ℂ) : S.om x = S.omR ‖x‖ := by
  conv_lhs => rw [← rot_arg_norm x]
  exact hS.radial _ _

/-- `Dω̄(r)v = ω̄'(r) Re v` at a point `r > 0` of the real axis. -/
theorem fderiv_om_ofReal {S : SectorSetting} (hS : S.Valid) {r : ℝ} (hr : 0 < r) (v : ℂ) :
    fderiv ℝ S.om (r : ℂ) v = S.dom r * v.re := by
  have hdiff : Differentiable ℝ S.om := hS.contDiff.differentiable (by simp)
  have hd : HasDerivAt S.omR (S.dom r) r := by
    have : DifferentiableAt ℝ S.omR r :=
      (hdiff (r : ℂ)).comp r Complex.ofRealCLM.differentiableAt
    exact this.hasDerivAt
  have hnorm : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_of_nonneg hr.le]
  have hz : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have h1 := Polar.hasFDerivAt_comp_norm hz (f₀ := S.omR) (by rw [hnorm]; exact hd)
  have e : (fun x : ℂ => S.omR ‖x‖) = S.om := funext fun x => (om_eq_omR_norm hS x).symm
  rw [e] at h1
  rw [h1.fderiv, hnorm, smul_apply, innerSL_apply_apply, Complex.inner,
    smul_eq_mul]
  simp only [Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  field_simp

/-- `Re K_BS(r - y) = Im y/(2π|r - y|²)`. -/
theorem bsKernel_sub_re (r : ℝ) (y : ℂ) :
    (biotSavartKernel ((r : ℂ) - y)).re = y.im / (2 * π * ‖(r : ℂ) - y‖ ^ 2) := by
  rw [biotSavartKernel, Complex.div_ofReal_re, Complex.I_mul_re]
  simp

theorem circleMap_zero_im (ρ θ : ℝ) : (circleMap 0 ρ θ).im = ρ * Real.sin θ := by
  simp [circleMap, Complex.mul_im, Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_re]

/-- The integrand of `(𝒦W)(r)` on the circle of radius `ρ > 0`. -/
theorem integrand_circleMap {S : SectorSetting} (hS : S.Valid) {r : ℝ} (hr : 0 < r) (ℓ : ℤ)
    (g : ℝ → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (θ : ℝ) :
    ((fderiv ℝ S.om (r : ℂ) (biotSavartKernel ((r : ℂ) - circleMap 0 ρ θ)) : ℝ) : ℂ) *
        ofProfile ℓ g (circleMap 0 ρ θ) =
      ((S.dom r / (2 * π) : ℝ) : ℂ) * g ρ *
        (((ρ * Real.sin θ / ‖(r : ℂ) - circleMap 0 ρ θ‖ ^ 2 : ℝ) : ℂ) *
          Complex.exp ((ℓ : ℂ) * θ * Complex.I)) := by
  rw [fderiv_om_ofReal hS hr, bsKernel_sub_re, circleMap_zero_im, ofProfile,
    norm_circleMap_zero, abs_of_pos hρ, angPhase_circleMap ℓ hρ]
  have e : S.dom r * (ρ * Real.sin θ / (2 * π * ‖(r : ℂ) - circleMap 0 ρ θ‖ ^ 2)) =
      S.dom r / (2 * π) * (ρ * Real.sin θ / ‖(r : ℂ) - circleMap 0 ρ θ‖ ^ 2) := by
    ring
  rw [e]
  push_cast
  ring

/-- The circle integral of the integrand, for `ρ > 0`, `ρ ≠ r`. -/
theorem circle_integral_eq {S : SectorSetting} (hS : S.Valid) {r : ℝ} (hr : 0 < r) (ℓ : ℤ)
    (g : ℝ → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (hrρ : r ≠ ρ) :
    ρ • ∫ θ in (0 : ℝ)..2 * π,
        ((fderiv ℝ S.om (r : ℂ) (biotSavartKernel ((r : ℂ) - circleMap 0 ρ θ)) : ℝ) : ℂ) *
          ofProfile ℓ g (circleMap 0 ρ θ) =
      (((S.dom r / (2 * π) : ℝ) : ℂ) * (Complex.I * π * (Int.sign ℓ : ℂ)) * (r : ℂ)⁻¹) *
        ((((min r ρ / max r ρ) ^ ℓ.natAbs : ℝ) : ℂ) * g ρ * (ρ : ℂ)) := by
  simp_rw [integrand_circleMap hS hr ℓ g hρ]
  rw [intervalIntegral.integral_const_mul,
    Multipole.intervalIntegral_sin_div_norm_sub_circleMap_sq_mul_exp hr hρ hrρ ℓ,
    Complex.real_smul]
  push_cast
  ring

/-- `(𝒦W)(r) = k_ℓ(r)(𝒢_ℓ g)(r)` at a radius `r > 0` where `(|K_BS| ⋆ |W|)(r) < ∞`. -/
theorem couplingFn_ofReal {S : SectorSetting} (hS : S.Valid) {g : ℝ → ℂ}
    (hg : S.IsProfileL2 g) (ℓ : ℤ) {r : ℝ} (hr : 0 < r)
    (hfin : Conv.convAbs biotSavartKernel (ofProfile ℓ g) (r : ℂ) < ∞) :
    S.couplingFn (ofProfile ℓ g) (r : ℂ) = S.KsecFn ℓ g r := by
  have hW := memLp_ofProfile hg ℓ
  set f : ℂ → ℂ := fun y =>
    ((fderiv ℝ S.om (r : ℂ) (biotSavartKernel ((r : ℂ) - y)) : ℝ) : ℂ) * ofProfile ℓ g y
    with hf
  have hfm : AEStronglyMeasurable f volume := by
    have h1 : Measurable fun y : ℂ =>
        ((fderiv ℝ S.om (r : ℂ) (biotSavartKernel ((r : ℂ) - y)) : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp ((fderiv ℝ S.om (r : ℂ)).continuous.measurable.comp
        (measurable_bsKernel.comp (measurable_const.sub measurable_id)))
    exact h1.aestronglyMeasurable.mul hW.aestronglyMeasurable
  have hint : Integrable f volume := by
    refine ⟨hfm, ?_⟩
    have hle : ∫⁻ y, ‖f y‖ₑ ≤ ‖fderiv ℝ S.om (r : ℂ)‖ₑ *
        Conv.convAbs biotSavartKernel (ofProfile ℓ g) (r : ℂ) := by
      simp only [Conv.convAbs]
      rw [← lintegral_const_mul' _ _ enorm_ne_top]
      refine lintegral_mono fun y => ?_
      simp only [hf]
      rw [enorm_mul, ← mul_assoc]
      gcongr
      rw [← ofReal_norm, Complex.norm_real, ofReal_norm]
      exact (fderiv ℝ S.om (r : ℂ)).le_opENorm _
    exact hle.trans_lt (ENNReal.mul_lt_top enorm_lt_top hfin)
  have hpolar := Polar.integral_eq_integral_Ioi_intervalIntegral hint
  set C : ℂ := ((S.dom r / (2 * π) : ℝ) : ℂ) * (Complex.I * π * (Int.sign ℓ : ℂ)) * (r : ℂ)⁻¹
    with hC
  have hae : ∀ᵐ ρ ∂(volume.restrict (Ioi (0 : ℝ))),
      ρ • ∫ θ in (0 : ℝ)..2 * π, f (circleMap 0 ρ θ) =
        C * ((((min r ρ / max r ρ) ^ ℓ.natAbs : ℝ) : ℂ) * g ρ * (ρ : ℂ)) := by
    have hne : ∀ᵐ ρ ∂(volume.restrict (Ioi (0 : ℝ))), ρ ≠ r := by
      refine ae_restrict_of_ae ?_
      rw [ae_iff]
      simp
    filter_upwards [hne, ae_restrict_mem measurableSet_Ioi] with ρ hρr hρ
    exact circle_integral_eq hS hr ℓ g hρ (Ne.symm hρr)
  have hJ : ∫ y, f y = C * ∫ ρ in Ioi (0 : ℝ),
      (((min r ρ / max r ρ) ^ ℓ.natAbs : ℝ) : ℂ) * g ρ * (ρ : ℂ) := by
    rw [hpolar, integral_congr_ae hae, integral_const_mul]
  have hcoef : -C = S.kcoef ℓ r * -((((2 * |(ℓ : ℝ)|)⁻¹ : ℝ)) : ℂ) := by
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
    by_cases hℓ : ℓ = 0
    · subst hℓ
      simp [hC]
    · have hsa : ((Int.sign ℓ : ℝ)) * |(ℓ : ℝ)| = (ℓ : ℝ) := by
        have := congrArg (fun z : ℤ => (z : ℝ)) (Int.sign_mul_abs ℓ)
        push_cast at this
        exact this
      have habs : |(ℓ : ℝ)| ≠ 0 := by
        rw [abs_ne_zero]
        exact_mod_cast hℓ
      have hℓC : (ℓ : ℂ) = ((Int.sign ℓ : ℝ) : ℂ) * ((|(ℓ : ℝ)| : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, hsa]
        push_cast
        rfl
      have habsC : ((|(ℓ : ℝ)| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast habs
      rw [hC, kcoef, hℓC]
      push_cast
      field_simp
  simp only [couplingFn]
  rw [show (fun y => ((fderiv ℝ S.om (r : ℂ) (biotSavartKernel ((r : ℂ) - y)) : ℝ) : ℂ) *
      ofProfile ℓ g y) = f from rfl, hJ, KsecFn, green, neg_mul_eq_neg_mul, hcoef]
  ring

end NonUniqueEuler.CouplingOfProfileH
