import NonUniqueEuler.H.Infra.AngularFourier.NormEquiv.ProfileDeriv.Angular

/-!
# Helpers for `P/Infra/AngularFourier/NormEquiv/ProfileDeriv`: the per-radius identities

For `φ` smooth and every `r ∈ ℝ` (`C = angCoef (cC ℓ) φ`, `S = angCoef (cS ℓ) φ`, `'` = `d/dr`):
* `key_one`: `r ∫₀^{2π} e^{iℓθ} ∂₁φ(r e^{iθ}) dθ = C(r) + r C'(r) + iℓ S(r)`;
* `key_two`: `r ∫₀^{2π} e^{iℓθ} ∂₂φ(r e^{iθ}) dθ = S(r) + r S'(r) - iℓ C(r)`.
Proof: `r ∂₁φ = cos θ · r ∂_rφ - sin θ ∂_θφ`, `r ∂₂φ = sin θ · r ∂_rφ + cos θ ∂_θφ` at
`r e^{iθ}` (`clm_one_decomp`, `clm_I_decomp`), then integrate by parts in `θ`
(`intervalIntegral.integral_mul_deriv_eq_deriv_mul`); the boundary terms vanish because
`sin 0 = sin 2π = 0`, resp. by `2π`-periodicity.
-/

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff

namespace NonUniqueEuler.Ang.NEProfileDerivAux

variable {φ : ℂ → ℂ}

theorem continuous_fderiv_circleMap (hφ : ContDiff ℝ ∞ φ) (r : ℝ) {v : ℝ → ℂ}
    (hv : Continuous v) : Continuous (fun θ => fderiv ℝ φ (circleMap 0 r θ) (v θ)) :=
  ((hφ.continuous_fderiv (by simp)).comp (continuous_circleMap 0 r)).clm_apply hv

theorem continuous_comp_circleMap (hφ : ContDiff ℝ ∞ φ) (r : ℝ) :
    Continuous (fun θ => φ (circleMap 0 r θ)) :=
  hφ.continuous.comp (continuous_circleMap 0 r)

theorem hasDerivAt_comp_circleMap (hφ : ContDiff ℝ ∞ φ) (r θ : ℝ) :
    HasDerivAt (fun t => φ (circleMap 0 r t))
      (fderiv ℝ φ (circleMap 0 r θ) (circleMap 0 r θ * Complex.I)) θ :=
  ((hφ.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_circleMap 0 r θ)

theorem continuous_circleMap_mul_I (r : ℝ) :
    Continuous (fun θ => circleMap 0 r θ * Complex.I) :=
  (continuous_circleMap 0 r).mul continuous_const

theorem continuous_exp_mul_I : Continuous (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) :=
  Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)

/-- Integration by parts against `sin`: `∫ cS ∂_θφ = -∫ (iℓ cS + cC) φ`. -/
theorem ibp_cS (hφ : ContDiff ℝ ∞ φ) (ℓ : ℤ) (r : ℝ) :
    ∫ θ in (0 : ℝ)..2 * π, cS ℓ θ * fderiv ℝ φ (circleMap 0 r θ) (circleMap 0 r θ * Complex.I) =
      -((ℓ : ℂ) * Complex.I * angCoef (cS ℓ) φ r + angCoef (cC ℓ) φ r) := by
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := 0) (b := 2 * π) (u := cS ℓ) (v := fun t => φ (circleMap 0 r t))
    (u' := fun θ => (ℓ : ℂ) * Complex.I * cS ℓ θ + cC ℓ θ)
    (v' := fun θ => fderiv ℝ φ (circleMap 0 r θ) (circleMap 0 r θ * Complex.I))
    (fun θ _ => hasDerivAt_cS ℓ θ) (fun θ _ => hasDerivAt_comp_circleMap hφ r θ)
    (((continuous_const.mul (contDiff_cS ℓ).continuous).add
      (contDiff_cC ℓ).continuous).intervalIntegrable 0 (2 * π))
    ((continuous_fderiv_circleMap hφ r (continuous_circleMap_mul_I r)).intervalIntegrable _ _)
  rw [hibp]
  have h0 : cS ℓ (2 * π) = 0 := by simp [cS]
  have h0' : cS ℓ 0 = 0 := by simp [cS]
  rw [h0, h0', zero_mul, zero_mul, sub_zero, zero_sub]
  congr 1
  have hc1 : IntervalIntegrable (fun θ => (ℓ : ℂ) * Complex.I * (cS ℓ θ * φ (circleMap 0 r θ)))
      volume 0 (2 * π) :=
    (continuous_const.mul ((contDiff_cS ℓ).continuous.mul
      (continuous_comp_circleMap hφ r))).intervalIntegrable _ _
  have hc2 : IntervalIntegrable (fun θ => cC ℓ θ * φ (circleMap 0 r θ)) volume 0 (2 * π) :=
    ((contDiff_cC ℓ).continuous.mul (continuous_comp_circleMap hφ r)).intervalIntegrable _ _
  have e : (fun θ => ((ℓ : ℂ) * Complex.I * cS ℓ θ + cC ℓ θ) * φ (circleMap 0 r θ)) =
      fun θ => (ℓ : ℂ) * Complex.I * (cS ℓ θ * φ (circleMap 0 r θ)) +
        cC ℓ θ * φ (circleMap 0 r θ) := by
    funext θ; ring
  rw [e, intervalIntegral.integral_add hc1 hc2, intervalIntegral.integral_const_mul]
  rfl

/-- Integration by parts against `cos`: `∫ cC ∂_θφ = -∫ (iℓ cC - cS) φ` (periodicity). -/
theorem ibp_cC (hφ : ContDiff ℝ ∞ φ) (ℓ : ℤ) (r : ℝ) :
    ∫ θ in (0 : ℝ)..2 * π, cC ℓ θ * fderiv ℝ φ (circleMap 0 r θ) (circleMap 0 r θ * Complex.I) =
      -((ℓ : ℂ) * Complex.I * angCoef (cC ℓ) φ r - angCoef (cS ℓ) φ r) := by
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := 0) (b := 2 * π) (u := cC ℓ) (v := fun t => φ (circleMap 0 r t))
    (u' := fun θ => (ℓ : ℂ) * Complex.I * cC ℓ θ - cS ℓ θ)
    (v' := fun θ => fderiv ℝ φ (circleMap 0 r θ) (circleMap 0 r θ * Complex.I))
    (fun θ _ => hasDerivAt_cC ℓ θ) (fun θ _ => hasDerivAt_comp_circleMap hφ r θ)
    (((continuous_const.mul (contDiff_cC ℓ).continuous).sub
      (contDiff_cS ℓ).continuous).intervalIntegrable 0 (2 * π))
    ((continuous_fderiv_circleMap hφ r (continuous_circleMap_mul_I r)).intervalIntegrable _ _)
  rw [hibp]
  have h2π : cC ℓ (2 * π) = cC ℓ 0 := by
    have e : (ℓ : ℂ) * ((2 * π : ℝ) : ℂ) * Complex.I = (ℓ : ℂ) * (2 * π * Complex.I) := by
      push_cast; ring
    simp only [cC, eA, e, Complex.exp_int_mul_two_pi_mul_I, Real.cos_two_pi]
    simp
  have hper : φ (circleMap 0 r (2 * π)) = φ (circleMap 0 r 0) := by
    rw [← zero_add (2 * π), periodic_circleMap 0 r 0]
  rw [h2π, hper, sub_self, zero_sub]
  congr 1
  have hc1 : IntervalIntegrable (fun θ => (ℓ : ℂ) * Complex.I * (cC ℓ θ * φ (circleMap 0 r θ)))
      volume 0 (2 * π) :=
    (continuous_const.mul ((contDiff_cC ℓ).continuous.mul
      (continuous_comp_circleMap hφ r))).intervalIntegrable _ _
  have hc2 : IntervalIntegrable (fun θ => cS ℓ θ * φ (circleMap 0 r θ)) volume 0 (2 * π) :=
    ((contDiff_cS ℓ).continuous.mul (continuous_comp_circleMap hφ r)).intervalIntegrable _ _
  have e : (fun θ => ((ℓ : ℂ) * Complex.I * cC ℓ θ - cS ℓ θ) * φ (circleMap 0 r θ)) =
      fun θ => (ℓ : ℂ) * Complex.I * (cC ℓ θ * φ (circleMap 0 r θ)) -
        cS ℓ θ * φ (circleMap 0 r θ) := by
    funext θ; ring
  rw [e, intervalIntegral.integral_sub hc1 hc2, intervalIntegral.integral_const_mul]
  rfl

/-- `r ∫ e^{iℓθ} ∂₁φ(r e^{iθ}) dθ = C + r C' + iℓ S`. -/
theorem key_one (hφ : ContDiff ℝ ∞ φ) (ℓ : ℤ) (r : ℝ) :
    (r : ℂ) * ∫ θ in (0 : ℝ)..2 * π, eA ℓ θ * fderiv ℝ φ (circleMap 0 r θ) 1 =
      angCoef (cC ℓ) φ r +
        (r : ℂ) * (∫ θ in (0 : ℝ)..2 * π,
          cC ℓ θ * fderiv ℝ φ (circleMap 0 r θ) (Complex.exp ((θ : ℂ) * Complex.I))) +
        (ℓ : ℂ) * Complex.I * angCoef (cS ℓ) φ r := by
  have hpt : ∀ θ : ℝ, (r : ℂ) * (eA ℓ θ * fderiv ℝ φ (circleMap 0 r θ) 1) =
      (r : ℂ) * (cC ℓ θ * fderiv ℝ φ (circleMap 0 r θ) (Complex.exp ((θ : ℂ) * Complex.I))) -
        cS ℓ θ * fderiv ℝ φ (circleMap 0 r θ) (circleMap 0 r θ * Complex.I) := by
    intro θ
    have h1 := clm_one_decomp (fderiv ℝ φ (circleMap 0 r θ)) r θ
    rw [clm_circleMap] at h1
    rw [cC, cS]
    linear_combination (eA ℓ θ) * h1
  rw [← intervalIntegral.integral_const_mul]
  simp_rw [hpt]
  have hi1 : IntervalIntegrable (fun θ => (r : ℂ) * (cC ℓ θ *
      fderiv ℝ φ (circleMap 0 r θ) (Complex.exp ((θ : ℂ) * Complex.I)))) volume 0 (2 * π) :=
    (continuous_const.mul ((contDiff_cC ℓ).continuous.mul
      (continuous_fderiv_circleMap hφ r continuous_exp_mul_I))).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun θ => cS ℓ θ *
      fderiv ℝ φ (circleMap 0 r θ) (circleMap 0 r θ * Complex.I)) volume 0 (2 * π) :=
    ((contDiff_cS ℓ).continuous.mul
      (continuous_fderiv_circleMap hφ r (continuous_circleMap_mul_I r))).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul, ibp_cS hφ ℓ r]
  ring

/-- `r ∫ e^{iℓθ} ∂₂φ(r e^{iθ}) dθ = S + r S' - iℓ C`. -/
theorem key_two (hφ : ContDiff ℝ ∞ φ) (ℓ : ℤ) (r : ℝ) :
    (r : ℂ) * ∫ θ in (0 : ℝ)..2 * π, eA ℓ θ * fderiv ℝ φ (circleMap 0 r θ) Complex.I =
      angCoef (cS ℓ) φ r +
        (r : ℂ) * (∫ θ in (0 : ℝ)..2 * π,
          cS ℓ θ * fderiv ℝ φ (circleMap 0 r θ) (Complex.exp ((θ : ℂ) * Complex.I))) -
        (ℓ : ℂ) * Complex.I * angCoef (cC ℓ) φ r := by
  have hpt : ∀ θ : ℝ, (r : ℂ) * (eA ℓ θ * fderiv ℝ φ (circleMap 0 r θ) Complex.I) =
      (r : ℂ) * (cS ℓ θ * fderiv ℝ φ (circleMap 0 r θ) (Complex.exp ((θ : ℂ) * Complex.I))) +
        cC ℓ θ * fderiv ℝ φ (circleMap 0 r θ) (circleMap 0 r θ * Complex.I) := by
    intro θ
    have h1 := clm_I_decomp (fderiv ℝ φ (circleMap 0 r θ)) r θ
    rw [clm_circleMap] at h1
    rw [cC, cS]
    linear_combination (eA ℓ θ) * h1
  rw [← intervalIntegral.integral_const_mul]
  simp_rw [hpt]
  have hi1 : IntervalIntegrable (fun θ => (r : ℂ) * (cS ℓ θ *
      fderiv ℝ φ (circleMap 0 r θ) (Complex.exp ((θ : ℂ) * Complex.I)))) volume 0 (2 * π) :=
    (continuous_const.mul ((contDiff_cS ℓ).continuous.mul
      (continuous_fderiv_circleMap hφ r continuous_exp_mul_I))).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun θ => cC ℓ θ *
      fderiv ℝ φ (circleMap 0 r θ) (circleMap 0 r θ * Complex.I)) volume 0 (2 * π) :=
    ((contDiff_cC ℓ).continuous.mul
      (continuous_fderiv_circleMap hφ r (continuous_circleMap_mul_I r))).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul, ibp_cC hφ ℓ r]
  ring

end NonUniqueEuler.Ang.NEProfileDerivAux
