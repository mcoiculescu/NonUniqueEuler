import NonUniqueEuler.H.Infra.AngularFourier.Derivatives.ProfileDeriv.Smooth
import NonUniqueEuler.I.Infra.Polar.Fubini

/-!
# Helpers for `P/Infra/AngularFourier/Derivatives/ProfileDeriv`: testing against `W ℓ ζ`

For `ζ` a test function on `(0, ∞)` and `F` with `F · W ℓ ζ` integrable,
`∫_ℂ F(x) e^{-iℓθ} ζ(|x|)/|x| dx = 2π ∫_ℝ F_ℓ(r) ζ(r) dr` (`integral_mul_W`), by Fubini in
polar coordinates (`Polar.integral_eq_integral_Ioi_intervalIntegral`) and
`W ℓ ζ (r e^{iθ}) = e^{-iℓθ} ζ(r)/r` (`W_circleMap`).
-/

noncomputable section

open MeasureTheory Set Real Filter Topology
open scoped ENNReal ContDiff

namespace NonUniqueEuler.Ang.ProfileDerivAux

theorem integral_mul_W {F : ℂ → ℂ} {ζ : ℝ → ℂ} (hζ : Sob.IsTestFn (Ioi 0) ζ) (ℓ : ℤ)
    (hint : Integrable (fun x => F x * W ℓ ζ x)) :
    ∫ x, F x * W ℓ ζ x = (2 * π : ℂ) * ∫ r, Polar.angularSector F ℓ r * ζ r := by
  rw [Polar.integral_eq_integral_Ioi_intervalIntegral hint]
  have hpt : ∀ r ∈ Ioi (0 : ℝ),
      r • (∫ θ in (0 : ℝ)..2 * π, F (circleMap 0 r θ) * W ℓ ζ (circleMap 0 r θ)) =
        (2 * π : ℂ) * (Polar.angularSector F ℓ r * ζ r) := by
    intro r hr
    have hr0 : (0 : ℝ) < r := hr
    simp_rw [W_circleMap ℓ ζ hr0]
    have e : (fun θ : ℝ => F (circleMap 0 r θ) *
        (Complex.exp (-((ℓ : ℂ) * θ * Complex.I)) * (ζ r / (r : ℂ)))) =
        fun θ : ℝ => (F ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
          Complex.exp (-((ℓ : ℂ) * θ * Complex.I))) * (ζ r / (r : ℂ)) := by
      funext θ
      rw [circleMap_zero]
      ring
    rw [e, intervalIntegral.integral_mul_const, Polar.angularSector, Complex.real_smul]
    generalize (∫ θ in (0 : ℝ)..2 * π, F ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
      Complex.exp (-((ℓ : ℂ) * θ * Complex.I))) = A
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
    have hπ : (2 * π : ℂ) ≠ 0 := by
      have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      exact mul_ne_zero two_ne_zero this
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  congr 1
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro r hr
  rw [eq_zero_of_nonpos hζ (not_lt.1 hr), mul_zero]

end NonUniqueEuler.Ang.ProfileDerivAux
