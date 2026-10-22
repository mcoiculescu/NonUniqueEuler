import NonUniqueEuler.Defs.Infra.Multipole
import NonUniqueEuler.Defs.Infra.AngularFourier
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Helper for `lem:sector`(1): rotation reduction for the logarithmic potential of a sector function

Helper file of `P/Sec4/Sector.lean` (fully proved). For `W = g(|y|)e^{iℓθ}`, the rotation by
`arg x` gives `Δ⁻¹W(x) = e^{iℓ arg x} · Δ⁻¹W(|x|)` for `x ≠ 0` (`logPotential_ofProfile_rot`),
so it suffices to know `Δ⁻¹W` on the positive real axis (`I/Sec4/Sector/LogPotReal.lean`).
-/

noncomputable section

open MeasureTheory Set Real

namespace NonUniqueEuler.SectorH

open Ang

theorem measurableEmbedding_rot (θ : ℝ) : MeasurableEmbedding (rot θ) := by
  rw [Polar.rot_eq_rotation]
  exact (rotation (Circle.exp θ)).toHomeomorph.measurableEmbedding

theorem rot_arg_norm (x : ℂ) : rot (Complex.arg x) (‖x‖ : ℂ) = x := by
  rw [rot, mul_comm]
  exact Complex.norm_mul_exp_arg_mul_I x

theorem angPhase_rot (ℓ : ℤ) (θ : ℝ) (y : ℂ) :
    angPhase ℓ (rot θ y) = Complex.exp ((ℓ : ℂ) * θ * Complex.I) * angPhase ℓ y := by
  rw [angPhase, angPhase, Polar.norm_rot, rot, mul_div_assoc, mul_zpow, mul_assoc,
    Complex.exp_int_mul]

theorem angPhase_ofReal (ℓ : ℤ) {r : ℝ} (hr : 0 < r) : angPhase ℓ (r : ℂ) = 1 := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [angPhase, Complex.norm_real, Real.norm_of_nonneg hr.le, div_self hr', one_zpow]

theorem ofProfile_rot (ℓ : ℤ) (g : ℝ → ℂ) (θ : ℝ) (y : ℂ) :
    ofProfile ℓ g (rot θ y) = Complex.exp ((ℓ : ℂ) * θ * Complex.I) * ofProfile ℓ g y := by
  rw [ofProfile, ofProfile, Polar.norm_rot, angPhase_rot]
  ring

/-- `Δ⁻¹(g e^{iℓθ})(x) = e^{iℓθ_x} Δ⁻¹(g e^{iℓθ})(|x|)` for `x ≠ 0`. -/
theorem logPotential_ofProfile_rot (ℓ : ℤ) (g : ℝ → ℂ) {x : ℂ} (hx : x ≠ 0) :
    Multipole.logPotential (ofProfile ℓ g) x =
      angPhase ℓ x * Multipole.logPotential (ofProfile ℓ g) (‖x‖ : ℂ) := by
  set θ := Complex.arg x
  have hxr : rot θ (‖x‖ : ℂ) = x := rot_arg_norm x
  have hphase : angPhase ℓ x = Complex.exp ((ℓ : ℂ) * θ * Complex.I) := by
    conv_lhs => rw [← hxr]
    rw [angPhase_rot, angPhase_ofReal ℓ (norm_pos_iff.2 hx), mul_one]
  simp only [Multipole.logPotential]
  rw [← (Polar.measurePreserving_rot θ).integral_comp (measurableEmbedding_rot θ)]
  have e : ∀ y : ℂ, (Real.log ‖x - rot θ y‖ : ℂ) * ofProfile ℓ g (rot θ y) =
      Complex.exp ((ℓ : ℂ) * θ * Complex.I) *
        ((Real.log ‖(‖x‖ : ℂ) - y‖ : ℂ) * ofProfile ℓ g y) := by
    intro y
    have : x - rot θ y = rot θ ((‖x‖ : ℂ) - y) := by
      conv_lhs => rw [← hxr]
      simp only [rot]
      ring
    rw [this, Polar.norm_rot, ofProfile_rot]
    ring
  simp_rw [e]
  rw [integral_const_mul, hphase]
  ring

end NonUniqueEuler.SectorH
