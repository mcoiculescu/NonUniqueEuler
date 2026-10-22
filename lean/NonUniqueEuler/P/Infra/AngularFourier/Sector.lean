import NonUniqueEuler.Defs.Infra.AngularFourier
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Proof: the sector projections `P_ℓ`, pointwise identities (library I-ANG)

Proof of `NonUniqueEuler/I/Infra/AngularFourier/Sector.lean` (same declarations, statements
copied verbatim).

Method (as in the interface docstring). All identities are pointwise and need no integrability:
* a `2π`-periodic integrand can be shifted, `∫₀^{2π} G(φ + θ) dφ = ∫₀^{2π} G`
  (`intervalIntegral.integral_comp_add_right`, `Function.Periodic.intervalIntegral_add_eq`,
  both valid without integrability hypotheses);
* polar form: `rot φ x = |x| e^{i(φ + arg x)}` (`Complex.norm_mul_exp_arg_mul_I`);
* if `f ∘ O_φ = e^{iℓφ} f` pointwise, then `P_m f = δ_{mℓ} f`, from
  `(2π)⁻¹ ∫₀^{2π} e^{i(ℓ-m)φ} dφ = δ_{mℓ}` (`integral_exp_mul_complex`,
  `Complex.exp_int_mul_two_pi_mul_I`).
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace NonUniqueEuler.Ang

/-! ### Helper lemmas -/

/-- Shifting the variable of a `2π`-periodic integrand over a full period. -/
private theorem integral_shift_periodic {G : ℝ → ℂ} (hG : Function.Periodic G (2 * π))
    (θ : ℝ) : ∫ φ in (0 : ℝ)..2 * π, G (φ + θ) = ∫ φ in (0 : ℝ)..2 * π, G φ := by
  rw [intervalIntegral.integral_comp_add_right, zero_add, add_comm (2 * π) θ,
    hG.intervalIntegral_add_eq θ 0, zero_add]

/-- `θ ↦ e^{iθ}` is `2π`-periodic. -/
private theorem exp_mul_I_periodic (θ : ℝ) :
    Complex.exp (((θ + 2 * π : ℝ) : ℂ) * Complex.I) = Complex.exp ((θ : ℂ) * Complex.I) := by
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- `θ ↦ e^{-iℓθ}` is `2π`-periodic. -/
private theorem exp_neg_int_mul_periodic (ℓ : ℤ) (θ : ℝ) :
    Complex.exp (-((ℓ : ℂ) * ((θ + 2 * π : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (-((ℓ : ℂ) * θ * Complex.I)) := by
  have h : -((ℓ : ℂ) * ((θ + 2 * π : ℝ) : ℂ) * Complex.I) =
      -((ℓ : ℂ) * θ * Complex.I) + ((-ℓ : ℤ) : ℂ) * (2 * π * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- `rot` is `2π`-periodic in the angle. -/
private theorem rot_add_two_pi (θ : ℝ) (x : ℂ) : rot (θ + 2 * π) x = rot θ x := by
  simp only [rot]
  rw [exp_mul_I_periodic θ]

/-- The phase is equivariant: `angPhase ℓ (O_φ x) = e^{iℓφ} angPhase ℓ x`. -/
private theorem angPhase_rot (ℓ : ℤ) (φ : ℝ) (x : ℂ) :
    angPhase ℓ (rot φ x) = Complex.exp ((ℓ : ℂ) * φ * Complex.I) * angPhase ℓ x := by
  unfold angPhase
  rw [Polar.norm_rot, rot, mul_div_assoc, mul_zpow, ← Complex.exp_int_mul, mul_assoc]

/-- If `f ∘ O_φ = e^{iℓφ} f` pointwise, then `P_m f = δ_{mℓ} f`. -/
private theorem sectorProj_of_rot_eq (m ℓ : ℤ) {f : ℂ → ℂ}
    (hf : ∀ (φ : ℝ) (x : ℂ), f (rot φ x) = Complex.exp ((ℓ : ℂ) * φ * Complex.I) * f x) :
    sectorProj m f = if m = ℓ then f else 0 := by
  funext x
  unfold sectorProj
  have hpt : ∀ φ : ℝ, Complex.exp (-((m : ℂ) * φ * Complex.I)) * f (rot φ x) =
      Complex.exp ((((ℓ - m : ℤ) : ℂ) * Complex.I) * φ) * f x := by
    intro φ
    rw [hf, ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast; ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_mul_const]
  have hpi : (2 * π : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  split_ifs with h
  · subst h
    simp only [sub_self, Int.cast_zero, zero_mul, Complex.exp_zero, intervalIntegral.integral_const,
      sub_zero, Complex.real_smul, mul_one]
    push_cast
    rw [← mul_assoc, inv_mul_cancel₀ hpi, one_mul]
  · have hc : (((ℓ - m : ℤ) : ℂ) * Complex.I) ≠ 0 := by
      refine mul_ne_zero ?_ Complex.I_ne_zero
      exact_mod_cast sub_ne_zero.2 (Ne.symm h)
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp (((ℓ - m : ℤ) : ℂ) * Complex.I * ((2 * π : ℝ) : ℂ)) = 1 := by
      have : ((ℓ - m : ℤ) : ℂ) * Complex.I * ((2 * π : ℝ) : ℂ) =
          ((ℓ - m : ℤ) : ℂ) * (2 * π * Complex.I) := by push_cast; ring
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    rw [h1]
    simp

/-! ### The interface statements -/

/-- `P_ℓ g(x) = g_ℓ(|x|) e^{iℓθ}` for `x ≠ 0`. -/
theorem sectorProj_eq_angularSector (ℓ : ℤ) (g : ℂ → ℂ) {x : ℂ} (hx : x ≠ 0) :
    sectorProj ℓ g x = Polar.angularSector g ℓ ‖x‖ * angPhase ℓ x := by
  have hr : ((‖x‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hx)
  set a := Complex.arg x with ha
  let F : ℝ → ℂ := fun θ => g ((‖x‖ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
      Complex.exp (-((ℓ : ℂ) * θ * Complex.I))
  have hFper : Function.Periodic F (2 * π) := by
    intro θ
    simp only [F]
    rw [exp_mul_I_periodic θ, exp_neg_int_mul_periodic ℓ θ]
  have hpolar : ∀ φ : ℝ, rot φ x = (‖x‖ : ℂ) * Complex.exp (((φ + a : ℝ) : ℂ) * Complex.I) := by
    intro φ
    rw [rot]
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I x]
    push_cast
    rw [add_mul, Complex.exp_add]
    ring
  have hpt : ∀ φ : ℝ, Complex.exp (-((ℓ : ℂ) * φ * Complex.I)) * g (rot φ x) =
      Complex.exp ((ℓ : ℂ) * a * Complex.I) * F (φ + a) := by
    intro φ
    simp only [F]
    rw [hpolar φ, mul_comm (g _), ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast; ring
  have hphase : angPhase ℓ x = Complex.exp ((ℓ : ℂ) * a * Complex.I) := by
    have hxa : x / (‖x‖ : ℂ) = Complex.exp ((a : ℂ) * Complex.I) := by
      rw [div_eq_iff hr, mul_comm]
      exact (Complex.norm_mul_exp_arg_mul_I x).symm
    rw [angPhase, hxa, ← Complex.exp_int_mul, mul_assoc]
  unfold sectorProj
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, integral_shift_periodic hFper, hphase]
  unfold Polar.angularSector
  ring

/-- Equivariance: `P_ℓ g ∘ O_θ = e^{iℓθ} P_ℓ g`. -/
theorem sectorProj_rot (ℓ : ℤ) (g : ℂ → ℂ) (θ : ℝ) (x : ℂ) :
    sectorProj ℓ g (rot θ x) = Complex.exp ((ℓ : ℂ) * θ * Complex.I) * sectorProj ℓ g x := by
  let G : ℝ → ℂ := fun ψ => Complex.exp (-((ℓ : ℂ) * ψ * Complex.I)) * g (rot ψ x)
  have hGper : Function.Periodic G (2 * π) := by
    intro ψ
    simp only [G]
    rw [exp_neg_int_mul_periodic ℓ ψ, rot_add_two_pi]
  have hpt : ∀ φ : ℝ, Complex.exp (-((ℓ : ℂ) * φ * Complex.I)) * g (rot φ (rot θ x)) =
      Complex.exp ((ℓ : ℂ) * θ * Complex.I) * G (φ + θ) := by
    intro φ
    simp only [G]
    rw [← Polar.rot_add, ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast; ring
  unfold sectorProj
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, integral_shift_periodic hGper]
  ring

theorem sectorProj_sectorProj (ℓ m : ℤ) (g : ℂ → ℂ) :
    sectorProj ℓ (sectorProj m g) = if ℓ = m then sectorProj m g else 0 :=
  sectorProj_of_rot_eq ℓ m (sectorProj_rot m g)

theorem sectorProj_ofProfile (m ℓ : ℤ) (h : ℝ → ℂ) :
    sectorProj m (ofProfile ℓ h) = if m = ℓ then ofProfile ℓ h else 0 := by
  refine sectorProj_of_rot_eq m ℓ ?_
  intro φ x
  rw [ofProfile, ofProfile, Polar.norm_rot, angPhase_rot]
  ring

/-- `P_ℓ` commutes with multiplication by radial functions. -/
theorem sectorProj_radial_mul (ℓ : ℤ) (a : ℝ → ℂ) (g : ℂ → ℂ) :
    sectorProj ℓ (fun x => a ‖x‖ * g x) = fun x => a ‖x‖ * sectorProj ℓ g x := by
  funext x
  unfold sectorProj
  simp only [Polar.norm_rot]
  simp_rw [mul_left_comm (Complex.exp _) (a ‖x‖)]
  rw [intervalIntegral.integral_const_mul]
  ring

end NonUniqueEuler.Ang
