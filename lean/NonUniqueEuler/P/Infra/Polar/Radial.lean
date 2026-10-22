import NonUniqueEuler.Defs.Infra.Polar
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Proof: radial integrals on `ℂ` (I-POLAR)

Proof of `NonUniqueEuler/I/Infra/Polar/Radial.lean`: same declarations, same statements.

* `integral_comp_norm`, `integrable_comp_norm_iff`, `integrableOn_ball_comp_norm_iff`: Mathlib's
  `integral_fun_norm_addHaar`, `integrable_fun_norm_addHaar`, `integrableOn_fun_norm_addHaar`
  with `Module.finrank ℝ ℂ = 2` and `volume.real (ball 0 1) = π`.
* `lintegral_comp_norm`: `Complex.lintegral_comp_polarCoord_symm` and Tonelli on
  `Ioi 0 ×ˢ Ioo (-π) π`.
* Disks, annuli, exteriors: the private lemma `setIntegral_preimage_norm` (the radial formula for
  `{x | ‖x‖ ∈ A}`, `A` measurable), then rewriting `Ioi 0 ∩ A`.
-/

noncomputable section

open MeasureTheory Set Metric Real
open scoped ENNReal

namespace NonUniqueEuler.Polar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- `volume.real (ball 0 1) = π` in `ℂ`. -/
private theorem volume_real_ball_one : (volume : Measure ℂ).real (ball (0 : ℂ) 1) = π := by
  simp [Measure.real, Complex.volume_ball]

/-! ### Radial functions -/

/-- `∫_ℂ f(‖x‖) dx = 2π ∫₀^∞ r f(r) dr` (no integrability hypothesis: both sides are `0` when
the integrands are not integrable). -/
theorem integral_comp_norm (f : ℝ → E) :
    ∫ x : ℂ, f ‖x‖ = (2 * π) • ∫ r in Ioi (0 : ℝ), r • f r := by
  have h := integral_fun_norm_addHaar (volume : Measure ℂ) f
  rw [Complex.finrank_real_complex, volume_real_ball_one] at h
  rw [h, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  simp

theorem integrable_comp_norm_iff {f : ℝ → E} :
    Integrable (fun x : ℂ => f ‖x‖) ↔ IntegrableOn (fun r : ℝ => r • f r) (Ioi 0) := by
  have h := integrable_fun_norm_addHaar (volume : Measure ℂ) (f := f)
  rw [Complex.finrank_real_complex] at h
  simpa using h

/-- The lower-integral form of the radial formula. -/
theorem lintegral_comp_norm {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x : ℂ, f ‖x‖ = 2 * ENNReal.ofReal π * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * f r := by
  rw [← Complex.lintegral_comp_polarCoord_symm]
  have htarget : polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-π) π := rfl
  have hmeas : MeasurableSet (polarCoord.target) := by
    rw [htarget]; exact measurableSet_Ioi.prod measurableSet_Ioo
  rw [setLIntegral_congr_fun hmeas (g := fun p : ℝ × ℝ => ENNReal.ofReal p.1 * f p.1)
    (fun p hp => by
      rw [htarget] at hp
      have hp1 : (0 : ℝ) < p.1 := hp.1
      simp only [smul_eq_mul, Complex.norm_polarCoord_symm, abs_of_pos hp1])]
  rw [htarget, Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod (fun z : ℝ × ℝ => ENNReal.ofReal z.1 * f z.1)
      ((ENNReal.measurable_ofReal.comp measurable_fst).mul (hf.comp measurable_fst)).aemeasurable]
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ioo]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  have h2 : ENNReal.ofReal (π - -π) = 2 * ENNReal.ofReal π := by
    rw [sub_neg_eq_add, ← two_mul, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  rw [h2, mul_comm]

/-- The radial formula over `{x | ‖x‖ ∈ A}` for a measurable `A ⊆ ℝ`. -/
private theorem setIntegral_preimage_norm (f : ℝ → E) {A : Set ℝ} (hA : MeasurableSet A) :
    ∫ x in {x : ℂ | ‖x‖ ∈ A}, f ‖x‖ = (2 * π) • ∫ r in Ioi (0 : ℝ) ∩ A, r • f r := by
  have hmeas : MeasurableSet {x : ℂ | ‖x‖ ∈ A} := measurable_norm hA
  rw [← integral_indicator hmeas]
  have h1 : ({x : ℂ | ‖x‖ ∈ A}.indicator fun x => f ‖x‖) = fun x => A.indicator f ‖x‖ := by
    funext x
    by_cases hx : ‖x‖ ∈ A <;> simp [indicator, hx]
  rw [h1, integral_comp_norm, ← setIntegral_indicator hA]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  by_cases hr : r ∈ A <;> simp [indicator, hr]

/-- Radial integrals over a disk: `∫_{B_ρ} f(‖x‖) dx = 2π ∫₀^ρ r f(r) dr`. -/
theorem setIntegral_ball_comp_norm (f : ℝ → E) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∫ x in ball (0 : ℂ) ρ, f ‖x‖ = (2 * π) • ∫ r in (0 : ℝ)..ρ, r • f r := by
  have hset : ball (0 : ℂ) ρ = {x : ℂ | ‖x‖ ∈ Iio ρ} := by
    ext x; simp
  rw [hset, setIntegral_preimage_norm f measurableSet_Iio, Ioi_inter_Iio,
    intervalIntegral.integral_of_le hρ, integral_Ioc_eq_integral_Ioo]

/-- Radial integrals over an annulus: `∫_{a<‖x‖<b} f(‖x‖) dx = 2π ∫ₐᵇ r f(r) dr`. -/
theorem setIntegral_annulus_comp_norm (f : ℝ → E) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ x in annulus a b, f ‖x‖ = (2 * π) • ∫ r in a..b, r • f r := by
  have hset : annulus a b = {x : ℂ | ‖x‖ ∈ Ioo a b} := rfl
  have hinter : Ioi (0 : ℝ) ∩ Ioo a b = Ioo a b :=
    inter_eq_right.mpr fun r hr => lt_of_le_of_lt ha hr.1
  rw [hset, setIntegral_preimage_norm f measurableSet_Ioo, hinter,
    intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]

/-- Radial integrals outside a disk: `∫_{‖x‖>R} f(‖x‖) dx = 2π ∫_R^∞ r f(r) dr`. -/
theorem setIntegral_compl_ball_comp_norm (f : ℝ → E) {R : ℝ} (hR : 0 ≤ R) :
    ∫ x in {x : ℂ | R < ‖x‖}, f ‖x‖ = (2 * π) • ∫ r in Ioi R, r • f r := by
  have hset : {x : ℂ | R < ‖x‖} = {x : ℂ | ‖x‖ ∈ Ioi R} := rfl
  have hinter : Ioi (0 : ℝ) ∩ Ioi R = Ioi R :=
    inter_eq_right.mpr fun r hr => lt_of_le_of_lt hR hr
  rw [hset, setIntegral_preimage_norm f measurableSet_Ioi, hinter]

/-- Integrability of a radial function on a disk. -/
theorem integrableOn_ball_comp_norm_iff {f : ℝ → E} {ρ : ℝ} (hρ : 0 ≤ ρ) :
    IntegrableOn (fun x : ℂ => f ‖x‖) (ball 0 ρ) ↔
      IntegrableOn (fun r : ℝ => r • f r) (Ioo 0 ρ) := by
  have h := integrableOn_fun_norm_addHaar (volume : Measure ℂ) (f := f) (r := ρ)
  rw [Complex.finrank_real_complex] at h
  simpa using h

end NonUniqueEuler.Polar
