import NonUniqueEuler.Defs.Sec7.All
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Proof: homogeneity of `K_BS` (fields in ring units)

Proof of `I/Sec7/FieldUnits.lean` (the claim "since `K_BS` is homogeneous of degree `-1`, `V` is
the velocity field of `g̃` minus its monopole", `07_several_rings.tex:138-140`,
`06_datum.tex:150-154`).

1. `K_BS(r z) = r⁻¹ K_BS(z)` (`biotSavartKernel_ofReal_mul`, also at `z = 0` and `r = 0`).
2. Change of variables `x = r η` (`Measure.integral_comp_smul`, `finrank ℝ ℂ = 2`):
   `velocity g̃ y = A⁻¹ r⁻² ∫ r K(r y - x) g(x) dx = (A r)⁻¹ velocity g (r y)`
   (`velocity_scaleVort`), and `∫ g̃ = A⁻¹ r⁻² ∫ g` (`integral_scaleVort`).
3. The monopoles agree (`monopole_scaleVort`); subtract.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Rings

open RingData Datum

namespace FieldUnits

/-- Homogeneity of degree `-1`: `K_BS(r z) = r⁻¹ K_BS(z)` for every real `r`. -/
theorem biotSavartKernel_ofReal_mul (r : ℝ) (z : ℂ) :
    biotSavartKernel ((r : ℂ) * z) = ((r⁻¹ : ℝ) : ℂ) * biotSavartKernel z := by
  simp only [biotSavartKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hz' : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  push_cast
  field_simp

/-- Velocity in units: `K ∗ (A⁻¹ g(r ·)) (y) = (K ∗ g)(r y) / (A r)` for `r > 0`. -/
theorem velocity_scaleVort (A : ℝ) {r : ℝ} (hr : 0 < r) (g : ℂ → ℝ) (y : ℂ) :
    velocity (scaleVort A r g) y = scaleField A r (velocity g) y := by
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  set F : ℂ → ℂ := fun z =>
    ((r : ℂ) * (A⁻¹ : ℂ)) * (biotSavartKernel ((r : ℂ) * y - z) * (g z : ℂ)) with hF
  have hpt : ∀ η : ℂ, biotSavartKernel (y - η) * ((scaleVort A r g η : ℝ) : ℂ) =
      F (r • η) := by
    intro η
    have h1 : (r : ℂ) * y - r • η = (r : ℂ) * (y - η) := by
      rw [Complex.real_smul]; ring
    show _ = (r : ℂ) * (A⁻¹ : ℂ) * (biotSavartKernel ((r : ℂ) * y - r • η) * (g (r • η) : ℂ))
    rw [h1, biotSavartKernel_ofReal_mul, Complex.real_smul, scaleVort]
    push_cast
    field_simp
  have hint : ∫ z, F z = ((r : ℂ) * (A⁻¹ : ℂ)) * velocity g ((r : ℂ) * y) := by
    rw [hF, integral_const_mul]
    rfl
  calc velocity (scaleVort A r g) y
      = ∫ η, F (r • η) := by
        simp only [velocity]
        exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = |(r ^ Module.finrank ℝ ℂ)⁻¹| • ∫ z, F z := Measure.integral_comp_smul volume F r
    _ = scaleField A r (velocity g) y := by
        rw [hint, Complex.finrank_real_complex, abs_of_pos (inv_pos.2 (pow_pos hr 2)),
          Complex.real_smul, scaleField]
        rcases eq_or_ne A 0 with rfl | hA
        · simp
        have hA' : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hA
        push_cast
        field_simp

/-- Total mass in units: `∫ A⁻¹ g(r ·) = A⁻¹ r⁻² ∫ g` for `r > 0`. -/
theorem integral_scaleVort (A : ℝ) {r : ℝ} (hr : 0 < r) (g : ℂ → ℝ) :
    ∫ η, scaleVort A r g η = A⁻¹ * (r ^ 2)⁻¹ * ∫ x, g x := by
  have h1 : ∀ η : ℂ, scaleVort A r g η = A⁻¹ * g (r • η) := by
    intro η
    rw [scaleVort, Complex.real_smul]
  simp only [h1]
  rw [integral_const_mul, Measure.integral_comp_smul volume g r, Complex.finrank_real_complex,
    smul_eq_mul, abs_of_pos (inv_pos.2 (pow_pos hr 2))]
  ring

/-- Monopole in units: the monopole of `A⁻¹ g(r ·)` is the monopole of `g` in units `(A, r)`. -/
theorem monopole_scaleVort (A : ℝ) {r : ℝ} (hr : 0 < r) (g : ℂ → ℝ) (y : ℂ) :
    BS.monopole (scaleVort A r g) y = scaleField A r (BS.monopole g) y := by
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  simp only [BS.monopole, scaleField]
  rw [integral_scaleVort A hr g, biotSavartKernel_ofReal_mul]
  rcases eq_or_ne A 0 with rfl | hA
  · simp
  have hA' : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hA
  push_cast
  field_simp

end FieldUnits

open FieldUnits in
/-- **Homogeneity of `K_BS`** (`07_several_rings.tex:138-140`, `06_datum.tex:150-154`). For
`A, r > 0` and every vorticity `g`, the velocity, the monopole and the non-monopole field of
`g̃ = A⁻¹ g(r ·)` are those of `g` in the units `(A, r)`: `V ↦ V(r ·)/(Ar)`. -/
theorem fields_scaleVort {A r : ℝ} (hA : 0 < A) (hr : 0 < r) (g : ℂ → ℝ) :
    (∀ y : ℂ, velocity (scaleVort A r g) y = scaleField A r (velocity g) y) ∧
    (∀ y : ℂ, BS.monopole (scaleVort A r g) y = scaleField A r (BS.monopole g) y) ∧
    (∀ y : ℂ, BS.extField (scaleVort A r g) y = scaleField A r (BS.extField g) y) := by
  -- `A > 0` is not needed: the identities hold for every real `A` (both sides vanish at `A = 0`).
  have _ := hA
  refine ⟨fun y => velocity_scaleVort A hr g y, fun y => monopole_scaleVort A hr g y,
    fun y => ?_⟩
  rw [BS.extField, velocity_scaleVort A hr g y, monopole_scaleVort A hr g y]
  simp only [scaleField, BS.extField, sub_div]

end Rings

end NonUniqueEuler
