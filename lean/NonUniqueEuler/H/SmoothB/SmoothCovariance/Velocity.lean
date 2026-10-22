import NonUniqueEuler.Statement.Plane
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.Circle
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Helper for `P/SmoothB/SmoothCovariance`: covariance of the Biot–Savart law

* `biotSavartKernel_real_smul`: `K_BS(r z) = r⁻¹ K_BS(z)` (homogeneity of degree `-1`);
* `biotSavartKernel_rot`: `K_BS(O_θ z) = O_θ K_BS(z)` (`B_global_smooth.tex:534`);
* `velocity_scale`: `K ∗ (A⁻¹ g(r ·)) (y) = (Ar)⁻¹ (K ∗ g)(r y)` (`06_datum.tex:142-143`);
* `velocity_comp_rot`: `K ∗ (g ∘ O_θ) (x) = O_θ⁻¹ (K ∗ g)(O_θ x)` (`B_global_smooth.tex:536-537`).

The identities hold for every `g` (Lean's junk value `0` for non-integrable integrands is
respected by both changes of variables).
-/

noncomputable section

open MeasureTheory

namespace NonUniqueEuler.Smooth.Covariance

/-- Homogeneity of degree `-1`: `K_BS(r z) = r⁻¹ K_BS(z)` for every real `r`. -/
theorem biotSavartKernel_real_smul (r : ℝ) (z : ℂ) :
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

/-- Rotation covariance: `K_BS(O_θ z) = O_θ K_BS(z)`. -/
theorem biotSavartKernel_rot (θ : ℝ) (z : ℂ) :
    biotSavartKernel (rot θ z) = rot θ (biotSavartKernel z) := by
  simp only [biotSavartKernel, rot, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  ring

/-- Scaling of the Biot–Savart law (`06_datum.tex:142-143`): for `r > 0`,
`K ∗ (A⁻¹ g(r ·)) (y) = (Ar)⁻¹ (K ∗ g)(r y)`. -/
theorem velocity_scale (A : ℝ) {r : ℝ} (hr : 0 < r) (g : ℂ → ℝ) (x : ℂ) :
    velocity (fun y => A⁻¹ * g ((r : ℂ) * y)) x =
      (((A * r)⁻¹ : ℝ) : ℂ) * velocity g ((r : ℂ) * x) := by
  set F : ℂ → ℂ := fun z =>
    ((r : ℂ) * (A⁻¹ : ℂ)) * (biotSavartKernel ((r : ℂ) * x - z) * (g z : ℂ)) with hF
  have hpt : ∀ y : ℂ, biotSavartKernel (x - y) * (((A⁻¹ * g ((r : ℂ) * y) : ℝ)) : ℂ) =
      F (r • y) := by
    intro y
    have h1 : (r : ℂ) * x - r • y = (r : ℂ) * (x - y) := by
      rw [Complex.real_smul]; ring
    show _ = (r : ℂ) * (A⁻¹ : ℂ) * (biotSavartKernel ((r : ℂ) * x - r • y) * (g (r • y) : ℂ))
    rw [h1, biotSavartKernel_real_smul, Complex.real_smul]
    have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
    push_cast
    field_simp
  have hint : ∫ z, F z = ((r : ℂ) * (A⁻¹ : ℂ)) * velocity g ((r : ℂ) * x) := by
    rw [hF, integral_const_mul]
    rfl
  calc velocity (fun y => A⁻¹ * g ((r : ℂ) * y)) x
      = ∫ y, F (r • y) := by
        simp only [velocity]
        exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = |(r ^ Module.finrank ℝ ℂ)⁻¹| • ∫ z, F z := Measure.integral_comp_smul volume F r
    _ = (((A * r)⁻¹ : ℝ) : ℂ) * velocity g ((r : ℂ) * x) := by
        rw [hint, Complex.finrank_real_complex, abs_of_pos (inv_pos.2 (pow_pos hr 2)),
          Complex.real_smul]
        have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
        push_cast
        field_simp

/-- `rot θ` as a linear isometry equivalence of `ℂ`. -/
theorem rot_eq_rotation (θ : ℝ) (y : ℂ) : rot θ y = rotation (Circle.exp θ) y := by
  rw [rotation_apply, Circle.coe_exp, rot]

theorem rot_neg_rot (θ : ℝ) (y : ℂ) : rot (-θ) (rot θ y) = y := by
  simp only [rot, ← mul_assoc, ← Complex.exp_add]
  push_cast
  ring_nf
  simp

theorem rot_rot_neg (θ : ℝ) (y : ℂ) : rot θ (rot (-θ) y) = y := by
  simpa using rot_neg_rot (-θ) y

/-- Rotation covariance of the Biot–Savart law (`B_global_smooth.tex:536-537`):
`K ∗ (g ∘ O_θ) (x) = O_θ⁻¹ (K ∗ g)(O_θ x)`. -/
theorem velocity_comp_rot (g : ℂ → ℝ) (θ : ℝ) (x : ℂ) :
    velocity (fun y => g (rot θ y)) x = rot (-θ) (velocity g (rot θ x)) := by
  set G : ℂ → ℂ := fun z =>
    Complex.exp ((-θ : ℝ) * Complex.I) * (biotSavartKernel (rot θ x - z) * (g z : ℂ)) with hG
  have hpt : ∀ y : ℂ, biotSavartKernel (x - y) * (g (rot θ y) : ℂ) =
      G (rotation (Circle.exp θ) y) := by
    intro y
    rw [← rot_eq_rotation]
    have h1 : rot θ x - rot θ y = rot θ (x - y) := by simp only [rot]; ring
    have h2 : biotSavartKernel (x - y) = Complex.exp ((-θ : ℝ) * Complex.I) *
        biotSavartKernel (rot θ (x - y)) := by
      rw [biotSavartKernel_rot, ← rot, rot_neg_rot]
    simp only [hG, h1, h2]
    ring
  calc velocity (fun y => g (rot θ y)) x
      = ∫ y, G (rotation (Circle.exp θ) y) := by
        simp only [velocity]
        exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ∫ z, G z := integral_comp (rotation (Circle.exp θ)) G
    _ = rot (-θ) (velocity g (rot θ x)) := by
        rw [hG, integral_const_mul]
        rfl

end NonUniqueEuler.Smooth.Covariance
