import NonUniqueEuler.H.Sec5.ReductionField.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

/-!
# Helper for `lem:reduction`(1): radial and angular components on circles

Helper of `P/Sec5/ReductionField.lean` (`05_single_ring.tex:165-176`). On the circle
`x = r e^{iθ}`, `r > 0`:
* `radComp F x = ⟨F(x), e^{iθ}⟩` and `angComp F x = ⟨F(x), i e^{iθ}⟩` (the real inner product of
  `ℂ = ℝ²`, as in `I/Infra/Multipole/Circulation.lean`);
* for the point vortex: `vortex G · e_r = 0` and `vortex G · e_θ = G/r`.
-/

noncomputable section

open ComplexConjugate

namespace NonUniqueEuler

namespace OneRing

namespace RedFieldH

theorem norm_circle {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = r := by
  rw [norm_mul, norm_exp_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]

theorem unit_circle {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    (((‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ : ℝ) : ℂ))⁻¹ *
      ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = Complex.exp ((θ : ℂ) * Complex.I) := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [norm_circle hr, ← mul_assoc, inv_mul_cancel₀ hr0, one_mul]

theorem conj_exp_mul_I (θ : ℝ) :
    conj (Complex.exp ((θ : ℂ) * Complex.I)) = Complex.exp (-((θ : ℂ) * Complex.I)) := by
  rw [← Complex.exp_conj]
  simp [Complex.conj_ofReal]

theorem exp_mul_I_mul_conj (θ : ℝ) :
    Complex.exp ((θ : ℂ) * Complex.I) * conj (Complex.exp ((θ : ℂ) * Complex.I)) = 1 := by
  rw [conj_exp_mul_I, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

/-- `F · e_r = ⟨F, e^{iθ}⟩` on the circle `x = r e^{iθ}`. -/
theorem radComp_circle (F : ℂ → ℂ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    radComp F ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
      inner ℝ (F (circleMap 0 r θ)) (Complex.exp ((θ : ℂ) * Complex.I)) := by
  rw [radComp, unit_circle hr, circleMap_zero, Complex.inner, ← Complex.conj_re, map_mul,
    Complex.conj_conj, mul_comm]

/-- `F · e_θ = ⟨F, i e^{iθ}⟩` on the circle `x = r e^{iθ}`. -/
theorem angComp_circle (F : ℂ → ℂ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    angComp F ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
      inner ℝ (F (circleMap 0 r θ)) (Complex.I * Complex.exp ((θ : ℂ) * Complex.I)) := by
  have h := unit_circle hr θ
  rw [angComp, mul_left_comm, h, circleMap_zero, Complex.inner, ← Complex.conj_re (_ * conj _),
    map_mul, Complex.conj_conj, mul_comm]

/-- The point vortex has no radial component on circles. -/
theorem radComp_vortex_circle (G : ℝ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    radComp (vortex G) ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = 0 := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have he := exp_mul_I_mul_conj θ
  rw [radComp, unit_circle hr, vortex, norm_circle hr]
  have : (G : ℂ) * (Complex.I * ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) /
        (((r ^ 2 : ℝ)) : ℂ) * conj (Complex.exp ((θ : ℂ) * Complex.I)) =
      (((G / r : ℝ)) : ℂ) * Complex.I := by
    calc (G : ℂ) * (Complex.I * ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) /
          (((r ^ 2 : ℝ)) : ℂ) * conj (Complex.exp ((θ : ℂ) * Complex.I))
        = (G : ℂ) * Complex.I * (r : ℂ) / ((r : ℂ) ^ 2) *
            (Complex.exp ((θ : ℂ) * Complex.I) * conj (Complex.exp ((θ : ℂ) * Complex.I))) := by
          push_cast
          ring
      _ = (((G / r : ℝ)) : ℂ) * Complex.I := by
          rw [he]
          push_cast
          field_simp
  rw [this]
  simp

/-- The angular component of the point vortex on `|x| = r` is `G/r`. -/
theorem angComp_vortex_circle (G : ℝ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    angComp (vortex G) ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = G / r := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have he := exp_mul_I_mul_conj θ
  have h := unit_circle hr θ
  rw [angComp, mul_left_comm, h, vortex, norm_circle hr]
  have : (G : ℂ) * (Complex.I * ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) /
        (((r ^ 2 : ℝ)) : ℂ) * conj (Complex.I * Complex.exp ((θ : ℂ) * Complex.I)) =
      (((G / r : ℝ)) : ℂ) := by
    rw [map_mul, Complex.conj_I]
    calc (G : ℂ) * (Complex.I * ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) /
          (((r ^ 2 : ℝ)) : ℂ) * (-Complex.I * conj (Complex.exp ((θ : ℂ) * Complex.I)))
        = -(Complex.I * Complex.I) * (G : ℂ) * (r : ℂ) / ((r : ℂ) ^ 2) *
            (Complex.exp ((θ : ℂ) * Complex.I) * conj (Complex.exp ((θ : ℂ) * Complex.I))) := by
          push_cast
          ring
      _ = (((G / r : ℝ)) : ℂ) := by
          rw [he, Complex.I_mul_I]
          push_cast
          field_simp
  rw [this, Complex.ofReal_re]

end RedFieldH

end OneRing

end NonUniqueEuler
