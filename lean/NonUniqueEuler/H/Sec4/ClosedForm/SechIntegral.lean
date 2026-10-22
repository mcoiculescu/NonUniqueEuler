import NonUniqueEuler.I.Verify.ProfileBasic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Helper for `lem:closed-form`: the `sech²` integral

Proof of the identity used in `lem:closed-form`(2) (`04_ring.tex:812-818`):
`∫_ℝ e^{αx} ½ sech²x dx = πα/(2 sin(πα/2))` for `0 < α < 2`, written with
`H'(x) = 2H(x)H(-x) = ½ sech²x` (`AppA.hasDerivAt_H`):

`∫_ℝ e^{βx} · 2H(x)H(-x) dx = (β/2) π / sin(π β/2)`, `0 < β < 2`.

**Deviation (route).** The manuscript substitutes `t = e^{2x}` and uses Euler's Beta integral on
`(0, ∞)`. Mathlib's Beta integral is on `(0, 1)`, so we substitute `v = H(x)` instead
(`dv = H'(x) dx`, `e^{2x} = v/(1-v)`): the integral is `B(1 + β/2, 1 - β/2)`, and
`Γ(1+z)Γ(1-z) = zΓ(z)Γ(1-z) = zπ/sin(πz)` (`Complex.Gamma_mul_Gamma_eq_betaIntegral`,
`Complex.Gamma_add_one`, `Complex.Gamma_mul_Gamma_one_sub`). The change of variables
(`integral_image_eq_integral_abs_deriv_smul`) holds without integrability hypotheses.
-/

noncomputable section

open MeasureTheory Set Real

namespace NonUniqueEuler

namespace ClosedFormAux

open RingData AppA

theorem H_lt_one (x : ℝ) : H x < 1 := by
  have h1 := H_add_H_neg x
  have h2 := H_pos (-x)
  linarith

/-- `H(ℝ) = (0, 1)`. -/
theorem H_image_univ : H '' univ = Ioo 0 1 := by
  ext v
  constructor
  · rintro ⟨x, -, rfl⟩
    exact ⟨H_pos x, H_lt_one x⟩
  · rintro ⟨h0, h1⟩
    refine ⟨Real.log (v / (1 - v)) / 2, mem_univ _, ?_⟩
    have h1' : 0 < 1 - v := by linarith
    have hq : 0 < v / (1 - v) := div_pos h0 h1'
    simp only [H]
    rw [show -2 * (Real.log (v / (1 - v)) / 2) = -Real.log (v / (1 - v)) by ring,
      Real.exp_neg, Real.exp_log hq]
    have hv : v ≠ 0 := h0.ne'
    have hv' : 1 - v ≠ 0 := h1'.ne'
    field_simp
    ring

/-- `H(x)/H(-x) = e^{2x}`. -/
theorem H_div_H_neg (x : ℝ) : H x / H (-x) = Real.exp (2 * x) := by
  simp only [H]
  rw [show -2 * -x = 2 * x by ring, show -2 * x = -(2 * x) by ring, Real.exp_neg]
  have := Real.exp_pos (2 * x)
  field_simp
  ring

/-- `H(x)^{β/2} (1 - H(x))^{-β/2} = e^{βx}`. -/
theorem rpow_H (β x : ℝ) : H x ^ (β / 2) * (1 - H x) ^ (-(β / 2)) = Real.exp (β * x) := by
  have h1 : 1 - H x = H (-x) := by linarith [H_add_H_neg x]
  rw [h1, Real.rpow_neg (H_pos (-x)).le, ← div_eq_mul_inv,
    ← Real.div_rpow (H_pos x).le (H_pos (-x)).le, H_div_H_neg, ← Real.exp_mul]
  congr 1
  ring

/-- The substitution `v = H(x)`. -/
theorem integral_exp_mul_dH_eq_Ioo (β : ℝ) :
    ∫ x, Real.exp (β * x) * (2 * (H x * H (-x))) =
      ∫ v in Ioo (0 : ℝ) 1, v ^ (β / 2) * (1 - v) ^ (-(β / 2)) := by
  have hcv := integral_image_eq_integral_abs_deriv_smul (s := univ) (f := H)
    (f' := fun x => 2 * (H x * H (-x))) MeasurableSet.univ
    (fun x _ => (hasDerivAt_H x).hasDerivWithinAt) strictMono_H.injective.injOn
    (fun v => v ^ (β / 2) * (1 - v) ^ (-(β / 2)))
  rw [H_image_univ, Measure.restrict_univ] at hcv
  rw [hcv]
  congr 1
  funext x
  have hpos : 0 < 2 * (H x * H (-x)) := by
    have := H_pos x
    have := H_pos (-x)
    positivity
  rw [smul_eq_mul, rpow_H, abs_of_pos hpos]
  ring

/-- The integral over `(0, 1)` is the Beta integral `B(1 + β/2, 1 - β/2)`. -/
theorem integral_Ioo_rpow_eq_beta (β : ℝ) :
    ((∫ v in Ioo (0 : ℝ) 1, v ^ (β / 2) * (1 - v) ^ (-(β / 2)) : ℝ) : ℂ) =
      Complex.betaIntegral (((β / 2 : ℝ) : ℂ) + 1) (1 - ((β / 2 : ℝ) : ℂ)) := by
  rw [Complex.betaIntegral, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioo (fun v hv => ?_)
  have h0 : 0 ≤ v := hv.1.le
  have h1 : 0 ≤ 1 - v := by linarith [hv.2]
  rw [Complex.ofReal_mul, Complex.ofReal_cpow h0, Complex.ofReal_cpow h1]
  have e1 : ((β / 2 : ℝ) : ℂ) + 1 - 1 = ((β / 2 : ℝ) : ℂ) := by ring
  have e2 : 1 - ((β / 2 : ℝ) : ℂ) - 1 = ((-(β / 2) : ℝ) : ℂ) := by push_cast; ring
  rw [e1, e2]
  push_cast
  ring

/-- `B(1 + z, 1 - z) = zπ/sin(πz)` for `z = β/2 ∈ (0, 1)`. -/
theorem betaIntegral_eq {β : ℝ} (h0 : 0 < β) (h2 : β < 2) :
    Complex.betaIntegral (((β / 2 : ℝ) : ℂ) + 1) (1 - ((β / 2 : ℝ) : ℂ)) =
      ((β / 2 * π / Real.sin (π * (β / 2)) : ℝ) : ℂ) := by
  set z : ℂ := ((β / 2 : ℝ) : ℂ) with hzdef
  have hz : z ≠ 0 := by
    rw [hzdef, Ne, Complex.ofReal_eq_zero]
    linarith
  have hre1 : 0 < (z + 1).re := by
    rw [hzdef, Complex.add_re, Complex.ofReal_re, Complex.one_re]
    linarith
  have hre2 : 0 < (1 - z).re := by
    rw [hzdef, Complex.sub_re, Complex.ofReal_re, Complex.one_re]
    linarith
  have hG2 : Complex.Gamma 2 = 1 := by
    simp
  have key := Complex.Gamma_mul_Gamma_eq_betaIntegral hre1 hre2
  rw [show z + 1 + (1 - z) = 2 by ring, hG2, one_mul, Complex.Gamma_add_one z hz, mul_assoc,
    Complex.Gamma_mul_Gamma_one_sub] at key
  rw [← key, hzdef]
  push_cast
  ring

/-- **The `sech²` integral** (`04_ring.tex:812-818`): for `0 < β < 2`,
`∫_ℝ e^{βx} · 2H(x)H(-x) dx = (β/2) π / sin(π β/2)`. -/
theorem integral_exp_mul_dH {β : ℝ} (h0 : 0 < β) (h2 : β < 2) :
    ∫ x, Real.exp (β * x) * (2 * (H x * H (-x))) = β / 2 * π / Real.sin (π * (β / 2)) := by
  rw [integral_exp_mul_dH_eq_Ioo]
  exact_mod_cast (integral_Ioo_rpow_eq_beta β).trans (betaIntegral_eq h0 h2)

end ClosedFormAux

end NonUniqueEuler
