import NonUniqueEuler.Defs.Infra.Multipole

/-!
# Section 2: the multipole coefficients (`def:multipole`)

Definitions for `def:multipole` (`02_prelim.tex:448-457`).

For an integer `m ≥ 1` and `g ∈ L¹(ℝ²; ℂ)` with compact support in `ℝ² ∖ {0}`:
`pout_m[g] = (2π)⁻¹ ∫ g(y) ȳ^m dy`, `pin_m[g] = (2π)⁻¹ ∫ g(y) y^{-m} dy`,
`Q_m[g] = ∫ g(y) y^m dy`. The definitions below make sense for every `g : ℂ → ℂ` (Bochner
integrals, `0` if not integrable); the hypotheses of `def:multipole` go into the statements that
use them. They are the I-MULT moments up to normalization (`pout_eq_conjMoment`,
`pin_eq_moment`, `Qm_eq_moment`). The stream-function identities after the definition
(`02_prelim.tex:459-468`: the angular sector `m` of `(2π)⁻¹ log|·| ∗ g` equals
`-(2m)⁻¹ pout_m[g] r^{-m}` for `r > ρ₂` and `-(2m)⁻¹ pin_m[g] r^m` for `r < ρ₁`) are the I-MULT
interface theorems `Multipole.angularSector_logPotential_exterior_pos` and
`Multipole.angularSector_logPotential_interior_pos` (`I/Infra/Multipole/LogPotential.lean`).
The remark "for real `g`, `2π pout_m[g]` is the complex conjugate of `Q_m[g]`" is
`two_pi_mul_pout_ofReal`.

All lemmas in this file are fully proved.
-/

noncomputable section

open MeasureTheory ComplexConjugate

namespace NonUniqueEuler.BS

/-- The outer multipole coefficient `pout_m[g] = (2π)⁻¹ ∫ g(y) ȳ^m dy` (`def:multipole`,
`02_prelim.tex:452-453`). -/
def pout (m : ℕ) (g : ℂ → ℂ) : ℂ :=
  (2 * Real.pi : ℂ)⁻¹ * ∫ y, g y * conj y ^ m

/-- The inner multipole coefficient `pin_m[g] = (2π)⁻¹ ∫ g(y) y^{-m} dy` (`def:multipole`,
`02_prelim.tex:453`). -/
def pin (m : ℕ) (g : ℂ → ℂ) : ℂ :=
  (2 * Real.pi : ℂ)⁻¹ * ∫ y, g y * (y ^ m)⁻¹

/-- The moment `Q_m[g] = ∫ g(y) y^m dy` (`def:multipole`, `02_prelim.tex:454`). -/
def Qm (m : ℕ) (g : ℂ → ℂ) : ℂ :=
  ∫ y, g y * y ^ m

/-! ### Basic lemmas (fully proved) -/

theorem pout_eq_conjMoment (m : ℕ) (g : ℂ → ℂ) :
    pout m g = (2 * Real.pi : ℂ)⁻¹ * Multipole.conjMoment g m := by
  simp [pout, Multipole.conjMoment, zpow_natCast]

theorem pin_eq_moment (m : ℕ) (g : ℂ → ℂ) :
    pin m g = (2 * Real.pi : ℂ)⁻¹ * Multipole.moment g (-(m : ℤ)) := by
  simp [pin, Multipole.moment, zpow_neg, zpow_natCast]

theorem Qm_eq_moment (m : ℕ) (g : ℂ → ℂ) : Qm m g = Multipole.moment g m := by
  simp [Qm, Multipole.moment, zpow_natCast]

/-- For real `g`, `2π pout_m[g]` is the complex conjugate of `Q_m[g]` (`02_prelim.tex:468`). -/
theorem two_pi_mul_pout_ofReal (m : ℕ) (g : ℂ → ℝ) :
    (2 * Real.pi : ℂ) * pout m (fun y => (g y : ℂ)) = conj (Qm m fun y => (g y : ℂ)) := by
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  rw [pout, Qm, ← integral_conj, mul_inv_cancel_left₀ hpi]
  congr 1
  funext y
  simp [map_mul, map_pow]

end NonUniqueEuler.BS
