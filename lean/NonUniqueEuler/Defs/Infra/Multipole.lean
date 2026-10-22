import NonUniqueEuler.Defs.Infra.Polar
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Complex-variable form of the Biot–Savart law (definitions; library I-MULT)

Manuscript-independent infrastructure (library I-MULT; restructuring R11).
With `z = x₁ + i x₂` and the statement-layer kernel `biotSavartKernel z = i z /(2π|z|²)`, the
manuscript uses (`02_prelim.tex:430-433`, eq:complex-velocity of `07_several_rings.tex`)
`u₁ - i u₂ = (2πi)⁻¹ ∫ ω(w)/(z-w) dw`, i.e. `conj (velocity ω z) = (2πi)⁻¹ · C[ω](z)` with the
Cauchy transform `C[g](z) = ∫ g(w) (z-w)⁻¹ dw`.

Definitions.
* `cauchyTransform g z = ∫ g(w) (z - w)⁻¹ dw` (Bochner integral; `0` where not integrable).
* `moment g l = ∫ g(w) w^l dw` for `l : ℤ`: the multipole coefficients. In the manuscript's
  notation (`def:multipole`, `02_prelim.tex:450-460`, proofs of `lem:hollow`, `lem:ext-multipole`):
  `Q_l[g] = moment g l`, `c_l(ν) = moment ν (-l)`, `pin_m[g] = (2π)⁻¹ moment g (-m)`.
* `conjMoment g l = ∫ g(w) w̄^l dw` for `l : ℤ`; `pout_m[g] = (2π)⁻¹ conjMoment g m`.
* `laurentTail a z = ∑' l, a l / z^(l+1)`: the exterior Laurent series (the field outside a
  confined body, `lem:ext-multipole`).
* `logPotential g x = (2π)⁻¹ ∫ log|x - y| g(y) dy` (complex-valued `g`): the stream function of
  `g` (`02_prelim.tex:38-43`; complex `g` for the sector functions `g(r) e^{iℓθ}` of
  `lem:sector`(1) and `lem:adjoint`(3)). For a real vorticity `ω` use
  `logPotential (fun y => (ω y : ℂ))`, whose values are real: it is `logPotentialReal ω`
  (`logPotential_ofReal`).
* `logPotentialReal g x = (2π)⁻¹ ∫ log|x - y| g(y) dy` for real `g` (the stream function `ψ` of
  `lem:BS-basic`(d), `ψ_h` of `lem:reduction`(1)).

Fully proved basic lemmas:
* `conj_biotSavartKernel : conj (K z) = (2π i z)⁻¹` (for every `z`, including `z = 0`, where both
  sides are `0`);
* `velocity_eq_conj_cauchyTransform : velocity g x = conj ((2πi)⁻¹ · C[g](x))` (for every `x`,
  with no integrability hypothesis: both sides use the same Bochner integral up to `conj`);
* `logPotential_ofReal : logPotential (ofReal ∘ g) x = logPotentialReal g x`.

The theorems are stated in `NonUniqueEuler/I/Infra/Multipole/*.lean`.
-/

noncomputable section

open MeasureTheory Set Metric Real ComplexConjugate

namespace NonUniqueEuler.Multipole

/-- The Cauchy transform `C[g](z) = ∫ g(w) (z - w)⁻¹ dw`. -/
def cauchyTransform (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ w, g w * (z - w)⁻¹

/-- The multipole moment `∫ g(w) w^l dw`, `l : ℤ` (`Q_l`, `c_l`, `pin_m` of the manuscript). -/
def moment (g : ℂ → ℂ) (l : ℤ) : ℂ :=
  ∫ w, g w * w ^ l

/-- The conjugate moment `∫ g(w) w̄^l dw`, `l : ℤ` (`2π · pout_m[g] = conjMoment g m`). -/
def conjMoment (g : ℂ → ℂ) (l : ℤ) : ℂ :=
  ∫ w, g w * conj w ^ l

/-- The exterior Laurent series `∑_{l ≥ 0} a_l z^{-(l+1)}`. -/
def laurentTail (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑' l : ℕ, a l * (z ^ (l + 1))⁻¹

/-- The logarithmic potential (stream function) `(2π)⁻¹ ∫ log|x - y| g(y) dy`. -/
def logPotential (g : ℂ → ℂ) (x : ℂ) : ℂ :=
  (2 * π : ℂ)⁻¹ * ∫ y, (Real.log ‖x - y‖ : ℂ) * g y

/-- The real logarithmic potential `(2π)⁻¹ ∫ log|x - y| g(y) dy` of a real `g`. -/
def logPotentialReal (g : ℂ → ℝ) (x : ℂ) : ℝ :=
  (2 * π)⁻¹ * ∫ y, Real.log ‖x - y‖ * g y

/-! ### Basic lemmas (fully proved) -/

theorem logPotential_ofReal (g : ℂ → ℝ) (x : ℂ) :
    logPotential (fun y => (g y : ℂ)) x = (logPotentialReal g x : ℂ) := by
  simp only [logPotential, logPotentialReal, Complex.ofReal_mul]
  congr 1
  · push_cast
    ring
  · rw [← integral_complex_ofReal]
    push_cast
    rfl

/-- `conj (K z) = (2π i z)⁻¹`, i.e. `K₁ - i K₂ = 1/(2π i z)`, for every `z` (both sides vanish
at `z = 0`). -/
theorem conj_biotSavartKernel (z : ℂ) :
    conj (biotSavartKernel z) = (2 * π * Complex.I * z)⁻¹ := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [biotSavartKernel]
  · have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hcz : conj z ≠ 0 := (map_ne_zero _).mpr hz
    have hsq : ((2 * π * ‖z‖ ^ 2 : ℝ) : ℂ) = 2 * π * (z * conj z) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    simp only [biotSavartKernel, map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal]
    rw [hsq]
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring

/-- The complex form of the Biot–Savart law: `velocity g x = conj ((2πi)⁻¹ C[g](x))`, that is
`u₁ - i u₂ = (2πi)⁻¹ ∫ g(w)/(x - w) dw`, for every `x`. -/
theorem velocity_eq_conj_cauchyTransform (g : ℂ → ℝ) (x : ℂ) :
    velocity g x =
      conj ((2 * π * Complex.I)⁻¹ * cauchyTransform (fun w => (g w : ℂ)) x) := by
  rw [← Complex.conj_conj (velocity g x)]
  congr 1
  rw [velocity, ← integral_conj, cauchyTransform, ← integral_const_mul]
  congr 1
  funext y
  rw [map_mul, conj_biotSavartKernel, Complex.conj_ofReal, mul_inv]
  ring

end NonUniqueEuler.Multipole
