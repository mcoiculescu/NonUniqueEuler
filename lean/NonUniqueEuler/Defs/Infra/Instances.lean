import Mathlib.Data.ENNReal.Holder
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Shared typeclass instances

Proof (`P`) and helper (`H`) files declare no global instances: every interface file `I/X.lean`
re-exports `P/X`, so a global instance there would be visible to every consumer. This file holds
the single canonical copy of each instance that Mathlib does not provide; `P`/`H` files import
this file instead of declaring their own.

* `holderTriple_four_four_two`: `4⁻¹ + 4⁻¹ = 2⁻¹`, i.e. Hölder `L⁴ × L⁴ → L²`. Used in
  `H/Sec2/HkCalculus/Basic` and `H/SmoothB/CommR2/Bounds`.
* `isFiniteMeasure_volume_restrict_ball`: Lebesgue measure on `ℂ` restricted to a ball is
  finite. Used, with centre `0`, in `H/Sec3/Commutator/Basic` and
  `H/Sec3/Commutator/SmoothApprox/Sobolev`.

Not repeated here, because Mathlib already has it: `ENNReal.HolderTriple 2 2 1` is
`ENNReal.HolderConjugate 2 2`, the instance `ENNReal.HolderConjugate.instTwoTwo`
(`Mathlib/Data/ENNReal/Holder.lean`); see the `example` below.
-/

open MeasureTheory Metric
open scoped ENNReal

namespace NonUniqueEuler.Instances

/-- Hölder exponents `(4, 4, 2)`: `4⁻¹ + 4⁻¹ = 2⁻¹`. -/
instance holderTriple_four_four_two : ENNReal.HolderTriple 4 4 2 := by
  refine ⟨?_⟩
  have h4 : (4 : ℝ≥0∞) = 2 * 2 := by norm_num
  rw [h4, ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top), ← two_mul,
    ← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]

/-- Lebesgue measure on `ℂ` restricted to a ball is a finite measure. -/
instance isFiniteMeasure_volume_restrict_ball (x : ℂ) (r : ℝ) :
    IsFiniteMeasure (volume.restrict (ball x r)) :=
  isFiniteMeasure_restrict.2 measure_ball_lt_top.ne

/-- `ENNReal.HolderTriple 2 2 1` comes from Mathlib (`ENNReal.HolderConjugate.instTwoTwo`). -/
example : ENNReal.HolderTriple 2 2 1 := inferInstance

example (r : ℝ) : IsFiniteMeasure (volume.restrict (ball (0 : ℂ) r)) := inferInstance

end NonUniqueEuler.Instances
