import NonUniqueEuler.Statement.Plane
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-!
# Polar coordinates and radial calculus on `ℂ` (definitions; library I-POLAR)

Manuscript-independent infrastructure (library I-POLAR). The plane is `ℂ`
with `volume` (decision D1); rotations are `NonUniqueEuler.rot θ x = exp (θ I) * x`
(statement layer, `Statement/Plane.lean`).

Definitions.
* `angAvg g x`: the angular average `ḡ(x) = (2π)⁻¹ ∫₀^{2π} g(O_φ x) dφ` of
  `lem:hollow` (`02_prelim.tex:413-414`). It is *defined* as Mathlib's circle average
  `Real.circleAverage g 0 ‖x‖`; the rotation form is `angAvg_eq_intervalIntegral_rot`
  (`I/Infra/Polar/AngularAverage.lean`). So `angAvg g` is pointwise radial by definition.
* `angularSector g ℓ r`: the angular sector `g_ℓ(r) = (2π)⁻¹ ∫₀^{2π} g(r e^{iθ}) e^{-iℓθ} dθ`
  (`02_prelim.tex:27-33`). The library I-ANG builds
  the `L²` theory on top of it.
* `circ g r`: the manuscript's `Circ_g(r) = ∫_{B_r} g` (`02_prelim.tex:131`).
* `annulus a b`: the open annulus `{a < ‖x‖ < b}`.

Fully proved basic lemmas: `norm_rot`, `rot_eq_rotation`, `measurePreserving_rot`, `rot_add`,
`rot_zero`, `angAvg_rot`, `angAvg_of_norm_eq`, `isRadialPointwise_angAvg`, `mem_annulus`,
`isOpen_annulus`, `measurableSet_annulus`.

The theorems are stated in `NonUniqueEuler/I/Infra/Polar/*.lean`.
-/

noncomputable section

open MeasureTheory Set Metric Real

namespace NonUniqueEuler.Polar

/-- The angular average `ḡ(x) = (2π)⁻¹ ∫₀^{2π} g(O_φ x) dφ` (`02_prelim.tex:413-414`), defined as
the circle average of `g` over the circle of radius `‖x‖` centred at `0`. -/
def angAvg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℂ → E) (x : ℂ) : E :=
  Real.circleAverage g 0 ‖x‖

/-- The angular sector `g_ℓ(r) = (2π)⁻¹ ∫₀^{2π} g(r e^{iθ}) e^{-iℓθ} dθ` (`02_prelim.tex:30-31`).
It is the junk value `0` where `θ ↦ g (r e^{iθ})` is not integrable. -/
def angularSector (g : ℂ → ℂ) (ℓ : ℤ) (r : ℝ) : ℂ :=
  (2 * π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π,
    g ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) * Complex.exp (-((ℓ : ℂ) * θ * Complex.I))

/-- The manuscript's `Circ_g(r) = ∫_{B_r} g` (`02_prelim.tex:131`), with `B_r` the open disk. -/
def circ (g : ℂ → ℝ) (r : ℝ) : ℝ :=
  ∫ y in ball (0 : ℂ) r, g y

/-- The open annulus `{x : a < ‖x‖ < b}`. -/
def annulus (a b : ℝ) : Set ℂ :=
  {x | a < ‖x‖ ∧ ‖x‖ < b}

/-! ### Basic lemmas (fully proved) -/

theorem mem_annulus {a b : ℝ} {x : ℂ} : x ∈ annulus a b ↔ a < ‖x‖ ∧ ‖x‖ < b := Iff.rfl

theorem isOpen_annulus (a b : ℝ) : IsOpen (annulus a b) :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

theorem measurableSet_annulus (a b : ℝ) : MeasurableSet (annulus a b) :=
  (isOpen_annulus a b).measurableSet

@[simp] theorem norm_rot (θ : ℝ) (x : ℂ) : ‖rot θ x‖ = ‖x‖ := by
  simp [rot, Complex.norm_exp_ofReal_mul_I]

theorem rot_zero (x : ℂ) : rot 0 x = x := by simp [rot]

theorem rot_add (θ φ : ℝ) (x : ℂ) : rot (θ + φ) x = rot θ (rot φ x) := by
  simp only [rot, Complex.ofReal_add, add_mul, Complex.exp_add, mul_assoc]

/-- `rot θ` is Mathlib's `rotation` by the unit complex number `e^{iθ}`. -/
theorem rot_eq_rotation (θ : ℝ) : rot θ = ⇑(rotation (Circle.exp θ)) := by
  funext x
  simp [rot, rotation_apply, Circle.coe_exp]

/-- Rotations preserve Lebesgue measure. -/
theorem measurePreserving_rot (θ : ℝ) : MeasurePreserving (rot θ) volume volume := by
  rw [rot_eq_rotation]
  exact (rotation (Circle.exp θ)).measurePreserving

theorem angAvg_of_norm_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℂ → E)
    {x y : ℂ} (h : ‖x‖ = ‖y‖) : angAvg g x = angAvg g y := by
  simp [angAvg, h]

@[simp] theorem angAvg_rot {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℂ → E)
    (θ : ℝ) (x : ℂ) : angAvg g (rot θ x) = angAvg g x :=
  angAvg_of_norm_eq g (norm_rot θ x)

/-- The angular average is pointwise radial. -/
theorem isRadialPointwise_angAvg (g : ℂ → ℝ) : IsRadialPointwise (angAvg g) :=
  fun θ x => angAvg_rot g θ x

end NonUniqueEuler.Polar
