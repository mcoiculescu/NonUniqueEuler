import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Statement layer: the plane, rotations and the Biot–Savart law

Statement layer: definitions and statements only, no proofs.

Manuscript sources (`manuscript/tex/sections/`):
* `02_prelim.tex:13-14`  we identify `ℝ²` with `ℂ`;
* `02_prelim.tex:21-26`  rotations `O_θ` (multiplication by `e^{iθ}`), `m`-fold symmetry
  and radial functions (both almost everywhere);
* `01_intro.tex:12-14`, `02_prelim.tex:36-38`  the Biot–Savart kernel
  `K(x) = x^⊥ / (2π|x|²)`, `x^⊥ = (-x₂, x₁)`, and `v = K * ω`.

Conventions.
* The plane is `ℂ`, with its Euclidean norm `‖·‖` and its Lebesgue measure `volume`
  (Mathlib proves `volume` on `ℂ` is the push-forward of Lebesgue measure on `ℝ × ℝ`,
  `Complex.volume_preserving_equiv_real_prod`).
* Vorticities are real valued, `ℂ → ℝ`; velocities are `ℂ`-valued (a vector of `ℝ²`
  written as a complex number).
* `x^⊥ = (-x₂, x₁)` is `I * x` for `x = x₁ + i x₂`.
-/

noncomputable section

open MeasureTheory

namespace NonUniqueEuler

/-- The rotation `O_θ` of the plane by the angle `θ`: multiplication by `e^{iθ}`
(`02_prelim.tex:21-22`). -/
def rot (θ : ℝ) (x : ℂ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I) * x

/-- A function on the plane is `m`-fold symmetric if `g ∘ O_{2π/m} = g` almost everywhere
(`02_prelim.tex:23-25`). -/
def IsMFoldSymmetric (m : ℕ) (g : ℂ → ℝ) : Prop :=
  (fun x => g (rot (2 * Real.pi / m) x)) =ᵐ[volume] g

/-- A function on the plane is radial if `g ∘ O_θ = g` almost everywhere, for every `θ`
(`02_prelim.tex:25-26`). -/
def IsRadial (g : ℂ → ℝ) : Prop :=
  ∀ θ : ℝ, (fun x => g (rot θ x)) =ᵐ[volume] g

/-- Pointwise rotation invariance. This is stronger than `IsRadial`; the main theorem asserts
it for the explicit datum `f`, which is defined pointwise. -/
def IsRadialPointwise (g : ℂ → ℝ) : Prop :=
  ∀ θ : ℝ, ∀ x : ℂ, g (rot θ x) = g x

/-- The Biot–Savart kernel `K(z) = z^⊥ / (2π|z|²)` with `z^⊥ = i z`
(`01_intro.tex:12`, `02_prelim.tex:36`). At `z = 0` Lean's division gives `0`; this single
point is a null set and plays no role. -/
def biotSavartKernel (z : ℂ) : ℂ :=
  (Complex.I * z) / ((2 * Real.pi * ‖z‖ ^ 2 : ℝ) : ℂ)

/-- The Biot–Savart velocity `v = K * g`, `v(x) = ∫ K(x - y) g(y) dy`
(`02_prelim.tex:37-38`: "whenever the integral converges"). Lean's Bochner integral is `0`
where the integrand is not integrable; the weak-solution definitions require separately that
the integral converges absolutely almost everywhere (`IsWeakSolution.velocity_convergent`), so
this junk value never enters. -/
def velocity (g : ℂ → ℝ) (x : ℂ) : ℂ :=
  ∫ y, biotSavartKernel (x - y) * (g y : ℂ)

end NonUniqueEuler
