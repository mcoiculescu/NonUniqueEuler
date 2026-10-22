import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Exponentials of bounded operators from the spectrum (definitions; library I-DUNF)

Manuscript-independent infrastructure (library I-DUNF; restructuring R2,
decision D10). For a bounded operator `A : X →L[ℂ] X` on a complex Banach space, the exponential
bound `‖exp(tA)‖ ≤ C e^{σt}` from `spectrum ℂ A ⊆ {Re < σ}` is proved with a Dunford integral on a
single circle; the gap bound of `prop:semigroup` comes from deflating `A` by a rank-one
projection. This file fixes the vocabulary:

* `expDunford A c ρ t = (2πi)⁻¹ ∮_{|z - c| = ρ} e^{tz} (z - A)⁻¹ dz` (Mathlib's `resolvent`, so
  `resolvent A z = Ring.inverse (algebraMap ℂ _ z - A)`);
* `rankOneProj f g = f(·) g` (`ContinuousLinearMap.smulRight`), the projection
  `P g' = ℓ_*(g') g_*` of `thm:evans-simple`(2) when `f g = 1`;
* `deflate A P z₀ μ₀ = A - (z₀ - μ₀) P`, which moves the eigenvalue `z₀` of `A` with spectral
  projection `P` to `μ₀` (library I-DUNF, deflation);
* `IsSimpleSpectralProj A P z₀`: `P` is a bounded projection with `A P = P A = z₀ P`, a
  punctured neighbourhood of `z₀` lies in the resolvent set, and
  `z ↦ (z - A)⁻¹ - (z - z₀)⁻¹ P` has a limit at `z₀`. This is the restated
  `thm:evans-simple`(2) (R2: "Laurent form" of a simple isolated eigenvalue with Riesz
  projection `P`), the input of the deflation lemmas.

The exponential is Mathlib's `NormedSpace.exp` in the Banach algebra `X →L[ℂ] X`; the
time-`t` operator is `NormedSpace.exp ((t : ℂ) • A)`. Multiplication in `X →L[ℂ] X` is
composition. All lemmas in this file are fully proved.
-/

noncomputable section

open Filter Topology
open scoped Real

namespace NonUniqueEuler.Dunford

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The Dunford integral of `e^{tz}` on the circle `|z - c| = ρ`:
`(2πi)⁻¹ ∮ e^{tz} (z - A)⁻¹ dz`. -/
def expDunford (A : X →L[ℂ] X) (c : ℂ) (ρ : ℝ) (t : ℂ) : X →L[ℂ] X :=
  (2 * π * Complex.I)⁻¹ • ∮ z in C(c, ρ), Complex.exp (t * z) • resolvent A z

/-- The rank-one operator `x ↦ f(x) g`. -/
def rankOneProj (f : X →L[ℂ] ℂ) (g : X) : X →L[ℂ] X :=
  f.smulRight g

/-- The deflated operator `A - (z₀ - μ₀) P`. -/
def deflate (A P : X →L[ℂ] X) (z₀ μ₀ : ℂ) : X →L[ℂ] X :=
  A - (z₀ - μ₀) • P

/-- `P` is the spectral projection of a simple isolated eigenvalue `z₀` of `A`, in the Laurent
form of restructuring R2: `P² = P`, `A P = P A = z₀ P`, the punctured neighbourhoods of `z₀` are
in the resolvent set, and `(z - A)⁻¹ - (z - z₀)⁻¹ P` extends continuously to `z = z₀`. -/
structure IsSimpleSpectralProj (A P : X →L[ℂ] X) (z₀ : ℂ) : Prop where
  idem : P * P = P
  mul_proj : A * P = z₀ • P
  proj_mul : P * A = z₀ • P
  eventually_mem_resolventSet : ∀ᶠ z in 𝓝[≠] z₀, z ∈ resolventSet ℂ A
  laurent : ∃ R₀ : X →L[ℂ] X,
    Tendsto (fun z => resolvent A z - (z - z₀)⁻¹ • P) (𝓝[≠] z₀) (𝓝 R₀)

@[simp] theorem rankOneProj_apply (f : X →L[ℂ] ℂ) (g x : X) :
    rankOneProj f g x = f x • g :=
  rfl

/-- `x ↦ f(x) g` is a projection when `f g = 1`. -/
theorem rankOneProj_mul_self {f : X →L[ℂ] ℂ} {g : X} (h : f g = 1) :
    rankOneProj f g * rankOneProj f g = rankOneProj f g := by
  ext x
  simp [h]

/-- If `g` is an eigenvector of `A` with eigenvalue `μ`, then `A P = μ P`. -/
theorem mul_rankOneProj {A : X →L[ℂ] X} {f : X →L[ℂ] ℂ} {g : X} {μ : ℂ} (h : A g = μ • g) :
    A * rankOneProj f g = μ • rankOneProj f g := by
  ext x
  simp [h, smul_smul, mul_comm]

/-- If `f` is a left eigenvector of `A` with eigenvalue `μ`, then `P A = μ P`. -/
theorem rankOneProj_mul {A : X →L[ℂ] X} {f : X →L[ℂ] ℂ} {g : X} {μ : ℂ}
    (h : f.comp A = μ • f) : rankOneProj f g * A = μ • rankOneProj f g := by
  ext x
  have hx : f (A x) = μ * f x := by
    simpa using congrArg (fun T : X →L[ℂ] ℂ => T x) h
  simp [hx, smul_smul]

theorem deflate_apply (A P : X →L[ℂ] X) (z₀ μ₀ : ℂ) (x : X) :
    deflate A P z₀ μ₀ x = A x - (z₀ - μ₀) • P x :=
  rfl

end NonUniqueEuler.Dunford
