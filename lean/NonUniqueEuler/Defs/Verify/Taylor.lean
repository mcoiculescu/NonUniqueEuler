import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Taylor coefficients (definitions)

Manuscript: the proof of Proposition A.3 (`prop:enclosure`, `A_verification.tex:340-345`):
"for `ξ ∈ ℝ` and a smooth function `F` we write `F_k(ξ) = F^{(k)}(ξ)/k!`".

* `AppA.taylorCoeff f k x = (k!)⁻¹ • f^{(k)}(x)` for `f : ℝ → F` (`F = ℝ` or `ℂ`, or any normed
  `ℝ`-space), with `iteratedDeriv` (derivatives on all of `ℝ`).
* `AppA.taylorPoly f N s h = Σ_{k < N} h^k • f_k(s)`, the Taylor polynomial of order `N` at `s`
  evaluated at the step `h`.

Only C^∞ calculus in `ξ` is used (no analyticity in `ξ`): Taylor's theorem with the Lagrange
remainder, applied to real and imaginary parts (interface `I/Verify/TaylorRemainder.lean`).
-/

noncomputable section

namespace NonUniqueEuler

namespace AppA

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The Taylor coefficient `f_k(x) = f^{(k)}(x) / k!`. -/
def taylorCoeff (f : ℝ → F) (k : ℕ) (x : ℝ) : F :=
  ((Nat.factorial k : ℝ)⁻¹) • iteratedDeriv k f x

/-- The Taylor polynomial `Σ_{k < N} h^k • f_k(s)`. -/
def taylorPoly (f : ℝ → F) (N : ℕ) (s h : ℝ) : F :=
  ∑ k ∈ Finset.range N, h ^ k • taylorCoeff f k s

theorem taylorCoeff_zero (f : ℝ → F) (x : ℝ) : taylorCoeff f 0 x = f x := by
  simp [taylorCoeff]

end AppA

end NonUniqueEuler
