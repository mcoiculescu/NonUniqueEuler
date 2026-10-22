import NonUniqueEuler.Statement.Ring
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Statement layer: the Evans function and the numerical hypothesis (N1)–(N3)

Statement layer: definitions and statements only, no proofs.

Manuscript source: Hypothesis `hyp:N`, `04_ring.tex:1123-1151` (with `04_ring.tex:187-198`,
Definition `def:evans`, and `04_ring.tex:166-171`, the Riccati coefficient). The Python package
writes the same equation in the variable `s` on `[s_L, s_R]` with coefficient
`m² + i m ω_s / (λ + i m Ω_G)` (`euler-ring-certificate/docs/method.md`).

Everything here is stated purely mathematically, for an arbitrary admissible cutoff `χ`
(`A_verification.tex:26-28`: the verification holds for every such `χ`).

The Evans function. For an integer `ℓ ≥ 1`, `G ≥ 0` and `Re λ > 0`, `ψ = ψ_ℓ(·; λ, G)` is the
solution on `[ξ_L, ξ_R]` of `ψ'' = V ψ`, `ψ(ξ_L) = 1`, `ψ'(ξ_L) = ℓ`, with
`V(ξ) = ℓ² + i ℓ ϖ'(ξ) / (λ + i ℓ Ω_G(ξ))`, and `E_ℓ(λ; G) = e^{-ℓ(ξ_R - ξ_L)} (ψ'(ξ_R) + ℓ ψ(ξ_R))`.
We write the equation as a first-order system for the pair `(ψ, ψ')`, with one-sided
derivatives at the endpoints (`HasDerivWithinAt` on `[ξ_L, ξ_R]`), and define `E_ℓ` from a pair
chosen by `Classical.epsilon` among the solutions. For `Re λ > 0` the coefficient `V` is
continuous on `[ξ_L, ξ_R]` (`|λ + i ℓ Ω_G| ≥ Re λ`), so the solution exists and is unique, and
`E_ℓ(λ; G)` is the manuscript's number; the proof layer proves existence and uniqueness. The
hypothesis (N) only evaluates `E_3` at points with `Re λ ≥ 9/200 > 0` (and its complex
derivative there, which only involves values on the open half-plane `Re λ > 0`).

Multiplicity. (N1) says that `E_3(·; G)` has exactly one zero, counted with multiplicity, in
`{Re λ ≥ 9/200}`. Since `E_3(·; G)` is holomorphic on `{Re λ > 0}` (`lem:evans-basic`), this is
equivalent to: there is exactly one zero `λ₀` there, and `∂_λ E_3(λ₀; G) ≠ 0` (a simple zero).
We state it in this second form, which is also the form used in the proof
(`thm:evans-simple`(2), `04_ring.tex:462`).
-/

noncomputable section

open Set MeasureTheory

namespace NonUniqueEuler

open RingData

/-- `Ω_G(ξ) = e^{-2ξ} (G + ∫_{-∞}^ξ ϖ(ξ') e^{2ξ'} dξ')` (`04_ring.tex:1127-1129`). -/
def OmegaG (χ : ℝ → ℝ) (G ξ : ℝ) : ℝ :=
  Real.exp (-2 * ξ) * (G + ∫ ξ' in Iic ξ, prof χ ξ' * Real.exp (2 * ξ'))

/-- The coefficient `V_ℓ(ξ; λ, G) = ℓ² + i ℓ ϖ'(ξ) / (λ + i ℓ Ω_G(ξ))` (`04_ring.tex:1133`). -/
def riccatiCoeff (χ : ℝ → ℝ) (ℓ : ℕ) (z : ℂ) (G ξ : ℝ) : ℂ :=
  (ℓ : ℂ) ^ 2 + Complex.I * (ℓ : ℂ) * ((deriv (prof χ) ξ : ℝ) : ℂ) /
    (z + Complex.I * (ℓ : ℂ) * ((OmegaG χ G ξ : ℝ) : ℂ))

/-- `(ψ, ψ')` solves `ψ'' = V_ℓ(·; λ, G) ψ` on `[ξ_L, ξ_R]` with `ψ(ξ_L) = 1`, `ψ'(ξ_L) = ℓ`
(`04_ring.tex:1130-1135`), written as a first-order system with one-sided derivatives at the
endpoints. -/
structure IsEvansSolution (χ : ℝ → ℝ) (ℓ : ℕ) (z : ℂ) (G : ℝ) (ψ ψ' : ℝ → ℂ) : Prop where
  hasDerivWithinAt : ∀ ξ ∈ Icc ξL ξR, HasDerivWithinAt ψ (ψ' ξ) (Icc ξL ξR) ξ
  hasDerivWithinAt' : ∀ ξ ∈ Icc ξL ξR,
    HasDerivWithinAt ψ' (riccatiCoeff χ ℓ z G ξ * ψ ξ) (Icc ξL ξR) ξ
  init : ψ ξL = 1
  init' : ψ' ξL = (ℓ : ℂ)

/-- A solution pair `(ψ_ℓ, ψ_ℓ')`, chosen among the solutions (there is exactly one on
`[ξ_L, ξ_R]` when `Re λ > 0`). -/
def evansSolution (χ : ℝ → ℝ) (ℓ : ℕ) (z : ℂ) (G : ℝ) : (ℝ → ℂ) × (ℝ → ℂ) :=
  Classical.epsilon fun p : (ℝ → ℂ) × (ℝ → ℂ) => IsEvansSolution χ ℓ z G p.1 p.2

/-- **The Evans function** `E_ℓ(λ; G) = e^{-ℓ(ξ_R - ξ_L)} (ψ'(ξ_R) + ℓ ψ(ξ_R))`
(`04_ring.tex:1136-1139`). -/
def evans (χ : ℝ → ℝ) (ℓ : ℕ) (z : ℂ) (G : ℝ) : ℂ :=
  ((Real.exp (-(ℓ : ℝ) * (ξR - ξL)) : ℝ) : ℂ) *
    ((evansSolution χ ℓ z G).2 ξR + (ℓ : ℂ) * (evansSolution χ ℓ z G).1 ξR)

/-- `Θ_ℓ = π ℓ d / sin(π ℓ d)` (`04_ring.tex:1141`). -/
def Θ (ℓ : ℕ) : ℝ := Real.pi * ℓ * d / Real.sin (Real.pi * ℓ * d)

/-- `ε_* = max{H((ξ_a - a₀)/d), H(-ξ_b/d)}` (`04_ring.tex:1142`). -/
def εstar : ℝ := max (H ((ξa - a₀) / d)) (H (-ξb / d))

/-- (N1) (`04_ring.tex:1144-1146`): for every `G ∈ [0, 1/50]`, `E_3(·; G)` has exactly one zero,
counted with multiplicity, in the closed half-plane `{Re λ ≥ 9/200}`; stated as "exactly one
zero, and it is simple". -/
def N1 (χ : ℝ → ℝ) : Prop :=
  ∀ G ∈ Icc (0 : ℝ) (1 / 50), ∃ z₀ : ℂ,
    9 / 200 ≤ z₀.re ∧ evans χ 3 z₀ G = 0 ∧ deriv (fun z => evans χ 3 z G) z₀ ≠ 0 ∧
      ∀ z : ℂ, 9 / 200 ≤ z.re → evans χ 3 z G = 0 → z = z₀

/-- (N2) (`04_ring.tex:1147-1148`): for every `G ∈ [0, 1/50]`, `E_3(·; G)` has no zero in the
closed strip `{9/200 ≤ Re λ ≤ 211/2500}`. -/
def N2 (χ : ℝ → ℝ) : Prop :=
  ∀ G ∈ Icc (0 : ℝ) (1 / 50), ∀ z : ℂ,
    9 / 200 ≤ z.re → z.re ≤ 211 / 2500 → evans χ 3 z G ≠ 0

/-- (N3) (`04_ring.tex:1149`): for `ℓ ∈ {6, 9}`, `e^{ℓ a₀} Θ_ℓ + ε_* < 9/100`. -/
def N3 : Prop :=
  ∀ ℓ ∈ ({6, 9} : Set ℕ), Real.exp (ℓ * a₀) * Θ ℓ + εstar < 9 / 100

/-- **Hypothesis (N)** (`hyp:N`, `04_ring.tex:1123-1151`) for the admissible cutoff `χ`. -/
structure NumericalHypothesis (χ : ℝ → ℝ) : Prop where
  n1 : N1 χ
  n2 : N2 χ
  n3 : N3

end NonUniqueEuler
