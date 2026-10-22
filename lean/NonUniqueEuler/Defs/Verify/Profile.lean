import NonUniqueEuler.Statement.Evans
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Profile objects of Appendix A (definitions)

Manuscript: the notation at the start of Appendix A (`A_verification.tex:21-41`: `x_a`, `y_b`,
`G'_max = d`, `|Y|_w`), Lemma A.1 (`lem:end-regions`: `A`, `B`, `ε_end`, the comparison
solution `ψ₀`), Lemma A.2 (`lem:apriori`: `TV`, `Ω_max`), and the proof of Proposition A.3
(`A_verification.tex:346-370`: `Ā`, `B̄`, `q`, `g`).

All objects are stated with the statement-layer objects `H`, `prof χ`, `OmegaG`,
`riccatiCoeff` (namespace `NonUniqueEuler`, `NonUniqueEuler.RingData`). Everything is in the
namespace `NonUniqueEuler.AppA`.

| Lean | manuscript |
|---|---|
| `profA ξ = H((ξ - a₀)/d)`, `profAbar ξ = H((a₀ - ξ)/d)` | `A`, `Ā = 1 - A` |
| `profB ξ = H(-ξ/d)`, `profBbar ξ = H(ξ/d)` | `B`, `B̄ = 1 - B` |
| `profW = profA * profB` | `AB`; `prof χ = χ · AB` (`prof_eq_mul_profW`) |
| `profQ ξ = profW ξ · e^{2ξ}` | `q = ϖ e^{2ξ}` on `[ξa, ξb]` |
| `gInt χ ξ = ∫_{-∞}^ξ ϖ e^{2ξ'}` | `g`; `Ω_G = e^{-2ξ}(G + g)` (`OmegaG_eq`) |
| `xa`, `yb` | `x_a = (ξa - a₀)/d`, `y_b = -ξb/d` |
| `TV χ = ∫_ℝ |ϖ'|` | `TV` (Lemma A.2) |
| `OmegaMax = 1/2 + d e^{-2ξL}` | `Ω_max` (Lemma A.2, with `G'_max = d`) |
| `epsEnd z = 3e^{-50}/Re z` | `ε_end` (Lemma A.1(2)) |
| `evansDelta χ ℓ z G ξ = iℓϖ'/(λ + iℓΩ_G)` | `δ`; `V = ℓ² + δ` (`riccatiCoeff_eq_add_evansDelta`) |
| `wnorm ℓ u v = max(ℓ|u|, |v|)` | `|(u, v)|_w` |
| `cmpSol ℓ α u v`, `cmpSol' ℓ α u v` | `ψ₀`, `ψ₀'`: the solution of `ψ₀'' = ℓ²ψ₀`, `ψ₀(α) = u`, `ψ₀'(α) = v` |
| `endL = ξa - ξL`, `endR = ξR - ξb` | `L₁`, `L₂` (Proposition A.3 (ii), (iv)) |
-/

noncomputable section

open Set MeasureTheory

namespace NonUniqueEuler

namespace AppA

open RingData

/-- `A(ξ) = H((ξ - a₀)/d)`. -/
def profA (ξ : ℝ) : ℝ := H ((ξ - a₀) / d)

/-- `Ā(ξ) = H((a₀ - ξ)/d) = 1 - A(ξ)`. -/
def profAbar (ξ : ℝ) : ℝ := H ((a₀ - ξ) / d)

/-- `B(ξ) = H(-ξ/d)`. -/
def profB (ξ : ℝ) : ℝ := H (-ξ / d)

/-- `B̄(ξ) = H(ξ/d) = 1 - B(ξ)`. -/
def profBbar (ξ : ℝ) : ℝ := H (ξ / d)

/-- `w = AB`, the profile without the cutoff: `prof χ = χ · w`. -/
def profW (ξ : ℝ) : ℝ := profA ξ * profB ξ

/-- `q = w e^{2ξ}` (equal to `prof χ · e^{2ξ}` on `[ξa, ξb]`). -/
def profQ (ξ : ℝ) : ℝ := profW ξ * Real.exp (2 * ξ)

/-- `g(ξ) = ∫_{-∞}^ξ ϖ(ξ') e^{2ξ'} dξ'`, the integral in `Ω_G`. -/
def gInt (χ : ℝ → ℝ) (ξ : ℝ) : ℝ := ∫ t in Iic ξ, prof χ t * Real.exp (2 * t)

/-- `x_a = (ξa - a₀)/d`. -/
def xa : ℝ := (ξa - a₀) / d

/-- `y_b = -ξb/d`. -/
def yb : ℝ := -ξb / d

/-- `TV = ∫_ℝ |ϖ'|`, the total variation of the profile. -/
def TV (χ : ℝ → ℝ) : ℝ := ∫ ξ, |deriv (prof χ) ξ|

/-- `Ω_max = 1/2 + G'_max e^{-2ξL}`, with `G'_max = d`. -/
def OmegaMax : ℝ := 1 / 2 + d * Real.exp (-2 * ξL)

/-- `ε_end = 3e^{-50}/Re λ`. -/
def epsEnd (z : ℂ) : ℝ := 3 * Real.exp (-50) / z.re

/-- `L₁ = ξa - ξL`, the length of the left end region. -/
def endL : ℝ := ξa - ξL

/-- `L₂ = ξR - ξb`, the length of the right end region. -/
def endR : ℝ := ξR - ξb

/-- `δ = iℓϖ'/(λ + iℓΩ_G)`, so that the Evans equation is `ψ'' = (ℓ² + δ)ψ`. -/
def evansDelta (χ : ℝ → ℝ) (ℓ : ℕ) (z : ℂ) (G ξ : ℝ) : ℂ :=
  Complex.I * (ℓ : ℂ) * ((deriv (prof χ) ξ : ℝ) : ℂ) /
    (z + Complex.I * (ℓ : ℂ) * ((OmegaG χ G ξ : ℝ) : ℂ))

/-- The weighted norm `|(u, v)|_w = max(ℓ|u|, |v|)`. -/
def wnorm (ℓ : ℝ) (u v : ℂ) : ℝ := max (ℓ * ‖u‖) ‖v‖

/-- The comparison solution `ψ₀(ξ) = u cosh(ℓ(ξ-α)) + (v/ℓ) sinh(ℓ(ξ-α))` of `ψ₀'' = ℓ²ψ₀`,
`ψ₀(α) = u`, `ψ₀'(α) = v`. -/
def cmpSol (ℓ α : ℝ) (u v : ℂ) (ξ : ℝ) : ℂ :=
  u * ((Real.cosh (ℓ * (ξ - α)) : ℝ) : ℂ) + v / (ℓ : ℂ) * ((Real.sinh (ℓ * (ξ - α)) : ℝ) : ℂ)

/-- The derivative `ψ₀'(ξ) = uℓ sinh(ℓ(ξ-α)) + v cosh(ℓ(ξ-α))` of `cmpSol`. -/
def cmpSol' (ℓ α : ℝ) (u v : ℂ) (ξ : ℝ) : ℂ :=
  u * (ℓ : ℂ) * ((Real.sinh (ℓ * (ξ - α)) : ℝ) : ℂ) + v * ((Real.cosh (ℓ * (ξ - α)) : ℝ) : ℂ)

/-! ### Bridges to the statement layer (proved) -/

theorem prof_eq_mul_profW (χ : ℝ → ℝ) (ξ : ℝ) : prof χ ξ = χ ξ * profW ξ := by
  simp [prof, profW, profA, profB, mul_assoc]

theorem OmegaG_eq (χ : ℝ → ℝ) (G ξ : ℝ) :
    OmegaG χ G ξ = Real.exp (-2 * ξ) * (G + gInt χ ξ) := rfl

theorem riccatiCoeff_eq_add_evansDelta (χ : ℝ → ℝ) (ℓ : ℕ) (z : ℂ) (G ξ : ℝ) :
    riccatiCoeff χ ℓ z G ξ = (ℓ : ℂ) ^ 2 + evansDelta χ ℓ z G ξ := rfl

theorem cmpSol_self (ℓ α : ℝ) (u v : ℂ) : cmpSol ℓ α u v α = u := by
  simp [cmpSol]

theorem cmpSol'_self (ℓ α : ℝ) (u v : ℂ) : cmpSol' ℓ α u v α = v := by
  simp [cmpSol']

end AppA

end NonUniqueEuler
