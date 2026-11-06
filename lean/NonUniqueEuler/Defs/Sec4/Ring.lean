import NonUniqueEuler.Statement.Evans
import NonUniqueEuler.Defs.Infra.SectorSpace

/-!
# Part I Section 4.1: the ring — annuli and closed-form quantities (definitions)

Manuscript `manuscript/part1/sections/04_ring.tex`.

The data of Part I Definition 4.1 (`def:ring`) are in the statement layer
(`Statement/Ring.lean`, namespace `NonUniqueEuler.RingData`): `a₀ d ξL ξa ξb ξR`, `H`,
`IsAdmissibleCutoff`, `prof` (`ϖ`), `ringRef` (`ω̄_c`), `Rc`, `ringPhi` (`Φ`), `a`, `Gmax`, and
`Gbar`, which is the manuscript's `G₁ = (1/50) R_c⁻²` (Part I Definition 4.1 (`def:ring`); the statement layer
writes it `Ḡ`). `Θ ℓ` and `εstar` (`ε_*`) are in `Statement/Evans.lean`. They are not redefined.

This file adds, in the same namespace `NonUniqueEuler.RingData`:
* the closed annuli of ring units (Part II Section 1.4 (`sec:II-prelim`), before Lemma 1.4 (`lem:annuli`)), as `Sect.closedAnnulus`:
  `ringAnn = {a ≤ |y| ≤ 1}`, `annNm = 𝒩_-`, `annNn = 𝒩`, `annNflat = N♭`, `annN = N`,
  `annN' = N'`;
* the annulus `N_* = {½e^{ξL} ≤ |x| ≤ 2e^{ξR}}` of the ring in reference units
  (`annRef`, Part I Lemma 4.6 (`lem:evans-basic`), the two mode settings preceding Part I Equation 13 (`eq:evans-units`));
* `ξc = a₀/2` and the two factors `Z^a_ℓ`, `Z^b_ℓ` of `lem:closed-form`(2)
  (Part I Lemma 4.11 (`lem:closed-form`)).

All lemmas here are fully proved.
-/

noncomputable section

open Set MeasureTheory

namespace NonUniqueEuler

namespace RingData

open Sect

/-! ### The annuli of ring units (Part II Section 1.4 (`sec:II-prelim`), before Lemma 1.4 (`lem:annuli`)) -/

/-- `{a ≤ |y| ≤ 1}`, which contains `supp Φ` (Part I Lemma 4.2 (`lem:ring-facts`)). -/
def ringAnn : Set ℂ := closedAnnulus a 1

/-- `𝒩_- = {⅞a ≤ |y| ≤ 5/4}` (Part II Section 1.4 (`sec:II-prelim`), before Lemma 1.4 (`lem:annuli`), `\NNm`). -/
def annNm : Set ℂ := closedAnnulus (7 / 8 * a) (5 / 4)

/-- `𝒩 = {¾a ≤ |y| ≤ 3/2}` (Part II Section 1.4 (`sec:II-prelim`), before Lemma 1.4 (`lem:annuli`), `\NN`). -/
def annNn : Set ℂ := closedAnnulus (3 / 4 * a) (3 / 2)

/-- `N♭ = {⅝a ≤ |y| ≤ 7/4}` (Part II Section 1.4 (`sec:II-prelim`), before Lemma 1.4 (`lem:annuli`), `\Nflat`). -/
def annNflat : Set ℂ := closedAnnulus (5 / 8 * a) (7 / 4)

/-- `N = {a/2 ≤ |y| ≤ 2}` (Part I Section 4.1 (`sec:ring-def`), after Part I Lemma 4.2 (`lem:ring-facts`)). This is the annulus `N_*` of the sector setting of
`Φ` in ring units (the two mode settings preceding Part I Equation 13 (`eq:evans-units`)), and `X^s` consists of functions supported in it
(the ring-unit spaces and operator preceding Part I Proposition 4.19 (`prop:SU`)). -/
def annN : Set ℂ := closedAnnulus (a / 2) 2

/-- `N' = {a/4 ≤ |y| ≤ 3}` (Part I Section 4.1 (`sec:ring-def`), after Part I Lemma 4.2 (`lem:ring-facts`)). -/
def annN' : Set ℂ := closedAnnulus (a / 4) 3

/-- The annulus `N_* = {½e^{ξL} ≤ |x| ≤ 2e^{ξR}}` of the sector setting of the ring in reference
units (Part I Lemma 4.6 (`lem:evans-basic`), the two mode settings preceding Part I Equation 13 (`eq:evans-units`)). -/
def annRef : Set ℂ := closedAnnulus (Real.exp ξL / 2) (2 * Real.exp ξR)

/-! ### Part I Lemma 4.11 (`lem:closed-form`) -/

/-- `ξ_c = a₀/2` (Part I Lemma 4.11 (`lem:closed-form`)), the point where `ϖ'` changes sign (`lem:closed-form`(1)). -/
def ξc : ℝ := a₀ / 2

/-- `Z^a_ℓ = ∫_{\{ϖ' > 0\}} e^{2ℓ(ξ - a₀/2)} ϖ'(ξ) dξ` (Part I Lemma 4.11 (`lem:closed-form`)). -/
def ZedgeA (χ : ℝ → ℝ) (ℓ : ℕ) : ℝ :=
  ∫ ξ in {ξ : ℝ | 0 < deriv (prof χ) ξ}, Real.exp (2 * ℓ * (ξ - ξc)) * deriv (prof χ) ξ

/-- `Z^b_ℓ = ∫_{\{ϖ' < 0\}} e^{-2ℓ(ξ - a₀/2)} |ϖ'(ξ)| dξ` (Part I Lemma 4.11 (`lem:closed-form`)). -/
def ZedgeB (χ : ℝ → ℝ) (ℓ : ℕ) : ℝ :=
  ∫ ξ in {ξ : ℝ | deriv (prof χ) ξ < 0}, Real.exp (-(2 * ℓ * (ξ - ξc))) * |deriv (prof χ) ξ|

/-! ### Basic lemmas (fully proved) -/

theorem isRotInvariant_annN : IsRotInvariant annN := isRotInvariant_closedAnnulus _ _

theorem isRotInvariant_annRef : IsRotInvariant annRef := isRotInvariant_closedAnnulus _ _

theorem isCompact_annN : IsCompact annN := isCompact_closedAnnulus _ _

theorem isCompact_annN' : IsCompact annN' := isCompact_closedAnnulus _ _

theorem mem_annN {y : ℂ} : y ∈ annN ↔ a / 2 ≤ ‖y‖ ∧ ‖y‖ ≤ 2 := Iff.rfl

theorem mem_annN' {y : ℂ} : y ∈ annN' ↔ a / 4 ≤ ‖y‖ ∧ ‖y‖ ≤ 3 := Iff.rfl

theorem mem_ringAnn {y : ℂ} : y ∈ ringAnn ↔ a ≤ ‖y‖ ∧ ‖y‖ ≤ 1 := Iff.rfl

theorem mem_annNm {y : ℂ} : y ∈ annNm ↔ 7 / 8 * a ≤ ‖y‖ ∧ ‖y‖ ≤ 5 / 4 := Iff.rfl

theorem mem_annNn {y : ℂ} : y ∈ annNn ↔ 3 / 4 * a ≤ ‖y‖ ∧ ‖y‖ ≤ 3 / 2 := Iff.rfl

theorem mem_annNflat {y : ℂ} : y ∈ annNflat ↔ 5 / 8 * a ≤ ‖y‖ ∧ ‖y‖ ≤ 7 / 4 := Iff.rfl

end RingData

end NonUniqueEuler
