import NonUniqueEuler.Defs.Sec4.Setting

/-!
# Part I Section 4.2: profile-level predicates for `lem:sector` (extra definitions)

Manuscript
Part I Definition 4.3 (`def:sector-setting`) (the set `Y^0_ℓ`) and `lem:sector`(1) (Part I Lemma 4.5 (`lem:sector`), proof
Part I Lemma 4.5 (`lem:sector`)).

* `S.IsProfileL2 g`: the radial profile `g` lies in `Y^0_ℓ` *as a set*: `g ∈ L²([ρ₋, ρ₊])` and
  `g = 0` a.e. on `(0, ∞) \ [ρ₋, ρ₊]` (Part I Definition 4.3 (`def:sector-setting`): "as a set,
  `Y^0_ℓ = L²([ρ₋,ρ₊], r dr)`"; since `0 < ρ₋`, the weight `r` does not change the space).
  The set does not depend on `ℓ`.
* `IsRadialPoissonSol ℓ g ψ`: `ψ` solves `ψ'' + ψ'/r - ℓ²ψ/r² = g` on `(0, ∞)` in the sense
  of the proof of `lem:sector`(1) (Part I Lemma 4.5 (`lem:sector`): `ψ ∈ C¹` with `ψ'` absolutely
  continuous, the equation almost everywhere), written in the equivalent integrated form
  `ψ'(b) - ψ'(a) = ∫_a^b (g - ψ'/r + ℓ²ψ/r²) dr` for all `a, b > 0`, with `ψ'` continuous on
  `(0, ∞)` (so the integrand is locally integrable whenever `g` is, and no junk value of the
  interval integral can enter).

Nothing here is a manuscript statement; there are no lemmas.
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler

namespace SectorSetting

/-- `g ∈ Y^0_ℓ` as a set of radial profiles (Part I Definition 4.3 (`def:sector-setting`)): `g ∈ L²([ρ₋, ρ₊])` and `g`
vanishes almost everywhere on `(0, ∞) \ [ρ₋, ρ₊]`. -/
def IsProfileL2 (S : SectorSetting) (g : ℝ → ℂ) : Prop :=
  MemLp g 2 (volume.restrict (Icc S.ρm S.ρp)) ∧
    ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), r ∉ Icc S.ρm S.ρp → g r = 0

/-- `ψ` solves the radial Poisson equation `ψ'' + ψ'/r - ℓ²ψ/r² = g` on `(0, ∞)`
(Part I Lemma 4.5(1) (`lem:sector`)), in integrated form: `ψ` is differentiable on `(0,∞)`
with a continuous derivative `ψ'`, and `ψ'(b) - ψ'(a) = ∫_a^b (g - ψ'/r + ℓ²ψ/r²) dr`. -/
def IsRadialPoissonSol (ℓ : ℤ) (g ψ : ℝ → ℂ) : Prop :=
  ∃ ψ' : ℝ → ℂ, (∀ r : ℝ, 0 < r → HasDerivAt ψ (ψ' r) r) ∧ ContinuousOn ψ' (Ioi 0) ∧
    ∀ a b : ℝ, 0 < a → 0 < b →
      ψ' b - ψ' a =
        ∫ r in a..b, (g r - ψ' r / (r : ℂ) + (ℓ : ℂ) ^ 2 * ψ r / (r : ℂ) ^ 2)

end SectorSetting

end NonUniqueEuler
