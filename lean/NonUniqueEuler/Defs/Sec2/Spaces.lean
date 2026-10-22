import NonUniqueEuler.Statement.WeakSolution
import Mathlib.Data.Real.ConjExponents

/-!
# Section 2 conventions: spaces of functions of `(t, x)`

Definitions for the convention on Bochner spaces of `02_prelim.tex:101-120`.

The manuscript identifies elements of `L^∞(I; L^b(Ω))` and `L¹(I; L^b(Ω))` with measurable
functions on `I × Ω`, and (for `b < ∞`) characterizes membership by essential boundedness,
respectively integrability, of `t ↦ ‖u(t)‖_{L^b(Ω)}` (Pettis). We take this characterization as
the definition (decision D4; the same choice as `MemX` of the statement layer), for functions
`u : ℝ → ℂ → E` (time first, D3) with values in a normed group `E` (real scalars, or vector fields
in `ℂ`).

* `MemLinfLp I Ω b u`: `u ∈ L^∞(I; L^b(Ω))`;
* `MemL1Lp I Ω b u`: `u ∈ L¹(I; L^b(Ω))`;
* `MemL1AddLinf v`: `v ∈ L¹ + L^∞(ℝ²)` (`lem:velocity`(a));
* `WeakTendstoLp p ωs ω`: `ωₙ ⇀ ω` weakly in `L^p(ℝ²)`, `1 < p < ∞`, tested against `L^{p'}`
  (`lem:velocity`(b)). For `p = 2` the type-level `WeakL2.WeakTendsto` of I-WEAKL2 is the
  Hilbert-space form (bridge `WeakL2.weakTendsto_toLp_iff`).

For `b = ∞` the manuscript writes `L^∞(I; L^∞(Ω))` for `L^∞(I × Ω)` and defines
`L¹(I; L^∞(Ω))` by `∫_I ‖u(t)‖_{L^∞(Ω)} dt < ∞`; the slice-wise definitions below are used for
every `b`. For `b = ∞` and `L^∞`, they agree with `u ∈ L^∞(I × Ω)` for a.e.-measurable `u`
(Tonelli applied to `{|u| > M}`); this equivalence is not needed and is not
proved here. Intersections (`L^∞(I; L¹ ∩ L^q)`) are conjunctions. The `W^{1,a}` and `loc`
variants of `02_prelim.tex:112-116` are not defined (restructuring R7: Section 3 uses exponent 2
and explicit approximations instead).

`memX_iff` relates the statement layer's `MemX q T` (`X_q(T) = L^∞(0,T; L¹ ∩ L^q)`) to these
predicates. All lemmas in this file are fully proved.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace NonUniqueEuler.Prelim

variable {E : Type*} [NormedAddCommGroup E]

/-- `u ∈ L^∞(I; L^b(Ω))` (`02_prelim.tex:101-120`): `u` is a.e. strongly measurable on `I × Ω`,
and for a.e. `t ∈ I`, `u(t) ∈ L^b(Ω)` with `‖u(t)‖_{L^b(Ω)} ≤ M` for one constant `M`. -/
structure MemLinfLp (I : Set ℝ) (Ω : Set ℂ) (b : ℝ≥0∞) (u : ℝ → ℂ → E) : Prop where
  aestronglyMeasurable : AEStronglyMeasurable (Function.uncurry u) (volume.restrict (I ×ˢ Ω))
  essBounded : ∃ M : ℝ, ∀ᵐ t ∂(volume.restrict I),
    MemLp (u t) b (volume.restrict Ω) ∧ (eLpNorm (u t) b (volume.restrict Ω)).toReal ≤ M

/-- `u ∈ L¹(I; L^b(Ω))` (`02_prelim.tex:101-120`): `u` is a.e. strongly measurable on `I × Ω`,
`u(t) ∈ L^b(Ω)` for a.e. `t ∈ I`, and `t ↦ ‖u(t)‖_{L^b(Ω)}` is integrable on `I`. -/
structure MemL1Lp (I : Set ℝ) (Ω : Set ℂ) (b : ℝ≥0∞) (u : ℝ → ℂ → E) : Prop where
  aestronglyMeasurable : AEStronglyMeasurable (Function.uncurry u) (volume.restrict (I ×ˢ Ω))
  memLp : ∀ᵐ t ∂(volume.restrict I), MemLp (u t) b (volume.restrict Ω)
  integrable : Integrable (fun t => (eLpNorm (u t) b (volume.restrict Ω)).toReal)
    (volume.restrict I)

/-- `v ∈ L¹ + L^∞(ℝ²)` (`lem:velocity`(a), `02_prelim.tex:312`): `v = v₁ + v₂` a.e. with
`v₁ ∈ L¹`, `v₂ ∈ L^∞`. -/
def MemL1AddLinf (v : ℂ → E) : Prop :=
  ∃ v₁ v₂ : ℂ → E, MemLp v₁ 1 volume ∧ MemLp v₂ ⊤ volume ∧ v =ᵐ[volume] v₁ + v₂

/-- `ωₙ ⇀ ω` weakly in `L^p(ℝ²)` (`lem:velocity`(b), `02_prelim.tex:316-318`), for real
functions and `1 < p < ∞`: all `ωₙ` and `ω` lie in `L^p`, and `∫ ωₙ φ → ∫ ω φ` for every
`φ ∈ L^{p'}`, `p' = p/(p-1)` (the dual of `L^p`). -/
def WeakTendstoLp (p : ℝ) (ωs : ℕ → ℂ → ℝ) (ω : ℂ → ℝ) : Prop :=
  (∀ n, MemLp (ωs n) (ENNReal.ofReal p) volume) ∧ MemLp ω (ENNReal.ofReal p) volume ∧
    ∀ φ : ℂ → ℝ, MemLp φ (ENNReal.ofReal p.conjExponent) volume →
      Filter.Tendsto (fun n => ∫ x, ωs n x * φ x) Filter.atTop (nhds (∫ x, ω x * φ x))

/-! ### Basic lemmas (fully proved) -/

theorem MemLinfLp.mono_set {I I' : Set ℝ} {Ω : Set ℂ} {b : ℝ≥0∞} {u : ℝ → ℂ → E}
    (h : MemLinfLp I Ω b u) (hI : I' ⊆ I) : MemLinfLp I' Ω b u := by
  refine ⟨h.aestronglyMeasurable.mono_measure
    (Measure.restrict_mono (prod_mono hI subset_rfl) le_rfl), ?_⟩
  obtain ⟨M, hM⟩ := h.essBounded
  exact ⟨M, ae_restrict_of_ae_restrict_of_subset hI hM⟩

/-- `X_q(T) = L^∞(0,T; L¹ ∩ L^q(ℝ²))`: the statement layer's `MemX q T` is the conjunction of
`L^∞(0,T; L¹)` and `L^∞(0,T; L^q)` (`02_prelim.tex:122-124`). -/
theorem memX_iff {q T : ℝ} {ω : ℝ → ℂ → ℝ} :
    MemX q T ω ↔ MemLinfLp (Ioo 0 T) univ 1 ω ∧ MemLinfLp (Ioo 0 T) univ (ENNReal.ofReal q) ω := by
  constructor
  · rintro ⟨hm, M, hM⟩
    refine ⟨⟨hm, M, hM.mono fun t ht => ?_⟩, ⟨hm, M, hM.mono fun t ht => ?_⟩⟩
    · rw [Measure.restrict_univ]
      exact ⟨ht.1, le_trans (le_add_of_nonneg_right ENNReal.toReal_nonneg) ht.2.2⟩
    · rw [Measure.restrict_univ]
      exact ⟨ht.2.1, le_trans (le_add_of_nonneg_left ENNReal.toReal_nonneg) ht.2.2⟩
  · rintro ⟨⟨hm, M₁, h₁⟩, ⟨_, M₂, h₂⟩⟩
    refine ⟨hm, M₁ + M₂, (h₁.and h₂).mono fun t ht => ?_⟩
    rw [Measure.restrict_univ] at ht
    exact ⟨ht.1.1, ht.2.1, add_le_add ht.1.2 ht.2.2⟩

end NonUniqueEuler.Prelim
