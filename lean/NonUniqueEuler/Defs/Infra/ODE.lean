import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Linear second-order ODEs `ψ'' = V ψ + F` (definitions; library I-ODE)

Manuscript-independent infrastructure (library I-ODE), shared by Part (1)
(Section 4: Evans function, resolvent, eigenfunctions) and Part (2) (Appendix A: validated
enclosures of the Evans function).

The equation `ψ'' = V(ξ) ψ + F(ξ)`, with complex coefficient `V : ℝ → ℂ` and forcing
`F : ℝ → ℂ`, is written as the first-order system for the pair `(ψ, ψ')`, with derivatives
*within* a set `s ⊆ ℝ` of the variable (one-sided at the endpoints of an interval). This is the
format of the statement layer's `IsEvansSolution` (`Statement/Evans.lean`): for
`s = Icc ξL ξR`, `IsEvansSolution χ ℓ z G ψ ψ'` is
`IsSolOn (fun ξ => riccatiCoeff χ ℓ z G ξ) (Icc ξL ξR) ψ ψ'` plus the two initial conditions.

* `IsSolOn V s ψ ψ'`: `(ψ, ψ')` solves `ψ'' = V ψ` on `s`;
* `IsInhomSolOn V F s ψ ψ'`: `(ψ, ψ')` solves `ψ'' = V ψ + F` on `s`;
* `sol V ξ₀ y₀ : ℝ → ℂ × ℂ`: the global solution `ξ ↦ (ψ ξ, ψ' ξ)` on `ℝ` with
  `(ψ, ψ')(ξ₀) = y₀`, chosen by `Classical.choose` (zero if there is none; it exists and is
  unique when `V` is continuous, `I/Infra/ODE/Existence.lean`, `I/Infra/ODE/Uniqueness.lean`);
* `wronskian ψ₁ ψ₁' ψ₂ ψ₂' ξ = ψ₁ ψ₂' - ψ₁' ψ₂` at `ξ`;
* `voc`, `voc'`: the variation-of-constants particular solution and its derivative.

The parameter-dependent theorems (continuity, holomorphy) apply to `fun p => sol (V · p) ξ₀ y₀`.
All lemmas in this file are fully proved.
-/

noncomputable section

open Set Filter Topology

namespace NonUniqueEuler.LinODE

/-- `(ψ, ψ')` solves the homogeneous equation `ψ'' = V ψ` on the set `s`, as a first-order
system with derivatives within `s`. -/
structure IsSolOn (V : ℝ → ℂ) (s : Set ℝ) (ψ ψ' : ℝ → ℂ) : Prop where
  hasDerivWithinAt : ∀ ξ ∈ s, HasDerivWithinAt ψ (ψ' ξ) s ξ
  hasDerivWithinAt' : ∀ ξ ∈ s, HasDerivWithinAt ψ' (V ξ * ψ ξ) s ξ

/-- `(ψ, ψ')` solves the inhomogeneous equation `ψ'' = V ψ + F` on the set `s`. -/
structure IsInhomSolOn (V F : ℝ → ℂ) (s : Set ℝ) (ψ ψ' : ℝ → ℂ) : Prop where
  hasDerivWithinAt : ∀ ξ ∈ s, HasDerivWithinAt ψ (ψ' ξ) s ξ
  hasDerivWithinAt' : ∀ ξ ∈ s, HasDerivWithinAt ψ' (V ξ * ψ ξ + F ξ) s ξ

/-- The global solution of `ψ'' = V ψ` on `ℝ` with `(ψ ξ₀, ψ' ξ₀) = y₀`, as the path
`ξ ↦ (ψ ξ, ψ' ξ)`; chosen by choice, `0` if there is none. -/
@[irreducible] def sol (V : ℝ → ℂ) (ξ₀ : ℝ) (y₀ : ℂ × ℂ) : ℝ → ℂ × ℂ :=
  open scoped Classical in
  if h : ∃ Y : ℝ → ℂ × ℂ, IsSolOn V univ (fun ξ => (Y ξ).1) (fun ξ => (Y ξ).2) ∧ Y ξ₀ = y₀
  then Classical.choose h else 0

/-- The Wronskian `W = ψ₁ ψ₂' - ψ₁' ψ₂`. -/
def wronskian (ψ₁ ψ₁' ψ₂ ψ₂' : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  ψ₁ ξ * ψ₂' ξ - ψ₁' ξ * ψ₂ ξ

/-- Variation of constants: for homogeneous solutions `ψ₁, ψ₂` with Wronskian `W`,
`W⁻¹ (ψ₂(ξ) ∫_c^ξ ψ₁ F - ψ₁(ξ) ∫_d^ξ ψ₂ F)` is a particular solution of `ψ'' = V ψ + F`.
The parentheses around the first integral are needed: the `∫ η in c..ξ,` binder extends to the
right. -/
def voc (ψ₁ ψ₂ F : ℝ → ℂ) (W : ℂ) (c d ξ : ℝ) : ℂ :=
  W⁻¹ * (ψ₂ ξ * (∫ η in c..ξ, ψ₁ η * F η) - ψ₁ ξ * ∫ η in d..ξ, ψ₂ η * F η)

/-- The derivative of `voc`: `W⁻¹ (ψ₂'(ξ) ∫_c^ξ ψ₁ F - ψ₁'(ξ) ∫_d^ξ ψ₂ F)`. -/
def voc' (ψ₁ ψ₁' ψ₂ ψ₂' F : ℝ → ℂ) (W : ℂ) (c d ξ : ℝ) : ℂ :=
  W⁻¹ * (ψ₂' ξ * (∫ η in c..ξ, ψ₁ η * F η) - ψ₁' ξ * ∫ η in d..ξ, ψ₂ η * F η)

variable {V F : ℝ → ℂ} {s t : Set ℝ} {ψ ψ' φ φ' : ℝ → ℂ}

theorem isInhomSolOn_zero_iff : IsInhomSolOn V 0 s ψ ψ' ↔ IsSolOn V s ψ ψ' := by
  constructor
  · intro h
    exact ⟨h.hasDerivWithinAt, fun ξ hξ => by simpa using h.hasDerivWithinAt' ξ hξ⟩
  · intro h
    exact ⟨h.hasDerivWithinAt, fun ξ hξ => by simpa using h.hasDerivWithinAt' ξ hξ⟩

namespace IsSolOn

theorem toInhom (h : IsSolOn V s ψ ψ') : IsInhomSolOn V 0 s ψ ψ' :=
  isInhomSolOn_zero_iff.2 h

theorem mono (h : IsSolOn V s ψ ψ') (hts : t ⊆ s) : IsSolOn V t ψ ψ' :=
  ⟨fun ξ hξ => (h.hasDerivWithinAt ξ (hts hξ)).mono hts,
    fun ξ hξ => (h.hasDerivWithinAt' ξ (hts hξ)).mono hts⟩

theorem continuousOn (h : IsSolOn V s ψ ψ') : ContinuousOn ψ s :=
  fun ξ hξ => (h.hasDerivWithinAt ξ hξ).continuousWithinAt

theorem continuousOn' (h : IsSolOn V s ψ ψ') : ContinuousOn ψ' s :=
  fun ξ hξ => (h.hasDerivWithinAt' ξ hξ).continuousWithinAt

theorem add (h : IsSolOn V s ψ ψ') (h' : IsSolOn V s φ φ') :
    IsSolOn V s (fun ξ => ψ ξ + φ ξ) (fun ξ => ψ' ξ + φ' ξ) :=
  ⟨fun ξ hξ => HasDerivWithinAt.add (h.hasDerivWithinAt ξ hξ) (h'.hasDerivWithinAt ξ hξ),
    fun ξ hξ => by
      have := HasDerivWithinAt.add (h.hasDerivWithinAt' ξ hξ) (h'.hasDerivWithinAt' ξ hξ)
      exact this.congr_deriv (by ring)⟩

theorem const_mul (h : IsSolOn V s ψ ψ') (c : ℂ) :
    IsSolOn V s (fun ξ => c * ψ ξ) (fun ξ => c * ψ' ξ) :=
  ⟨fun ξ hξ => (h.hasDerivWithinAt ξ hξ).const_mul c,
    fun ξ hξ => by
      have := (h.hasDerivWithinAt' ξ hξ).const_mul c
      simpa [mul_left_comm] using this⟩

theorem zero : IsSolOn V s (fun _ => 0) (fun _ => 0) :=
  ⟨fun _ _ => by simpa using hasDerivWithinAt_const _ _ (0 : ℂ),
    fun _ _ => by simpa using hasDerivWithinAt_const _ _ (0 : ℂ)⟩

end IsSolOn

namespace IsInhomSolOn

theorem mono (h : IsInhomSolOn V F s ψ ψ') (hts : t ⊆ s) : IsInhomSolOn V F t ψ ψ' :=
  ⟨fun ξ hξ => (h.hasDerivWithinAt ξ (hts hξ)).mono hts,
    fun ξ hξ => (h.hasDerivWithinAt' ξ (hts hξ)).mono hts⟩

theorem continuousOn (h : IsInhomSolOn V F s ψ ψ') : ContinuousOn ψ s :=
  fun ξ hξ => (h.hasDerivWithinAt ξ hξ).continuousWithinAt

theorem continuousOn' (h : IsInhomSolOn V F s ψ ψ') : ContinuousOn ψ' s :=
  fun ξ hξ => (h.hasDerivWithinAt' ξ hξ).continuousWithinAt

/-- The difference of two solutions with the same forcing solves the homogeneous equation. -/
theorem sub (h : IsInhomSolOn V F s ψ ψ') (h' : IsInhomSolOn V F s φ φ') :
    IsSolOn V s (fun ξ => ψ ξ - φ ξ) (fun ξ => ψ' ξ - φ' ξ) :=
  ⟨fun ξ hξ => HasDerivWithinAt.sub (h.hasDerivWithinAt ξ hξ) (h'.hasDerivWithinAt ξ hξ),
    fun ξ hξ => by
      have := HasDerivWithinAt.sub (h.hasDerivWithinAt' ξ hξ) (h'.hasDerivWithinAt' ξ hξ)
      exact this.congr_deriv (by ring)⟩

/-- Adding a homogeneous solution to an inhomogeneous one. -/
theorem add_isSolOn (h : IsInhomSolOn V F s ψ ψ') (h' : IsSolOn V s φ φ') :
    IsInhomSolOn V F s (fun ξ => ψ ξ + φ ξ) (fun ξ => ψ' ξ + φ' ξ) :=
  ⟨fun ξ hξ => HasDerivWithinAt.add (h.hasDerivWithinAt ξ hξ) (h'.hasDerivWithinAt ξ hξ),
    fun ξ hξ => by
      have := HasDerivWithinAt.add (h.hasDerivWithinAt' ξ hξ) (h'.hasDerivWithinAt' ξ hξ)
      exact this.congr_deriv (by ring)⟩

end IsInhomSolOn

/-- On `univ`, derivatives within the set are ordinary derivatives. -/
theorem isSolOn_univ_iff :
    IsSolOn V univ ψ ψ' ↔
      (∀ ξ, HasDerivAt ψ (ψ' ξ) ξ) ∧ ∀ ξ, HasDerivAt ψ' (V ξ * ψ ξ) ξ := by
  constructor
  · intro h
    exact ⟨fun ξ => (h.hasDerivWithinAt ξ (mem_univ ξ)).hasDerivAt Filter.univ_mem,
      fun ξ => (h.hasDerivWithinAt' ξ (mem_univ ξ)).hasDerivAt Filter.univ_mem⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨fun ξ _ => (h₁ ξ).hasDerivWithinAt, fun ξ _ => (h₂ ξ).hasDerivWithinAt⟩

/-- If some global solution with the given data exists, `sol` is one. -/
theorem sol_spec_of_exists {V : ℝ → ℂ} {ξ₀ : ℝ} {y₀ : ℂ × ℂ}
    (h : ∃ Y : ℝ → ℂ × ℂ, IsSolOn V univ (fun ξ => (Y ξ).1) (fun ξ => (Y ξ).2) ∧ Y ξ₀ = y₀) :
    IsSolOn V univ (fun ξ => (sol V ξ₀ y₀ ξ).1) (fun ξ => (sol V ξ₀ y₀ ξ).2) ∧
      sol V ξ₀ y₀ ξ₀ = y₀ := by
  classical
  rw [sol, dite_eq_left_of_eq_true (eq_true h)]
  exact Classical.choose_spec h

end NonUniqueEuler.LinODE
