import NonUniqueEuler.Statement.WeakSolution
import NonUniqueEuler.Defs.Infra.WeakL2
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Jointly measurable representatives of `L²`-valued paths (definitions; library I-JOINT)

Manuscript-independent infrastructure (library I-JOINT; restructuring R5).
Section 3 works with paths `u : τ → Lp ℝ 2 μ` (weakly continuous in time), while the statement
layer (`Statement/WeakSolution.lean`, decision D4) works with functions `ℝ → ℂ → ℝ` that are
measurable on the slab `(0, T) × ℂ`. This file fixes the bridge vocabulary:

* `IsJointRep U u s`: `U : τ → α → ℝ` is jointly measurable and `U t = u t` a.e. for **every**
  `t ∈ s` (not just almost every `t`);
* `jointRep u s`: such a representative chosen by `Classical.choose` (zero if none exists;
  `I/Infra/JointRep/Representative.lean` proves existence for strongly measurable and for weakly
  continuous paths);
* `toPath ω t`: the class in `L²(μ)` of the time slice `ω t` (zero when `ω t ∉ L²`), the
  converse bridge from functions to paths;
* `volume_restrict_slab`: the slab measure is the product of the restricted measures.

All lemmas here are fully proved.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace NonUniqueEuler.JointRep

variable {τ α : Type*} [MeasurableSpace τ] [MeasurableSpace α] {μ : Measure α}

/-- `U` is a jointly measurable representative of the path `u` at the times `t ∈ s`. -/
structure IsJointRep (U : τ → α → ℝ) (u : τ → Lp ℝ 2 μ) (s : Set τ) : Prop where
  measurable : Measurable (Function.uncurry U)
  ae_eq : ∀ t ∈ s, U t =ᵐ[μ] u t

/-- A jointly measurable representative of `u` on `s`, chosen by choice; `0` if there is none.
-/
@[irreducible] def jointRep (u : τ → Lp ℝ 2 μ) (s : Set τ) : τ → α → ℝ :=
  open scoped Classical in
  if h : ∃ U : τ → α → ℝ, IsJointRep U u s then Classical.choose h else 0

theorem jointRep_spec {u : τ → Lp ℝ 2 μ} {s : Set τ} (h : ∃ U : τ → α → ℝ, IsJointRep U u s) :
    IsJointRep (jointRep u s) u s := by
  classical
  rw [jointRep, dite_eq_left_of_eq_true (eq_true h)]
  exact Classical.choose_spec h

namespace IsJointRep

variable {U : τ → α → ℝ} {u : τ → Lp ℝ 2 μ} {s t : Set τ}

theorem mono (h : IsJointRep U u s) (hts : t ⊆ s) : IsJointRep U u t :=
  ⟨h.measurable, fun t' ht' => h.ae_eq t' (hts ht')⟩

/-- The time slices of a representative are measurable. -/
theorem measurable_slice (h : IsJointRep U u s) (t₀ : τ) : Measurable (U t₀) :=
  h.measurable.comp measurable_prodMk_left

/-- The time slices of a representative are in `L²` at the times of `s`. -/
theorem memLp (h : IsJointRep U u s) {t₀ : τ} (ht₀ : t₀ ∈ s) : MemLp (U t₀) 2 μ :=
  (Lp.memLp (u t₀)).ae_eq (h.ae_eq t₀ ht₀).symm

/-- The slice at `t₀ ∈ s`, turned back into an element of `L²`, is `u t₀`. -/
theorem toLp_eq (h : IsJointRep U u s) {t₀ : τ} (ht₀ : t₀ ∈ s) :
    (h.memLp ht₀).toLp (U t₀) = u t₀ := by
  rw [← Lp.toLp_coeFn (u t₀) (Lp.memLp (u t₀))]
  exact (MemLp.toLp_eq_toLp_iff _ _).2 (h.ae_eq t₀ ht₀)

end IsJointRep

/-- The path of `L²` classes of the time slices of `ω` (zero at the times where the slice is not
in `L²`). -/
@[irreducible] def toPath (ω : τ → α → ℝ) (t : τ) : Lp ℝ 2 μ :=
  open scoped Classical in
  if h : MemLp (ω t) 2 μ then h.toLp (ω t) else 0

omit [MeasurableSpace τ] in
theorem toPath_of_memLp {ω : τ → α → ℝ} {t : τ} (h : MemLp (ω t) 2 μ) :
    (toPath ω t : Lp ℝ 2 μ) = h.toLp (ω t) := by
  classical
  rw [toPath, dite_eq_left_of_eq_true (eq_true h)]

omit [MeasurableSpace τ] in
theorem coeFn_toPath {ω : τ → α → ℝ} {t : τ} (h : MemLp (ω t) 2 μ) :
    ((toPath ω t : Lp ℝ 2 μ) : α → ℝ) =ᵐ[μ] ω t := by
  rw [toPath_of_memLp h]
  exact h.coeFn_toLp

/-- The measure of the slab `(0, T) × ℂ` is the product of the restricted measures. -/
theorem volume_restrict_slab (T : ℝ) :
    (volume : Measure (ℝ × ℂ)).restrict (slab T) =
      (volume.restrict (Ioo (0 : ℝ) T)).prod (volume : Measure ℂ) := by
  rw [slab, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

end NonUniqueEuler.JointRep
