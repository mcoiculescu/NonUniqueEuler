import NonUniqueEuler.Statement.WeakSolution
import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Equimeasurability (definitions; library I-EQM)

Manuscript-independent infrastructure (library I-EQM). The notion itself,
`NonUniqueEuler.Equimeasurable g h` (Part I, Definition 2.4, `def:equimeasurable`: `g, h ∈ L¹`
and `|{g > s}| = |{h > s}|`, `|{g < -s}| = |{h < -s}|` for all `s > 0`), is in the statement layer
(`Statement/WeakSolution.lean`).

Definition.
* `IsLipO β`: `β : ℝ → ℝ` is Lipschitz and `β 0 = 0`; the manuscript's class `Lip₀`
  (Part I, Section 2.1, conventions in `sec:prelim`), used in Part I, Lemmas 3.4 (`lem:transport`) and 3.5
  (`lem:renorm-all-t`), Equation (9) (`eq:conservation`). The former separate
  `lem:lip-renorm` is retained in the Lean decomposition.

Fully proved basic lemmas: `Equimeasurable.refl`, `Equimeasurable.symm`,
`Equimeasurable.trans`, `Equimeasurable.memLp_one_left/right`, `IsLipO.comp`, `isLipO_id`,
`isLipO_abs`.

The theorems are stated in `NonUniqueEuler/I/Infra/Equimeasurable/*.lean`.
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler

namespace Equimeas

/-- The manuscript's class `Lip₀` (Part I, Section 2.1, conventions in `sec:prelim`): Lipschitz `β : ℝ → ℝ` with `β 0 = 0`. -/
def IsLipO (β : ℝ → ℝ) : Prop :=
  (∃ K : NNReal, LipschitzWith K β) ∧ β 0 = 0

theorem IsLipO.comp {β γ : ℝ → ℝ} (hβ : IsLipO β) (hγ : IsLipO γ) : IsLipO (β ∘ γ) := by
  obtain ⟨⟨K, hK⟩, h0⟩ := hβ
  obtain ⟨⟨L, hL⟩, h0'⟩ := hγ
  exact ⟨⟨K * L, hK.comp hL⟩, by simp [h0', h0]⟩

theorem isLipO_id : IsLipO id := ⟨⟨1, LipschitzWith.id⟩, rfl⟩

theorem isLipO_abs : IsLipO (fun s : ℝ => |s|) :=
  ⟨⟨1, LipschitzWith.of_dist_le_mul fun a b => by
    simpa [Real.dist_eq] using abs_abs_sub_abs_le_abs_sub a b⟩, abs_zero⟩

end Equimeas

namespace Equimeasurable

theorem memLp_one_left {g h : ℂ → ℝ} (H : Equimeasurable g h) : MemLp g 1 := H.1

theorem memLp_one_right {g h : ℂ → ℝ} (H : Equimeasurable g h) : MemLp h 1 := H.2.1

theorem refl {g : ℂ → ℝ} (hg : MemLp g 1) : Equimeasurable g g :=
  ⟨hg, hg, fun _ _ => ⟨rfl, rfl⟩⟩

theorem symm {g h : ℂ → ℝ} (H : Equimeasurable g h) : Equimeasurable h g :=
  ⟨H.2.1, H.1, fun s hs => ⟨(H.2.2 s hs).1.symm, (H.2.2 s hs).2.symm⟩⟩

theorem trans {g h k : ℂ → ℝ} (H₁ : Equimeasurable g h) (H₂ : Equimeasurable h k) :
    Equimeasurable g k :=
  ⟨H₁.1, H₂.2.1, fun s hs =>
    ⟨(H₁.2.2 s hs).1.trans (H₂.2.2 s hs).1, (H₁.2.2 s hs).2.trans (H₂.2.2 s hs).2⟩⟩

end Equimeasurable

end NonUniqueEuler
