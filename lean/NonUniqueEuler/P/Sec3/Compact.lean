import NonUniqueEuler.Defs.Sec3.Compact
import NonUniqueEuler.H.Sec3.Compact.Extract
import NonUniqueEuler.H.Sec3.Compact.Limit
import NonUniqueEuler.H.Sec3.Compact.Velocity
import NonUniqueEuler.H.Sec3.Compact.Identity

/-!
# Proof: `prop:compact`, compactness of weak solutions with bounded `L¹ ∩ L²` norms

Proof of `I/Sec3/Compact.lean` (`03_compactness.tex:251-340`). Same declaration, same statement.

The steps are in the helper files `H/Sec3/Compact/*.lean` (namespace
`NonUniqueEuler.Compact.PropCompact`):

1. `exists_subseq_weakLimit` (`Extract.lean`): `lem:weak-cont`(b) and `lem:velocity`(a) make
   `t ↦ ∫ ωₙ(t) ψ` uniformly Lipschitz for `ψ` in the test family; weak Arzelà–Ascoli
   (I-WEAKL2) gives a subsequence and a weakly continuous limit path `U` in `L²`.
2. `exists_limit_of_path` (`Limit.lean`): a jointly measurable representative `ω` of `U`
   (I-JOINT); weak continuity, (i), (ii) and `‖ω(t)‖_{L¹∩L²} ≤ M` (weak lower semicontinuity);
   `memX_of_bound`: `ω ∈ X₂(T)`.
3. `velocity_tendsto_bochner` (`Velocity.lean`): (iii), from `lem:velocity`(b) at each time and
   dominated convergence in `t`.
4. `isWeakSolution_limit` (`Identity.lean`): passage to the limit in `(eq:weak)`.

The bound `M` is first replaced by `max M 0` (`seq_max_zero`), which changes neither the
hypotheses nor the conclusion (`ofReal_max_zero`).
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace NonUniqueEuler.Compact

open Weak

/-- **`prop:compact`** (`03_compactness.tex:251-271`): under the hypotheses `IsCompactSeq T M gs g
ωs`, there are a subsequence `φ` and a weak solution `ω` in `X₂(T)` with datum `g`, weakly
continuous into `L²` on `[0, T]`, such that (i)–(iii) of `IsCompactLimit` hold for `ωs ∘ φ`, and
`sup_{t ∈ [0,T]} ‖ω(t)‖_{L¹∩L²} ≤ M` (the "in particular" of (ii)). -/
theorem compact {T M : ℝ} {gs : ℕ → ℂ → ℝ} {g : ℂ → ℝ} {ωs : ℕ → ℝ → ℂ → ℝ}
    (h : IsCompactSeq T M gs g ωs) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ω : ℝ → ℂ → ℝ,
      IsCompactLimit T g (fun n => ωs (φ n)) ω ∧
      ∀ t ∈ Icc 0 T, normL1LpE 2 (ω t) ≤ ENNReal.ofReal M := by
  have h' := PropCompact.seq_max_zero h
  have hM : (0 : ℝ) ≤ max M 0 := le_max_right _ _
  obtain ⟨φ, hφ, U, -, hUc, hconv⟩ := PropCompact.exists_subseq_weakLimit h' hM
  have hs := h'.subseq hφ
  obtain ⟨ω, hωm, hωc, hi, hii, hωb⟩ := PropCompact.exists_limit_of_path hs hUc hconv
  have hω2 : ∀ t ∈ Icc 0 T, MemLp (ω t) 2 volume := hωc.memLp
  have hX := PropCompact.memX_of_bound hM hωm hω2 hωb
  refine ⟨φ, hφ, ω, ⟨PropCompact.isWeakSolution_limit hs hM hX hi hω2 hωb, hωc, hi, hii,
    PropCompact.velocity_tendsto_bochner hs hM hi hω2 hωb⟩, fun t ht => ?_⟩
  rw [← PropCompact.ofReal_max_zero M]
  exact hωb t ht

end NonUniqueEuler.Compact
