import NonUniqueEuler.Defs.SmoothB.Iteration
import NonUniqueEuler.H.SmoothB.IterHs.Base
import NonUniqueEuler.H.SmoothB.IterHs.Step

/-!
# Proof of `lem:iter-Hs` (uniform `H^s` bounds on the iterates)

Proof of `I/SmoothB/IterHs.lean` (same declaration, same statement), following
`B_global_smooth.tex:315-349`: induction on `s`.

* Membership: every slice `ω^{[j]}(t)` is smooth with compact support
  (`IterHsH.memH_iter_slice`, from `lem:iterates`(i)).
* `s = 1`: `IterHsH.iter_Hs_one` (`H/SmoothB/IterHs/Base.lean`): `‖ω^{[j]}(t)‖_{L²} = ‖ω₀‖_{L²}`
  and `‖∇ω^{[j]}(t)‖²_{L²} ≤ π R(T)² Ψ(T)²`.
* `s - 1 → s` (`s ≥ 2`): `IterHsH.iter_Hs_step` (`H/SmoothB/IterHs/Step.lean`): the top-order
  energy `𝓗(t) = ∑_{|α| = s} ‖∂^α ω^{[j+1]}(t)‖²_{L²}` satisfies
  `|𝓗'| ≤ 𝓑_s(T)(𝓗 + 𝓜_{s-1}(T)² + 1)` on `[-T, T]` (commutator estimate `lem:comm-R2`, the
  transport term vanishing by `div v^{[j]} = 0`), and Grönwall gives the bound.

Helpers: `H/SmoothB/IterHs/{Slice, Energy, Gronwall, Base, Commutator, Step}.lean`.
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler.Smooth

variable {ω₀ : ℂ → ℝ} {R₀ : ℝ}

/-- `lem:iter-Hs`: for every integer `s ≥ 1`, `T > 0`, `j ≥ 0` and `|t| ≤ T`,
`ω^{[j]}(t) ∈ H^s` and `‖ω^{[j]}(t)‖_{H^s} ≤ 𝓜_s(T)`. -/
theorem iter_Hs (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) {s : ℕ} (hs : 1 ≤ s) {T : ℝ}
    (hT : 0 < T) (j : ℕ) {t : ℝ} (ht : |t| ≤ T) :
    Sob.MemH s (fun x => (iter ω₀ j t x : ℂ)) ∧
      Sob.normH s (fun x => (iter ω₀ j t x : ℂ)) ≤ calM ω₀ R₀ s T := by
  refine ⟨IterHsH.memH_iter_slice h hne s j t, ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, s = n + 1 := ⟨s - 1, by omega⟩
  clear hs
  induction n generalizing j t with
  | zero => exact IterHsH.iter_Hs_one h hne hT j ht
  | succ n ih => exact IterHsH.iter_Hs_step h hne n hT (fun i τ hτ => ih i hτ) j ht

end NonUniqueEuler.Smooth
