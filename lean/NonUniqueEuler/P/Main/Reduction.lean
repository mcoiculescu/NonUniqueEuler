import NonUniqueEuler.Statement.MainTheorem
import NonUniqueEuler.I.Sec10.Nonempty
import NonUniqueEuler.I.Sec11.MainExplicit
import NonUniqueEuler.I.Sec6.Integrability

/-!
# Proof: the conditional reduction

Proof of `I/Main/Reduction.lean`: Part II, Proposition 1.2 (`prop:reduction`),
proved in Section 8 (`sec:bootstrap`, `manuscript/part2/sections/11_bootstrap.tex`).
For every admissible cutoff `χ`, Hypothesis (N) for `χ` implies `MainTheorem χ`,
including the explicit clauses retained in the Lean statement.

The Lean proof retains the following decomposition of the current reduction proof:
1. by Part II, Lemma 7.1 (`lem:nonempty`) (`Relay.nonempty`, `I/Sec10/Nonempty.lean`) and its proved corollary
   `Relay.Params.exists_lists_of` (`Defs/Sec10/Params.lean`), there are parameters `p` with
   cutoff `χ` satisfying (P0)–(P6) (Part II, Definitions C.2–C.4, `def:P0-P4`, `def:P5`, `def:P6`);
2. by Part II, Proposition 3.2 (`prop:integrability`) (`Datum.integrability`, `I/Sec6/Integrability.lean`), the datum `f` is
   radial, nonnegative, in every `L^q`, `q ∈ [1, ∞)`, and not in `L^∞` (also used at the start of the current reduction proof);
3. by the retained explicit theorem (`Relay.main_explicit`, `I/Sec11/MainExplicit.lean`),
   its conclusions hold for every `A₁ > 0`; the former `thm:main-explicit` now lies
   within the proof of Part II, Proposition 1.2, rather than being a separate theorem;
4. the logical assembly (`μ`, `s̄` fixed before `A₁`; `T* = T_*`; "for every `T > T*`" from
   (ii) since `t₀ < T_*`) is the proved lemma `Relay.Params.mainTheorem_of`
   (`Defs/Sec11/Explicit.lean`).
-/

namespace NonUniqueEuler

open Relay

theorem main_theorem_of_N : ConditionalTheorem := by
  intro χ hχ hN
  obtain ⟨p, rfl, hL⟩ := Params.exists_lists_of (nonempty χ hχ hN)
  exact Params.mainTheorem_of hL
    (fun A₁ hA₁ => (Datum.integrability p.χ hχ (hL.datumParams hA₁)).1)
    (fun A₁ hA₁ => main_explicit p hχ hN hL hA₁)

end NonUniqueEuler
