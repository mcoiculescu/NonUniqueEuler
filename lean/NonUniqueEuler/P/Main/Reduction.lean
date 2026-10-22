import NonUniqueEuler.Statement.MainTheorem
import NonUniqueEuler.I.Sec10.Nonempty
import NonUniqueEuler.I.Sec11.MainExplicit
import NonUniqueEuler.I.Sec6.Integrability

/-!
# Proof: the conditional theorem (part 1)

Proof of `I/Main/Reduction.lean`: `prop:reduction` (`01_intro.tex:301-305`, proof
`11_bootstrap.tex:723-739`). For every admissible cutoff `χ`, Hypothesis (N) for `χ` implies
Theorem 1.1 for `χ`.

The proof follows the manuscript:
1. by `lem:nonempty` (`Relay.nonempty`, `I/Sec10/Nonempty.lean`) and its proved corollary
   `Relay.Params.exists_lists_of` (`Defs/Sec10/Params.lean`), there are parameters `p` with
   cutoff `χ` satisfying (P0)–(P6) (`11_bootstrap.tex:724-725`);
2. by `prop:integrability` (`Datum.integrability`, `I/Sec6/Integrability.lean`), the datum `f` is
   radial, nonnegative, in every `L^q`, `q ∈ [1, ∞)`, and not in `L^∞` (`11_bootstrap.tex:729-731`);
3. by `thm:main-explicit` (`Relay.main_explicit`, `I/Sec11/MainExplicit.lean`), the conclusions of
   the explicit theorem hold for every `A₁ > 0` (`11_bootstrap.tex:728-736`);
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
