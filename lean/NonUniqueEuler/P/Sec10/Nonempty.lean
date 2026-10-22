import NonUniqueEuler.H.Sec10.Nonempty.KappaFive
import NonUniqueEuler.H.Sec10.Nonempty.SbarB
import NonUniqueEuler.I.Sec10.Nonempty.E22

/-!
# Proof of `lem:nonempty` (the parameter lists can be satisfied)

Proof of `I/Sec10/Nonempty.lean` (`10_parameters.tex:278-290`, proof `:292-375`). Same declaration,
statement copied verbatim.

* (P0)–(P4): `NonemptyH.exists_structural` (`H/Sec10/Nonempty/Structural.lean`).
* (P5): each of (κ1)–(κ7) holds for all small `κ` (`H/Sec10/Nonempty/Kappa.lean`, `KappaFive.lean`),
  so (κ1)–(κ7) hold on some `(0, x₀]`, and every `κ_seed ∈ (0, x₀/2]` is admissible
  (`κ† = x₀/2`, as in the manuscript).
* (P6): for a fixed admissible `κ_seed`, each condition of (P6) holds for all small `s̄`
  (`H/Sec10/Nonempty/SbarA.lean`, `SbarB.lean`; (B4) by `det_of_small`; `eq:E22` by the
  sub-interface `I/Sec10/Nonempty/E22.lean`, see `Standing.CondE22`), so all hold on some
  `(0, s̄₀]`.

The proof works with filters `𝓝[>] 0` instead of the explicit thresholds `x₀ = min_i x_i`,
`s̄₀ = min_i s̄_i` of the manuscript (the same argument).
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace Relay

open RingData Datum

open NonemptyH in
/-- **`lem:nonempty`** (`10_parameters.tex:278-290`). Assume (N1)–(N3) for the admissible cutoff
`χ`. The choices (P0)–(P6) can be made in this order: there are parameters `p` with cutoff `χ`
satisfying the structural list (P0)–(P4) such that the set of admissible seed sizes in (P5)
contains an interval `(0, κ†]` with `κ† > 0`, and for every admissible seed size `κ` the set of
admissible scale ratios `s̄` in (P6) contains an interval `(0, s̄₀]` with `s̄₀ > 0`. -/
theorem nonempty (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) :
    ∃ p : Params, p.χ = χ ∧ p.Structural ∧
      (∃ κdag : ℝ, 0 < κdag ∧ ∀ κ ∈ Ioc (0 : ℝ) κdag, p.ref.KappaList κ) ∧
      ∀ κ : ℝ, p.ref.KappaList κ → ∃ sbar₀ : ℝ, 0 < sbar₀ ∧ ∀ sbar ∈ Ioc (0 : ℝ) sbar₀,
        ({ p with κs := κ, sbar := sbar } : Params).SbarOK := by
  obtain ⟨p, rfl, hp⟩ := exists_structural χ hχ hN
  have hpos : p.ref.ConstPos := structural_constPos hχ hN hp
  refine ⟨p, rfl, hp, ?_, ?_⟩
  · -- (P5)
    have hev : ∀ᶠ κ in 𝓝[>] (0 : ℝ), p.ref.CondKappa κ := by
      filter_upwards [eventually_k1 hp, eventually_k2 hpos hp, eventually_k3 hpos hp,
        eventually_k4 hpos, eventually_k5 hχ hN hpos hp, eventually_k6 hpos,
        eventually_k7 hpos hp] with κ h1 h2 h3 h4 h5 h6 h7
      exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
    obtain ⟨x₀, hx₀, hx⟩ := exists_Ioc_of_eventually hev
    refine ⟨x₀ / 2, by positivity, fun κs hκs => ⟨hκs.1, fun κ hκ => hx κ ⟨hκ.1, ?_⟩⟩⟩
    linarith [hκ.2, hκs.2]
  · -- (P6)
    intro κ hκ
    obtain ⟨s₂₂, hs₂₂, hE⟩ := e22_small p hχ hN hp κ
    have hev : ∀ᶠ sb in 𝓝[>] (0 : ℝ), ({ p with κs := κ, sbar := sb } : Params).SbarOK := by
      filter_upwards [eventually_sbar_pos, eventually_b1_le, eventually_b1_pow,
        eventually_b2 (p := p), eventually_b3 (p := p), eventually_b4 hχ hN hp,
        eventually_b5 hp, eventually_b6 (p := p) hκ.pos, eventually_b7_KO (p := p),
        eventually_b7_CO (p := p), eventually_b7_mu (p := p), eventually_of_Ioc hs₂₂ hE,
        eventually_b8_etab (p := p), eventually_b8_level κ hp, eventually_b8_seed (p := p) κ,
        eventually_b9_maj hpos, eventually_b9_eta (p := p), eventually_b10 (p := p),
        eventually_b11_handoff (p := p), eventually_b11_kick hpos hp]
        with sb h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19
      exact
        { sbar_pos := h0
          b1_le := h1
          b1_pow := h2
          b2 := h3
          b3 := h4
          b4 := h5
          b5 := h6
          b6 := h7
          b7 := ⟨⟨h8, h9, h10⟩, h11⟩
          b8_etab := h12
          b8_level := h13
          b8_seed := h14
          b9_maj := h15
          b9_eta := h16
          b10 := h17
          b11_handoff := h18
          b11_kick := h19 }
    exact exists_Ioc_of_eventually hev

end Relay

end NonUniqueEuler
