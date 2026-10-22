import NonUniqueEuler.Defs.Sec10.All
import NonUniqueEuler.I.Sec10.ConstantsPos
import NonUniqueEuler.I.Sec4.PropU
import NonUniqueEuler.H.Sec10.Nonempty.Limits

/-!
# Helper for `lem:nonempty`: the structural list (P0)–(P4) can be satisfied

Helper of `P/Sec10/Nonempty.lean`, first paragraph of the proof of `lem:nonempty`
(`10_parameters.tex:295-315`).

* `dH_pos`: `d_H > 0` (both branches of the choice of the constants of `thm:active`);
* `structural_constPos`: the signs `Standing.ConstPos` for `p.ref` from (P0)–(P4)
  (`constants_pos`, `I/Sec10/ConstantsPos.lean`);
* `exists_structural`: there are parameters with cutoff `χ` satisfying (P0)–(P4): `s = 3`,
  `σ' ∈ (9/200, min(σ_b, 3σ/4))` (nonempty by `prop:U`(a): `σ_b > 211/2500`, `σ = σ(0) ≥ σ_b`),
  `δ₀ = min(d_H, δ_kick, δ_rd) > 0`, `μ = μ_max > 1`, and `T_pin` with `r_T(T_pin) ≤ 1/64`
  (`r_T(T) → 0`, `σ > 0`).

All lemmas are fully proved. Namespace `NonUniqueEuler.Relay.NonemptyH`.
-/

noncomputable section

open Set Filter Topology

namespace NonUniqueEuler

namespace Relay

open RingData Datum

namespace NonemptyH

/-- `d_H > 0` (`thm:active`: `d_H ∈ (0,1)`; junk value `1/2`). -/
theorem dH_pos (χ : ℝ → ℝ) (s : ℕ) (σ' : ℝ) : 0 < OneRing.dH χ s σ' := by
  unfold OneRing.dH OneRing.activeConsts
  split_ifs with h
  · exact h.choose_spec.1.1
  · norm_num

/-- The signs of the constants of (P0)–(P4) for `p.ref`, from the structural list. -/
theorem structural_constPos {p : Params} (hχ : IsAdmissibleCutoff p.χ)
    (hN : NumericalHypothesis p.χ) (hp : p.Structural) : p.ref.ConstPos :=
  constants_pos p.ref hχ hN hp.p0.σ'_gt hp.p0.σ'_lt_sigma hp.p1.δ₀_pos hp.p2.one_lt_μ
    hp.p3.Tpin_pos

/-- `0 < G₁`. -/
theorem Gbar_pos : 0 < Gbar := by
  unfold Gbar Rc
  positivity

/-- **(P0)–(P4) can be satisfied** (`10_parameters.tex:295-315`). -/
theorem exists_structural (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ)
    (hN : NumericalHypothesis χ) : ∃ p : Params, p.χ = χ ∧ p.Structural := by
  obtain ⟨-, -, ⟨G₀, -, hsb, hmin⟩, hsb_gt, -⟩ := Eig.propU_a χ hχ hN
  have hσ0 : Eig.sigb χ ≤ Eig.sigma χ 0 := hsb ▸ hmin 0 ⟨le_rfl, Gbar_pos.le⟩
  have hm : 9 / 200 < min (Eig.sigb χ) (3 / 4 * Eig.sigma χ 0) :=
    lt_min (by linarith) (by linarith)
  set σ' : ℝ := (9 / 200 + min (Eig.sigb χ) (3 / 4 * Eig.sigma χ 0)) / 2 with hσ'_def
  have h1 : 9 / 200 < σ' := by rw [hσ'_def]; linarith
  have h2 : σ' < Eig.sigb χ := by
    have := min_le_left (Eig.sigb χ) (3 / 4 * Eig.sigma χ 0)
    rw [hσ'_def]; linarith
  have h3 : σ' < 3 / 4 * Eig.sigma χ 0 := by
    have := min_le_right (Eig.sigb χ) (3 / 4 * Eig.sigma χ 0)
    rw [hσ'_def]; linarith
  -- an auxiliary datum, to read off the signs of the constants that depend on `χ, s, σ'` only
  let p₀ : Params := ⟨χ, 3, σ', 1, 2, 1, 0, 0⟩
  have hpos₀ : p₀.ref.ConstPos :=
    constants_pos p₀.ref hχ hN h1 h3 one_pos one_lt_two one_pos
  set δ₀ : ℝ := min (OneRing.dH χ 3 σ') (min p₀.ref.deltaKick p₀.ref.deltaRd) with hδ₀_def
  have hδ₀ : 0 < δ₀ := lt_min (dH_pos _ _ _) (lt_min hpos₀.deltaKick_pos hpos₀.deltaRd_pos)
  set μ : ℝ := 1 + min (p₀.ref.cPrime * δ₀) (1 / 16) with hμ_def
  have hμ : 1 < μ := by
    have : 0 < min (p₀.ref.cPrime * δ₀) (1 / 16) :=
      lt_min (mul_pos hpos₀.cPrime_pos hδ₀) (by norm_num)
    rw [hμ_def]; linarith
  have hσpos : 0 < Eig.sigma χ 0 / 4 := by
    have := hpos₀.sigma0_pos
    exact div_pos this (by norm_num)
  obtain ⟨T, hT, hrT⟩ : ∃ T : ℝ, 0 < T ∧
      (1 + T) ^ 3 * Real.exp (-(Eig.sigma χ 0 / 4 * T)) ≤ 1 / 64 := by
    have hev := (tendsto_rT hσpos).eventually (eventually_le_nhds (show (0 : ℝ) < 1 / 64 by
      norm_num))
    obtain ⟨T, hT⟩ := (hev.and (eventually_gt_atTop 0)).exists
    exact ⟨T, hT.2, hT.1⟩
  refine ⟨⟨χ, 3, σ', δ₀, μ, T, 0, 0⟩, rfl, ⟨⟨le_rfl, h1, h2, h3⟩, ⟨hδ₀, ?_, ?_, ?_⟩, ⟨hμ, ?_⟩,
    ⟨hT, ?_⟩⟩⟩
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)
  · exact le_rfl
  · have he : Eig.sigma χ 0 * T / 4 = Eig.sigma χ 0 / 4 * T := by ring
    show (1 + T) ^ 3 * Real.exp (-(Eig.sigma χ 0 * T / 4)) ≤ 1 / 64
    rw [he]
    exact hrT

end NonemptyH

end Relay

end NonUniqueEuler
