import NonUniqueEuler.Defs.Sec9.All
import NonUniqueEuler.I.Sec6.InnerCirc
import NonUniqueEuler.I.Sec4.PropU

/-!
# Proof of the facts stated with the standing assumptions (SA) of Section 9

Proof of the interface `I/Sec9/Standing.lean` (`09_relay.tex:84-91`, `:117-118`).

* `standing_levels`: `inner_circ` (`I/Sec6/InnerCirc.lean`) with (SA3) `C_G μ s̄² ≤ G₁` gives
  `G_k ∈ [0, C_G μ s̄²] ⊆ [0, G₁]` and `P.GSmall`; `propU_a` (`I/Sec4/PropU.lean`) gives
  `σ_b = σ(G₀) ≤ σ(G)` on `[0, G₁]` and `σ_b > 211/2500`, hence `σ_b ≤ σ_k` and `σ_b ≤ σ(0)`.
* `det_of_small`: `ε = σ(0)(μ-1)/(8μ) > 0`; continuity of `λ_*` at `0` within `[0, G₁]`
  (`propU_a`) gives `δ > 0`; `s₀ = min 1 (m/(C_G μ + 1))` with `m = min(δ/2, G₁)` makes
  `C_G μ s̄² ≤ m` for `s̄ ∈ (0, s₀]` (no square root and no case split on `C_G = 0`).
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace Relay

open RingData Datum

/-- `G₁ > 0`. -/
private theorem Gbar_pos' : (0 : ℝ) < Gbar := by
  unfold Gbar Rc
  positivity

/-- **Consequences of (SA) for every level** (`09_relay.tex:84-87`, `:117-118`): `σ_b > 0`,
`σ_b ≤ σ = σ(0)`, `G_k ≤ G₁` for all levels (`P.GSmall`), and for every level `1 ≤ k ≤ n`:
`0 ≤ G_k ≤ C_G μ s̄²`, `G_k ∈ [0, G₁]` and `σ_k ≥ σ_b`. -/
theorem standing_levels (S : Standing) (hS : S.Holds) :
    0 < S.sigb ∧ S.sigb ≤ S.sigma0 ∧ S.P.GSmall ∧
      ∀ k ∈ Finset.Icc 1 S.P.n,
        S.P.G k ∈ Icc (0 : ℝ) (CG S.P.χ * S.P.μ * S.P.sbar ^ 2) ∧
          S.P.G k ∈ Icc (0 : ℝ) Gbar ∧ S.sigb ≤ S.P.sigma k := by
  obtain ⟨-, -, hG3, hG4⟩ := Approx.inner_circ S.P hS.valid hS.hN
  obtain ⟨hGbar, hsmall⟩ := hG4 hS.CG_le
  obtain ⟨-, -, ⟨G₀, -, hsb, hmin⟩, hgap, -⟩ := Eig.propU_a S.P.χ hS.admissible hS.hN
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) Gbar := ⟨le_rfl, Gbar_pos'.le⟩
  refine ⟨?_, ?_, hsmall, ?_⟩
  · show 0 < Eig.sigb S.P.χ
    linarith
  · show Eig.sigb S.P.χ ≤ Eig.sigma S.P.χ 0
    rw [hsb]
    exact hmin 0 h0
  · intro k hk
    obtain ⟨hGk0, hGk1, hGk2⟩ := hG3 k hk
    refine ⟨⟨hGk0, hGk1.trans hGk2⟩, hGbar k hk, ?_⟩
    show Eig.sigb S.P.χ ≤ Eig.sigma S.P.χ (S.P.G k)
    rw [hsb]
    exact hmin _ (hGbar k hk)

/-- **(Det) is a smallness condition on `s̄` at fixed `μ`** (`09_relay.tex:88-91`): for an
admissible cutoff with (N1)–(N3) and `μ > 1` there is `s₀ > 0` such that for every `s̄ ∈ (0, s₀]`,
`|λ_*(G) - z| ≤ σ(μ-1)/(8μ)` for all `G ∈ [0, C_G μ s̄²]`. -/
theorem det_of_small (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {μ : ℝ} (hμ : 1 < μ) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ sbar ∈ Ioc (0 : ℝ) s₀,
      ∀ G ∈ Icc (0 : ℝ) (CG χ * μ * sbar ^ 2), Kick.Detuned χ μ G := by
  obtain ⟨hcont, -, ⟨G₀, -, hsb, hmin⟩, hgap, -⟩ := Eig.propU_a χ hχ hN
  have hGb := Gbar_pos'
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) Gbar := ⟨le_rfl, hGb.le⟩
  -- `σ(0) ≥ σ_b > 0`
  have hσ0 : 0 < Eig.sigma χ 0 := by
    have := hmin 0 h0
    rw [← hsb] at this
    linarith
  have hμ0 : 0 < μ := by linarith
  set ε : ℝ := Eig.sigma χ 0 * (μ - 1) / (8 * μ) with hε_def
  have hε : 0 < ε := by
    have : 0 < μ - 1 := by linarith
    positivity
  -- continuity of `λ_*` at `0` within `[0, G₁]`
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousWithinAt_iff.1 (hcont 0 h0) ε hε
  set m : ℝ := min (δ / 2) Gbar with hm_def
  have hm : 0 < m := lt_min (by positivity) hGb
  have hCG := CG_nonneg χ
  have hD : 0 < CG χ * μ + 1 := by positivity
  refine ⟨min 1 (m / (CG χ * μ + 1)), lt_min one_pos (by positivity), ?_⟩
  intro sbar hsbar G hG
  obtain ⟨hs0, hs1⟩ := hsbar
  have hs_le1 : sbar ≤ 1 := hs1.trans (min_le_left _ _)
  have hs_le2 : sbar ≤ m / (CG χ * μ + 1) := hs1.trans (min_le_right _ _)
  -- `C_G μ s̄² ≤ m`
  have hsq : sbar ^ 2 ≤ m / (CG χ * μ + 1) := by
    have : sbar ^ 2 ≤ sbar := by nlinarith
    linarith
  have hCGs : CG χ * μ * sbar ^ 2 ≤ m := by
    have h1 : CG χ * μ * sbar ^ 2 ≤ CG χ * μ * (m / (CG χ * μ + 1)) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    have h2 : CG χ * μ * (m / (CG χ * μ + 1)) ≤ m := by
      rw [mul_div_assoc', div_le_iff₀ hD]
      nlinarith
    linarith
  obtain ⟨hG0, hG1⟩ := hG
  have hGm : G ≤ m := hG1.trans hCGs
  have hGmem : G ∈ Icc (0 : ℝ) Gbar := ⟨hG0, hGm.trans (min_le_right _ _)⟩
  have hGδ : dist G 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hG0]
    have : G ≤ δ / 2 := hGm.trans (min_le_left _ _)
    linarith
  have hlt := hδε hGmem hGδ
  rw [dist_eq_norm] at hlt
  exact hlt.le

end Relay

end NonUniqueEuler
