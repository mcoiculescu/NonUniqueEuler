import NonUniqueEuler.Defs.Sec9.All
import NonUniqueEuler.I.Sec9.Detuning

/-!
# Proof of `lem:gamma` (the exponent `γ_j` stays below `1`)

Proof of the interface `I/Sec9/Gamma.lean` (`09_relay.tex:139-163`).

* `detuning` (`I/Sec9/Detuning.lean`), applied at the levels `j` and `j+1`, gives
  `σ_{j+1} ≥ 15σ/16`, `σ' < 15σ/16`, `|σ_{j+1} - σ| ≤ e_μσ` with `e_μ ≤ 1/136`, and
  `μσ_{j+1} - σ_j ≥ (3/4)σ(μ-1)`.
* The rest is real algebra over named variables (`gamma_real`):
  - `σ_j ≤ μσ_{j+1} - (13/20)(μ-1)σ_{j+1}` because `(13/20)σ_{j+1} ≤ (13/20)(137/136)σ ≤ (3/4)σ`;
    this is `σ_j/(μσ_{j+1}) ≤ 1 - (13/20)(μ-1)/μ`;
  - `μσ'/(μσ_{j+1}) = σ'/σ_{j+1} ≤ 16σ'/(15σ)`, i.e. `≤ 1 - c_γ`.

**Deviation (harmless).** The manuscript bounds `1 - σ_j/(μσ_{j+1})` from below by
`(3/4)(μ-1)/μ` via `σ_j ≤ (1+e_μ)σ`, `σ_{j+1} ≥ (1-e_μ)σ`; we instead use the two-level bound
`μσ_{j+1} - σ_j ≥ (3/4)σ(μ-1)` of `lem:detuning` together with `σ_{j+1} ≤ (1+e_μ)σ`, which gives
the (weaker, sufficient) margin `(13/20)(μ-1)/μ` directly. Positivity of `σ` comes from
`9/200 < σ' < 15σ/16`.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace Relay

open RingData Datum

/-- The algebraic core of `lem:gamma`, over named real variables: `a = σ_j`, `b = σ_{j+1}`,
`σ = σ(0)`, `σ'`, `e = e_μ`. -/
private theorem gamma_real {μ σ σ' e a b : ℝ} (h1 : 1 < μ) (hσ'pos : 0 < σ')
    (hσ'15 : σ' < 15 / 16 * σ) (he : e ≤ 1 / 136) (hbabs : |b - σ| ≤ e * σ)
    (hb15 : 15 / 16 * σ ≤ b) (hpair : 3 / 4 * σ * (μ - 1) ≤ μ * b - a) :
    min (13 / 20 * ((μ - 1) / μ)) (1 - 16 * σ' / (15 * σ)) ≤ 1 - max a (μ * σ') / (μ * b) ∧
      0 < min (13 / 20 * ((μ - 1) / μ)) (1 - 16 * σ' / (15 * σ)) := by
  have hμ0 : 0 < μ := by linarith
  have hσ : 0 < σ := by linarith
  have hb : 0 < b := by linarith
  have hμb : 0 < μ * b := mul_pos hμ0 hb
  set m := min (13 / 20 * ((μ - 1) / μ)) (1 - 16 * σ' / (15 * σ)) with hm
  have hm1 : m ≤ 13 / 20 * ((μ - 1) / μ) := min_le_left _ _
  have hm2 : m ≤ 1 - 16 * σ' / (15 * σ) := min_le_right _ _
  -- `b ≤ (137/136) σ`
  have heσ : e * σ ≤ 1 / 136 * σ := mul_le_mul_of_nonneg_right he hσ.le
  have hbhi : b ≤ σ + e * σ := by linarith [le_abs_self (b - σ)]
  have hb137 : b ≤ 137 / 136 * σ := by linarith
  -- first branch: `a ≤ (1 - m) μ b`
  have hid1 : (1 - 13 / 20 * ((μ - 1) / μ)) * (μ * b) = μ * b - 13 / 20 * (μ - 1) * b := by
    field_simp
  have hmono1 : (1 - 13 / 20 * ((μ - 1) / μ)) * (μ * b) ≤ (1 - m) * (μ * b) :=
    mul_le_mul_of_nonneg_right (by linarith) hμb.le
  have hμ1 : 0 ≤ μ - 1 := by linarith
  have hkey1 : 13 / 20 * (μ - 1) * b ≤ 3 / 4 * σ * (μ - 1) := by
    have hb' : 13 / 20 * b ≤ 3 / 4 * σ := by linarith
    have := mul_le_mul_of_nonneg_right hb' hμ1
    linarith
  have ha : a ≤ (1 - m) * (μ * b) := by linarith
  -- second branch: `μ σ' ≤ (1 - m) μ b`
  have hq0 : 0 ≤ 16 * σ' / (15 * σ) := by positivity
  have hmono2 : 16 * σ' / (15 * σ) * (μ * b) ≤ (1 - m) * (μ * b) :=
    mul_le_mul_of_nonneg_right (by linarith) hμb.le
  have hlow2 : 16 * σ' / (15 * σ) * (μ * (15 / 16 * σ)) ≤ 16 * σ' / (15 * σ) * (μ * b) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb15 hμ0.le) hq0
  have hid2 : 16 * σ' / (15 * σ) * (μ * (15 / 16 * σ)) = μ * σ' := by
    field_simp
  have hs : μ * σ' ≤ (1 - m) * (μ * b) := by linarith
  refine ⟨?_, ?_⟩
  · have hmax : max a (μ * σ') / (μ * b) ≤ 1 - m := by
      rw [div_le_iff₀ hμb]
      exact max_le ha hs
    linarith
  · refine lt_min ?_ ?_
    · have : 0 < (μ - 1) / μ := div_pos (by linarith) hμ0
      positivity
    · rw [sub_pos, div_lt_one (by positivity)]
      linarith

/-- **`lem:gamma`** (`09_relay.tex:139-141`): under (SA) and (Det), for every level `1 ≤ j < n`,
`1 - γ_j ≥ γ'_μ > 0`. -/
theorem gamma (S : Standing) (hS : S.Holds) (hDet : S.Det) :
    ∀ j ∈ Finset.Ico 1 S.P.n, S.gammaMu' ≤ 1 - S.gammaJ j ∧ 0 < S.gammaMu' := by
  intro j hj
  rw [Finset.mem_Ico] at hj
  have hj1 : j ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.2 ⟨hj.1, hj.2.le⟩
  have hj2 : j + 1 ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  obtain ⟨he136, -, hlev⟩ := detuning S hS hDet
  obtain ⟨-, -, hσ'15, -, -, -⟩ := hlev j hj1
  obtain ⟨hbabs, hb15, -, -, -, hpairs⟩ := hlev (j + 1) hj2
  obtain ⟨hpair, h34, -, -⟩ := hpairs j hj1
  have hσ'pos : 0 < S.σ' := by linarith [hS.σ'_gt]
  exact gamma_real hS.one_lt_μ hσ'pos hσ'15 he136 hbabs hb15 (h34.trans hpair)

end Relay

end NonUniqueEuler
