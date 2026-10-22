import NonUniqueEuler.Defs.Sec9.All
import NonUniqueEuler.I.Sec9.Standing

/-!
# Proof of `lem:detuning` (the rate gap between neighbouring rings)

Proof of the interface `I/Sec9/Detuning.lean` (`09_relay.tex:104-136`).

* `standing_levels` (`I/Sec9/Standing.lean`) gives `0 < σ_b ≤ σ` and `G_i ∈ [0, C_G μ s̄²]` for
  every level, so (Det) gives `|σ_i - σ| = |Re(λ_*(G_i) - z)| ≤ e_μ σ`.
* The remaining inequalities are real algebra in `μ ∈ (1, 17/16]`, `0 < σ_b ≤ σ`, `σ' < 3σ/4`;
  they are proved over named real variables in `detuning_real_*` below.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace Relay

open RingData Datum

/-! ### The algebraic core (named real variables) -/

/-- `e_μ = (μ-1)/(8μ) ≤ 1/136` for `1 < μ ≤ 17/16`. -/
private theorem detuning_real_emu_le {μ : ℝ} (h1 : 1 < μ) (h2 : μ ≤ 17 / 16) :
    (μ - 1) / (8 * μ) ≤ 1 / 136 := by
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- `e_μ(μ+1) ≤ (μ-1)/4` for `1 < μ`. -/
private theorem detuning_real_emu_mul_le {μ : ℝ} (h1 : 1 < μ) :
    (μ - 1) / (8 * μ) * (μ + 1) ≤ (μ - 1) / 4 := by
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  nlinarith

/-- The per-level bounds from `|σ_i - σ| ≤ eσ`, `e ≤ 1/136`, `σ > 0`, `σ' < 3σ/4`,
`1 < μ ≤ 17/16`: `σ_i ≥ 15σ/16`, `σ' < 15σ/16`, `σ/4 ≤ σ_i/μ ≤ 17σ/16`. -/
private theorem detuning_real_level {μ σ σ' e σi : ℝ} (h1 : 1 < μ) (h2 : μ ≤ 17 / 16)
    (hσ : 0 < σ) (hσ' : σ' < 3 / 4 * σ) (he : e ≤ 1 / 136)
    (hi : |σi - σ| ≤ e * σ) :
    15 / 16 * σ ≤ σi ∧ σ' < 15 / 16 * σ ∧ σ / 4 ≤ σi / μ ∧ σi / μ ≤ 17 / 16 * σ := by
  have hμ0 : 0 < μ := by linarith
  have heσ : e * σ ≤ 1 / 136 * σ := mul_le_mul_of_nonneg_right he hσ.le
  have hlo : σ - e * σ ≤ σi := by linarith [neg_abs_le (σi - σ)]
  have hhi : σi ≤ σ + e * σ := by linarith [le_abs_self (σi - σ)]
  have h15 : 15 / 16 * σ ≤ σi := by linarith
  refine ⟨h15, by linarith, ?_, ?_⟩
  · rw [le_div_iff₀ hμ0]
    nlinarith
  · rw [div_le_iff₀ hμ0]
    nlinarith

/-- The two-level bound `σ((μ-1) - e(μ+1)) ≤ μσ_i - σ_l` from `|σ_i - σ|, |σ_l - σ| ≤ eσ`. -/
private theorem detuning_real_pair {μ σ e σi σl : ℝ} (hμ0 : 0 ≤ μ)
    (hi : |σi - σ| ≤ e * σ) (hl : |σl - σ| ≤ e * σ) :
    σ * ((μ - 1) - e * (μ + 1)) ≤ μ * σi - σl := by
  have hlo : σ - e * σ ≤ σi := by linarith [neg_abs_le (σi - σ)]
  have hhi : σl ≤ σ + e * σ := by linarith [le_abs_self (σl - σ)]
  have hm : μ * (σ - e * σ) ≤ μ * σi := mul_le_mul_of_nonneg_left hlo hμ0
  nlinarith

/-- `(3/4)σ(μ-1) ≤ σ((μ-1) - e(μ+1))` from `e(μ+1) ≤ (μ-1)/4` and `σ ≥ 0`. -/
private theorem detuning_real_three_quarters {μ σ e : ℝ} (hσ : 0 ≤ σ)
    (he : e * (μ + 1) ≤ (μ - 1) / 4) :
    3 / 4 * σ * (μ - 1) ≤ σ * ((μ - 1) - e * (μ + 1)) := by
  have := mul_le_mul_of_nonneg_left he hσ
  nlinarith

/-- `(1/2)σ_b(μ-1) ≤ (3/4)σ(μ-1)` from `0 < σ_b ≤ σ` and `1 < μ`. -/
private theorem detuning_real_half {μ σ σb : ℝ} (h1 : 1 < μ) (hb : 0 < σb) (hbσ : σb ≤ σ) :
    1 / 2 * σb * (μ - 1) ≤ 3 / 4 * σ * (μ - 1) := by
  have : σb * (μ - 1) ≤ σ * (μ - 1) := mul_le_mul_of_nonneg_right hbσ (by linarith)
  nlinarith [mul_pos hb (show (0 : ℝ) < μ - 1 by linarith)]

/-- The "in particular": for `i < l`, `σ_i μ^{i-l} ≤ σ_l - σ_b(μ-1)/(2μ)`, from
`(1/2)σ_b(μ-1) ≤ μσ_l - σ_i`, `σ_i ≥ 0` and `μ > 1`. -/
private theorem detuning_real_zpow {μ σb σi σl : ℝ} {i l : ℕ} (h1 : 1 < μ) (hσi : 0 ≤ σi)
    (hil : i < l) (hgap : 1 / 2 * σb * (μ - 1) ≤ μ * σl - σi) :
    σi * μ ^ ((i : ℤ) - l) ≤ σl - σb * (μ - 1) / (2 * μ) := by
  have hμ0 : 0 < μ := by linarith
  have hexp : ((i : ℤ) - l) ≤ -1 := by omega
  have hz : μ ^ ((i : ℤ) - l) ≤ μ ^ (-1 : ℤ) := zpow_le_zpow_right₀ h1.le hexp
  rw [zpow_neg_one] at hz
  have h1' : σi * μ ^ ((i : ℤ) - l) ≤ σi * μ⁻¹ := mul_le_mul_of_nonneg_left hz hσi
  have h2' : σi * μ⁻¹ ≤ σl - σb * (μ - 1) / (2 * μ) := by
    have hc : σb * (μ - 1) / (2 * μ) * μ = 1 / 2 * σb * (μ - 1) := by
      field_simp
    rw [← div_eq_mul_inv, div_le_iff₀ hμ0, sub_mul, hc]
    linarith
  exact h1'.trans h2'

/-! ### The lemma -/

/-- **`lem:detuning`** (`09_relay.tex:104-111`): under (SA) and (Det), with `e_μ = (μ-1)/(8μ)`:
`e_μ ≤ 1/136`, `e_μ(μ+1) ≤ (μ-1)/4`, and for all levels `i, l ∈ [1,n]`: `|σ_i - σ| ≤ e_μσ`,
`σ_i ≥ 15σ/16 > σ'`, `σ/4 ≤ x_i ≤ 17σ/16`,
`μσ_i - σ_l ≥ σ((μ-1) - e_μ(μ+1)) ≥ (3/4)σ(μ-1) ≥ (1/2)σ_b(μ-1)`, and
`σ_i μ^{i-l} ≤ σ_l - σ_b(μ-1)/(2μ)` if `i < l`. -/
theorem detuning (S : Standing) (hS : S.Holds) (hDet : S.Det) :
    S.emu ≤ 1 / 136 ∧ S.emu * (S.P.μ + 1) ≤ (S.P.μ - 1) / 4 ∧
    ∀ i ∈ Finset.Icc 1 S.P.n,
      |S.P.sigma i - S.sigma0| ≤ S.emu * S.sigma0 ∧ 15 / 16 * S.sigma0 ≤ S.P.sigma i ∧
      S.σ' < 15 / 16 * S.sigma0 ∧ S.sigma0 / 4 ≤ S.P.xk i ∧ S.P.xk i ≤ 17 / 16 * S.sigma0 ∧
      ∀ l ∈ Finset.Icc 1 S.P.n,
        S.sigma0 * ((S.P.μ - 1) - S.emu * (S.P.μ + 1)) ≤ S.P.μ * S.P.sigma i - S.P.sigma l ∧
        3 / 4 * S.sigma0 * (S.P.μ - 1) ≤ S.sigma0 * ((S.P.μ - 1) - S.emu * (S.P.μ + 1)) ∧
        1 / 2 * S.sigb * (S.P.μ - 1) ≤ 3 / 4 * S.sigma0 * (S.P.μ - 1) ∧
        (i < l → S.P.sigma i * S.P.μ ^ ((i : ℤ) - l) ≤
          S.P.sigma l - S.sigb * (S.P.μ - 1) / (2 * S.P.μ)) := by
  obtain ⟨hb, hbσ, -, hlev⟩ := standing_levels S hS
  have h1 : 1 < S.P.μ := hS.one_lt_μ
  have h2 : S.P.μ ≤ 17 / 16 := hS.μ_le
  have hσ : 0 < S.sigma0 := hb.trans_le hbσ
  have hσ' : S.σ' < 3 / 4 * S.sigma0 := hS.σ'_lt_sigma
  have hemu : S.emu = (S.P.μ - 1) / (8 * S.P.μ) := rfl
  have he : S.emu ≤ 1 / 136 := hemu ▸ detuning_real_emu_le h1 h2
  have hem : S.emu * (S.P.μ + 1) ≤ (S.P.μ - 1) / 4 := hemu ▸ detuning_real_emu_mul_le h1
  -- `|σ_k - σ| ≤ e_μ σ` for every level, from (Det).
  have hdet : ∀ k ∈ Finset.Icc 1 S.P.n, |S.P.sigma k - S.sigma0| ≤ S.emu * S.sigma0 := by
    intro k hk
    have hD : ‖Eig.lam S.P.χ (S.P.G k) - Eig.z S.P.χ‖ ≤
        Eig.sigma S.P.χ 0 * (S.P.μ - 1) / (8 * S.P.μ) := hDet _ (hlev k hk).1
    have hre : S.P.sigma k - S.sigma0 = (Eig.lam S.P.χ (S.P.G k) - Eig.z S.P.χ).re := by
      rw [Complex.sub_re]
      rfl
    rw [hre]
    refine (Complex.abs_re_le_norm _).trans (hD.trans_eq ?_)
    rw [hemu, Standing.sigma0_def]
    ring
  refine ⟨he, hem, fun i hi => ?_⟩
  have hdi := hdet i hi
  obtain ⟨h15, hσ'15, hx1, hx2⟩ := detuning_real_level h1 h2 hσ hσ' he hdi
  refine ⟨hdi, h15, hσ'15, hx1, hx2, fun l hl => ?_⟩
  have hdl := hdet l hl
  have hμ0 : 0 ≤ S.P.μ := by linarith
  have h34 := detuning_real_three_quarters (σ := S.sigma0) hσ.le hem
  have hhalf := detuning_real_half (μ := S.P.μ) h1 hb hbσ
  refine ⟨detuning_real_pair hμ0 hdi hdl, h34, hhalf, fun hil => ?_⟩
  have hσi : 0 ≤ S.P.sigma i := le_trans (by positivity) h15
  have hgap : 1 / 2 * S.sigb * (S.P.μ - 1) ≤ S.P.μ * S.P.sigma l - S.P.sigma i :=
    hhalf.trans (h34.trans (detuning_real_pair hμ0 hdl hdi))
  exact detuning_real_zpow h1 hσi hil hgap

end Relay

end NonUniqueEuler
