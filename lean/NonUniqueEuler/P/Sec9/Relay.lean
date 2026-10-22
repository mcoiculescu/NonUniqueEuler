import NonUniqueEuler.Defs.Sec9.All
import NonUniqueEuler.H.Sec9.Relay.Main

/-!
# Proof: `prop:relay` (the majorant of a quiet ring is bounded by the next ring)

Proof of `I/Sec9/Relay.lean` (`09_relay.tex:390-593`). The steps (helpers in
`H/Sec9/Relay/*.lean`, namespace `Relay.RelayH`):
1. `maj_le_two_majIn` (`09_relay.tex:460-470`): `maj_j ≤ maj^in_j + θ_jτ'maj_j(τ')` from (H2) and
   (M1) (`lem:majorant`), so `maj_j ≤ 2maj^in_j` on `[0,τ]`; the integrability of `η^in_j`,
   `η^out_j` is their continuity (`FieldContinuity`), from (Loc)(2) for the quiet ring `j`.
2. `quiet_o` (`09_relay.tex:471-498`, `eq:relay-quiet`): `lem:transfer-step`(1) with `s' = s_h`,
   `thm:quiet`(c) for ring `j+1` ((H3)), (M1) for `maj_{j+1}` and `lem:detuning`; this is (o), and
   with step 1 it gives (i) (if `j+1 = n`, (i) concerns only `τ = 0`).
3. `majIn_after_act` (`09_relay.tex:500-590`): for `τ^act < τ ≤ t̄♯_j`, the Duhamel integral is
   split at `τ^act` and `min(τ, τ^sat)`; the three parts are bounded by (o) and (H4)
   (`phase1_exp`), by `lem:transfer-step`(1) with `s' = s`, (H4) and `thm:active`'s last
   assertion (`active_pointwise`, `phase2_pt`, `phase2_int`), and by `lem:transfer`(3)
   (`debris_pointwise`); the sum is half the right side of `eq:relay` (`final_alg`). With step 1
   this gives (ii) (`τ = t̄♯_j > τ^act`) and (iii).

Deviation (minor, `debris_pointwise`): `lem:transfer`(3) is applied with
`R = min(ϱ_j(t), ar_j/8)` instead of `R_t = max{|x| : x ∈ D_{j+1}(t)}`.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace Relay

open RingData Datum

/-- **`prop:relay`** (`09_relay.tex:390-439`): under (SA), (Det), `C₀ ≥ 1`, `K₁ > 0` and the
hypotheses (H1)–(H4) at level `j` and ring-`j` time `τ ∈ [0, t̄♯_j]` (`S.RelayHyp C₀ K₁ j τ`):
`maj_j ≤ 2maj^in_j` on `[0,τ]`; (o) if `j+1 < n`,
`maj^in_j(τ') ≤ C_M(2C_Q/(σ_b(μ-1)) + 1)ε_j maj_{j+1}(μτ')` on `[0, min(τ, A_jt♯_{j+1})]`;
(i) if `τ ≤ A_jt♯_{j+1}`, `maj_j(τ) ≤ 2C_M(2C_Q/(σ_b(μ-1)) + 1)ε_j maj_{j+1}(μτ)`; (ii) if
`τ = t̄♯_j`, `eq:relay`: `maj_j(t̄♯_j) ≤ 2C_Mε_je^{x_jT_pin}[4C₂δ₀/(σ_b(μ-1)) + C_D(T_pin) + Ξ_{j+1}]`;
(iii) if `A_jt♯_{j+1} < τ < t̄♯_j`, `maj_j(τ)` is at most the right side of `eq:relay`. -/
theorem relay (S : Standing) (hS : S.Holds) (hDet : S.Det) {C₀ K₁ : ℝ} (hC₀ : 1 ≤ C₀)
    (hK₁ : 0 < K₁) {j : ℕ} {τ : ℝ} (h : S.RelayHyp C₀ K₁ j τ) :
    (∀ τ' ∈ Icc (0 : ℝ) τ, S.maj j τ' ≤ 2 * S.majIn j τ') ∧
    (j + 1 < S.P.n → ∀ τ' ∈ Icc (0 : ℝ) (min τ (S.P.A j * S.P.tsh (j + 1))),
      S.majIn j τ' ≤ S.Crelay * S.P.eps j * S.maj (j + 1) (S.P.μ * τ')) ∧
    (τ ≤ S.P.A j * S.P.tsh (j + 1) →
      S.maj j τ ≤ 2 * S.Crelay * S.P.eps j * S.maj (j + 1) (S.P.μ * τ)) ∧
    (τ = S.P.tash j → S.maj j τ ≤ S.relayBound j (S.XiNext C₀ K₁ j)) ∧
    (S.P.A j * S.P.tsh (j + 1) < τ → τ < S.P.tash j →
      S.maj j τ ≤ S.relayBound j (S.XiNext C₀ K₁ j)) := by
  have h0 : ∀ τ' ∈ Icc (0 : ℝ) τ, S.maj j τ' ≤ 2 * S.majIn j τ' := fun τ' hτ' =>
    RelayH.maj_le_two_majIn h hS hτ'
  have hτ : τ ∈ Icc (0 : ℝ) τ := ⟨h.τ_nonneg, le_rfl⟩
  have hafter : S.P.A j * S.P.tsh (j + 1) < τ →
      S.maj j τ ≤ S.relayBound j (S.XiNext C₀ K₁ j) := by
    intro hact
    have hm := RelayH.majIn_after_act h hS hDet hC₀ hK₁ hact
    calc S.maj j τ ≤ 2 * S.majIn j τ := h0 τ hτ
      _ ≤ 2 * (S.CM * S.P.eps j * Real.exp (S.P.xk j * S.P.Tpin) *
            (4 * S.C2 * S.P.δ₀ / (S.sigb * (S.P.μ - 1)) + CD S.P.Tpin + S.XiNext C₀ K₁ j)) := by
          linarith
      _ = S.relayBound j (S.XiNext C₀ K₁ j) := by
          rw [Standing.relayBound_def]
          ring
  refine ⟨h0, fun hjn τ' hτ' => RelayH.quiet_o h hS hDet hjn hτ', ?_, ?_,
    fun hact _ => hafter hact⟩
  · intro hle
    rcases lt_or_eq_of_le (Nat.succ_le_of_lt h.lt_n) with hjn | hjn
    · have ho := RelayH.quiet_o h hS hDet hjn (τ' := τ) ⟨h.τ_nonneg, le_min le_rfl hle⟩
      calc S.maj j τ ≤ 2 * S.majIn j τ := h0 τ hτ
        _ ≤ 2 * (S.Crelay * S.P.eps j * S.maj (j + 1) (S.P.μ * τ)) := by linarith
        _ = 2 * S.Crelay * S.P.eps j * S.maj (j + 1) (S.P.μ * τ) := by ring
    · -- `j + 1 = n`: `t♯_n = 0`, so `τ = 0` and both sides vanish
      have hjn' : j + 1 = S.P.n := hjn
      have hτ0 : τ = 0 := by
        refine le_antisymm ?_ h.τ_nonneg
        rw [hjn', S.P.tsh_n, mul_zero] at hle
        exact hle
      rw [hτ0, mul_zero, S.maj_zero, S.maj_zero, mul_zero]
  · intro heq
    refine hafter ?_
    rw [heq]
    exact RelayH.tauAct_lt_tash h hS

end Relay

end NonUniqueEuler
