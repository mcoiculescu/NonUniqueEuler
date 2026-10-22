import NonUniqueEuler.Defs.Sec9.Phases

/-!
# Section 9.2: quiet rings — `lem:O`, `prop:relay`, `lem:Oprime` (definitions)

Manuscript `09_relay.tex:93-738`.

* `lem:O` (`:228-250`): `S.KO` (`K_O`), `S.Ptil i j` (`P̃_{i,j} = ∏_{p=i}^{j-1} K_O ε_p`), `S.theta j`
  (`θ_j`), the three smallness conditions `S.OSmall`, the hypotheses `S.OHyp j τ` and the
  conclusions `S.OConcl j τ` (used together by `lem:Oprime`);
* `prop:relay` (`:390-439`): `S.CXi C₀ K₁` (`C_Ξ`), `Relay.CD T` (`C_D(T)`), `S.XiNext C₀ K₁ j`
  (`Ξ_{j+1}`), `S.relayBound j Ξ` (the right side of `eq:relay` with `Ξ` in place of `Ξ_{j+1}`),
  `S.Crelay` (`C_M(2C_Q/(σ_b(μ-1)) + 1)`, the constant of (o), (i)), and the hypotheses
  (H1)–(H4) `S.RelayHyp C₀ K₁ j τ`;
* `lem:Oprime` (`:605-631`): `S.Cop C₀ K₁` (`C_op`), `S.etabK C₀ K₁ k` (`η_{b,k}`, `= 0` for `k = 1`),
  `S.etab C₀ K₁` (`η_b`), and the hypotheses `S.OprimeHyp C₀ K₁ C_F k t`.

`lem:detuning`, `lem:gamma`, `lem:transfer-step` need no new definition (`S.emu`, `S.gammaJ`,
`S.gammaMu'`, `P.b i k`). Here `m = 3`. All lemmas here are fully proved.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

open RingData Datum

/-- `C_D(T) = (2 + 2C_* T)^m T` (`prop:relay`(ii), `09_relay.tex:427`; `C_*` of `lem:speed`). -/
def CD (T : ℝ) : ℝ := (2 + 2 * Cstar * T) ^ 3 * T

theorem CD_def (T : ℝ) : CD T = (2 + 2 * Cstar * T) ^ 3 * T := rfl

namespace Standing

variable (S : Standing)

/-! ### `lem:O` (`09_relay.tex:228-250`) -/

/-- `K_O = 8C_M(C_Q C_Duh + 1) + 32 C_M C_Q C_Duh` (`lem:O`, `09_relay.tex:232`). -/
def KO : ℝ := 8 * S.CM * (S.CQ * S.CDuh + 1) + 32 * S.CM * S.CQ * S.CDuh

/-- `P̃_{i,j} = ∏_{p=i}^{j-1} K_O ε_p` (`lem:O`, `09_relay.tex:242`; `= 1` if `j ≤ i`). -/
def Ptil (i j : ℕ) : ℝ := ∏ p ∈ Finset.Ico i j, S.KO * S.P.eps p

/-- `θ_j = 4 C_O C_Q K_O s_{j-1}^{2m}` for `j ≥ 2`, `θ_1 = 0` (`lem:O`, `09_relay.tex:244-245`;
`0` also at the junk level `j = 0`). -/
def theta (j : ℕ) : ℝ := if 2 ≤ j then 4 * S.CO * S.CQ * S.KO * S.P.s (j - 1) ^ (2 * 3) else 0

/-- **The smallness conditions of `lem:O`** (`09_relay.tex:238-239`; the first three parts of
(B7)): `K_O s̄^{2m} ≤ 1/4`, `16 C_O C_Q C_Duh K_O s̄^{2m} ≤ 1`, `K_O μ s̄^{m+2} ≤ 1/2`. -/
structure OSmall : Prop where
  KO_sbar : S.KO * S.P.sbar ^ (2 * 3) ≤ 1 / 4
  CO_KO_sbar : 16 * S.CO * S.CQ * S.CDuh * S.KO * S.P.sbar ^ (2 * 3) ≤ 1
  KO_mu_sbar : S.KO * S.P.μ * S.P.sbar ^ (3 + 2) ≤ 1 / 2

/-- **The hypotheses of `lem:O`** for the level `j` and the ring-`j` time `τ`
(`09_relay.tex:234-239`; (SA) and (Det) are separate hypotheses): `1 ≤ j < n`, the clock is defined
up to level `j+1`, `τ ∈ [0, t̄♯_j]`; for every `t ∈ [0, τ/A_j]` and every ring `i ≤ j`:
`S_l(t) ∩ B_{6r_i} = ∅` for `l < i` (`HOutDefined`), `D_{i+1}(t) ⊂ B_{ar_i/8}` (`HInDefined`) and
`η_i(A_i t) ≤ 1`; `maj_j ≤ maj_*` on `[0,τ]`; and the smallness conditions `OSmall`. -/
structure OHyp (j : ℕ) (τ : ℝ) : Prop where
  one_le : 1 ≤ j
  lt_n : j < S.P.n
  clock : S.P.ClockUpTo (j + 1)
  τ_nonneg : 0 ≤ τ
  τ_le : τ ≤ S.P.tash j
  geom : ∀ t ∈ Icc (0 : ℝ) (τ / S.P.A j), ∀ i ∈ Finset.Icc 1 j,
    S.P.HOutDefined i t ∧ S.P.HInDefined i t ∧ S.eta i (S.P.A i * t) ≤ 1
  maj_le : ∀ τ' ∈ Icc (0 : ℝ) τ, S.maj j τ' ≤ S.majst
  small : S.OSmall

/-- **The conclusions of `lem:O`** for the level `j` and the ring-`j` time `τ`
(`09_relay.tex:240-249`): for `t ∈ [0, τ/A_j]` and `i < j`,
`maj_i(A_i t) ≤ (3/4) P̃_{i,j} maj_j(A_j t)`; for `t ∈ [0, τ/A_j]`,
`η^out_j(A_j t) ≤ θ_j maj_j(A_j t)`; and for `t ∈ (0, τ/A_j]` and `i ≤ j`, the hypotheses of
`thm:quiet` hold for ring `i` on `[0, A_i t]`, and so do its conclusions (a)–(c). -/
structure OConcl (j : ℕ) (τ : ℝ) : Prop where
  maj_le : ∀ t ∈ Icc (0 : ℝ) (τ / S.P.A j), ∀ i ∈ Finset.Ico 1 j,
    S.maj i (S.P.A i * t) ≤ 3 / 4 * S.Ptil i j * S.maj j (S.P.A j * t)
  etaOut_le : ∀ t ∈ Icc (0 : ℝ) (τ / S.P.A j),
    S.etaOut j (S.P.A j * t) ≤ S.theta j * S.maj j (S.P.A j * t)
  quiet : ∀ t ∈ Ioc (0 : ℝ) (τ / S.P.A j), ∀ i ∈ Finset.Icc 1 j,
    S.QuietHyp i (S.P.A i * t) ∧ S.QuietConcl i (S.P.A i * t)

/-! ### `prop:relay` (`09_relay.tex:390-439`) -/

/-- `C_Ξ(C₀, K₁) = max(1, 2C_Q) K₁ + (2C₂C(C₀) + C₀)/(σ_b min(1,σ_b)^m)` (`prop:relay`,
`09_relay.tex:392-395`). -/
def CXi (C₀ K₁ : ℝ) : ℝ :=
  max 1 (2 * S.CQ) * K₁ + (2 * S.C2 * S.Cact C₀ + C₀) / (S.sigb * min 1 S.sigb ^ 3)

/-- `Ξ_{j+1} = C_Ξ (1 + 1/(σ_b(μ-1))) δ₀ (κ♯_{j+1}/δ₀)^{1-γ_j} ⟨log(δ₀/κ♯_{j+1})⟩^{m+1}`
(`prop:relay`(ii), `09_relay.tex:430-431`), indexed by the level `j` (the term of ring `j+1` in the
bound of ring `j`). -/
def XiNext (C₀ K₁ : ℝ) (j : ℕ) : ℝ :=
  S.CXi C₀ K₁ * (1 + 1 / (S.sigb * (S.P.μ - 1))) * S.P.δ₀ *
    (S.P.ksh (j + 1) / S.P.δ₀) ^ (1 - S.gammaJ j) *
      Prelim.jap (Real.log (S.P.δ₀ / S.P.ksh (j + 1))) ^ (3 + 1)

/-- The right side of `eq:relay` with `Ξ` in place of `Ξ_{j+1}` (`09_relay.tex:426-428`):
`2C_M ε_j e^{x_j T_pin}[4C₂δ₀/(σ_b(μ-1)) + C_D(T_pin) + Ξ]`. `eq:relay` itself is
`maj_j(t̄♯_j) ≤ S.relayBound j (S.XiNext C₀ K₁ j)`; `lem:K1` assumes it with `Ξ ≤ δ₀/(σ_b(μ-1))`. -/
def relayBound (j : ℕ) (Ξ : ℝ) : ℝ :=
  2 * S.CM * S.P.eps j * Real.exp (S.P.xk j * S.P.Tpin) *
    (4 * S.C2 * S.P.δ₀ / (S.sigb * (S.P.μ - 1)) + CD S.P.Tpin + Ξ)

/-- The constant `C_M(2C_Q/(σ_b(μ-1)) + 1)` of `prop:relay`(o), (i) and `eq:relay-quiet`
(`09_relay.tex:420-423`, `:490`). -/
def Crelay : ℝ := S.CM * (2 * S.CQ / (S.sigb * (S.P.μ - 1)) + 1)

/-- **The hypotheses of `prop:relay`** for the level `j`, the ring-`j` time `τ` and the constants
`C₀ ≥ 1`, `K₁ > 0` (`09_relay.tex:399-415`; (SA), (Det) and `1 ≤ C₀`, `0 < K₁` are separate):
`1 ≤ j < n`, the clock is defined up to level `j+1`, `τ ∈ [0, t̄♯_j]`, and
* (H1) (Loc) at every `t ∈ [0, τ/A_j]`;
* (H2) `η^out_j ≤ θ_j maj_j` on `[0,τ]` and `θ_j τ ≤ 1/2`;
* (H3) if `j+1 < n`, the conclusions of `thm:quiet` hold for ring `j+1` on
  `[0, A_{j+1} min(τ/A_j, t♯_{j+1})]`;
* (H4) if `τ/A_j > t♯_{j+1}`: `maj_{j+1}(t̄♯_{j+1}) ≤ K₁κ♯_{j+1}`, and for
  `t ∈ [t♯_{j+1}, min(τ/A_j, T_{j+1})]`, `u = A_{j+1}(t - t♯_{j+1})`: `D_{j+2}(t) ⊂ B_{ar_{j+1}/8}`,
  `‖w_{j+1}(t)‖_{H^s} ≤ 2C₂ â_{j+1}(u)(1 + ρ̂_{j+1}(u))` and
  `‖h^in_{j+1}(t̄♯_{j+1} + u)‖_{C^{M_h}(N')} ≤ C₀ κ♯_{j+1} ⟨u⟩^m` (here `t̄♯_{j+1} + u = A_{j+1} t`).
Item (o) of the proposition uses only (H1) and (H3). -/
structure RelayHyp (C₀ K₁ : ℝ) (j : ℕ) (τ : ℝ) : Prop where
  one_le : 1 ≤ j
  lt_n : j < S.P.n
  clock : S.P.ClockUpTo (j + 1)
  τ_nonneg : 0 ≤ τ
  τ_le : τ ≤ S.P.tash j
  h1 : ∀ t ∈ Icc (0 : ℝ) (τ / S.P.A j), S.P.Loc t
  h2 : (∀ τ' ∈ Icc (0 : ℝ) τ, S.etaOut j τ' ≤ S.theta j * S.maj j τ') ∧ S.theta j * τ ≤ 1 / 2
  h3 : j + 1 < S.P.n →
    S.QuietConcl (j + 1) (S.P.A (j + 1) * min (τ / S.P.A j) (S.P.tsh (j + 1)))
  h4 : S.P.tsh (j + 1) < τ / S.P.A j →
    S.maj (j + 1) (S.P.tash (j + 1)) ≤ K₁ * S.P.ksh (j + 1) ∧
      ∀ t ∈ Icc (S.P.tsh (j + 1)) (min (τ / S.P.A j) (S.P.T (j + 1))),
        S.P.HInDefined (j + 1) t ∧
          Sob.normH S.s (S.P.w (j + 1) t) ≤
            2 * S.C2 * S.ahatK (j + 1) (S.P.activeTime (j + 1) t) *
              (1 + S.rhoHatK C₀ (j + 1) (S.P.activeTime (j + 1) t)) ∧
          S.etaIn (j + 1) (S.P.A (j + 1) * t) ≤
            C₀ * S.P.ksh (j + 1) * Prelim.jap (S.P.activeTime (j + 1) t) ^ 3

/-! ### `lem:Oprime` (`09_relay.tex:605-631`) -/

/-- `C_op(C₀, K₁) = 4C_OC_QC_M[2C_QK₁ + 4C₂ + σ_bK₁ + 2σ_b(2C₂C(C₀) + C₀) I_m(9σ/64)]`
(`lem:Oprime`, `09_relay.tex:607-610`). -/
def Cop (C₀ K₁ : ℝ) : ℝ :=
  4 * S.CO * S.CQ * S.CM * (2 * S.CQ * K₁ + 4 * S.C2 + S.sigb * K₁ +
    2 * S.sigb * (2 * S.C2 * S.Cact C₀ + C₀) * Ip 3 (9 * S.sigma0 / 64))

/-- `η_{b,k} = C_op s_{k-1}^{2m}/(σ_b(μ-1))` for `k ≥ 2` (`eq:etab`, `09_relay.tex:628`), and
`η_{b,1} = 0` (`10_parameters.tex`, (P6); `h^out_1 = 0`). -/
def etabK (C₀ K₁ : ℝ) (k : ℕ) : ℝ :=
  if 2 ≤ k then S.Cop C₀ K₁ * S.P.s (k - 1) ^ (2 * 3) / (S.sigb * (S.P.μ - 1)) else 0

/-- `η_b = C_op s̄^{2m}/(σ_b(μ-1))` (`eq:etab`, `09_relay.tex:628`). -/
def etab (C₀ K₁ : ℝ) : ℝ := S.Cop C₀ K₁ * S.P.sbar ^ (2 * 3) / (S.sigb * (S.P.μ - 1))

/-- **The hypotheses of `lem:Oprime`** for the level `k`, the time `t` and the constants `C₀`,
`K₁`, `C_F` (`09_relay.tex:614-624`; (SA), (Det), `C₀ ≥ 1`, `K₁ > 0`, `C_F ∈ (0, C₀]` are
separate): `1 ≤ k ≤ n`, the clock is defined up to level `k`, `t ∈ Ph_k`, and on `[0,t]`:
(Loc); if `k ≥ 2`, the hypotheses and conclusions of `lem:O` for `j = k-1` and `τ = A_{k-1}t`, and
`θ_{k-1} A_{k-1} t ≤ 1/2`; for `u ∈ [0, A_k(t - t♯_k)]` the active bound
`‖w_k(t♯_k + u/A_k)‖_{H^s} ≤ 2C₂ â_k(u)(1 + ρ̂_k(u))` and the inner bound
`‖h^in_k(t̄♯_k + u)‖_{C^{M_h}(N')} ≤ C_F κ♯_k ⟨u⟩^m`; and, if `k < n`, the conclusions of `thm:quiet`
for ring `k` on `[0, t̄♯_k]`, `maj_k(t̄♯_k) ≤ K₁κ♯_k`, and `D_{k+1}(t') ⊂ B_{ar_k/8}` for
`t' ∈ [t♯_k, t]`. The conclusion of the lemma is
`‖h^out_k(t̄♯_k + u)‖_{C^{M_h}(N')} ≤ η_{b,k} â_k(u)` on `[0, A_k(t - t♯_k)]` (with `η_{b,1} = 0`). -/
structure OprimeHyp (C₀ K₁ CF : ℝ) (k : ℕ) (t : ℝ) : Prop where
  one_le : 1 ≤ k
  le_n : k ≤ S.P.n
  clock : S.P.ClockUpTo k
  mem_phase : t ∈ S.P.Phase k
  loc : ∀ t' ∈ Icc (0 : ℝ) t, S.P.Loc t'
  outer : 2 ≤ k → S.OHyp (k - 1) (S.P.A (k - 1) * t) ∧ S.OConcl (k - 1) (S.P.A (k - 1) * t) ∧
    S.theta (k - 1) * (S.P.A (k - 1) * t) ≤ 1 / 2
  active : ∀ u ∈ Icc (0 : ℝ) (S.P.activeTime k t),
    Sob.normH S.s (S.P.w k (S.P.tsh k + u / S.P.A k)) ≤
      2 * S.C2 * S.ahatK k u * (1 + S.rhoHatK C₀ k u)
  inner : ∀ u ∈ Icc (0 : ℝ) (S.P.activeTime k t),
    S.etaIn k (S.P.tash k + u) ≤ CF * S.P.ksh k * Prelim.jap u ^ 3
  quiet : k < S.P.n → S.QuietConcl k (S.P.tash k) ∧ S.maj k (S.P.tash k) ≤ K₁ * S.P.ksh k ∧
    ∀ t' ∈ Icc (S.P.tsh k) t, S.P.HInDefined k t'

/-! ### Basic lemmas (fully proved) -/

theorem Ptil_def (i j : ℕ) : S.Ptil i j = ∏ p ∈ Finset.Ico i j, S.KO * S.P.eps p := rfl

theorem Ptil_self (i : ℕ) : S.Ptil i i = 1 := by
  simp [Ptil]

/-- `P̃_{i,l} P̃_{l,j} = P̃_{i,j}` for `i ≤ l ≤ j` (`09_relay.tex:267`). -/
theorem Ptil_mul {i l j : ℕ} (hil : i ≤ l) (hlj : l ≤ j) : S.Ptil i l * S.Ptil l j = S.Ptil i j :=
  Finset.prod_Ico_consecutive _ hil hlj

theorem theta_of_two_le {j : ℕ} (hj : 2 ≤ j) :
    S.theta j = 4 * S.CO * S.CQ * S.KO * S.P.s (j - 1) ^ (2 * 3) := by
  simp [theta, hj]

theorem theta_of_le_one {j : ℕ} (hj : j ≤ 1) : S.theta j = 0 := by
  simp [theta, show ¬ 2 ≤ j by omega]

theorem theta_one : S.theta 1 = 0 := S.theta_of_le_one le_rfl

theorem etabK_of_two_le (C₀ K₁ : ℝ) {k : ℕ} (hk : 2 ≤ k) :
    S.etabK C₀ K₁ k = S.Cop C₀ K₁ * S.P.s (k - 1) ^ (2 * 3) / (S.sigb * (S.P.μ - 1)) := by
  simp [etabK, hk]

theorem etabK_of_le_one (C₀ K₁ : ℝ) {k : ℕ} (hk : k ≤ 1) : S.etabK C₀ K₁ k = 0 := by
  simp [etabK, show ¬ 2 ≤ k by omega]

theorem etabK_one (C₀ K₁ : ℝ) : S.etabK C₀ K₁ 1 = 0 := S.etabK_of_le_one C₀ K₁ le_rfl

theorem relayBound_def (j : ℕ) (Ξ : ℝ) :
    S.relayBound j Ξ = 2 * S.CM * S.P.eps j * Real.exp (S.P.xk j * S.P.Tpin) *
      (4 * S.C2 * S.P.δ₀ / (S.sigb * (S.P.μ - 1)) + CD S.P.Tpin + Ξ) := rfl

theorem relayBound_mono (j : ℕ) {Ξ Ξ' : ℝ} (hΞ : Ξ ≤ Ξ') (h : 0 ≤ S.CM * S.P.eps j) :
    S.relayBound j Ξ ≤ S.relayBound j Ξ' := by
  unfold relayBound
  have h2 : 0 ≤ 2 * S.CM * S.P.eps j * Real.exp (S.P.xk j * S.P.Tpin) := by
    have := Real.exp_pos (S.P.xk j * S.P.Tpin)
    have : 0 ≤ 2 * (S.CM * S.P.eps j) := by positivity
    nlinarith
  exact mul_le_mul_of_nonneg_left (by linarith) h2

end Standing

end Relay

end NonUniqueEuler
