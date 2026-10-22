import NonUniqueEuler.H.Sec11.BootQuietSize.Basic
import NonUniqueEuler.I.Sec9.QuietTime
import NonUniqueEuler.I.Sec10.ThetaQuiet

/-!
# Helper for `P/Sec11/BootQuietSize.lean`: the hypotheses of `prop:relay` in Step 5

Helper of the proof of Step 5 of `prop:bootstrap` (`11_bootstrap.tex:497-511`): for a ring `j < n`
with `t♯_j` defined and quiet at `t'`, the hypotheses (H1)–(H4) of `prop:relay` hold for `j` and
`τ = A_jt'` with `C₀ = S.C0`, `K₁ = S.K1` (`relayHyp`):
* (H1) (Loc) on `[0, t']`: `lem:geometry`(c);
* (H2) `η^out_j ≤ θ_jmaj_j` on `[0, τ]` (Step 2, `lem:O`) and `θ_jτ ≤ ½` (`lem:quiet-time` at `t'`
  and `lem:theta-quiet`; `theta_tau_le`);
* (H3) Step 2 for ring `j+1` at `min(t', t♯_{j+1})`;
* (H4) if `t' > t♯_{j+1}`, as in Step 3 with `k = j`: `eq:handoff` for ring `j+1` (or `t̄♯_n = 0`),
  `lem:geometry`(b), (BA°)(t') with `eq:boot-switch`/`eq:boot-start` at `t♯_{j+1}`, and
  `eq:boot-inner` for ring `j+1` with `C_F ≤ C₀`.
All proved.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

namespace BootQuietSizeH

open RingData Datum

variable {S : Standing}

/-- **`θ_jA_jt' ≤ ½`** (`11_bootstrap.tex:500-505`): `lem:quiet-time` at the time `t'` gives
`A_jt' ≤ τ̄♯_j` (the levels `i ∈ (j, n)` with `t♯_i ≤ t'` by Step 3, `κ♯_n ≥ ½κ_seed` by Step 0), and
`lem:theta-quiet` gives `θ_jτ̄♯_j ≤ ½`. -/
theorem theta_tau_le (hS : S.Holds) (hL : S.ParamLists) {t' : ℝ} (ht0 : 0 ≤ t')
    (h0 : S.BootStartConcl)
    (hlev : ∀ i ∈ Finset.Ico 1 S.P.n, S.P.ClockUpTo (i + 1) → S.P.tsh i ≤ t' → S.HandoffStep i)
    {j : ℕ} (hj : j ∈ Finset.Ico 1 S.P.n) (hq : S.P.QuietAt j t') :
    S.theta j * (S.P.A j * t') ≤ 1 / 2 := by
  obtain ⟨hj1, hjn⟩ := Finset.mem_Ico.1 hj
  have hpos := constPos hS
  have hcl : ∀ i ∈ Finset.Ioc j S.P.n, S.P.ClockUpTo (i + 1) → S.P.tsh i ≤ t' →
      S.P.ClockUpTo i ∧ (i < S.P.n → S.Klo * S.P.s i ^ (3 + 2) ≤ S.P.ksh i) := by
    intro i hi hci hti
    obtain ⟨hji, hin⟩ := Finset.mem_Ioc.1 hi
    by_cases hlt : i < S.P.n
    · have hH := hlev i (Finset.mem_Ico.2 ⟨by omega, hlt⟩) hci hti
      exact ⟨hH.clock, fun _ => hH.amp_lo⟩
    · have hieq : i = S.P.n := by omega
      exact ⟨hieq ▸ h0.clock_n, fun h => absurd h hlt⟩
  have htj : S.P.ClockUpTo (j + 1) → t' ≤ S.P.tsh j := fun hc =>
    hq.resolve_left (not_not.2 hc)
  have hτ := quiet_time S hS hL.det hL.sbar.b6 hj1 hjn ht0 hcl htj h0.ksh_n.1
  have hθ := (theta_quiet S hS hL.sbar.b7 hj1 hjn).2
  have hθ0 := theta_nonneg hpos hS j
  calc S.theta j * (S.P.A j * t') ≤ S.theta j * S.tauBarSh j :=
        mul_le_mul_of_nonneg_left hτ hθ0
    _ ≤ min (1 / 2) (1 / (4 * Eig.Cls S.P.χ * S.K1)) := hθ
    _ ≤ 1 / 2 := min_le_left _ _

/-- **(BA3) for ring `j+1` on `[t♯_{j+1}, t']`** (`11_bootstrap.tex:357-360`, used in Step 5 as in
Step 3): (BA°)(t') away from `t♯_{j+1}`, and `eq:boot-switch` (`j+1 < n`) or `eq:boot-start`
(`j+1 = n`) at `t♯_{j+1}`. -/
theorem ba3_next {t' : ℝ} (h0 : S.BootStartConcl) (hBA : S.BAcirc t')
    (hlev : ∀ i ∈ Finset.Ico 1 S.P.n, S.P.ClockUpTo (i + 1) → S.P.tsh i ≤ t' → S.HandoffStep i)
    {j : ℕ} (hj : j ∈ Finset.Ico 1 S.P.n) (hc : S.P.ClockUpTo (j + 1))
    (hlt : S.P.tsh (j + 1) < t') {t : ℝ} (ht0 : 0 ≤ t) (ht : t ∈ Icc (S.P.tsh (j + 1)) t')
    (htT : t ≤ S.P.T (j + 1)) :
    Sob.normH S.s (S.P.w (j + 1) t) ≤
      2 * S.C2 * S.ahatK (j + 1) (S.P.activeTime (j + 1) t) *
        (1 + S.rhoHatK S.C0 (j + 1) (S.P.activeTime (j + 1) t)) := by
  obtain ⟨hj1, hjn⟩ := Finset.mem_Ico.1 hj
  have hmem : j + 1 ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  by_cases heq : t = S.P.tsh (j + 1)
  · rw [heq]
    have hu : S.P.activeTime (j + 1) (S.P.tsh (j + 1)) = 0 := by
      simp only [Approx.activeTime, sub_self, mul_zero]
    rw [hu]
    have hb : Sob.normH S.s (S.P.w (j + 1) (S.P.tsh (j + 1))) ≤ S.C0 * S.P.ksh (j + 1) ∧
        S.C0 * S.P.ksh (j + 1) <
          S.C2 * S.ahatK (j + 1) 0 * (1 + S.rhoHatK S.C0 (j + 1) 0) := by
      by_cases hjn1 : j + 1 < S.P.n
      · have hH := hlev (j + 1) (Finset.mem_Ico.2 ⟨by omega, hjn1⟩)
          (hc.mono (Nat.le_succ _)) hlt.le
        exact ⟨hH.switch_le.trans hH.switch_C0, hH.switch_lt⟩
      · have hjeq : j + 1 = S.P.n := by omega
        rw [hjeq, S.P.tsh_n]
        exact ⟨h0.start_le, h0.start_lt⟩
    have hk0 : 0 ≤ S.C0 * S.P.ksh (j + 1) := mul_nonneg S.C0_pos.le (S.P.ksh_nonneg _)
    have h2 : 2 * S.C2 * S.ahatK (j + 1) 0 * (1 + S.rhoHatK S.C0 (j + 1) 0) =
        2 * (S.C2 * S.ahatK (j + 1) 0 * (1 + S.rhoHatK S.C0 (j + 1) 0)) := by ring
    rw [h2]
    linarith [hb.1, hb.2]
  · exact hBA.ba3 t ⟨ht0, ht.2⟩ (j + 1) hmem heq ⟨hc, ht.1, htT⟩

/-- **The hypotheses of `prop:relay` in Step 5** (`11_bootstrap.tex:497-511`): for `j < n` with
`t♯_j` defined and `t' ≤ t♯_j`, `S.RelayHyp S.C0 S.K1 j (A_jt')`. -/
theorem relayHyp (hS : S.Holds) (hL : S.ParamLists) {t' : ℝ} (ht0 : 0 ≤ t')
    (h0 : S.BootStartConcl) (hBA : S.BAcirc t') (hgeo : S.GeometryConcl t')
    (hquiet : ∀ t'' ∈ Icc (0 : ℝ) t', S.QuietStepAt t'')
    (hlev : ∀ i ∈ Finset.Ico 1 S.P.n, S.P.ClockUpTo (i + 1) → S.P.tsh i ≤ t' → S.HandoffStep i)
    (hact : ∀ i ∈ Finset.Icc 1 S.P.n, S.P.ClockUpTo i → S.P.tsh i < t' →
      S.ActiveStep i (S.P.activeTime i (min t' (S.P.T i))))
    {j : ℕ} (hj : j ∈ Finset.Ico 1 S.P.n) (hc : S.P.ClockUpTo (j + 1)) (hq : t' ≤ S.P.tsh j) :
    S.RelayHyp S.C0 S.K1 j (S.P.A j * t') := by
  obtain ⟨hj1, hjn⟩ := Finset.mem_Ico.1 hj
  have hpos := constPos hS
  have hA := A_pos hS j
  have hdiv : S.P.A j * t' / S.P.A j = t' := mul_div_cancel_left₀ t' hA.ne'
  have hqa : S.P.QuietAt j t' := Or.inr hq
  have hQ := hquiet t' ⟨ht0, le_rfl⟩ j hj hqa
  have hO := (hQ.lemO hc).2
  have hmem : j + 1 ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hsh0 : 0 ≤ S.P.tsh (j + 1) :=
    tsh_nonneg hS (by omega : 1 ≤ j + 1) hc (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩)
  refine
    { one_le := hj1
      lt_n := hjn
      clock := hc
      τ_nonneg := mul_nonneg hA.le ht0
      τ_le := mul_le_mul_of_nonneg_left hq hA.le
      h1 := ?_
      h2 := ⟨?_, theta_tau_le hS hL ht0 h0 hlev hj hqa⟩
      h3 := ?_
      h4 := ?_ }
  · rw [hdiv]
    exact hgeo.loc
  · intro τ' hτ'
    have hmem' : τ' / S.P.A j ∈ Icc (0 : ℝ) (S.P.A j * t' / S.P.A j) :=
      ⟨div_nonneg hτ'.1 hA.le, div_le_div_of_nonneg_right hτ'.2 hA.le⟩
    have := hO.etaOut_le (τ' / S.P.A j) hmem'
    rwa [mul_div_cancel₀ τ' hA.ne'] at this
  · intro hjn1
    rw [hdiv]
    have ht1 : min t' (S.P.tsh (j + 1)) ∈ Icc (0 : ℝ) t' :=
      ⟨le_min ht0 hsh0, min_le_left _ _⟩
    have hq1 : S.P.QuietAt (j + 1) (min t' (S.P.tsh (j + 1))) := Or.inr (min_le_right _ _)
    exact (hquiet _ ht1 (j + 1) (Finset.mem_Ico.2 ⟨by omega, hjn1⟩) hq1).concl
  · rw [hdiv]
    intro hlt
    refine ⟨?_, ?_⟩
    · by_cases hjn1 : j + 1 < S.P.n
      · have hH := hlev (j + 1) (Finset.mem_Ico.2 ⟨by omega, hjn1⟩)
          (hc.mono (Nat.le_succ _)) hlt.le
        exact hH.handoff.2.2.1
      · have hjeq : j + 1 = S.P.n := by omega
        rw [hjeq, Approx.tash_def, S.P.tsh_n, mul_zero, S.maj_zero]
        exact mul_nonneg hpos.K1_pos.le (S.P.ksh_nonneg _)
    · intro t ht
      have ht0' : 0 ≤ t := le_trans hsh0 ht.1
      have htt' : t ≤ t' := le_trans ht.2 (min_le_left _ _)
      have htT : t ≤ S.P.T (j + 1) := le_trans ht.2 (min_le_right _ _)
      refine ⟨?_, ba3_next h0 hBA hlev hj hc hlt ht0' ⟨ht.1, htt'⟩ htT, ?_⟩
      · exact (hgeo.ring t ⟨ht0', htt'⟩ (j + 1) hmem
          (fun h => absurd h.2 (not_lt.2 htT))).2.1
      · have hAS := hact (j + 1) hmem hc hlt
        have hA1 := A_pos hS (j + 1)
        have hu : S.P.activeTime (j + 1) t ∈
            Icc (0 : ℝ) (S.P.activeTime (j + 1) (min t' (S.P.T (j + 1)))) := by
          simp only [Approx.activeTime]
          refine ⟨mul_nonneg hA1.le (by linarith [ht.1]), ?_⟩
          exact mul_le_mul_of_nonneg_left (by linarith [ht.2]) hA1.le
        have hin := (hAS.inner _ hu).2
        have heq : S.P.tash (j + 1) + S.P.activeTime (j + 1) t = S.P.A (j + 1) * t := by
          simp only [Approx.tash_def, Approx.activeTime]
          ring
        rw [heq] at hin
        refine hin.trans ?_
        have hJ : 0 ≤ S.P.ksh (j + 1) * Prelim.jap (S.P.activeTime (j + 1) t) ^ 3 :=
          mul_nonneg (S.P.ksh_nonneg _) (pow_nonneg (Prelim.jap_nonneg _) _)
        have := mul_le_mul_of_nonneg_right S.CF_le_C0 hJ
        calc S.CF * S.P.ksh (j + 1) * Prelim.jap (S.P.activeTime (j + 1) t) ^ 3 =
              S.CF * (S.P.ksh (j + 1) * Prelim.jap (S.P.activeTime (j + 1) t) ^ 3) := by ring
          _ ≤ S.C0 * (S.P.ksh (j + 1) * Prelim.jap (S.P.activeTime (j + 1) t) ^ 3) := this
          _ = S.C0 * S.P.ksh (j + 1) * Prelim.jap (S.P.activeTime (j + 1) t) ^ 3 := by ring

end BootQuietSizeH

end Relay

end NonUniqueEuler
