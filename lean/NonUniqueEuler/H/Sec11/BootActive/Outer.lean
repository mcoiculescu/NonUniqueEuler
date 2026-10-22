import NonUniqueEuler.H.Sec11.BootActive.Inner
import NonUniqueEuler.I.Sec9.Oprime
import NonUniqueEuler.I.Sec9.QuietTime
import NonUniqueEuler.I.Sec10.ThetaQuiet

/-!
# Helper for `P/Sec11/BootActive.lean`: (Init) and the outer field (`lem:Oprime`)

Step 4 of the proof of `prop:bootstrap` (`11_bootstrap.tex:410-460`):
* `boot_switch`: `‖w_k(t♯_k)‖_{H^s} ≤ C₀κ♯_k < C₂â_k(0)(1 + ρ̂_k(0))` (`eq:boot-switch` from Step 3,
  or `eq:boot-start` from Step 0 if `k = n`);
* `boot_init`: (Init) of `thm:active` for ring `k` (`eq:handoff` with `C_hand ≤ C₀`, or Step 0);
* `boot_oprimeHyp`: the hypotheses of `lem:Oprime` with `C₀`, `K₁`, `C_F` at the time `t'`:
  (Loc) from `lem:geometry`(c); for `k ≥ 2`, Step 2 for ring `k-1` at `t'` and
  `θ_{k-1}A_{k-1}t' ≤ θ_{k-1}τ̄♯_{k-1} ≤ ½` (`lem:quiet-time` at `t'`, with the levels `i ≥ k` from
  Step 3 and Step 0, and `lem:theta-quiet`); (BA3) for ring `k` on `(t♯_k, t']` from (BA°)(t') and at
  `t♯_k` from `boot_switch`; the inner bound `eq:boot-inner`; for `k < n`, Step 2 for ring `k` at
  `t♯_k`, `eq:handoff` and `lem:geometry`(b).
All proved.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

namespace BootActiveH

open RingData Datum

variable {S : Standing}

/-- `eq:boot-switch` / `eq:boot-start` (`11_bootstrap.tex:384-388`, `:245-250`). -/
theorem boot_switch {k : ℕ} (hk : k ∈ Finset.Icc 1 S.P.n) (h0 : S.BootStartConcl)
    (hlev : ∀ i ∈ Finset.Ico k S.P.n, S.HandoffStep i) :
    Sob.normH S.s (S.P.w k (S.P.tsh k)) ≤ S.C0 * S.P.ksh k ∧
      S.C0 * S.P.ksh k < S.C2 * S.ahatK k 0 * (1 + S.rhoHatK S.C0 k 0) := by
  obtain ⟨-, hkn⟩ := Finset.mem_Icc.1 hk
  rcases eq_or_lt_of_le hkn with hkn' | hkn'
  · rw [hkn', S.P.tsh_n]
    exact ⟨h0.start_le, h0.start_lt⟩
  · have h := hlev k (Finset.mem_Ico.2 ⟨le_rfl, hkn'⟩)
    exact ⟨h.switch_le.trans h.switch_C0, h.switch_lt⟩

/-- (Init) of `thm:active` for ring `k` with `C₀` (`11_bootstrap.tex:410-412`). -/
theorem boot_init {k : ℕ} (hk : k ∈ Finset.Icc 1 S.P.n) (h0 : S.BootStartConcl)
    (hlev : ∀ i ∈ Finset.Ico k S.P.n, S.HandoffStep i) : S.ActiveInitK S.C0 k := by
  obtain ⟨-, hkn⟩ := Finset.mem_Icc.1 hk
  rcases eq_or_lt_of_le hkn with hkn' | hkn'
  · rw [hkn']
    exact h0.init_n
  · obtain ⟨-, -, -, hw, hsupp⟩ := (hlev k (Finset.mem_Ico.2 ⟨le_rfl, hkn'⟩)).handoff
    refine ⟨?_, hsupp⟩
    have h1 : S.K1 * S.CQ * S.P.ksh k ≤ S.C0 * S.P.ksh k :=
      mul_le_mul_of_nonneg_right S.Chand_le_C0 (S.P.ksh_nonneg k)
    exact hw.trans h1

/-- (BA3) for ring `k` with the factor `2C₂` on `[0, ū]` in active time (`11_bootstrap.tex:448-449`):
at `u = 0` from `eq:boot-switch`/`eq:boot-start`, for `u > 0` from (BA°)(t'). -/
theorem boot_active_bound (hS : S.Holds) {k : ℕ} (hk : k ∈ Finset.Icc 1 S.P.n)
    (hc : S.P.ClockUpTo k) {t' : ℝ} (ht' : t' ∈ S.P.Phase k) (h0 : S.BootStartConcl)
    (hBA : S.BAcirc t') (hlev : ∀ i ∈ Finset.Ico k S.P.n, S.HandoffStep i) :
    ∀ u ∈ Icc (0 : ℝ) (S.P.activeTime k t'),
      Sob.normH S.s (S.P.w k (S.P.tsh k + u / S.P.A k)) ≤
        2 * S.C2 * S.ahatK k u * (1 + S.rhoHatK S.C0 k u) := by
  intro u hu
  obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.1 hk
  have hA := A_pos hS k
  have htsh0 : 0 ≤ S.P.tsh k := (activeConfig_units S hS hk1 hkn hc).1
  rcases eq_or_lt_of_le hu.1 with hu0 | hu0
  · subst hu0
    rw [zero_div, add_zero]
    have h := boot_switch hk h0 hlev
    have hC0 := S.C0_pos
    have hks := S.P.ksh_nonneg k
    have h1 : 0 ≤ S.C0 * S.P.ksh k := mul_nonneg hC0.le hks
    linarith [h.1, h.2]
  · have hmem := tsh_add_mem hS hu
    have hne : S.P.tsh k + u / S.P.A k ≠ S.P.tsh k := by
      have := div_pos hu0 hA
      intro h
      linarith
    have hba := hBA.ba3 (S.P.tsh k + u / S.P.A k) ⟨le_trans htsh0 hmem.1, hmem.2⟩ k hk hne
    have hact : S.P.ActiveAt k (S.P.tsh k + u / S.P.A k) := ⟨hc, hmem.1, hmem.2.trans ht'.2⟩
    have := hba hact
    rwa [activeTime_tsh_add hS] at this

/-- `t' ≤ t♯_{k-1}` for `t' ∈ Ph_k`, `2 ≤ k ≤ n` (`t♯_{k-1} = T_k + T_pin/A_k`). -/
theorem le_tsh_pred (hS : S.Holds) {k : ℕ} (hk2 : 2 ≤ k) (hkn : k ≤ S.P.n) {t' : ℝ}
    (ht' : t' ∈ S.P.Phase k) : t' ≤ S.P.tsh (k - 1) := by
  have h := S.P.tsh_eq_T_add (k := k - 1) (by omega)
  rw [show k - 1 + 1 = k by omega] at h
  rw [h]
  have := div_nonneg hS.Tpin_pos.le (A_pos hS k).le
  linarith [ht'.2]

/-- **The hypotheses of `lem:Oprime`** with `C₀`, `K₁`, `C_F` for ring `k` at the time `t'`
(`11_bootstrap.tex:437-459`). -/
theorem boot_oprimeHyp (S : Standing) (hS : S.Holds) (hL : S.ParamLists) {k : ℕ}
    (hk : k ∈ Finset.Icc 1 S.P.n) (hc : S.P.ClockUpTo k) {t' : ℝ} (ht' : t' ∈ S.P.Phase k)
    (htsh : S.P.tsh k < t') (h0 : S.BootStartConcl)
    (hBA : S.BAcirc t') (hgeo : S.GeometryConcl t')
    (hquiet : ∀ t'' ∈ Icc (0 : ℝ) t', S.QuietStepAt t'')
    (hlev : ∀ i ∈ Finset.Ico k S.P.n, S.HandoffStep i) :
    S.OprimeHyp S.C0 S.K1 S.CF k t' := by
  obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.1 hk
  have hpos := constPos hS
  have hDet := hL.det
  have htsh0 : 0 ≤ S.P.tsh k := (activeConfig_units S hS hk1 hkn hc).1
  have ht'0 : 0 ≤ t' := htsh0.trans htsh.le
  have hamp : k < S.P.n → S.Klo * S.P.s k ^ (3 + 2) ≤ S.P.ksh k := fun hkn' =>
    (hlev k (Finset.mem_Ico.2 ⟨le_rfl, hkn'⟩)).amp_lo
  refine
    { one_le := hk1
      le_n := hkn
      clock := hc
      mem_phase := ht'
      loc := hgeo.loc
      outer := ?_
      active := boot_active_bound hS hk hc ht' h0 hBA hlev
      inner := fun u hu => (boot_inner S hS hk hc ht' htsh hgeo hamp u hu).2
      quiet := ?_ }
  · intro hk2
    have hk1' : k - 1 + 1 = k := by omega
    have hj : k - 1 ∈ Finset.Ico 1 S.P.n := Finset.mem_Ico.2 ⟨by omega, by omega⟩
    have hle := le_tsh_pred hS hk2 hkn ht'
    have hqs := hquiet t' ⟨ht'0, le_rfl⟩ (k - 1) hj (Or.inr hle)
    have hlem := hqs.lemO (by rw [hk1']; exact hc)
    refine ⟨hlem.1, hlem.2, ?_⟩
    -- `θ_{k-1}A_{k-1}t' ≤ θ_{k-1}τ̄♯_{k-1} ≤ ½`
    have hqt := quiet_time S hS hDet hL.sbar.b6 (j := k - 1) (by omega) (by omega) ht'0
      (fun i hi _ _ => by
        have hki : k ≤ i := by have := (Finset.mem_Ioc.1 hi).1; omega
        exact ⟨hc.mono hki, fun hin => (hlev i (Finset.mem_Ico.2 ⟨hki, hin⟩)).amp_lo⟩)
      (fun _ => hle) h0.ksh_n.1
    have hθ := (theta_quiet S hS hL.sbar.b7 (j := k - 1) (by omega) (by omega)).2
    have hθ0 := theta_nonneg hpos hS (k - 1)
    calc S.theta (k - 1) * (S.P.A (k - 1) * t') ≤ S.theta (k - 1) * S.tauBarSh (k - 1) :=
          mul_le_mul_of_nonneg_left hqt hθ0
      _ ≤ min (1 / 2) (1 / (4 * Eig.Cls S.P.χ * S.K1)) := hθ
      _ ≤ 1 / 2 := min_le_left _ _
  · intro hkn'
    have hqs := hquiet (S.P.tsh k) ⟨htsh0, htsh.le⟩ k (Finset.mem_Ico.2 ⟨hk1, hkn'⟩)
      (Or.inr le_rfl)
    refine ⟨hqs.concl, (hlev k (Finset.mem_Ico.2 ⟨le_rfl, hkn'⟩)).handoff.2.2.1, ?_⟩
    intro t'' ht''
    have hnd : ¬ S.P.DebrisAt k t'' := fun h => absurd h.2 (not_lt.2 (ht''.2.trans ht'.2))
    exact (hgeo.ring t'' ⟨htsh0.trans ht''.1, ht''.2⟩ k hk hnd).2.1

/-- **The outer field** (`lem:Oprime`, `11_bootstrap.tex:437-460`): on `[0, ū]`,
`h^out_k(t̄♯_k + u) ∈ C^{M_h}(N')` with `η^out_k(t̄♯_k + u) ≤ η_{b,k}â_k(u)`; and `η_{b,k} ≤ η_b`. -/
theorem boot_outer (S : Standing) (hS : S.Holds) (hL : S.ParamLists) {k : ℕ}
    (hk : k ∈ Finset.Icc 1 S.P.n) (hc : S.P.ClockUpTo k) {t' : ℝ} (ht' : t' ∈ S.P.Phase k)
    (htsh : S.P.tsh k < t') (h0 : S.BootStartConcl)
    (hBA : S.BAcirc t') (hgeo : S.GeometryConcl t')
    (hquiet : ∀ t'' ∈ Icc (0 : ℝ) t', S.QuietStepAt t'')
    (hlev : ∀ i ∈ Finset.Ico k S.P.n, S.HandoffStep i) :
    (∀ u ∈ Icc (0 : ℝ) (S.P.activeTime k t'), MemCk S.Mh annN' (S.P.hOut k (S.P.tash k + u)) ∧
      S.etaOut k (S.P.tash k + u) ≤ S.etabK S.C0 S.K1 k * S.ahatK k u) ∧
    S.etabK S.C0 S.K1 k ≤ S.etab S.C0 S.K1 := by
  have hpos := constPos hS
  exact Oprime S hS hL.det S.one_le_C0 hpos.K1_pos hpos.CF_mem
    (boot_oprimeHyp S hS hL hk hc ht' htsh h0 hBA hgeo hquiet hlev)

end BootActiveH

end Relay

end NonUniqueEuler
