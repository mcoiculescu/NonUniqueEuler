import NonUniqueEuler.H.Sec11.BootActive.DriftStep

/-!
# Proof: Step 4 of the proof of `prop:bootstrap` (the active phase of ring `k`) and
`eq:boot-inner`

Proof of `I/Sec11/BootActive.lean` (`11_bootstrap.tex:390-484`). The steps are in the helpers
`H/Sec11/BootActive/*.lean`:
* `ū = A_k(t' - t♯_k) ∈ (0, T̂_k]` (`Basic.lean`);
* (Field), inner part, `eq:boot-inner` (`Inner.lean`, `boot_inner`);
* (Init) (`Outer.lean`, `boot_init`), (Field), outer part, by `lem:Oprime` (`boot_outer`);
* (Coef): the hypotheses of `lem:drift` (`DriftStep.lean`, `boot_driftHyp`) and
  `C_ls η_{b,k} T̂_k ≤ 1/32` (`boot_cls`), then `lem:drift` (`drift`) with `r_T(T_pin) ≤ 1/64` of (P3);
* (Small) `κ♯_k ≤ 2κ_seed ≤ κ₀(C₀)`: `κ♯_k ≤ K_up s_k^{m+2} ≤ K_up s̄^{m+2} ≤ κ_seed` (Step 3, (B6)) for
  `k < n`, `κ♯_n ≤ 2κ_seed` (Step 0), and (κ4);
* `thm:active`, `cor:active-moment` for ring `k` on `[0, ū]` (`active_ring`).
The hypothesis `t' ≤ T_end` is not used (it only places `t'` in the range of the bootstrap).
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

open RingData Datum

namespace BootActiveH

/-- `s_k ≤ s̄` (`s_k = s̄/(2μ)^k`, `μ > 1`). -/
theorem s_le_sbar {S : Standing} (hS : S.Holds) (k : ℕ) : S.P.s k ≤ S.P.sbar := by
  rw [Approx.s_def, ratio]
  have hμ := hS.one_lt_μ
  exact div_le_self hS.sbar_pos.le (one_le_pow₀ (by linarith))

/-- (Small) of `thm:active` for ring `k`: `κ♯_k ≤ κ₀(C₀)` (`11_bootstrap.tex:406-409`). -/
theorem boot_small {S : Standing} (hS : S.Holds) (hL : S.ParamLists) {k : ℕ}
    (hk : k ∈ Finset.Icc 1 S.P.n) (hc : S.P.ClockUpTo k) (h0 : S.BootStartConcl)
    (hlev : ∀ i ∈ Finset.Ico k S.P.n, S.HandoffStep i) : S.P.ksh k ≤ S.kappa0 S.C0 := by
  obtain ⟨-, hkn⟩ := Finset.mem_Icc.1 hk
  have hk0 : 0 < S.P.ksh k := (hc.ksh_mem le_rfl hkn).1
  have hκs := hS.kseed_pos
  have hle : S.P.ksh k ≤ 2 * S.P.κs := by
    rcases eq_or_lt_of_le hkn with hkn' | hkn'
    · rw [hkn']
      exact h0.ksh_n.2
    · have hup := (hlev k (Finset.mem_Ico.2 ⟨le_rfl, hkn'⟩)).amp_up
      have hKup := (constPos hS).Kup_pos
      have hs0 := (hS.valid.s_pos k).le
      have hs := s_le_sbar hS k
      have h1 : S.Kup * S.P.s k ^ (3 + 2) ≤ S.Kup * S.P.sbar ^ (3 + 2) := by gcongr
      have h2 := hL.sbar.b6
      linarith
  exact (hL.kappa.2 (S.P.ksh k) ⟨hk0, hle⟩).k4

end BootActiveH

/-- **Step 4 of the proof of `prop:bootstrap`** (`11_bootstrap.tex:390-484`), with `eq:boot-inner`:
the active phase of ring `k` up to the time `t' ∈ Ph_k`, `t♯_k < t' ≤ T_end`. Given Step 0, (BA°)(t'),
`lem:geometry` with `t'`, Step 2 on `[0, t']` and Step 3 at the levels `i ∈ [k, n)`, the conclusions of
Step 4 hold for ring `k` with `ū = A_k(t' - t♯_k)` (`S.ActiveStep k ū`). -/
theorem boot_active (S : Standing) (hS : S.Holds) (hL : S.ParamLists) {k : ℕ}
    (hk : k ∈ Finset.Icc 1 S.P.n) (hc : S.P.ClockUpTo k) {t' : ℝ} (ht' : t' ∈ S.P.Phase k)
    (htsh : S.P.tsh k < t') (hTend : t' ≤ S.P.Tend) (h0 : S.BootStartConcl)
    (hBA : S.BAcirc t') (hgeo : S.GeometryConcl t')
    (hquiet : ∀ t'' ∈ Icc (0 : ℝ) t', S.QuietStepAt t'')
    (hlev : ∀ i ∈ Finset.Ico k S.P.n, S.HandoffStep i) :
    S.ActiveStep k (S.P.activeTime k t') := by
  obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.1 hk
  have hpos := BootActiveH.constPos hS
  have hubar0 := BootActiveH.activeTime_pos hS htsh
  have hubarT := BootActiveH.activeTime_le_That hS hkn ht'.2
  have hamp : k < S.P.n → S.Klo * S.P.s k ^ (3 + 2) ≤ S.P.ksh k := fun hkn' =>
    (hlev k (Finset.mem_Ico.2 ⟨le_rfl, hkn'⟩)).amp_lo
  -- (Field), inner part: `eq:boot-inner`
  have hinner := BootActiveH.boot_inner S hS hk hc ht' htsh hgeo hamp
  -- (Field), outer part: `lem:Oprime`
  have houter := BootActiveH.boot_outer S hS hL hk hc ht' htsh h0 hBA hgeo hquiet hlev
  -- (Coef): `lem:drift`
  have hdriftH := BootActiveH.boot_driftHyp S hS hL hk hc ht' htsh h0 hBA hgeo hquiet hlev
  have hcls := BootActiveH.boot_cls S hS hL hk hc h0 hlev houter.2
  have hη := BootActiveH.etabK_nonneg hpos hS k
  have hdr := drift S hS hL.det hk1 hkn hc ⟨hubar0.le, hubarT⟩ hη hdriftH
  have hdr2 := hdr.2 hL.structural.p3.rT_le hcls
  have hcoef : S.CoefK S.C0 k (S.P.activeTime k t') := hdr2.2.1 S.C0 S.C0_pos.le
  -- (Field) of `thm:active` with `h₁ = h^in_k(t̄♯_k + ·)`, `h₂ = h^out_k(t̄♯_k + ·)`
  have hM := S.M_le_Mh
  have hfield : S.ActiveFieldK S.C0 (S.etabK S.C0 S.K1 k) k (S.P.activeTime k t') := by
    refine ⟨fun u => S.P.hIn k (S.P.tash k + u), fun u => S.P.hOut k (S.P.tash k + u),
      fun u hu => ?_⟩
    have hi := hinner u hu
    have ho := houter.1 u hu
    refine ⟨⟨univ, isOpen_univ, subset_univ _, fun x _ => rfl⟩, hi.1.mono_order hM, ?_,
      ho.1.mono_order hM, (normCk_mono_order ho.1 hM).trans ho.2⟩
    have hks := S.P.ksh_nonneg k
    have hj := BootActiveH.jap_nonneg u
    calc normCk S.M annN' (S.P.hIn k (S.P.tash k + u))
        ≤ S.etaIn k (S.P.tash k + u) := normCk_mono_order hi.1 hM
      _ ≤ S.CF * S.P.ksh k * Prelim.jap u ^ 3 := hi.2
      _ ≤ S.C0 * S.P.ksh k * Prelim.jap u ^ 3 := by
          gcongr
          exact S.CF_le_C0
  -- `η_{b,k} ∈ [0, η_max]` ((B8))
  have hηmax : S.etabK S.C0 S.K1 k ∈ Icc (0 : ℝ) OneRing.etaMax := by
    refine ⟨hη, houter.2.trans (hL.sbar.b8_etab.trans ?_)⟩
    simp only [OneRing.etaMax]
    norm_num
  -- `thm:active` and `cor:active-moment` for ring `k` on `[0, ū]`
  have hact := active_ring S hS S.one_le_C0 hk1 hkn hc hubar0 hdriftH.geom hηmax
    (BootActiveH.boot_init hk h0 hlev) hfield hcoef (BootActiveH.boot_small hS hL hk hc h0 hlev)
  rw [min_eq_left hubarT] at hact
  exact
    { ubar_pos := hubar0
      ubar_le := hubarT
      inner := hinner
      outer := houter.1
      field := hfield
      drift := hdriftH
      cls := hcls
      coefK := hcoef
      coef := hdr2.2.2
      concl := hact }

end Relay

end NonUniqueEuler
