import NonUniqueEuler.Defs.Sec11.Extra2Boot
import NonUniqueEuler.H.Sec11.BootHandoff.Kick
import NonUniqueEuler.H.Sec11.BootHandoff.Relay
import NonUniqueEuler.I.Sec9.KickTrue
import NonUniqueEuler.I.Sec9.Relay
import NonUniqueEuler.I.Sec9.Gamma
import NonUniqueEuler.I.Sec9.K1
import NonUniqueEuler.I.Sec9.Handoff
import NonUniqueEuler.I.Sec9.Amp

/-!
# Proof: Step 3 of the proof of `prop:bootstrap` (the hand-off of ring `k` at `t♯_k`)

Proof of the interface `I/Sec11/BootHandoff.lean` (`11_bootstrap.tex:298-388`). The steps, in the
manuscript's order:
1. `eq:boot-kappa` (`BootHandoffH.kappa`);
2. `lem:kicktrue` (`kicktrue`, hypotheses `BootHandoffH.kickTrueHyp`): `eq:boot-kick`;
3. `lem:quiet-time`, `lem:theta-quiet` (`BootHandoffH.theta`): `eq:boot-theta`; `prop:relay`
   (`relay`, hypotheses `BootHandoffH.relayHyp`): `eq:relay` at `t̄♯_k`; `lem:gamma` and (κ7)
   (`BootHandoffH.xiNext_le`); `lem:K1` (`K1_bound`): `maj_k(t̄♯_k) ≤ Āε_k` and
   `2maj_k(t̄♯_k) ≤ ½K₁|c^in_k|`;
4. `lem:handoff` (`handoff`): `eq:handoff`; `cor:amp` (`amp`): the amplitude bounds; then the clock
   is defined up to level `k`;
5. `eq:boot-switch`.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

open RingData Datum

/-- **Step 3 of the proof of `prop:bootstrap`** (`11_bootstrap.tex:298-388`): the hand-off of ring
`k < n` at `t♯_k`. Given Step 0, (BA°)(t♯_k), `lem:geometry` with `t♯_k`, Step 2 on `[0, t♯_k]`, Step 3
at the levels `i ∈ (k, n)` and Step 4 for ring `k+1` on `Ph_{k+1}`, the conclusions of Step 3 hold at
the level `k` (`S.HandoffStep k`). -/
theorem boot_handoff (S : Standing) (hS : S.Holds) (hL : S.ParamLists) {k : ℕ}
    (hk : k ∈ Finset.Ico 1 S.P.n) (hc : S.P.ClockUpTo (k + 1)) (hkt : S.P.tsh k ≤ S.P.Tend)
    (h0 : S.BootStartConcl) (hBA : S.BAcirc (S.P.tsh k)) (hgeo : S.GeometryConcl (S.P.tsh k))
    (hquiet : ∀ t' ∈ Icc (0 : ℝ) (S.P.tsh k), S.QuietStepAt t')
    (hdeep : ∀ i ∈ Finset.Ioo k S.P.n, S.HandoffStep i)
    (hact : S.ActiveStep (k + 1) (S.P.That (k + 1))) : S.HandoffStep k := by
  have hk1 : 1 ≤ k := (Finset.mem_Ico.1 hk).1
  have hkn : k < S.P.n := (Finset.mem_Ico.1 hk).2
  have hkI : k ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.2 ⟨hk1, hkn.le⟩
  have hpos := BootHandoffH.constPos hS
  have hDet := hL.det
  have hK1 := hpos.K1_pos
  have htsh0 := BootHandoffH.tsh_nonneg hS hk1 hkn hc
  -- Step 3.1: `eq:boot-kappa`
  obtain ⟨hκpos, hκle⟩ := BootHandoffH.kappa hS hL hk hc h0 hdeep
  -- Step 3.2: `lem:kicktrue`, `eq:boot-kick`
  obtain ⟨hqs, hkick⟩ := kicktrue S hS hDet S.one_le_C0 hK1 hk1 hkn hc
    (BootHandoffH.kickTrueHyp hS hL hk hc h0 hgeo hquiet hdeep hact)
  have hkickT := hkick S.P.Tpin ⟨hS.Tpin_pos.le, le_rfl⟩
  -- Step 3.3: `eq:boot-theta`, `eq:relay`, `lem:K1`
  obtain ⟨hθle, hθsmall⟩ := BootHandoffH.theta hS hL hk hc h0 hdeep
  have hθhalf : S.theta k * S.P.tash k ≤ 1 / 2 := hθle.trans (hθsmall.trans (min_le_left _ _))
  have hrelay : S.maj k (S.P.tash k) ≤ S.relayBound k (S.XiNext S.C0 S.K1 k) :=
    (relay S hS hDet S.one_le_C0 hK1
      (BootHandoffH.relayHyp hS hk hc h0 hBA hgeo hquiet hdeep hact hθhalf)).2.2.2.1 rfl
  have hdef : ∀ t ∈ Icc (0 : ℝ) (S.P.tsh k), S.P.HDefined k t := fun t ht =>
    (hgeo.ring t ht k hkI (BootHandoffH.not_debris_of_le_tsh hS hkI ht.2)).2.2.1
  have hin : ∀ t ∈ Icc (0 : ℝ) (S.P.tsh k), S.P.HInDefined k t := fun t ht => (hdef t ht).1
  have hγ := (gamma S hS hDet k hk).1
  obtain ⟨hm1, hm2, hm3⟩ := K1_bound S hS hDet hk1 hkn hc hdef hrelay
    (BootHandoffH.xiNext_le hS hL hk hc hκle hγ)
  have hmaj : S.maj k (S.P.tash k) ≤ S.Abar * S.P.eps k := hm1.trans hm2
  have hcin : 2 * S.maj k (S.P.tash k) ≤ 1 / 2 * S.K1 * ‖S.P.cinK k‖ :=
    (hm3 (S.P.kickQs k) hqs.1 hkickT.1).2
  -- Step 3.4: `lem:handoff`, `eq:handoff`
  have hmaj0 : 0 ≤ S.maj k (S.P.tash k) :=
    BootHandoffH.maj_nonneg k (mul_nonneg (BootHandoffH.A_pos hS k).le htsh0)
  have hθ0 := BootHandoffH.theta_nonneg hpos hS k
  have hCls := hpos.Cls_pos
  have hθK : Eig.Cls S.P.χ * S.theta k * S.P.tash k * S.K1 ≤ 1 / 4 := by
    have h1 : S.theta k * S.P.tash k ≤ 1 / (4 * Eig.Cls S.P.χ * S.K1) :=
      hθle.trans (hθsmall.trans (min_le_right _ _))
    have h2 : 0 < 4 * Eig.Cls S.P.χ * S.K1 := by positivity
    rw [le_div_iff₀ h2] at h1
    nlinarith [h1]
  have hsmall : Eig.ellNorm S.P.χ * S.CQ * S.K1 * S.maj k (S.P.tash k) ≤ 1 / 2 := by
    have hc1 : 0 ≤ Eig.ellNorm S.P.χ * S.CQ * S.K1 :=
      mul_nonneg (mul_nonneg hpos.ellNorm_pos.le hpos.CQ_nonneg) hK1.le
    have he : S.Abar * S.P.eps k ≤ S.Abar * S.P.μ * S.P.sbar ^ (3 + 2) := by
      rw [Approx.eps, mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hpos.Abar_pos.le
      exact mul_le_mul_of_nonneg_left (BootHandoffH.s_pow_le hS k)
        (by linarith [hS.one_lt_μ])
    have h11 := hL.sbar.b11_handoff
    calc Eig.ellNorm S.P.χ * S.CQ * S.K1 * S.maj k (S.P.tash k)
        ≤ Eig.ellNorm S.P.χ * S.CQ * S.K1 * (S.Abar * S.P.μ * S.P.sbar ^ (3 + 2)) :=
          mul_le_mul_of_nonneg_left (hmaj.trans he) hc1
      _ = Eig.ellNorm S.P.χ * S.CQ * S.K1 * S.Abar * S.P.μ * S.P.sbar ^ (3 + 2) := by ring
      _ ≤ 1 / 2 := h11
  have hHO : S.HandoffEq k := handoff S hS hDet hK1 hk1 hkn hc
    { quiet := (BootHandoffH.quietStep_self hS hk hc hquiet).hyp
      θ_nonneg := hθ0
      etaOut_le := BootHandoffH.etaOut_le_theta hS hk hc hquiet
      theta_small := hθK
      maj_le_cin := by linarith [hcin, hmaj0]
      maj_small := hsmall }
  -- `cor:amp`: the amplitude bounds
  have hSk : S.P.PertDefined k (S.P.tsh k) := hHO.2.2.2.2.trans (BootHandoffH.Nmk_subset_Nk k)
  obtain ⟨hA1, hA2⟩ := amp S hS hDet hk1 hkn hc hin hSk hHO.1 hHO.2.1 hqs hkickT
  -- the clock is defined up to level `k`
  have hkpos : 0 < S.P.ksh k := by
    have := mul_pos hpos.Klo_pos (pow_pos (BootHandoffH.s_pos hS k) (3 + 2))
    linarith
  have hklt : S.P.ksh k < S.P.δ₀ := by
    have h1 : S.Kup * S.P.s k ^ (3 + 2) ≤ S.Kup * S.P.sbar ^ (3 + 2) :=
      mul_le_mul_of_nonneg_left (BootHandoffH.s_pow_le hS k) hpos.Kup_pos.le
    have h2 := hL.sbar.b6
    have h3 := hL.kappa.two_lt_δ₀ hS.δ₀_pos hS.one_lt_μ
    have h4 := hS.kseed_pos
    linarith
  have hclock : S.P.ClockUpTo k := by
    intro i hi
    by_cases hik : i = k
    · subst hik
      exact ⟨hSk, hkpos, hklt⟩
    · exact hc i (Finset.mem_Icc.2 ⟨by have := (Finset.mem_Icc.1 hi).1; omega,
        (Finset.mem_Icc.1 hi).2⟩)
  -- Step 3.5: `eq:boot-switch`
  have hsw : Sob.normH S.s (S.P.w k (S.P.tsh k)) ≤ S.Chand * S.P.ksh k :=
    (BootHandoffH.normH_mono (BootHandoffH.s_le_sh S) _).trans hHO.2.2.2.1
  have hswC0 : S.Chand * S.P.ksh k ≤ S.C0 * S.P.ksh k :=
    mul_le_mul_of_nonneg_right S.Chand_le_C0 (S.P.ksh_nonneg k)
  have hswlt : S.C0 * S.P.ksh k < S.C2 * S.ahatK k 0 * (1 + S.rhoHatK S.C0 k 0) := by
    rw [S.ahatK_zero, BootHandoffH.rhoHatK_zero hS hkI]
    have hC2 := hpos.one_le_C2
    have hC0 := S.one_le_C0
    have h1 : S.P.ksh k * (1 + S.C0) ≤ S.C2 * S.P.ksh k * (1 + S.C0) := by
      have := mul_le_mul_of_nonneg_right hC2 (mul_nonneg hkpos.le (by linarith : 0 ≤ 1 + S.C0))
      linarith
    nlinarith [h1]
  exact
    { kappa_pos := hκpos
      kappa_le := hκle
      qs_mem := hqs
      kick := hkick
      theta_le := hθle
      theta_small := hθsmall
      relay := hrelay
      maj_le := hmaj
      maj_le_cin := hcin
      handoff := hHO
      amp_lo := hA1
      amp_up := hA2
      clock := hclock
      switch_le := hsw
      switch_C0 := hswC0
      switch_lt := hswlt }

end Relay

end NonUniqueEuler
