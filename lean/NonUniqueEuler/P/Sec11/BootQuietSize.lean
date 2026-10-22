import NonUniqueEuler.Defs.Sec11.Extra2Boot
import NonUniqueEuler.I.Sec9.Relay
import NonUniqueEuler.I.Sec9.Gamma
import NonUniqueEuler.I.Sec9.Detuning
import NonUniqueEuler.H.Sec11.BootQuietSize.Bounds
import NonUniqueEuler.H.Sec11.BootQuietSize.RelayHyp

/-!
# Proof: Step 5 of the proof of `prop:bootstrap` (the size of the quiet rings)

Proof of `I/Sec11/BootQuietSize.lean` (`11_bootstrap.tex:486-530`). Same declaration, same
statement.

**Structure.**
* `BootQuietSizeH.quiet_size_defined`: the case `t♯_j` defined (`:492-523`). `prop:relay` applies to
  `j` and `τ = A_jt'` (hypotheses: `BootQuietSizeH.relayHyp`). If `τ ≤ A_jt♯_{j+1}`: for `j+1 = n`,
  `τ = 0` and `maj_j(0) = 0`; for `j+1 < n`, ring `j+1` is quiet at `t'`, and `prop:relay`(i),
  (BA2) for ring `j+1` (with `μA_jt' = A_{j+1}t'`) and (B10) give `maj_j(τ) ≤ Āε_j`
  (`BootQuietSizeH.b10_bound`). Otherwise `prop:relay`(ii) (`τ = t̄♯_j`) or (iii) bound `maj_j(τ)` by
  `eq:relay`; `κ♯_{j+1} ∈ (0, 2κ_seed]` (Step 3 for ring `j+1` with (B6), or Step 0), (κ7),
  `lem:gamma` give `Ξ_{j+1} ≤ δ₀/(σ_b(μ-1))` (`BootQuietSizeH.XiNext_le`), and `lem:detuning`
  (`x_j ≤ 17σ/16`) with the definition of `Ā` gives `≤ Āε_j` (`BootQuietSizeH.relayBound_le_Abar`).
* `boot_quiet_size`: `h_j` is defined on `[0, t']` by `lem:geometry`(b). If `t♯_j` is not defined,
  the clock stops at `k_s > j` (`def:stop`); if `k_s = n` then `T_end = 0`, `t' = 0` and
  `maj_j(0) = 0`; otherwise ring `k_s` is quiet at `t' ≤ T_end = t♯_{k_s}`, the defined case gives
  `maj_{k_s}(A_{k_s}t') ≤ Āε_{k_s}`, and Step 2 (`QuietStep.stopped`) with (B7) gives
  `maj_j(τ) ≤ ¾P̃_{j,k_s}Āε_{k_s} ≤ ⅜Āε_j` (`BootQuietSizeH.Ptil_mul_le`).

No deviation from the manuscript.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

open RingData Datum

namespace BootQuietSizeH

variable {S : Standing}

/-- **Step 5 when `t♯_j` is defined** (`11_bootstrap.tex:492-523`): for a ring `j < n` with
`t♯_j` defined and `t' ≤ t♯_j`, `maj_j(A_jt') ≤ Āε_j`. -/
theorem quiet_size_defined (S : Standing) (hS : S.Holds) (hL : S.ParamLists) {t' : ℝ}
    (ht0 : 0 ≤ t') (h0 : S.BootStartConcl) (hBA : S.BAcirc t')
    (hgeo : S.GeometryConcl t') (hquiet : ∀ t'' ∈ Icc (0 : ℝ) t', S.QuietStepAt t'')
    (hlev : ∀ i ∈ Finset.Ico 1 S.P.n, S.P.ClockUpTo (i + 1) → S.P.tsh i ≤ t' → S.HandoffStep i)
    (hact : ∀ i ∈ Finset.Icc 1 S.P.n, S.P.ClockUpTo i → S.P.tsh i < t' →
      S.ActiveStep i (S.P.activeTime i (min t' (S.P.T i))))
    {j : ℕ} (hj : j ∈ Finset.Ico 1 S.P.n) (hc : S.P.ClockUpTo (j + 1)) (hq : t' ≤ S.P.tsh j) :
    S.maj j (S.P.A j * t') ≤ S.Abar * S.P.eps j := by
  obtain ⟨hj1, hjn⟩ := Finset.mem_Ico.1 hj
  have hpos := constPos hS
  have hDet := hL.det
  have hA := A_pos hS j
  have hX : 0 ≤ S.Abar * S.P.eps j := mul_nonneg hpos.Abar_pos.le (eps_nonneg hS j)
  have hR := relayHyp hS hL ht0 h0 hBA hgeo hquiet hlev hact hj hc hq
  obtain ⟨-, -, hi, hii, hiii⟩ := relay S hS hDet S.one_le_C0 hpos.K1_pos hR
  by_cases hle : S.P.A j * t' ≤ S.P.A j * S.P.tsh (j + 1)
  · -- `τ ≤ A_j t♯_{j+1}`: `prop:relay`(i) and (BA2) for ring `j+1`, or `τ = 0`.
    by_cases hjn1 : j + 1 < S.P.n
    · have hm := hi hle
      have hq1 : S.P.QuietAt (j + 1) t' := Or.inr (le_of_mul_le_mul_left hle hA)
      have hBA2 := (hBA.ba2 t' ⟨ht0, le_rfl⟩ (j + 1)
        (Finset.mem_Ico.2 ⟨by omega, hjn1⟩) hq1).2
      rw [A_succ hj1, mul_assoc] at hBA2
      exact hm.trans (b10_bound hpos hS (S.b10_iff_Crelay.1 hL.sbar.b10) hBA2)
    · have hjeq : j + 1 = S.P.n := by omega
      rw [hjeq, S.P.tsh_n, mul_zero] at hle
      have hτ : S.P.A j * t' = 0 := le_antisymm hle (mul_nonneg hA.le ht0)
      rw [hτ, S.maj_zero]
      exact hX
  · -- `τ > A_j t♯_{j+1}`: `eq:relay`, `Ξ_{j+1} ≤ δ₀/(σ_b(μ-1))`, `x_j ≤ 17σ/16`.
    rw [not_le] at hle
    have hrel : S.maj j (S.P.A j * t') ≤ S.relayBound j (S.XiNext S.C0 S.K1 j) := by
      rcases eq_or_lt_of_le hR.τ_le with h | h
      · exact hii h
      · exact hiii hle h
    have hlt : S.P.tsh (j + 1) < t' := lt_of_mul_lt_mul_left hle hA.le
    have hκ : S.P.ksh (j + 1) ∈ Ioo (0 : ℝ) S.P.δ₀ := hc.ksh_mem le_rfl (by omega)
    have hκ2 : S.P.ksh (j + 1) ≤ 2 * S.P.κs := by
      by_cases hjn1 : j + 1 < S.P.n
      · have hH := hlev (j + 1) (Finset.mem_Ico.2 ⟨by omega, hjn1⟩)
          (hc.mono (Nat.le_succ _)) hlt.le
        have h1 : S.P.ksh (j + 1) ≤ S.P.κs :=
          (hH.amp_up.trans (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (s_pos hS _).le (s_le_sbar hS _) _) hpos.Kup_pos.le)).trans
            hL.sbar.b6
        linarith [hS.kseed_pos]
      · have hjeq : j + 1 = S.P.n := by omega
        rw [hjeq]
        exact h0.ksh_n.2
    have h7 := (hL.kappa.cond hκ.1 hκ2).k7
    have hγ := (gamma S hS hDet j hj).1
    have hΞ := XiNext_le hS hpos.sigb_pos hγ hκ h7
    have hx := ((detuning S hS hDet).2.2 j (Finset.mem_Icc.2 ⟨hj1, hjn.le⟩)).2.2.2.2.1
    calc S.maj j (S.P.A j * t') ≤ S.relayBound j (S.XiNext S.C0 S.K1 j) := hrel
      _ ≤ S.relayBound j (S.P.δ₀ / (S.sigb * (S.P.μ - 1))) :=
          S.relayBound_mono j hΞ (mul_nonneg hpos.CM_pos.le (eps_nonneg hS j))
      _ ≤ S.Abar * S.P.eps j := relayBound_le_Abar hpos hS hx

end BootQuietSizeH

open BootQuietSizeH in
/-- **Step 5 of the proof of `prop:bootstrap`** (`11_bootstrap.tex:486-530`): given Step 0,
(BA°)(t'), `lem:geometry` with `t'`, Step 2 on `[0, t']`, Step 3 at the levels `i < n` with
`t♯_i ≤ t'` and Step 4 for the rings `i` with `t♯_i < t'` up to `min(t', T_i)`, (BA2) holds at `t'`
with `Ā` in place of `2Ā`. -/
theorem boot_quiet_size (S : Standing) (hS : S.Holds) (hL : S.ParamLists) {t' : ℝ}
    (ht' : t' ∈ Icc (0 : ℝ) S.P.Tend) (h0 : S.BootStartConcl) (hBA : S.BAcirc t')
    (hgeo : S.GeometryConcl t') (hquiet : ∀ t'' ∈ Icc (0 : ℝ) t', S.QuietStepAt t'')
    (hlev : ∀ i ∈ Finset.Ico 1 S.P.n, S.P.ClockUpTo (i + 1) → S.P.tsh i ≤ t' → S.HandoffStep i)
    (hact : ∀ i ∈ Finset.Icc 1 S.P.n, S.P.ClockUpTo i → S.P.tsh i < t' →
      S.ActiveStep i (S.P.activeTime i (min t' (S.P.T i)))) :
    S.BA2At S.Abar t' := by
  intro j hj hq
  obtain ⟨hj1, hjn⟩ := Finset.mem_Ico.1 hj
  have hpos := constPos hS
  have hjI : j ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.2 ⟨hj1, hjn.le⟩
  have hX : 0 ≤ S.Abar * S.P.eps j := mul_nonneg hpos.Abar_pos.le (eps_nonneg hS j)
  -- `h_j` is defined on `[0, t']` (`lem:geometry`(b)).
  refine ⟨fun t'' ht'' =>
    (hgeo.ring t'' ht'' j hjI (not_debris_of_quiet hS hjI hq ht''.2)).2.2.1, ?_⟩
  by_cases hc : S.P.ClockUpTo (j + 1)
  · exact quiet_size_defined S hS hL ht'.1 h0 hBA hgeo hquiet hlev hact hj hc
      (hq.resolve_left (not_not.2 hc))
  · -- `t♯_j` is not defined: the clock stops at `k_s > j`.
    have hst := (hquiet t' ⟨ht'.1, le_rfl⟩ j hj hq).stopped hc
    have hc1 : ¬ S.P.ClockUpTo 1 := fun h => hc (h.mono (by omega))
    have hstop := Approx.stopsAt_stopLevel hc1
    have hjks : j < S.P.stopLevel := by
      have := (hstop.clockUpTo_iff (j + 1)).not.1 hc
      omega
    have hks1 : 1 ≤ S.P.stopLevel := hstop.1
    have hksn : S.P.stopLevel ≤ S.P.n := hstop.2.1
    have hcks : S.P.ClockUpTo (S.P.stopLevel + 1) := hstop.2.2.1
    rcases lt_or_eq_of_le hksn with hlt | heq
    · have hq' : t' ≤ S.P.tsh S.P.stopLevel := hstop.Tend_eq ▸ ht'.2
      have hks := quiet_size_defined S hS hL ht'.1 h0 hBA hgeo hquiet hlev hact
        (Finset.mem_Ico.2 ⟨hks1, hlt⟩) hcks hq'
      exact hst.trans (Ptil_mul_le hpos hS hL.sbar.b7.small hjks hks)
    · have hstopn : S.P.StopsAt S.P.n := heq ▸ hstop
      have ht0 : t' = 0 := le_antisymm (hstopn.Tend_eq_zero ▸ ht'.2) ht'.1
      rw [ht0, mul_zero, S.maj_zero]
      exact hX

end Relay

end NonUniqueEuler
