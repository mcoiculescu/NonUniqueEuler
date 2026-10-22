import NonUniqueEuler.Defs.Sec11.Extra2Boot
import NonUniqueEuler.I.Sec6.Clock
import NonUniqueEuler.I.Sec9.Standing
import NonUniqueEuler.I.Sec9.O
import NonUniqueEuler.I.Sec9.QuietRing
import NonUniqueEuler.I.Sec10.ConstantsPos
import NonUniqueEuler.I.Sec11.Stop

/-!
# Proof: Step 2 of the proof of `prop:bootstrap` (quiet rings) and `eq:boot-quiet`

Proof of `I/Sec11/BootQuiet.lean` (`11_bootstrap.tex:270-296`): same declaration, same statement.

* `quietAt_anti_BQ`: a ring quiet at `t'` is quiet at every earlier time (`QuietAt` is
  `¬ ClockUpTo (j+1) ∨ t ≤ t♯_j`).
* `not_debris_of_quiet_BQ`: a quiet ring is not debris (`t♯_i < T_i`, `lem:clock`(1),
  `clock_order`, with `P.GSmall` from `standing_levels`).
* `maj_le_majst_BQ`: for a ring `j < n` quiet at `t'`, `maj_j ≤ 2Āε_j ≤ 2Āμs̄^{m+2} ≤ maj_*` on
  `[0, A_jt']` ((BA2) with `2Ā` from (BA°)(t'), `s_j ≤ s̄`, `Ā > 0` (`constants_pos`), (B9)).
* `quietHyp_BQ`: the hypotheses of `thm:quiet` for a ring `j < n` quiet at `t'` on `[0, A_jt']`
  (`lem:geometry`(b) on `[0, t']` for `HDefined` and `η_j ≤ 1`; `G_j ∈ [0, G₁]` from
  `standing_levels`; `maj_le_majst_BQ`).
* `oHyp_BQ`: the hypotheses of `lem:O` for a level `k < n` with `t♯_k` defined and `t' ≤ t♯_k`
  (the rings `i ≤ k` are quiet on `[0, t']`, `quiet_of_lt`; `lem:geometry`(b); (B7) for `OSmall`).
* `boot_quiet`: `thm:quiet` for ring `j` (`quiet_ring`) gives `eq:boot-quiet`; if `t♯_j` is defined,
  `lem:O` (`O`, with (Det) = (B4)); otherwise the clock stops at `k_s` with `j < k_s < n`
  (`stopsAt_stopLevel`, `StopsAt.clockUpTo_iff`, Step 0: the clock is defined up to level `n`),
  ring `k_s` is quiet on `[0, T_end] = [0, t♯_{k_s}]`, and `OConcl.maj_le` of `lem:O` for `k_s` at
  `t'` gives `maj_j(A_jt') ≤ ¾P̃_{j,k_s}maj_{k_s}(A_{k_s}t')`.

Deviation (minor): in the case "`t♯_j` not defined" the manuscript obtains the hypotheses of
`thm:quiet` for ring `j` from `lem:O` applied to `k_s`; here they are obtained directly, exactly as
in the case "`t♯_j` defined" (ring `j` is quiet on `[0, t']`, so `lem:geometry`(b), (BA2) and (B9)
apply to it). This also covers `t' = 0` without a separate argument.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

open RingData Datum

variable {S : Standing}

/-- A ring quiet at `t` is quiet at every earlier time. -/
private theorem quietAt_anti_BQ {i : ℕ} {t t'' : ℝ} (h : S.P.QuietAt i t) (ht : t'' ≤ t) :
    S.P.QuietAt i t'' :=
  h.imp id fun h' => ht.trans h'

/-- A quiet ring is not debris (`t♯_i < T_i` when `T_i` is defined, `lem:clock`(1)). -/
private theorem not_debris_of_quiet_BQ (hS : S.Holds) {i : ℕ} (hi : i ∈ Finset.Icc 1 S.P.n)
    {t : ℝ} (hq : S.P.QuietAt i t) : ¬ S.P.DebrisAt i t := by
  rintro ⟨hc, hT⟩
  rcases hq with hq | hq
  · exact hq (hc.mono (Nat.le_succ i))
  · have hG := (standing_levels S hS).2.2.1
    have hi' := Finset.mem_Icc.1 hi
    have hlt := (Approx.clock_order S.P hS.valid hS.hN hG hi'.1 hc).1 i
      (Finset.mem_Icc.2 ⟨le_rfl, hi'.2⟩)
    linarith

/-- `τ ∈ [0, A t']` gives `τ / A ∈ [0, t']` (`A > 0`). -/
private theorem div_mem_Icc_BQ {A t' τ : ℝ} (hA : 0 < A) (hτ : τ ∈ Icc (0 : ℝ) (A * t')) :
    τ / A ∈ Icc (0 : ℝ) t' := by
  refine ⟨div_nonneg hτ.1 hA.le, ?_⟩
  rw [div_le_iff₀ hA, mul_comm]
  exact hτ.2

/-- **The bound `maj_j ≤ maj_*`** on `[0, A_jt']` for a ring `j < n` quiet at `t'`
(`11_bootstrap.tex:277-278`): (BA2) with `2Ā` and (B9), `maj_j ≤ 2Āε_j ≤ 2Āμs̄^{m+2} ≤ maj_*`. -/
private theorem maj_le_majst_BQ (hS : S.Holds) (hL : S.ParamLists) {t' : ℝ}
    (hBA : S.BAcirc t') {j : ℕ} (hj : j ∈ Finset.Ico 1 S.P.n) (hq : S.P.QuietAt j t') :
    ∀ τ ∈ Icc (0 : ℝ) (S.P.A j * t'), S.maj j τ ≤ S.majst := by
  intro τ hτ
  have hA := hS.valid.A_pos j
  have ht'' := div_mem_Icc_BQ hA hτ
  have hq'' := quietAt_anti_BQ hq ht''.2
  have hba := (hBA.ba2 (τ / S.P.A j) ⟨ht''.1, ht''.2.trans le_rfl⟩ j hj hq'').2
  rw [mul_div_cancel₀ τ hA.ne'] at hba
  have hpos := constants_pos S hS.valid.admissible hS.hN hS.σ'_gt hS.σ'_lt_sigma hS.δ₀_pos
    hS.one_lt_μ hS.Tpin_pos
  have hAbar : 0 ≤ S.Abar := hpos.Abar_pos.le
  have hs0 : 0 ≤ S.P.s j := (hS.valid.s_pos j).le
  have hs : S.P.s j ≤ S.P.sbar := by
    rw [Approx.s_def, ratio]
    exact div_le_self hS.sbar_pos.le (one_le_pow₀ (by linarith [hS.one_lt_μ]))
  have hμ : 0 ≤ S.P.μ := by linarith [hS.one_lt_μ]
  have hpow : S.P.s j ^ (3 + 2) ≤ S.P.sbar ^ (3 + 2) := pow_le_pow_left₀ hs0 hs _
  have heps : 2 * S.Abar * S.P.eps j ≤ 2 * S.Abar * S.P.μ * S.P.sbar ^ (3 + 2) := by
    rw [Approx.eps, mul_assoc (2 * S.Abar)]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hμ) (by positivity)
  exact hba.trans (heps.trans hL.sbar.b9_maj)

/-- **The hypotheses of `thm:quiet` for ring `j` on `[0, A_jt']`** (`11_bootstrap.tex:288-292`), for a
ring `j < n` quiet at `t'`: ring `j` is quiet, hence not debris, on `[0, t']`, so
`lem:geometry`(b) gives `HDefined` and `η_j ≤ 1`; `G_j ∈ [0, G₁]` (`lem:inner-circ`,
`standing_levels`); `maj_j ≤ maj_*` (`maj_le_majst_BQ`). -/
private theorem quietHyp_BQ (hS : S.Holds) (hL : S.ParamLists) {t' : ℝ} (hBA : S.BAcirc t')
    (hgeo : S.GeometryConcl t') {j : ℕ} (hj : j ∈ Finset.Ico 1 S.P.n) (hq : S.P.QuietAt j t') :
    S.QuietHyp j (S.P.A j * t') := by
  have hA := hS.valid.A_pos j
  have hj' := Finset.mem_Ico.1 hj
  have hjI : j ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.2 ⟨hj'.1, hj'.2.le⟩
  have hring : ∀ t'' ∈ Icc (0 : ℝ) t', S.GeometryRing j t'' := fun t'' ht'' =>
    hgeo.ring t'' ht'' j hjI (not_debris_of_quiet_BQ hS hjI (quietAt_anti_BQ hq ht''.2))
  refine
    { one_le := hj'.1
      lt_n := hj'.2
      hdef := ?_
      G_mem := ((standing_levels S hS).2.2.2 j hjI).2.1
      eta_le := ?_
      maj_le := maj_le_majst_BQ hS hL hBA hj hq }
  · intro t ht
    rw [mul_div_cancel_left₀ t' hA.ne'] at ht
    exact (hring t ht).2.2.1
  · intro τ hτ
    have ht'' := div_mem_Icc_BQ hA hτ
    have h := (hring _ ht'').2.2.2 hj'.2
    rwa [mul_div_cancel₀ τ hA.ne'] at h

/-- **The hypotheses of `lem:O` for the level `k` and `τ = A_kt'`** (`11_bootstrap.tex:273-280`), for a
level `k < n` with `t♯_k` defined and `0 ≤ t' ≤ t♯_k`: on `[0, t']` every ring `i ≤ k` is quiet
(`quiet_of_lt`), so `lem:geometry`(b) gives the geometric hypotheses and `η_i ≤ 1`; (BA2), (B9)
give `maj_k ≤ maj_*` on `[0, τ]`; (B7) gives the smallness conditions. -/
private theorem oHyp_BQ (hS : S.Holds) (hL : S.ParamLists) {t' : ℝ} (hBA : S.BAcirc t')
    (hgeo : S.GeometryConcl t') {k : ℕ} (hk : k ∈ Finset.Ico 1 S.P.n)
    (hc : S.P.ClockUpTo (k + 1)) (ht0 : 0 ≤ t') (hle : t' ≤ S.P.tsh k) :
    S.OHyp k (S.P.A k * t') := by
  have hA := hS.valid.A_pos k
  have hk' := Finset.mem_Ico.1 hk
  have hkI : k ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.2 ⟨hk'.1, hk'.2.le⟩
  have hq : S.P.QuietAt k t' := Or.inr hle
  refine
    { one_le := hk'.1
      lt_n := hk'.2
      clock := hc
      τ_nonneg := mul_nonneg hA.le ht0
      τ_le := ?_
      geom := ?_
      maj_le := maj_le_majst_BQ hS hL hBA hk hq
      small := hL.sbar.b7.small }
  · rw [Approx.tash_def]
    exact mul_le_mul_of_nonneg_left hle hA.le
  · intro t ht i hi
    rw [mul_div_cancel_left₀ t' hA.ne'] at ht
    have hi' := Finset.mem_Icc.1 hi
    have hiI : i ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.2 ⟨hi'.1, hi'.2.trans hk'.2.le⟩
    have hqk : S.P.QuietAt k t := quietAt_anti_BQ hq ht.2
    have hqi : S.P.QuietAt i t := by
      rcases lt_or_eq_of_le hi'.2 with hlt | heq
      · exact quiet_of_lt S hS hkI (Or.inl hqk) i (Finset.mem_Ico.2 ⟨hi'.1, hlt⟩)
      · rw [heq]
        exact hqk
    have hg := hgeo.ring t ht i hiI (not_debris_of_quiet_BQ hS hiI hqi)
    exact ⟨hg.2.2.1.2, hg.2.2.1.1, hg.2.2.2 (lt_of_le_of_lt hi'.2 hk'.2)⟩

/-- **Step 2 of the proof of `prop:bootstrap`** (`11_bootstrap.tex:270-296`), with
`eq:boot-quiet`: if `t' ∈ [0, T_end]`, Step 0 holds, (BA°)(t') holds and the conclusions of
`lem:geometry` with `t'` hold, then the conclusions of Step 2 hold at `t'` for every ring `j < n`
quiet at `t'` (`S.QuietStepAt t'`). -/
theorem boot_quiet (S : Standing) (hS : S.Holds) (hL : S.ParamLists) {t' : ℝ}
    (ht' : t' ∈ Icc (0 : ℝ) S.P.Tend) (h0 : S.BootStartConcl) (hBA : S.BAcirc t')
    (hgeo : S.GeometryConcl t') : S.QuietStepAt t' := by
  intro j hj hq
  have hA := hS.valid.A_pos j
  have hj' := Finset.mem_Ico.1 hj
  have hyp := quietHyp_BQ hS hL hBA hgeo hj hq
  have concl := quiet_ring S hS hyp
  have hDet : S.Det := hL.sbar.b4
  refine ⟨?_, hyp, concl, ?_, ?_⟩
  · -- `eq:boot-quiet` from `thm:quiet`(a), (c) for ring `j` on `[0, A_jt']`
    intro t'' ht''
    have hτ : S.P.A j * t'' ∈ Icc (0 : ℝ) (S.P.A j * t') :=
      ⟨mul_nonneg hA.le ht''.1, mul_le_mul_of_nonneg_left ht''.2 hA.le⟩
    have h1 := concl.supp _ hτ
    have h2 := concl.bound _ hτ
    rw [mul_div_cancel_left₀ t'' hA.ne'] at h1 h2
    exact ⟨h1, h2⟩
  · -- `t♯_j` defined: `lem:O` for `j` and `τ = A_jt'`
    intro hc
    have hle : t' ≤ S.P.tsh j := hq.resolve_left (not_not_intro hc)
    have hO := oHyp_BQ hS hL hBA hgeo hj hc ht'.1 hle
    exact ⟨hO, O S hS hDet hO⟩
  · -- `t♯_j` not defined: the clock stops at `k_s`, `j < k_s < n`; `lem:O` for `k_s`
    intro hc
    have h1 : ¬ S.P.ClockUpTo 1 := fun h => hc (h.mono (by omega))
    have hst := Approx.stopsAt_stopLevel h1
    have hks_n : S.P.stopLevel < S.P.n := (hst.clockUpTo_iff S.P.n).1 h0.clock_n
    have hjks : j < S.P.stopLevel := by
      by_contra hcon
      exact hc ((hst.clockUpTo_iff (j + 1)).2 (by omega))
    have hks : S.P.stopLevel ∈ Finset.Ico 1 S.P.n := Finset.mem_Ico.2 ⟨hst.1, hks_n⟩
    have hle : t' ≤ S.P.tsh S.P.stopLevel := by
      rw [← hst.Tend_eq]
      exact ht'.2
    have hO := oHyp_BQ hS hL hBA hgeo hks hst.2.2.1 ht'.1 hle
    have hC := O S hS hDet hO
    have hA' := hS.valid.A_pos S.P.stopLevel
    have ht : t' ∈ Icc (0 : ℝ) (S.P.A S.P.stopLevel * t' / S.P.A S.P.stopLevel) := by
      rw [mul_div_cancel_left₀ t' hA'.ne']
      exact ⟨ht'.1, le_rfl⟩
    exact hC.maj_le t' ht j (Finset.mem_Ico.2 ⟨hj'.1, hjks⟩)

end Relay

end NonUniqueEuler
