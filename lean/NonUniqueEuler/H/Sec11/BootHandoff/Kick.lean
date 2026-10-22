import NonUniqueEuler.H.Sec11.BootHandoff.Basic

/-!
# Helper for `P/Sec11/BootHandoff.lean`: `eq:boot-kappa` and the hypotheses of `lem:kicktrue`

Step 3 of the proof of `prop:bootstrap` (`11_bootstrap.tex:304-334`):
* `kappa`: `eq:boot-kappa`, `0 < κ♯_{k+1} ≤ 2κ_seed` (Step 3 for ring `k+1` with (B6), or Step 0 if
  `k+1 = n`);
* `kickTrueHyp`: the hypotheses `S.KickTrueHyp S.C0 S.K1 k` of `lem:kicktrue`, from `lem:geometry`
  (a), (b), Step 2, Step 3 for ring `k+1`, Step 4 for ring `k+1`, (P1)–(P3), (κ1)–(κ3) at
  `κ♯_{k+1}` and (B11) (the list at `11_bootstrap.tex:316-334`). All proved.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

namespace BootHandoffH

open RingData Datum

variable {S : Standing}

/-- `e_{k+1} = T_{k+1}` when `T_{k+1}` is defined. -/
theorem endW_of_clock {k : ℕ} (hc : S.P.ClockUpTo k) : S.P.endW k = S.P.T k := by
  simp only [Approx.endW, hc, ↓reduceIte]

/-- `t♯_k ≤ e_k` for a level `k ∈ [1, n]`. -/
theorem tsh_le_endW (hS : S.Holds) {k : ℕ} (hk : k ∈ Finset.Icc 1 S.P.n) :
    S.P.tsh k ≤ S.P.endW k := by
  unfold Approx.endW
  split_ifs with h
  · exact tsh_le_T hS hk (h.ksh_mem le_rfl (Finset.mem_Icc.1 hk).2)
  · exact le_rfl

/-- **`eq:boot-kappa`** (`11_bootstrap.tex:304-308`): `0 < κ♯_{k+1} ≤ 2κ_seed`, by Step 3 for ring
`k+1` (`κ♯_{k+1} ≤ K_up s_{k+1}^{m+2} ≤ K_up s̄^{m+2} ≤ κ_seed`, (B6)) or by Step 0 if `k+1 = n`. -/
theorem kappa (hS : S.Holds) (hL : S.ParamLists) {k : ℕ} (hk : k ∈ Finset.Ico 1 S.P.n)
    (hc : S.P.ClockUpTo (k + 1)) (h0 : S.BootStartConcl)
    (hdeep : ∀ i ∈ Finset.Ioo k S.P.n, S.HandoffStep i) :
    0 < S.P.ksh (k + 1) ∧ S.P.ksh (k + 1) ≤ 2 * S.P.κs := by
  have hkn := (Finset.mem_Ico.1 hk).2
  refine ⟨(hc.ksh_mem le_rfl (by omega)).1, ?_⟩
  have hκs := hS.kseed_pos
  by_cases h : k + 1 < S.P.n
  · have hd := hdeep (k + 1) (Finset.mem_Ioo.2 ⟨by omega, h⟩)
    have hpos := constPos hS
    have h1 : S.Kup * S.P.s (k + 1) ^ (3 + 2) ≤ S.Kup * S.P.sbar ^ (3 + 2) :=
      mul_le_mul_of_nonneg_left (s_pow_le hS _) hpos.Kup_pos.le
    have h2 := hL.sbar.b6
    linarith [hd.amp_up]
  · have hn : k + 1 = S.P.n := by omega
    rw [hn]
    exact h0.ksh_n.2

/-- **The hypotheses of `lem:kicktrue`** for the level `k` with `C₀ = S.C0`, `K₁ = S.K1`
(`11_bootstrap.tex:311-334`). -/
theorem kickTrueHyp (hS : S.Holds) (hL : S.ParamLists) {k : ℕ} (hk : k ∈ Finset.Ico 1 S.P.n)
    (hc : S.P.ClockUpTo (k + 1)) (h0 : S.BootStartConcl) (hgeo : S.GeometryConcl (S.P.tsh k))
    (hquiet : ∀ t' ∈ Icc (0 : ℝ) (S.P.tsh k), S.QuietStepAt t')
    (hdeep : ∀ i ∈ Finset.Ioo k S.P.n, S.HandoffStep i)
    (hact : S.ActiveStep (k + 1) (S.P.That (k + 1))) : S.KickTrueHyp S.C0 S.K1 k := by
  have hk1 := (Finset.mem_Ico.1 hk).1
  have hkn := (Finset.mem_Ico.1 hk).2
  have hpos := constPos hS
  have hkI : k ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.2 ⟨hk1, hkn.le⟩
  obtain ⟨htsh1, htshT, hTtsh, htsheq⟩ := clock_around hS hk1 hkn hc
  obtain ⟨hκpos, hκle⟩ := kappa hS hL hk hc h0 hdeep
  have hκ := hL.kappa.cond hκpos hκle
  have hC2 : 0 ≤ S.C2 := le_trans zero_le_one hpos.one_le_C2
  have hle := etabK_le_etab hpos hS (k + 1)
  refine
    { hin := fun t ht => (hgeo.ring t ht k hkI (not_debris_of_le_tsh hS hkI ht.2)).2.1
      active := fun u hu => activeConclAt_mono hle hC2 hpos.C3_pos.le (hact.concl u hu)
      drift := ⟨S.etabK S.C0 S.K1 (k + 1), ⟨etabK_nonneg hpos hS _, hle⟩, hact.drift, hact.cls⟩
      rT_le := hL.structural.p3.rT_le
      deeper := ?_
      pin := ?_
      ineqA := hL.structural.p1.kickIneqA hpos.sigma0_pos hpos.z_norm_pos hpos.C3_pos
      ineqB := hL.structural.p2.kickIneqB
      ineqC := hκ.k1
      ineqD := hκ.k2
      ineqE := hκ.k3
      ineqF := hL.sbar.b11_kick }
  · -- the deeper levels (`k + 1 < n`)
    intro h
    have hd := hdeep (k + 1) (Finset.mem_Ioo.2 ⟨by omega, h⟩)
    have hc2 : S.P.ClockUpTo (k + 1 + 1) := hc.mono (by omega)
    have hq := hquiet (S.P.tsh (k + 1)) ⟨htsh1, htshT.trans hTtsh⟩ (k + 1)
      (Finset.mem_Ico.2 ⟨by omega, h⟩) (Or.inr le_rfl)
    refine ⟨⟨by omega, h, hc2, hq.hyp⟩, hd.handoff.2.2.1, ?_, hd.amp_lo⟩
    -- `T_{k+2} ≤ t♯_{k+1} ≤ t♯_k`, and `min(t♯_k, e_{k+1}) = T_{k+1}`
    have heq2 := S.P.tsh_eq_T_add h
    have hT2 : S.P.T (k + 1 + 1) ≤ S.P.tsh k := by
      have := div_nonneg hS.Tpin_pos.le (A_pos hS (k + 1 + 1)).le
      linarith
    have hw := (hgeo.window (k + 1) (Finset.mem_Ico.2 ⟨by omega, h⟩) hc2 hT2).1
    rwa [endW_of_clock hc, min_eq_right hTtsh] at hw
  · -- the moment bound on `Pin_k`
    intro τK hτ
    have hw := hgeo.window k hk hc hTtsh
    have hmin : min (S.P.tsh k) (S.P.endW k) = S.P.tsh k := min_eq_left (tsh_le_endW hS hkI)
    have hA := A_pos hS (k + 1)
    have h1 : 0 ≤ τK / S.P.A (k + 1) := div_nonneg hτ.1 hA.le
    have h2 : τK / S.P.A (k + 1) ≤ S.P.Tpin / S.P.A (k + 1) :=
      div_le_div_of_nonneg_right hτ.2 hA.le
    have hmem : S.P.T (k + 1) + τK / S.P.A (k + 1) ∈
        Icc (S.P.T (k + 1)) (min (S.P.tsh k) (S.P.endW k)) := by
      rw [hmin]
      constructor <;> linarith
    have hq := (hw.2 _ hmem).2.2
    have hkt : S.P.kickTime k (S.P.T (k + 1) + τK / S.P.A (k + 1)) = τK := by
      simp only [Approx.kickTime]
      field_simp
      ring
    rw [hkt] at hq
    exact hq

end BootHandoffH

end Relay

end NonUniqueEuler
