import NonUniqueEuler.I.Sec9.TransferStep
import NonUniqueEuler.H.Sec9.Oprime.Defined

/-!
# Helpers for `lem:Oprime`: the reduction `eq:Op-red` and the hypotheses of `prop:relay`

Helper file of `P/Sec9/Oprime.lean`. Everything here is proved.

* `op_red` (`eq:Op-red`, `09_relay.tex:643-662`): for `t' ∈ [t♯_k, t]`, `k = j+1 ≥ 2`,
  `h^out_k(A_kt') ∈ C^{M_h}(N')` and `η^out_k(A_kt') ≤ 2C_OC_Q b_{j,k} maj_j(A_jt')`
  (`lem:transfer-step`(2) with `s' = s_h`, `thm:quiet`(c), `lem:O`, and
  `Σ_{i<j} b_{i,j}P̃_{i,j} ≤ 1/3`);
* `relayHyp` (`09_relay.tex:664-679`): the hypotheses (H1)–(H4) of `prop:relay` for `j = k-1`,
  `τ = A_jt` and the present `C₀`, `K₁` (with `maj_n(t̄♯_n) = maj_n(0) = 0` if `k = n`).
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

namespace OprimeH

open RingData Datum

theorem sigb_pos {S : Standing} (hS : S.Holds) : 0 < S.sigb := by
  have h1 := hS.σ'_gt
  have h2 := hS.σ'_lt_sigb
  show 0 < Eig.sigb S.P.χ
  linarith

variable {S : Standing} {C₀ K₁ CF : ℝ} {t : ℝ}

/-- **`eq:Op-red`** (`09_relay.tex:643-662`): for `t' ∈ [t♯_{j+1}, t]`,
`h^out_{j+1}(A_{j+1}t') ∈ C^{M_h}(N')` and
`η^out_{j+1}(A_{j+1}t') ≤ 2C_OC_Q b_{j,j+1} maj_j(A_jt')`. -/
theorem op_red (hS : S.Holds) {j : ℕ} (hj : 1 ≤ j) (h : S.OprimeHyp C₀ K₁ CF (j + 1) t)
    {t' : ℝ} (ht' : t' ∈ Icc (S.P.tsh (j + 1)) t) :
    MemCk S.Mh annN' (S.P.hOut (j + 1) (S.P.A (j + 1) * t')) ∧
      S.etaOut (j + 1) (S.P.A (j + 1) * t') ≤
        2 * S.CO * S.CQ * S.P.b j (j + 1) * S.maj j (S.P.A j * t') := by
  have h0 : 0 ≤ t' := (tsh_nonneg hS h).trans ht'.1
  have ht0 : t' ∈ Icc (0 : ℝ) t := ⟨h0, ht'.2⟩
  have hTS := transfer_step_two S hS (by omega : 1 ≤ j + 1) h.le_n h0 (hDefined_k hS hj h ht')
    (fun i hi => pertDefined hS h ht0 (by
      have := Finset.mem_Ico.mp hi
      exact Finset.mem_Icc.mpr ⟨this.1, this.2.le⟩)) S.sh
  refine ⟨hTS.1, hTS.2.trans ?_⟩
  set M := S.maj j (S.P.A j * t') with hM
  have hM0 : 0 ≤ M := maj_nonneg S j (mul_nonneg (hS.valid.A_pos j).le h0)
  have hCO := CO_pos S
  have hCQ := CQ_nonneg S
  have hsb := sigb_pos hS
  have hb := b_nonneg hS.valid j (j + 1)
  set c := S.P.b j (j + 1) * S.CQ * (3 / 4) with hc
  have hc0 : 0 ≤ c := by positivity
  have hterm : ∀ i ∈ Finset.Ico 1 j, S.P.b i (j + 1) * Sob.normH S.sh (S.P.w i t') ≤
      c * (S.P.b i j * S.Ptil i j) * M := by
    intro i hi
    have hi' := Finset.mem_Ico.mp hi
    have hw := normH_w_le hS hj h ht0 (Finset.mem_Icc.mpr ⟨hi'.1, hi'.2.le⟩)
    have hmaj := (oConcl hj h).maj_le t' (by rw [div_A hS]; exact ht0) i hi
    rw [← b_mul hS.valid i j (j + 1)]
    have hbij := b_nonneg hS.valid i j
    have hw' : Sob.normH S.sh (S.P.w i t') ≤ S.CQ * (3 / 4 * S.Ptil i j * M) :=
      hw.trans (mul_le_mul_of_nonneg_left hmaj hCQ)
    calc S.P.b j (j + 1) * S.P.b i j * Sob.normH S.sh (S.P.w i t')
        ≤ S.P.b j (j + 1) * S.P.b i j * (S.CQ * (3 / 4 * S.Ptil i j * M)) :=
          mul_le_mul_of_nonneg_left hw' (mul_nonneg hb hbij)
      _ = c * (S.P.b i j * S.Ptil i j) * M := by rw [hc]; ring
  have hlast : S.P.b j (j + 1) * Sob.normH S.sh (S.P.w j t') ≤ S.P.b j (j + 1) * S.CQ * M := by
    have hw := normH_w_le hS hj h ht0 (Finset.mem_Icc.mpr ⟨hj, le_rfl⟩)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hw hb
  have hsum := Finset.sum_le_sum hterm
  have hsumeq : ∑ i ∈ Finset.Ico 1 j, c * (S.P.b i j * S.Ptil i j) * M =
      c * (∑ i ∈ Finset.Ico 1 j, S.P.b i j * S.Ptil i j) * M := by
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [hsumeq] at hsum
  have hbP := sum_bPtil_le S hS hsb (oHyp hj h).small.KO_sbar j hj
  have hcM : c * (∑ i ∈ Finset.Ico 1 j, S.P.b i j * S.Ptil i j) * M ≤ c * (1 / 3) * M :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbP hc0) hM0
  rw [Finset.sum_Ico_succ_top hj]
  have hX : 0 ≤ S.CO * S.P.b j (j + 1) * S.CQ * M := by positivity
  have hfin : S.CO * (c * (1 / 3) * M + S.P.b j (j + 1) * S.CQ * M) =
      5 / 4 * (S.CO * S.P.b j (j + 1) * S.CQ * M) := by rw [hc]; ring
  calc S.CO * (∑ i ∈ Finset.Ico 1 j, S.P.b i (j + 1) * Sob.normH S.sh (S.P.w i t') +
        S.P.b j (j + 1) * Sob.normH S.sh (S.P.w j t'))
      ≤ S.CO * (c * (1 / 3) * M + S.P.b j (j + 1) * S.CQ * M) :=
        mul_le_mul_of_nonneg_left (add_le_add (hsum.trans hcM) hlast) hCO.le
    _ ≤ 2 * S.CO * S.CQ * S.P.b j (j + 1) * M := by
        rw [hfin]
        nlinarith

/-- The real time `t♯_k + u/A_k` of the active time `u` of ring `k` (`A_k ≠ 0`). -/
theorem tsh_add_activeTime (hS : S.Holds) (k : ℕ) (t' : ℝ) :
    S.P.tsh k + S.P.activeTime k t' / S.P.A k = t' := by
  have hA := (hS.valid.A_pos k).ne'
  simp only [Approx.activeTime]
  field_simp
  ring

theorem tash_add_activeTime (k : ℕ) (t' : ℝ) :
    S.P.tash k + S.P.activeTime k t' = S.P.A k * t' := by
  simp only [Approx.activeTime, Approx.tash_def]
  ring

theorem activeTime_mem {k : ℕ} (hS : S.Holds) {t' : ℝ} (ht' : t' ∈ Icc (S.P.tsh k) t) :
    S.P.activeTime k t' ∈ Icc (0 : ℝ) (S.P.activeTime k t) := by
  have hA := hS.valid.A_pos k
  simp only [Approx.activeTime]
  exact ⟨mul_nonneg hA.le (by linarith [ht'.1]),
    mul_le_mul_of_nonneg_left (by linarith [ht'.2]) hA.le⟩

/-- `t̄♯_n = 0`. -/
theorem tash_n : S.P.tash S.P.n = 0 := by
  rw [Approx.tash_def, S.P.tsh_n, mul_zero]

/-- **The hypotheses (H1)–(H4) of `prop:relay`** for `j = k-1`, `τ = A_jt`
(`09_relay.tex:664-679`). -/
theorem relayHyp (hS : S.Holds) (hK₁ : 0 < K₁) (hCF : CF ∈ Ioc 0 C₀) {j : ℕ} (hj : 1 ≤ j)
    (h : S.OprimeHyp C₀ K₁ CF (j + 1) t) : S.RelayHyp C₀ K₁ j (S.P.A j * t) where
  one_le := hj
  lt_n := by have := h.le_n; omega
  clock := h.clock
  τ_nonneg := (oHyp hj h).τ_nonneg
  τ_le := (oHyp hj h).τ_le
  h1 t' ht' := h.loc t' (by rwa [div_A hS] at ht')
  h2 := by
    refine ⟨fun τ' hτ' => ?_, theta_small hj h⟩
    have hA := hS.valid.A_pos j
    have hle : τ' / S.P.A j ≤ t := by
      rw [div_le_iff₀ hA, mul_comm]
      exact hτ'.2
    have := (oConcl hj h).etaOut_le (τ' / S.P.A j)
      ⟨div_nonneg hτ'.1 hA.le, by rw [div_A hS]; exact hle⟩
    rwa [mul_div_cancel₀ _ hA.ne'] at this
  h3 hlt := by
    rw [div_A hS, min_eq_right h.mem_phase.1]
    exact (h.quiet hlt).1
  h4 hlt := by
    rw [div_A hS, min_eq_left h.mem_phase.2]
    refine ⟨?_, fun t' ht' => ⟨hInDefined h ht', ?_, ?_⟩⟩
    · rcases lt_or_eq_of_le h.le_n with hkn | hkn
      · exact (h.quiet hkn).2.1
      · rw [hkn, tash_n, S.maj_zero]
        exact mul_nonneg hK₁.le (S.P.ksh_nonneg _)
    · have := h.active _ (activeTime_mem hS ht')
      rwa [tsh_add_activeTime hS] at this
    · have := h.inner _ (activeTime_mem hS ht')
      rw [tash_add_activeTime] at this
      refine this.trans ?_
      have hj3 : 0 ≤ Prelim.jap (S.P.activeTime (j + 1) t') ^ 3 :=
        pow_nonneg (Real.sqrt_nonneg _) 3
      have := S.P.ksh_nonneg (j + 1)
      have := hCF.2
      gcongr

end OprimeH

end Relay

end NonUniqueEuler
