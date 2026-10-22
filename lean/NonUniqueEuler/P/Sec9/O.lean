import NonUniqueEuler.H.Sec9.O.Improve
import NonUniqueEuler.I.Infra.Continuity.Bootstrap

/-!
# Proof: `lem:O` (the quiet outer rings stay below ring `j`)

Proof of `I/Sec9/O.lean` (`09_relay.tex:264-387`). The steps:
* `OProof.bootstrap_eps` (`09_relay.tex:300-357`): for the regularized majorant
  `maj^ε_j = maj_j + εe^{σ_j·}`, `0 < ε ≤ maj_*e^{-σ_jτ}`, the continuity argument
  (`Continuity.bootstrap_le`, the quantities `maj_i(A_i·)`, `i < j`) with the improvement step
  `OProof.improve` (`eq:O-improved`) gives `maj_i(A_it) ≤ (1/4)P̃_{i,j}maj^ε_j(A_jt)` on
  `[0, τ/A_j]`;
* `OProof.quarter_bound` (`09_relay.tex:362-366`): `ε → 0`;
* `OProof.etaOut_bound` (`09_relay.tex:367-387`): `lem:transfer-step`(2) at level `j`, `eq:O-Q`
  and the quarter bound give `η^out_j ≤ (1/3)C_OC_QK_Os_{j-1}^{2m}maj_j ≤ θ_jmaj_j`;
* the hypotheses and conclusions of `thm:quiet` for the rings `i ≤ j` (`OProof.quietHyp_of`,
  `quiet_ring`).

The case `τ = 0` needs no separate treatment: the continuity argument runs on `[0, 0]`.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace Relay

open RingData Datum

namespace OProof

/-- `x ≤ a + εb` for all small `ε > 0` (and `b ≥ 0`) implies `x ≤ a`. -/
theorem le_of_forall_small_eps {x a b ε₀ : ℝ} (hb : 0 ≤ b) (hε₀ : 0 < ε₀)
    (h : ∀ ε, 0 < ε → ε ≤ ε₀ → x ≤ a + ε * b) : x ≤ a := by
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hb1 : 0 < b + 1 := by linarith
  have hε : 0 < min ε₀ (δ / (b + 1)) := lt_min hε₀ (div_pos hδ hb1)
  have h1 := h (min ε₀ (δ / (b + 1))) hε (min_le_left _ _)
  have h2 : min ε₀ (δ / (b + 1)) * b ≤ δ := by
    have h3 : min ε₀ (δ / (b + 1)) ≤ δ / (b + 1) := min_le_right _ _
    have h4 : δ / (b + 1) * b ≤ δ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hb1]
      nlinarith
    calc min ε₀ (δ / (b + 1)) * b ≤ δ / (b + 1) * b := mul_le_mul_of_nonneg_right h3 hb
      _ ≤ δ := h4
  linarith

/-- `maj_k(0) = 0`. -/
theorem maj_zero (S : Standing) (k : ℕ) : S.maj k 0 = 0 := by
  show (∫ v in (0 : ℝ)..0, Real.exp (S.P.sigma k * (0 - v)) * S.P.eta S.Mh k v) = 0
  exact intervalIntegral.integral_same

/-- **The continuity argument of `lem:O`** (`09_relay.tex:300-357`) for the regularized
majorant `maj^ε_j = maj_j + εe^{σ_j·}`, `0 < ε ≤ maj_*e^{-σ_jτ}`: for `t ∈ [0, τ/A_j]` and
`i < j`, `maj_i(A_it) ≤ (1/4)P̃_{i,j}maj^ε_j(A_jt)` (`eq:O-improved` on the whole interval). -/
theorem bootstrap_eps (S : Standing) (hS : S.Holds) (hDet : S.Det) {j : ℕ} {τ : ℝ}
    (h : S.OHyp j τ) {ε : ℝ} (hε : 0 < ε)
    (hεle : ε ≤ S.majst * Real.exp (-(S.P.sigma j * τ))) :
    ∀ t ∈ Icc (0 : ℝ) (τ / S.P.A j), ∀ i ∈ Finset.Ico 1 j,
      S.maj i (S.P.A i * t) ≤
        1 / 4 * (S.Ptil i j * (S.maj j (S.P.A j * t) +
          ε * Real.exp (S.P.sigma j * (S.P.A j * t)))) := by
  have hAj := hS.valid.A_pos j
  have hAT : S.P.A j * (τ / S.P.A j) = τ := mul_div_cancel₀ τ hAj.ne'
  have hjj : j ∈ Finset.Icc 1 j := Finset.mem_Icc.mpr ⟨h.one_le, le_rfl⟩
  have hmapj : MapsTo (fun t => S.P.A j * t) (Icc (0 : ℝ) (τ / S.P.A j))
      (Icc 0 (S.P.A j * (τ / S.P.A j))) := fun t ht =>
    ⟨mul_nonneg hAj.le ht.1, mul_le_mul_of_nonneg_left ht.2 hAj.le⟩
  have hcmj : ContinuousOn (fun t => S.maj j (S.P.A j * t)) (Icc (0 : ℝ) (τ / S.P.A j)) :=
    (contOn_facts S hS h hjj).2.2.comp (continuousOn_const.mul continuousOn_id) hmapj
  have hcexp : ContinuousOn (fun t => ε * Real.exp (S.P.sigma j * (S.P.A j * t)))
      (Icc (0 : ℝ) (τ / S.P.A j)) :=
    (continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul (continuous_const.mul continuous_id)))).continuousOn
  have hGpos : ∀ i : ℕ, ∀ t ∈ Icc (0 : ℝ) (τ / S.P.A j),
      0 < S.Ptil i j * (S.maj j (S.P.A j * t) + ε * Real.exp (S.P.sigma j * (S.P.A j * t))) :=
    fun i t ht => mul_pos (Ptil_pos S hS i j)
      (add_pos_of_nonneg_of_pos (maj_nonneg S j (mul_nonneg hAj.le ht.1))
        (mul_pos hε (Real.exp_pos _)))
  have key := Continuity.bootstrap_le (ι := {i // i ∈ Finset.Ico 1 j}) (a := 0)
    (b := τ / S.P.A j)
    (F := fun i t => S.maj i.1 (S.P.A i.1 * t))
    (G := fun i t => S.Ptil i.1 j * (S.maj j (S.P.A j * t) +
      ε * Real.exp (S.P.sigma j * (S.P.A j * t))))
    (H := fun i t => 1 / 4 * (S.Ptil i.1 j * (S.maj j (S.P.A j * t) +
      ε * Real.exp (S.P.sigma j * (S.P.A j * t)))))
    (fun i => by
      have hi' := Finset.mem_Ico.mp i.2
      have hAi := hS.valid.A_pos i.1
      have hc := (contOn_facts S hS h (l := i.1) (Finset.mem_Icc.mpr ⟨hi'.1, hi'.2.le⟩)).2.2
      exact hc.comp (continuousOn_const.mul continuousOn_id) fun t ht =>
        ⟨mul_nonneg hAi.le ht.1, mul_le_mul_of_nonneg_left ht.2 hAi.le⟩)
    (fun i => continuousOn_const.mul (hcmj.add hcexp))
    (fun i t ht => by
      have := hGpos i.1 t ht
      linarith)
    (fun i => by
      have e : S.maj i.1 (S.P.A i.1 * 0) = 0 := by rw [mul_zero, maj_zero]
      have := (hGpos i.1 0 ⟨le_rfl, div_nonneg h.τ_nonneg hAj.le⟩).le
      linarith)
    (fun t ht hBH i => improve S hS hDet h hε hεle ht
      (fun s hs i' hi' => hBH s hs ⟨i', hi'⟩) i.1 i.2)
  intro t ht i hi
  exact key t ht ⟨i, hi⟩

/-- **`ε → 0`** (`09_relay.tex:362-366`): for `t ∈ [0, τ/A_j]` and `i < j`,
`maj_i(A_it) ≤ (1/4)P̃_{i,j}maj_j(A_jt)`. -/
theorem quarter_bound (S : Standing) (hS : S.Holds) (hDet : S.Det) {j : ℕ} {τ : ℝ}
    (h : S.OHyp j τ) : ∀ t ∈ Icc (0 : ℝ) (τ / S.P.A j), ∀ i ∈ Finset.Ico 1 j,
      S.maj i (S.P.A i * t) ≤ 1 / 4 * (S.Ptil i j * S.maj j (S.P.A j * t)) := by
  intro t ht i hi
  have hε₀ : 0 < S.majst * Real.exp (-(S.P.sigma j * τ)) :=
    mul_pos (majst_pos S) (Real.exp_pos _)
  have hP := Ptil_nonneg S hS i j
  have hb : 0 ≤ 1 / 4 * S.Ptil i j * Real.exp (S.P.sigma j * (S.P.A j * t)) := by
    have := Real.exp_pos (S.P.sigma j * (S.P.A j * t))
    positivity
  refine le_of_forall_small_eps hb hε₀ fun ε hε hεle => ?_
  have h1 := bootstrap_eps S hS hDet h hε hεle t ht i hi
  calc S.maj i (S.P.A i * t)
      ≤ 1 / 4 * (S.Ptil i j * (S.maj j (S.P.A j * t) +
          ε * Real.exp (S.P.sigma j * (S.P.A j * t)))) := h1
    _ = 1 / 4 * (S.Ptil i j * S.maj j (S.P.A j * t)) +
          ε * (1 / 4 * S.Ptil i j * Real.exp (S.P.sigma j * (S.P.A j * t))) := by ring

/-- `maj_l(A_ls) ≤ maj_*` for `s ∈ [0, τ/A_j]` and `1 ≤ l ≤ j`, from the quarter bound and
`P̃_{l,j} ≤ 1/2` (`09_relay.tex:310-312`). -/
theorem maj_le_majst (S : Standing) (hS : S.Holds) (hDet : S.Det) {j : ℕ} {τ : ℝ}
    (h : S.OHyp j τ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (τ / S.P.A j)) {l : ℕ}
    (hl : l ∈ Finset.Icc 1 j) : S.maj l (S.P.A l * s) ≤ S.majst := by
  have hAj := hS.valid.A_pos j
  have hAjs : S.P.A j * s ∈ Icc (0 : ℝ) τ := by
    refine ⟨mul_nonneg hAj.le hs.1, ?_⟩
    have := mul_le_mul_of_nonneg_left hs.2 hAj.le
    rwa [mul_div_cancel₀ τ hAj.ne'] at this
  have hmj := h.maj_le _ hAjs
  have hl' := Finset.mem_Icc.mp hl
  rcases Nat.lt_or_ge l j with hlj | hlj
  · have h1 := quarter_bound S hS hDet h s hs l (Finset.mem_Ico.mpr ⟨hl'.1, hlj⟩)
    have h2 := Ptil_le_half S hS h.small hlj
    have h3 := Ptil_nonneg S hS l j
    have h4 := maj_nonneg S j hAjs.1
    have h5 := majst_pos S
    have h6 : S.Ptil l j * S.maj j (S.P.A j * s) ≤ 1 / 2 * S.majst :=
      mul_le_mul h2 hmj h4 (by norm_num)
    linarith
  · have : l = j := le_antisymm hl'.2 hlj
    subst this
    exact hmj

/-- **`thm:quiet` for the rings `l ≤ j`** on `[0, A_lt]`, `t ∈ [0, τ/A_j]`
(`09_relay.tex:310-322`, `:384-387`). -/
theorem quiet_all (S : Standing) (hS : S.Holds) (hDet : S.Det) {j : ℕ} {τ : ℝ}
    (h : S.OHyp j τ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (τ / S.P.A j)) {l : ℕ}
    (hl : l ∈ Finset.Icc 1 j) :
    S.QuietHyp l (S.P.A l * t) ∧ S.QuietConcl l (S.P.A l * t) := by
  have hq := quietHyp_of S hS h ht hl fun s hs =>
    maj_le_majst S hS hDet h ⟨hs.1, hs.2.trans ht.2⟩ hl
  exact ⟨hq, quiet_ring S hS hq⟩

/-- `b_{l,j}P̃_{l,j} ≤ K_Os_{j-1}^{2m}(K_Os̄^{2m})^{j-1-l}` for `1 ≤ l < j`
(`09_relay.tex:338-343`, `:370-376`). -/
theorem b_mul_Ptil_le (S : Standing) (hS : S.Holds) {l j : ℕ} (hl : 1 ≤ l) (hlj : l < j) :
    S.P.b l j * S.Ptil l j ≤
      S.KO * S.P.s (j - 1) ^ 6 * (S.KO * S.P.sbar ^ 6) ^ (j - 1 - l) := by
  rw [b_mul_Ptil S hS hl hlj.le]
  have hsplit : ∏ p ∈ Finset.Ico l j, S.KO * S.P.s p ^ 6 =
      (∏ p ∈ Finset.Ico l (j - 1), S.KO * S.P.s p ^ 6) * (S.KO * S.P.s (j - 1) ^ 6) := by
    have := Finset.prod_Ico_succ_top (show l ≤ j - 1 by omega)
      (fun p => S.KO * S.P.s p ^ 6)
    rwa [show j - 1 + 1 = j by omega] at this
  rw [hsplit]
  have hK := (KO_pos S hS).le
  have hs0 := (hS.valid.s_pos (j - 1)).le
  have hq : 0 ≤ S.KO * S.P.s (j - 1) ^ 6 := by positivity
  have h1 := prod_KO_s6_le S hS l (j - 1)
  calc (∏ p ∈ Finset.Ico l (j - 1), S.KO * S.P.s p ^ 6) * (S.KO * S.P.s (j - 1) ^ 6)
      ≤ (S.KO * S.P.sbar ^ 6) ^ (j - 1 - l) * (S.KO * S.P.s (j - 1) ^ 6) :=
        mul_le_mul_of_nonneg_right h1 hq
    _ = _ := by ring

/-- **The outer field of ring `j`** (`09_relay.tex:367-387`): for `t ∈ [0, τ/A_j]`,
`η^out_j(A_jt) ≤ θ_jmaj_j(A_jt)`. -/
theorem etaOut_bound (S : Standing) (hS : S.Holds) (hDet : S.Det) {j : ℕ} {τ : ℝ}
    (h : S.OHyp j τ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (τ / S.P.A j)) :
    S.etaOut j (S.P.A j * t) ≤ S.theta j * S.maj j (S.P.A j * t) := by
  have hj1 := h.one_le
  have hjj : j ∈ Finset.Icc 1 j := Finset.mem_Icc.mpr ⟨hj1, le_rfl⟩
  have hdef : S.P.HDefined j t := ⟨(h.geom t ht j hjj).2.1, (h.geom t ht j hjj).1⟩
  have hpb : ∀ l ∈ Finset.Ico 1 j,
      S.P.PertDefined l t ∧ Sob.normH S.sh (S.P.w l t) ≤ S.CQ * S.maj l (S.P.A l * t) := by
    intro l hl
    have hl' := Finset.mem_Ico.mp hl
    have hlj : l ∈ Finset.Icc 1 j := Finset.mem_Icc.mpr ⟨hl'.1, hl'.2.le⟩
    exact pert_bound_of_quietConcl S hS (quiet_all S hS hDet h ht hlj).2 ⟨ht.1, le_rfl⟩
  have hT := (transfer_step_two S hS hj1 h.lt_n.le ht.1 hdef (fun l hl => (hpb l hl).1) S.sh).2
  have hAj := hS.valid.A_pos j
  have hmj0 : 0 ≤ S.maj j (S.P.A j * t) := maj_nonneg S j (mul_nonneg hAj.le ht.1)
  have hQ := CQ_nonneg S
  have hO := CO_pos S
  have hK := (KO_pos S hS).le
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · -- `j = 1`: no outer rings
    have hj : j = 1 := by omega
    subst hj
    rw [S.theta_one, zero_mul]
    simpa using hT
  · rw [S.theta_of_two_le hj2]
    set q := S.KO * S.P.sbar ^ 6 with hqdef
    have hq0 : 0 ≤ q := by positivity
    have hq : q ≤ 1 / 4 := h.small.KO_sbar
    have hs0 := (hS.valid.s_pos (j - 1)).le
    have hsum : ∑ l ∈ Finset.Ico 1 j, S.P.b l j * Sob.normH S.sh (S.P.w l t) ≤
        ∑ l ∈ Finset.Ico 1 j, S.CQ * (1 / 4) * S.maj j (S.P.A j * t) *
          (S.KO * S.P.s (j - 1) ^ 6) * q ^ (j - 1 - l) := by
      refine Finset.sum_le_sum fun l hl => ?_
      have hl' := Finset.mem_Ico.mp hl
      have hb := b_nonneg S.P hS.valid l j
      have h1 := (hpb l hl).2
      have h2 := quarter_bound S hS hDet h t ht l hl
      have h3 := b_mul_Ptil_le S hS hl'.1 hl'.2
      have hc : 0 ≤ S.CQ * (1 / 4) * S.maj j (S.P.A j * t) := by positivity
      calc S.P.b l j * Sob.normH S.sh (S.P.w l t)
          ≤ S.P.b l j * (S.CQ * (1 / 4 * (S.Ptil l j * S.maj j (S.P.A j * t)))) := by
            refine mul_le_mul_of_nonneg_left (h1.trans ?_) hb
            exact mul_le_mul_of_nonneg_left h2 hQ
        _ = S.CQ * (1 / 4) * S.maj j (S.P.A j * t) * (S.P.b l j * S.Ptil l j) := by ring
        _ ≤ S.CQ * (1 / 4) * S.maj j (S.P.A j * t) *
              (S.KO * S.P.s (j - 1) ^ 6 * q ^ (j - 1 - l)) :=
            mul_le_mul_of_nonneg_left h3 hc
        _ = _ := by ring
    rw [← Finset.mul_sum] at hsum
    have hgeom := geom_theta_le hq0 hq (by omega : 1 ≤ j)
    have hc : 0 ≤ S.CQ * (1 / 4) * S.maj j (S.P.A j * t) * (S.KO * S.P.s (j - 1) ^ 6) := by
      positivity
    have hsum2 : ∑ l ∈ Finset.Ico 1 j, S.P.b l j * Sob.normH S.sh (S.P.w l t) ≤
        S.CQ * (1 / 4) * S.maj j (S.P.A j * t) * (S.KO * S.P.s (j - 1) ^ 6) * (4 / 3) :=
      hsum.trans (mul_le_mul_of_nonneg_left hgeom hc)
    have hfin : S.CO * ∑ l ∈ Finset.Ico 1 j, S.P.b l j * Sob.normH S.sh (S.P.w l t) ≤
        S.CO * (S.CQ * (1 / 4) * S.maj j (S.P.A j * t) * (S.KO * S.P.s (j - 1) ^ 6) * (4 / 3)) :=
      mul_le_mul_of_nonneg_left hsum2 hO.le
    have hX : 0 ≤ S.CO * S.CQ * S.KO * S.P.s (j - 1) ^ 6 * S.maj j (S.P.A j * t) := by
      positivity
    have hfin2 : S.CO * (S.CQ * (1 / 4) * S.maj j (S.P.A j * t) * (S.KO * S.P.s (j - 1) ^ 6) *
        (4 / 3)) = 1 / 3 * (S.CO * S.CQ * S.KO * S.P.s (j - 1) ^ 6 * S.maj j (S.P.A j * t)) := by
      ring
    have hgoal : 4 * S.CO * S.CQ * S.KO * S.P.s (j - 1) ^ (2 * 3) * S.maj j (S.P.A j * t) =
        4 * (S.CO * S.CQ * S.KO * S.P.s (j - 1) ^ 6 * S.maj j (S.P.A j * t)) := by ring
    rw [hgoal]
    linarith

end OProof

/-- **`lem:O`** (`09_relay.tex:228-250`): under (SA), (Det) and the hypotheses `S.OHyp j τ`
(`1 ≤ j < n`, clock up to `j+1`, `τ ∈ [0, t̄♯_j]`, the geometric hypotheses and `η_i ≤ 1` for the rings
`i ≤ j` on `[0, τ/A_j]`, `maj_j ≤ maj_*` on `[0,τ]`, the smallness conditions `S.OSmall`), the
conclusions `S.OConcl j τ` hold: `maj_i(A_it) ≤ (3/4)P̃_{i,j}maj_j(A_jt)` for `i < j`,
`η^out_j(A_jt) ≤ θ_jmaj_j(A_jt)` on `[0, τ/A_j]`, and `thm:quiet` applies to every ring `i ≤ j` on
`[0, A_it]` for `t ∈ (0, τ/A_j]`. -/
theorem O (S : Standing) (hS : S.Holds) (hDet : S.Det) {j : ℕ} {τ : ℝ} (h : S.OHyp j τ) :
    S.OConcl j τ := by
  refine ⟨fun t ht i hi => ?_, fun t ht => OProof.etaOut_bound S hS hDet h ht,
    fun t ht i hi => OProof.quiet_all S hS hDet h (Ioc_subset_Icc_self ht) hi⟩
  have h1 := OProof.quarter_bound S hS hDet h t ht i hi
  have hAj := hS.valid.A_pos j
  have h2 : 0 ≤ S.Ptil i j * S.maj j (S.P.A j * t) :=
    mul_nonneg (OProof.Ptil_nonneg S hS i j) (OProof.maj_nonneg S j (mul_nonneg hAj.le ht.1))
  calc S.maj i (S.P.A i * t) ≤ 1 / 4 * (S.Ptil i j * S.maj j (S.P.A j * t)) := h1
    _ ≤ 3 / 4 * (S.Ptil i j * S.maj j (S.P.A j * t)) := by linarith
    _ = 3 / 4 * S.Ptil i j * S.maj j (S.P.A j * t) := by ring

end Relay

end NonUniqueEuler
