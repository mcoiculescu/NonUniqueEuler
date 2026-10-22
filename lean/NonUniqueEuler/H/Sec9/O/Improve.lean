import NonUniqueEuler.H.Sec9.O.Real
import NonUniqueEuler.H.Sec9.O.Chain
import NonUniqueEuler.H.Sec9.O.Quiet
import NonUniqueEuler.I.Sec9.Detuning
import NonUniqueEuler.I.Sec5.Majorant
import NonUniqueEuler.I.Sec6.FieldContinuity

/-!
# Helpers for `P/Sec9/O`: continuity facts and the improvement step `eq:O-improved`

* `OProof.contOn_facts`: under `S.OHyp j τ`, with `T = τ/A_j`, `η_i`, `η^in_j`, `η_j`, `maj_i` are
  continuous on `[0, A_iT]` (`I/Sec6/FieldContinuity.lean`), and `A_jT = τ`;
* `OProof.majj_M1`: (M1) of `lem:majorant` for `maj_j` on `[0, τ]`;
* `OProof.improve`: the improvement step of the continuity argument (`09_relay.tex:304-357`):
  if `eq:O-BH` holds on `[0,t]` (with the regularized majorant
  `maj^ε_j(τ') = maj_j(τ') + εe^{σ_jτ'}`, `0 < ε ≤ maj_*e^{-σ_jτ}`), then
  `maj_i(A_it) ≤ (1/4)P̃_{i,j}maj^ε_j(A_jt)` for every `i < j` (`eq:O-improved`).
-/

noncomputable section

open Set MeasureTheory

namespace NonUniqueEuler.Relay.OProof

open RingData Datum

/-- Continuity of the field norms and majorants of the rings `l ≤ j` on `[0, A_l τ/A_j]`, under
`S.OHyp j τ` (paragraph after `lem:regions-basic`, `06_datum.tex:319-321`). -/
theorem contOn_facts (S : Standing) (hS : S.Holds) {j : ℕ} {τ : ℝ} (h : S.OHyp j τ) {l : ℕ}
    (hl : l ∈ Finset.Icc 1 j) :
    ContinuousOn (S.P.eta S.Mh l) (Icc 0 (S.P.A l * (τ / S.P.A j))) ∧
      ContinuousOn (S.P.etaIn S.Mh l) (Icc 0 (S.P.A l * (τ / S.P.A j))) ∧
      ContinuousOn (S.P.majK S.Mh l) (Icc 0 (S.P.A l * (τ / S.P.A j))) := by
  have hl' := Finset.mem_Icc.mp hl
  have hln : l ≤ S.P.n := by linarith [h.lt_n, hl'.2]
  have hT0 : 0 ≤ τ / S.P.A j := div_nonneg h.τ_nonneg (hS.valid.A_pos j).le
  have hdef : ∀ s ∈ Icc (0 : ℝ) (τ / S.P.A j), S.P.HDefined l s := fun s hs =>
    ⟨(h.geom s hs l hl).2.1, (h.geom s hs l hl).1⟩
  have he := Approx.eta_continuous S.P hS.valid hS.hN hl'.1 hln (t₁ := 0) (t₂ := τ / S.P.A j) le_rfl S.Mh
  have hm := Approx.maj_continuous S.P hS.valid hS.hN hl'.1 hln hT0 S.Mh
  rw [mul_zero] at he
  exact ⟨he.2.2 hdef, he.1 fun s hs => (hdef s hs).1, hm.1 hdef⟩

/-- **(M1) of `lem:majorant` for `maj_j`** on `[0, τ]` (`09_relay.tex:302-303`). -/
theorem majj_M1 (S : Standing) (hS : S.Holds) {j : ℕ} {τ : ℝ} (h : S.OHyp j τ) {v τ' : ℝ}
    (hv : 0 ≤ v) (hvτ' : v ≤ τ') (hτ' : τ' ≤ τ) :
    Real.exp (S.P.sigma j * (τ' - v)) * S.maj j v ≤ S.maj j τ' := by
  have hj : j ∈ Finset.Icc 1 j := Finset.mem_Icc.mpr ⟨h.one_le, le_rfl⟩
  have hjN : j ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.mpr ⟨h.one_le, h.lt_n.le⟩
  have hc := (contOn_facts S hS h hj).1
  rw [mul_div_cancel₀ τ (hS.valid.A_pos j).ne'] at hc
  have hG := ((standing_levels S hS).2.2.2 j hjN).2.1
  have hM := OneRing.majorant S.P.χ hS.admissible hS.hN hG (T := τ) (η := S.P.eta S.Mh j)
    hc.integrableOn_Icc (fun t _ => S.P.eta_nonneg _ _ _)
  exact (hM.1 v τ' hv hvτ' hτ').1

/-- **The improvement step** (`09_relay.tex:304-357`, `eq:O-improved`). -/
theorem improve (S : Standing) (hS : S.Holds) (hDet : S.Det) {j : ℕ} {τ : ℝ} (h : S.OHyp j τ)
    {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ S.majst * Real.exp (-(S.P.sigma j * τ)))
    {t : ℝ} (ht : t ∈ Icc 0 (τ / S.P.A j))
    (hBH : ∀ s ∈ Icc 0 t, ∀ i ∈ Finset.Ico 1 j,
      S.maj i (S.P.A i * s) ≤
        S.Ptil i j * (S.maj j (S.P.A j * s) + ε * Real.exp (S.P.sigma j * (S.P.A j * s)))) :
    ∀ i ∈ Finset.Ico 1 j, S.maj i (S.P.A i * t) ≤
      1 / 4 * (S.Ptil i j * (S.maj j (S.P.A j * t) + ε * Real.exp (S.P.sigma j * (S.P.A j * t)))) := by
  intro i hi
  have hi' := Finset.mem_Ico.mp hi
  have hj1 := h.one_le
  have hjn := h.lt_n
  have hjN : j ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.mpr ⟨hj1, hjn.le⟩
  have hiN : i ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.mpr ⟨hi'.1, by omega⟩
  have hij : i ∈ Finset.Icc 1 j := Finset.mem_Icc.mpr ⟨hi'.1, hi'.2.le⟩
  have hjj : j ∈ Finset.Icc 1 j := Finset.mem_Icc.mpr ⟨hj1, le_rfl⟩
  have hAj := hS.valid.A_pos j
  have hAi := hS.valid.A_pos i
  have hAT : S.P.A j * (τ / S.P.A j) = τ := mul_div_cancel₀ τ hAj.ne'
  have hlev := (standing_levels S hS).2.2.2
  have hb := sigb_pos S hS
  have hσj : S.sigb ≤ S.P.sigma j := (hlev j hjN).2.2
  have hσj0 : 0 ≤ S.P.sigma j := by linarith
  have hmajst := majst_pos S
  have hμ := hS.one_lt_μ
  -- `A_j s ∈ [0, τ]` for `s ∈ [0,t]`
  have hAjs : ∀ s ∈ Icc (0 : ℝ) t, S.P.A j * s ∈ Icc (0 : ℝ) τ := fun s hs =>
    ⟨mul_nonneg hAj.le hs.1, by
      have := mul_le_mul_of_nonneg_left (hs.2.trans ht.2) hAj.le
      linarith⟩
  -- (i) `maj_l ≤ maj_*` on `[0,t]` for `l ≤ j`
  have hεexp : ∀ s ∈ Icc (0 : ℝ) t, ε * Real.exp (S.P.sigma j * (S.P.A j * s)) ≤ S.majst := by
    intro s hs
    have h1 := hAjs s hs
    calc ε * Real.exp (S.P.sigma j * (S.P.A j * s))
        ≤ S.majst * Real.exp (-(S.P.sigma j * τ)) * Real.exp (S.P.sigma j * (S.P.A j * s)) :=
          mul_le_mul_of_nonneg_right hεle (Real.exp_pos _).le
      _ = S.majst * Real.exp (S.P.sigma j * (S.P.A j * s - τ)) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
      _ ≤ S.majst * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ hmajst.le
          rw [Real.exp_le_one_iff]
          exact mul_nonpos_of_nonneg_of_nonpos hσj0 (by linarith [h1.2])
      _ = S.majst := mul_one _
  have hmjs : ∀ s ∈ Icc (0 : ℝ) t, S.maj j (S.P.A j * s) ≤ S.majst := fun s hs =>
    h.maj_le _ (hAjs s hs)
  have hm0 : ∀ s ∈ Icc (0 : ℝ) t,
      0 ≤ S.maj j (S.P.A j * s) + ε * Real.exp (S.P.sigma j * (S.P.A j * s)) := fun s hs =>
    add_nonneg (maj_nonneg S j (hAjs s hs).1) (mul_pos hε (Real.exp_pos _)).le
  have hsmall : ∀ l ∈ Finset.Icc 1 j, ∀ s ∈ Icc (0 : ℝ) t, S.maj l (S.P.A l * s) ≤ S.majst := by
    intro l hl s hs
    have hl' := Finset.mem_Icc.mp hl
    rcases Nat.lt_or_ge l j with hlj | hlj
    · have h1 := hBH s hs l (Finset.mem_Ico.mpr ⟨hl'.1, hlj⟩)
      have h2 := Ptil_le_half S hS h.small hlj
      have h3 := Ptil_nonneg S hS l j
      have h4 := hm0 s hs
      have h5 := hmjs s hs
      have h6 := hεexp s hs
      calc S.maj l (S.P.A l * s)
          ≤ S.Ptil l j * (S.maj j (S.P.A j * s) + ε * Real.exp (S.P.sigma j * (S.P.A j * s))) := h1
        _ ≤ 1 / 2 * (S.majst + S.majst) := by
            apply mul_le_mul h2 (by linarith) h4 (by norm_num)
        _ = S.majst := by ring
    · have : l = j := le_antisymm hl'.2 hlj
      subst this
      exact hmjs s hs
  -- (ii)-(iii) `thm:quiet` for the rings `l ≤ j` on `[0, A_l t]`
  have hPB : ∀ s ∈ Icc (0 : ℝ) t, ∀ l ∈ Finset.Icc 1 j,
      S.P.PertDefined l s ∧ Sob.normH S.sh (S.P.w l s) ≤ S.CQ * S.maj l (S.P.A l * s) :=
    fun s hs l hl => pert_bound_of_quietConcl S hS
      (quiet_ring S hS (quietHyp_of S hS h ht hl (hsmall l hl))) hs
  -- (iv) the pointwise bound on `η_i`
  have hpt : ∀ s ∈ Icc (0 : ℝ) t, S.eta i (S.P.A i * s) ≤ S.Ptil i j *
      ((8 / 7 * (S.CM / S.KO) * S.CQ + 4 / 3 * (S.CO * S.CQ * S.KO * S.P.sbar ^ 6)) *
          (S.maj j (S.P.A j * s) + ε * Real.exp (S.P.sigma j * (S.P.A j * s))) +
        S.CM / S.KO * S.etaIn j (S.P.A j * s)) := by
    intro s hs
    have hsT : s ∈ Icc (0 : ℝ) (τ / S.P.A j) := ⟨hs.1, hs.2.trans ht.2⟩
    refine eta_pointwise S hS h.small hi'.1 hi'.2 hjn hs.1 (hm0 s hs) ?_
      (fun p hp => (hPB s hs p hp).1) (fun p hp => (hPB s hs p hp).2) (hBH s hs)
      (le_add_of_nonneg_right (mul_pos hε (Real.exp_pos _)).le)
    intro p hp
    exact ⟨(h.geom s hsT p hp).2.1, (h.geom s hsT p hp).1⟩
  -- (v) the Duhamel integral
  set c : ℝ := S.P.μ ^ (j - i) with hcdef
  have hc1 : 1 ≤ c := one_le_pow₀ (by linarith)
  have hc0 : c ≠ 0 := by linarith
  have hcpos : 0 < c := by linarith
  have hAji : S.P.A j = c * S.P.A i := A_eq_pow_mul S.P hi'.1 hi'.2.le
  set τ' : ℝ := S.P.A j * t with hτ'def
  have hτ'0 : 0 ≤ τ' := mul_nonneg hAj.le ht.1
  have hτ'le : τ' ≤ τ := by
    have := mul_le_mul_of_nonneg_left ht.2 hAj.le
    linarith
  have hAit : S.P.A i * t = τ' / c := by
    rw [hτ'def, hAji]
    field_simp
  -- continuity on `[0, τ']`
  obtain ⟨hcei, -, -⟩ := contOn_facts S hS h hij
  obtain ⟨hcej, hcinj, hcmj⟩ := contOn_facts S hS h hjj
  rw [hAT] at hcej hcinj hcmj
  have hsubj : Icc (0 : ℝ) τ' ⊆ Icc 0 τ := Icc_subset_Icc le_rfl hτ'le
  have hf : ContinuousOn (fun v => S.P.eta S.Mh i (v / c)) (Icc 0 τ') := by
    refine hcei.comp (continuousOn_id.div_const c) fun v hv => ⟨div_nonneg hv.1 hcpos.le, ?_⟩
    rw [div_le_iff₀ hcpos]
    have h1 : S.P.A i * (τ / S.P.A j) * c = τ := by
      have := hAi.ne'
      rw [hAji]
      field_simp
    rw [h1]
    exact hv.2.trans hτ'le
  have hm : ContinuousOn (fun v => S.maj j v + ε * Real.exp (S.P.sigma j * v)) (Icc 0 τ') :=
    (hcmj.mono hsubj).add (continuousOn_const.mul
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn))
  have hδ : 0 < S.sigb * (S.P.μ - 1) / (2 * S.P.μ) := by
    have : 0 < S.P.μ - 1 := by linarith
    have : 0 < S.P.μ := by linarith
    positivity
  have hdet := (((detuning S hS hDet).2.2 i hiN).2.2.2.2.2 j hjN).2.2.2 hi'.2
  rw [zpow_sub_eq _ hi'.2.le, ← hcdef] at hdet
  have hσh : S.P.sigma i / c ≤ S.P.sigma j - S.sigb * (S.P.μ - 1) / (2 * S.P.μ) := by
    rwa [div_eq_mul_inv]
  have hP := Ptil_nonneg S hS i j
  obtain ⟨hX0, -, -⟩ := CM_div_KO_le S hS
  have hQ := CQ_nonneg S
  have hK := (KO_pos S hS).le
  have hO := (CO_pos S).le
  have ha1 : 0 ≤ 8 / 7 * (S.CM / S.KO) * S.CQ + 4 / 3 * (S.CO * S.CQ * S.KO * S.P.sbar ^ 6) := by
    positivity
  have hfb : ∀ v ∈ Icc (0 : ℝ) τ', S.P.eta S.Mh i (v / c) ≤ S.Ptil i j *
      ((8 / 7 * (S.CM / S.KO) * S.CQ + 4 / 3 * (S.CO * S.CQ * S.KO * S.P.sbar ^ 6)) *
          (S.maj j v + ε * Real.exp (S.P.sigma j * v)) + S.CM / S.KO * S.P.etaIn S.Mh j v) := by
    intro v hv
    have hs : v / S.P.A j ∈ Icc (0 : ℝ) t := by
      refine ⟨div_nonneg hv.1 hAj.le, ?_⟩
      rw [div_le_iff₀ hAj]
      linarith [hv.2]
    have h1 := hpt _ hs
    have e1 : S.P.A j * (v / S.P.A j) = v := mul_div_cancel₀ v hAj.ne'
    have e2 : S.P.A i * (v / S.P.A j) = v / c := by
      rw [hAji]
      field_simp
    rw [e1, e2] at h1
    exact h1
  have hm0' : ∀ v ∈ Icc (0 : ℝ) τ', 0 ≤ S.maj j v + ε * Real.exp (S.P.sigma j * v) := fun v hv =>
    add_nonneg (maj_nonneg S j hv.1) (mul_pos hε (Real.exp_pos _)).le
  have hm1 : ∀ v ∈ Icc (0 : ℝ) τ', Real.exp (S.P.sigma j * (τ' - v)) *
      (S.maj j v + ε * Real.exp (S.P.sigma j * v)) ≤
        S.maj j τ' + ε * Real.exp (S.P.sigma j * τ') := by
    intro v hv
    have h1 := majj_M1 S hS h hv.1 hv.2 hτ'le
    have h2 : Real.exp (S.P.sigma j * (τ' - v)) * (ε * Real.exp (S.P.sigma j * v)) =
        ε * Real.exp (S.P.sigma j * τ') := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    rw [mul_add, h2]
    linarith
  have key := duhamel_compare hτ'0 hc1 hδ hσh hP ha1 hX0 hf hm (hcinj.mono hsubj)
    (hcej.mono hsubj) hfb hm0' hm1 (fun v _ => S.P.etaIn_nonneg _ _ _)
    (fun v _ => le_add_of_nonneg_right (S.P.etaOut_nonneg _ _ _))
  -- the left side is `maj_i(A_i t)`
  have hlhs : S.maj i (S.P.A i * t) =
      c⁻¹ * ∫ v in (0 : ℝ)..τ', Real.exp (S.P.sigma i / c * (τ' - v)) * S.P.eta S.Mh i (v / c) := by
    rw [hAit]
    exact duh_subst hc0 _ _ _
  -- the right side
  have hmaj : (∫ v in (0 : ℝ)..τ', Real.exp (S.P.sigma j * (τ' - v)) * S.P.eta S.Mh j v) =
      S.maj j τ' := rfl
  rw [hmaj, ← hlhs] at key
  have hmτ' : 0 ≤ S.maj j τ' + ε * Real.exp (S.P.sigma j * τ') := hm0' τ' ⟨hτ'0, le_rfl⟩
  have hmajle : S.maj j τ' ≤ S.maj j τ' + ε * Real.exp (S.P.sigma j * τ') :=
    le_add_of_nonneg_right (mul_pos hε (Real.exp_pos _)).le
  have hDuh : (S.maj j τ' + ε * Real.exp (S.P.sigma j * τ')) /
      (S.sigb * (S.P.μ - 1) / (2 * S.P.μ)) = S.CDuh * (S.maj j τ' + ε * Real.exp (S.P.sigma j * τ')) := by
    rw [CDuh_eq S hS]
    ring
  rw [hDuh] at key
  have hbr := bracket_le S hS h.small
  set a1 := 8 / 7 * (S.CM / S.KO) * S.CQ + 4 / 3 * (S.CO * S.CQ * S.KO * S.P.sbar ^ 6)
  set a2 := S.CM / S.KO
  set mm := S.maj j τ' + ε * Real.exp (S.P.sigma j * τ')
  calc S.maj i (S.P.A i * t) ≤ S.Ptil i j * (a1 * (S.CDuh * mm) + a2 * S.maj j τ') := key
    _ ≤ S.Ptil i j * ((a1 * S.CDuh + a2) * mm) := by
        apply mul_le_mul_of_nonneg_left _ hP
        have := mul_le_mul_of_nonneg_left hmajle hX0
        nlinarith
    _ ≤ S.Ptil i j * (1 / 4 * mm) := by
        apply mul_le_mul_of_nonneg_left _ hP
        exact mul_le_mul_of_nonneg_right hbr hmτ'
    _ = 1 / 4 * (S.Ptil i j * mm) := by ring

end NonUniqueEuler.Relay.OProof
