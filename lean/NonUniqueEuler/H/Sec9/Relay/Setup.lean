import NonUniqueEuler.H.Sec9.Relay.Basic
import NonUniqueEuler.I.Sec9.Standing
import NonUniqueEuler.I.Sec6.Clock
import NonUniqueEuler.I.Sec6.FieldContinuity

/-!
# Helpers for `prop:relay`: constants, the clock of ring `j+1`, definedness of the fields

Helper file of `P/Sec9/Relay.lean` (`09_relay.tex:440-458`, `:519-527`). Everything here is
proved. Under `S.RelayHyp C₀ K₁ j τ` (with `τ^act = A_jt♯_{j+1}`, `τ^sat = A_jT_{j+1}`):

* signs of the chosen constants (`C_M > 0`, `C_Q ≥ 0`, `C₂ ≥ 1`, `C_* ≥ 0`), `σ_k ≥ σ_b > 0`;
* the clock: `κ♯_{j+1} ∈ (0,δ₀)`, `0 ≤ t♯_{j+1}`, `T̂_{j+1} ≥ 0`, `A_{j+1} = μA_j`,
  `τ^sat = τ^act + T̂_{j+1}/μ`, `t̄♯_j = τ^sat + T_pin/μ`;
* (Loc) consequences on `[0,τ/A_j]`: `h_j` is defined, `S_j(t) ⊂ N_j`, `h^out_{j+1}` is defined
  (the rings `i < j` lie outside `B_{6r_j} ⊃ B_{6r_{j+1}}`, ring `j` lies in `N_j`, which misses
  `B_{6r_{j+1}}`), `S_{j+1}(t) ⊂ N_{j+1}` for `t ≤ T_{j+1}`, `h_{j+1}` is defined for
  `t ≤ t♯_{j+1}`; and the confinement `D_{j+1}(t) ⊂ \bar B_{ϱ_j(t)}` for `t ≥ T_{j+1}`;
* continuity (hence integrability) of `η^in_j`, `η^out_j`, `η_j` on `[0,τ]` and of `η_{j+1}` on
  `[0,μτ']` for `τ' ≤ min(τ, τ^act)` (`FieldContinuity`).
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

namespace RelayH

open RingData Datum

/-! ### Signs of the constants -/

/-- `C^T_M > 0` (the spec of `lem:transfer`, or the junk value `1`). -/
theorem CTM_pos (χ : ℝ → ℝ) (Mh : ℕ) : 0 < Rings.CTM χ Mh := by
  classical
  by_cases h : ∃ CTM CTO : ℝ, Rings.IsTransferConst χ Mh CTM CTO
  · exact (Rings.transferConsts_spec h).CTM_pos
  · have h' : ¬ ∃ x : ℝ × ℝ, Rings.IsTransferConst χ Mh x.1 x.2 :=
      fun ⟨x, hx⟩ => h ⟨x.1, x.2, hx⟩
    rw [Rings.CTM, Rings.transferConsts, dite_eq_right h']
    norm_num

theorem CM_pos (S : Standing) : 0 < S.CM := by
  show 0 < Rings.CM S.P.χ S.Mh
  rw [Rings.CM_def]
  exact mul_pos (CTM_pos _ _) (lt_of_lt_of_le one_pos (le_max_left _ _))

/-- `C_Q ≥ 0` (the spec of `thm:quiet`, or the junk value `0`). -/
theorem CQ_nonneg (S : Standing) : 0 ≤ S.CQ := by
  classical
  show 0 ≤ OneRing.CQ S.P.χ S.sh S.NQ
  by_cases h : ∃ majst CQ CΔ : ℝ, OneRing.IsQuietConst S.P.χ S.sh S.NQ majst CQ CΔ
  · exact (OneRing.quietConsts_spec h).CQ_nonneg
  · have h' : ¬ ∃ x : ℝ × ℝ × ℝ, OneRing.IsQuietConst S.P.χ S.sh S.NQ x.1 x.2.1 x.2.2 :=
      fun ⟨x, hx⟩ => h ⟨x.1, x.2.1, x.2.2, hx⟩
    rw [OneRing.CQ, OneRing.quietConsts, dite_eq_right h']

/-- `C₂ ≥ 1` (the spec of `thm:active`, or the junk value `1`). -/
theorem one_le_C2 (S : Standing) : 1 ≤ S.C2 := by
  classical
  show 1 ≤ OneRing.C2 S.P.χ S.s S.σ'
  by_cases h : ∃ (dH C₂ C₃ : ℝ) (κ₀ : ℝ → ℝ), OneRing.IsActiveConst S.P.χ S.s S.σ' dH C₂ C₃ κ₀
  · exact (OneRing.activeConsts_spec h).2.1
  · have h' : ¬ ∃ x : ℝ × ℝ × ℝ × (ℝ → ℝ),
        OneRing.IsActiveConst S.P.χ S.s S.σ' x.1 x.2.1 x.2.2.1 x.2.2.2 :=
      fun ⟨x, hx⟩ => h ⟨x.1, x.2.1, x.2.2.1, x.2.2.2, hx⟩
    rw [OneRing.C2, OneRing.activeConsts, dite_eq_right h']

/-- `C_* = (1 + c₄)/(2π) M_vort^{1/2} ≥ 0`. -/
theorem Cstar_nonneg : 0 ≤ Cstar := by
  have hc : 0 ≤ BS.cLpLinf 4 := by
    unfold BS.cLpLinf
    apply Real.rpow_nonneg
    have h43 : (4 : ℝ).conjExponent = 4 / 3 := by
      unfold Real.conjExponent; norm_num
    rw [h43]
    have := Real.pi_pos
    apply div_nonneg <;> linarith
  unfold Cstar
  have hpi := Real.pi_pos
  positivity

theorem one_le_Mh (S : Standing) : 1 ≤ S.Mh := by
  rw [Standing.Mh_def]
  omega

/-! ### The levels -/

theorem sigb_pos (S : Standing) (hS : S.Holds) : 0 < S.sigb :=
  (standing_levels S hS).1

theorem gSmall (S : Standing) (hS : S.Holds) : S.P.GSmall :=
  (standing_levels S hS).2.2.1

theorem sigb_le_sigma (S : Standing) (hS : S.Holds) {k : ℕ} (hk : k ∈ Finset.Icc 1 S.P.n) :
    S.sigb ≤ S.P.sigma k :=
  ((standing_levels S hS).2.2.2 k hk).2.2

theorem sigma_pos (S : Standing) (hS : S.Holds) {k : ℕ} (hk : k ∈ Finset.Icc 1 S.P.n) :
    0 < S.P.sigma k :=
  lt_of_lt_of_le (sigb_pos S hS) (sigb_le_sigma S hS hk)

theorem G_mem (S : Standing) (hS : S.Holds) {k : ℕ} (hk : k ∈ Finset.Icc 1 S.P.n) :
    S.P.G k ∈ Icc (0 : ℝ) Gbar :=
  ((standing_levels S hS).2.2.2 k hk).2.1

theorem A_succ (P : Approx) {k : ℕ} (hk : 1 ≤ k) : P.A (k + 1) = P.μ * P.A k :=
  amp_succ _ _ hk

theorem r_succ (P : Approx) {k : ℕ} (hk : 1 ≤ k) : P.r (k + 1) = P.s k * P.r k :=
  radius_succ _ _ hk

/-- `s_k ≤ s̄/2` for `k ≥ 1`. -/
theorem s_le_half {P : Approx} (hP : P.Valid) {k : ℕ} (hk : 1 ≤ k) : P.s k ≤ P.sbar / 2 := by
  have hμ := hP.datumParams.one_lt_μ
  have hsb := hP.datumParams.sbar_pos
  show P.sbar / (2 * P.μ) ^ k ≤ P.sbar / 2
  have h2 : (2 : ℝ) ≤ (2 * P.μ) ^ k := by
    calc (2 : ℝ) ≤ 2 * P.μ := by linarith
      _ = (2 * P.μ) ^ 1 := (pow_one _).symm
      _ ≤ (2 * P.μ) ^ k := pow_le_pow_right₀ (by linarith) hk
  exact div_le_div_of_nonneg_left hsb.le (by norm_num) h2

/-- `s_k ≤ a/32` for `k ≥ 1` (`s̄ ≤ a/16`). -/
theorem s_le_a {P : Approx} (hP : P.Valid) {k : ℕ} (hk : 1 ≤ k) : P.s k ≤ a / 32 := by
  have := s_le_half hP hk
  have := hP.datumParams.sbar_le
  linarith

/-- `N_j ∩ B_{6r_{j+1}} = ∅` (`6s_j ≤ 6a/32 < a/2`). -/
theorem Nk_inter_ball (S : Standing) (hS : S.Holds) {j : ℕ} (hj : 1 ≤ j) :
    S.P.Nk j ∩ ball 0 (6 * S.P.r (j + 1)) = ∅ := by
  have hr := hS.valid.r_pos j
  have hrs : S.P.r (j + 1) = S.P.s j * S.P.r j := r_succ S.P hj
  have hs := s_le_a hS.valid hj
  have ha := Relay.zero_lt_a
  refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  have hxN : ((S.P.r j : ℝ) : ℂ)⁻¹ * x ∈ annN := hx.1
  have hxb : ‖x‖ < 6 * S.P.r (j + 1) := mem_ball_zero_iff.mp hx.2
  have h1 : a / 2 ≤ ‖((S.P.r j : ℝ) : ℂ)⁻¹ * x‖ := hxN.1
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hr.le] at h1
  have h2 : a / 2 * S.P.r j ≤ ‖x‖ := by
    have := mul_le_mul_of_nonneg_left h1 hr.le
    rwa [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul, mul_comm] at this
  rw [hrs] at hxb
  nlinarith

/-! ### The clock of ring `j+1` under the hypotheses of `prop:relay` -/

variable {S : Standing} {C₀ K₁ : ℝ} {j : ℕ} {τ : ℝ}

theorem j_mem (h : S.RelayHyp C₀ K₁ j τ) : j ∈ Finset.Icc 1 S.P.n :=
  Finset.mem_Icc.mpr ⟨h.one_le, h.lt_n.le⟩

theorem succ_mem (h : S.RelayHyp C₀ K₁ j τ) : j + 1 ∈ Finset.Icc 1 S.P.n :=
  Finset.mem_Icc.mpr ⟨by omega, h.lt_n⟩

theorem ksh_mem (h : S.RelayHyp C₀ K₁ j τ) :
    S.P.ksh (j + 1) ∈ Ioo (0 : ℝ) S.P.δ₀ :=
  h.clock.ksh_mem le_rfl h.lt_n

theorem tsh_succ_nonneg (h : S.RelayHyp C₀ K₁ j τ) (hS : S.Holds) :
    0 ≤ S.P.tsh (j + 1) :=
  (S.P.clock_order hS.valid hS.hN (gSmall S hS) (by omega) h.clock).2.2.2 (j + 1)
    (Finset.mem_Icc.mpr ⟨le_rfl, h.lt_n⟩)

/-- `T̂_{j+1} = σ_{j+1}⁻¹ log(δ₀/κ♯_{j+1}) ≥ 0`. -/
theorem That_nonneg (h : S.RelayHyp C₀ K₁ j τ) (hS : S.Holds) :
    0 ≤ S.P.That (j + 1) := by
  have hk := (ksh_mem h)
  have hσ := sigma_pos S hS (succ_mem h)
  unfold Approx.That
  refine mul_nonneg (inv_nonneg.2 hσ.le) (Real.log_nonneg ?_)
  rw [le_div_iff₀ hk.1, one_mul]
  exact hk.2.le

theorem T_succ (h : S.RelayHyp C₀ K₁ j τ) :
    S.P.T (j + 1) = S.P.tsh (j + 1) + S.P.That (j + 1) / S.P.A (j + 1) :=
  S.P.T_of_ne (by have := h.lt_n; omega)

theorem tsh_j (h : S.RelayHyp C₀ K₁ j τ) :
    S.P.tsh j = S.P.T (j + 1) + S.P.Tpin / S.P.A (j + 1) :=
  S.P.tsh_eq_T_add h.lt_n

/-- `τ^sat = τ^act + T̂_{j+1}/μ`. -/
theorem tauSat_eq (h : S.RelayHyp C₀ K₁ j τ) (hS : S.Holds) :
    S.P.A j * S.P.T (j + 1) = S.P.A j * S.P.tsh (j + 1) + S.P.That (j + 1) / S.P.μ := by
  have hA := hS.valid.A_pos j
  have hμ : 0 < S.P.μ := by linarith [hS.one_lt_μ]
  rw [(T_succ h), A_succ S.P h.one_le]
  field_simp

/-- `t̄♯_j = τ^sat + T_pin/μ`. -/
theorem tash_eq (h : S.RelayHyp C₀ K₁ j τ) (hS : S.Holds) :
    S.P.tash j = S.P.A j * S.P.T (j + 1) + S.P.Tpin / S.P.μ := by
  have hA := hS.valid.A_pos j
  have hμ : 0 < S.P.μ := by linarith [hS.one_lt_μ]
  rw [Approx.tash_def, (tsh_j h), A_succ S.P h.one_le]
  field_simp

theorem tauAct_lt_tash (h : S.RelayHyp C₀ K₁ j τ) (hS : S.Holds) :
    S.P.A j * S.P.tsh (j + 1) < S.P.tash j := by
  have hμ : 0 < S.P.μ := by linarith [hS.one_lt_μ]
  have hT := hS.Tpin_pos
  have hTh := (That_nonneg h) hS
  rw [(tash_eq h) hS, (tauSat_eq h) hS]
  have : 0 ≤ S.P.That (j + 1) / S.P.μ := div_nonneg hTh hμ.le
  have : 0 < S.P.Tpin / S.P.μ := div_pos hT hμ
  linarith

theorem div_le_tsh (h : S.RelayHyp C₀ K₁ j τ) (hS : S.Holds) :
    τ / S.P.A j ≤ S.P.tsh j := by
  have hA := hS.valid.A_pos j
  rw [div_le_iff₀ hA, mul_comm]
  exact h.τ_le

/-! ### (Loc) on `[0, τ/A_j]` -/

/-- Ring `j` is quiet on `[0, τ/A_j]`: (Loc)(2) for ring `j`. -/
theorem loc_j (h : S.RelayHyp C₀ K₁ j τ) (hS : S.Holds) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (τ / S.P.A j)) :
    S.P.HOutDefined j t ∧ S.P.HInDefined j t ∧
      (S.P.ClockUpTo (j + 1) → S.P.T (j + 1) ≤ t →
        S.P.D (j + 1) t ⊆ closedBall 0 (S.P.confRadius j t)) :=
  (h.h1 t ht).2 j (j_mem h) (Or.inr (ht.2.trans ((div_le_tsh h) hS)))

theorem hDefined_j (h : S.RelayHyp C₀ K₁ j τ) (hS : S.Holds) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (τ / S.P.A j)) : S.P.HDefined j t :=
  ⟨((loc_j h) hS ht).2.1, ((loc_j h) hS ht).1⟩

/-- `S_j(t) ⊂ N_j` on `[0, τ/A_j]` ((Loc)(1); `t ≤ t♯_j < T_j` if `T_j` is defined). -/
theorem pertDefined_j (h : S.RelayHyp C₀ K₁ j τ) (hS : S.Holds) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (τ / S.P.A j)) : S.P.PertDefined j t := by
  refine (h.h1 t ht).1 j (j_mem h) fun hc => ?_
  have hco := S.P.clock_order hS.valid hS.hN (gSmall S hS) h.one_le hc
  have h1 := hco.1 j (Finset.mem_Icc.mpr ⟨le_rfl, h.lt_n.le⟩)
  linarith [ht.2, (div_le_tsh h) hS]

/-- `S_{j+1}(t) ⊂ N_{j+1}` for `t ∈ [0, τ/A_j]` with `t ≤ T_{j+1}` ((Loc)(1)). -/
theorem pertDefined_succ (h : S.RelayHyp C₀ K₁ j τ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (τ / S.P.A j)) (htT : t ≤ S.P.T (j + 1)) :
    S.P.PertDefined (j + 1) t :=
  (h.h1 t ht).1 (j + 1) (succ_mem h) fun _ => htT

/-- `h_{j+1}` is defined at `t ∈ [0, τ/A_j]` with `t ≤ t♯_{j+1}` ((Loc)(2) for ring `j+1`). -/
theorem hDefined_succ_quiet (h : S.RelayHyp C₀ K₁ j τ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (τ / S.P.A j)) (hts : t ≤ S.P.tsh (j + 1)) :
    S.P.HDefined (j + 1) t := by
  have hl := (h.h1 t ht).2 (j + 1) (succ_mem h) (Or.inr hts)
  exact ⟨hl.2.1, hl.1⟩

/-- `h^out_{j+1}` is defined on `[0, τ/A_j]` (`09_relay.tex:521-526`): the rings `i < j` lie
outside `B_{6r_j} ⊃ B_{6r_{j+1}}`, and ring `j` lies in `N_j`, which misses `B_{6r_{j+1}}`. -/
theorem hOutDefined_succ (h : S.RelayHyp C₀ K₁ j τ) (hS : S.Holds) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (τ / S.P.A j)) : S.P.HOutDefined (j + 1) t := by
  intro i hi
  have hi' := Finset.mem_Ico.mp hi
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi'.2) with hlt | hij
  · have hout := ((loc_j h) hS ht).1 i (Finset.mem_Ico.mpr ⟨hi'.1, hlt⟩)
    refine Set.eq_empty_of_subset_empty ?_
    rw [← hout]
    refine Set.inter_subset_inter_right _ (ball_subset_ball ?_)
    have hr := hS.valid.r_pos j
    have hrs : S.P.r (j + 1) = S.P.s j * S.P.r j := r_succ S.P h.one_le
    have hs := s_le_a hS.valid h.one_le
    have ha := Relay.a_lt_one
    rw [hrs]
    nlinarith
  · subst hij
    refine Set.eq_empty_of_subset_empty ?_
    rw [← Nk_inter_ball S hS h.one_le]
    exact Set.inter_subset_inter_left _ ((pertDefined_j h) hS ht)

/-! ### Continuity of the field norms -/

theorem mul_div_A (hS : S.Holds) (k : ℕ) (x : ℝ) : S.P.A k * (x / S.P.A k) = x :=
  mul_div_cancel₀ _ (hS.valid.A_pos k).ne'

/-- `η^in_j`, `η^out_j` and `η_j` are continuous on `[0,τ]`. -/
theorem eta_cont_j (h : S.RelayHyp C₀ K₁ j τ) (hS : S.Holds) :
    ContinuousOn (S.etaIn j) (Icc 0 τ) ∧ ContinuousOn (S.etaOut j) (Icc 0 τ) ∧
      ContinuousOn (S.eta j) (Icc 0 τ) := by
  have hc := S.P.eta_continuous hS.valid hS.hN h.one_le h.lt_n.le (t₁ := 0)
    (t₂ := τ / S.P.A j) le_rfl S.Mh
  rw [mul_zero, mul_div_A hS] at hc
  refine ⟨hc.1 fun t ht => ((loc_j h) hS ht).2.1, hc.2.1 fun t ht => ((loc_j h) hS ht).1,
    hc.2.2 fun t ht => (hDefined_j h) hS ht⟩

/-- `η_{j+1}` is continuous on `[0, μτ']` for `τ' ≤ min(τ, τ^act)`. -/
theorem eta_cont_succ (h : S.RelayHyp C₀ K₁ j τ) (hS : S.Holds) {τ' : ℝ}
    (hτ' : τ' ∈ Icc (0 : ℝ) (min τ (S.P.A j * S.P.tsh (j + 1)))) :
    ContinuousOn (S.eta (j + 1)) (Icc 0 (S.P.μ * τ')) := by
  have hA := hS.valid.A_pos j
  have hc := (S.P.eta_continuous hS.valid hS.hN (by omega : 1 ≤ j + 1) h.lt_n (t₁ := 0)
    (t₂ := τ' / S.P.A j) le_rfl S.Mh).2.2
  have he : S.P.A (j + 1) * (τ' / S.P.A j) = S.P.μ * τ' := by
    rw [A_succ S.P h.one_le]
    field_simp
  rw [mul_zero, he] at hc
  refine hc fun t ht => (hDefined_succ_quiet h) ⟨ht.1, ht.2.trans ?_⟩ (ht.2.trans ?_)
  · exact div_le_div_of_nonneg_right (hτ'.2.trans (min_le_left _ _)) hA.le
  · rw [div_le_iff₀ hA, mul_comm]
    exact hτ'.2.trans (min_le_right _ _)

end RelayH

end Relay

end NonUniqueEuler
