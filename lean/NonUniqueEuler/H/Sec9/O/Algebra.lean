import NonUniqueEuler.Defs.Sec9.All
import NonUniqueEuler.I.Sec9.Standing
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Helpers for `P/Sec9/O`: constants, ring parameters, `P̃`, geometric sums

Algebraic facts used in the proof of `lem:O` (`09_relay.tex:264-387`):
* signs of the constants: `C_M, C_O > 0`, `maj_* ∈ (0,1]`, `C_Q ≥ 0` (unconditional: the chosen
  constants satisfy their specification, and the junk values have the same signs), `C_Duh > 0`,
  `K_O > 0`;
* `A_j = μ^{j-i}A_i`, `μ^{i-j} = (μ^{j-i})⁻¹`, `s_p ≤ s̄`, `r_i = r_l ∏_{p=l}^{i-1} s_p`;
* `P̃_{i,j} > 0`, `P̃_{i,j} ≤ 1/2` (`i < j`), `b_{l,i}P̃_{l,i} = ∏_{p=l}^{i-1} K_O s_p^{2m}`
  (`09_relay.tex:338-343`);
* finite geometric sums and the final numerical inequality (the bracket `≤ 1/4`,
  `09_relay.tex:352-357`).
-/

noncomputable section

open Set

namespace NonUniqueEuler.Relay.OProof

open RingData Datum

/-! ### Signs of the constants -/

/-- `C^T_M > 0` (the spec of `lem:transfer`, or the junk value `1`). -/
theorem CTM_pos (χ : ℝ → ℝ) (Mh : ℕ) : 0 < Rings.CTM χ Mh := by
  classical
  by_cases h : ∃ CTM CTO : ℝ, Rings.IsTransferConst χ Mh CTM CTO
  · exact (Rings.transferConsts_spec h).CTM_pos
  · have h' : ¬ ∃ x : ℝ × ℝ, Rings.IsTransferConst χ Mh x.1 x.2 :=
      fun ⟨x, hx⟩ => h ⟨x.1, x.2, hx⟩
    simp only [Rings.CTM, Rings.transferConsts, dif_neg h']
    norm_num

/-- `C^T_O > 0` (the spec of `lem:transfer`, or the junk value `1`). -/
theorem CTO_pos (χ : ℝ → ℝ) (Mh : ℕ) : 0 < Rings.CTO χ Mh := by
  classical
  by_cases h : ∃ CTM CTO : ℝ, Rings.IsTransferConst χ Mh CTM CTO
  · exact (Rings.transferConsts_spec h).CTO_pos
  · have h' : ¬ ∃ x : ℝ × ℝ, Rings.IsTransferConst χ Mh x.1 x.2 :=
      fun ⟨x, hx⟩ => h ⟨x.1, x.2, hx⟩
    simp only [Rings.CTO, Rings.transferConsts, dif_neg h']
    norm_num

theorem CM_pos (S : Standing) : 0 < S.CM := by
  show 0 < Rings.CM S.P.χ S.Mh
  rw [Rings.CM_def]
  exact mul_pos (CTM_pos _ _) (lt_of_lt_of_le one_pos (le_max_left _ _))

theorem CO_pos (S : Standing) : 0 < S.CO := by
  show 0 < Rings.CO S.P.χ S.Mh
  rw [Rings.CO_def]
  exact mul_pos (CTO_pos _ _) (lt_of_lt_of_le one_pos (le_max_left _ _))

/-- `maj_* ∈ (0,1]` and `C_Q ≥ 0` (the spec of `thm:quiet`, or the junk values `(1, 0, 0)`). -/
theorem quiet_consts (S : Standing) : 0 < S.majst ∧ S.majst ≤ 1 ∧ 0 ≤ S.CQ := by
  classical
  show 0 < OneRing.majst S.P.χ S.sh S.NQ ∧ OneRing.majst S.P.χ S.sh S.NQ ≤ 1 ∧
    0 ≤ OneRing.CQ S.P.χ S.sh S.NQ
  by_cases h : ∃ majst CQ CΔ : ℝ, OneRing.IsQuietConst S.P.χ S.sh S.NQ majst CQ CΔ
  · have hq := OneRing.quietConsts_spec h
    exact ⟨hq.majst_mem.1, hq.majst_mem.2, hq.CQ_nonneg⟩
  · have h' : ¬ ∃ x : ℝ × ℝ × ℝ, OneRing.IsQuietConst S.P.χ S.sh S.NQ x.1 x.2.1 x.2.2 :=
      fun ⟨x, hx⟩ => h ⟨x.1, x.2.1, x.2.2, hx⟩
    simp only [OneRing.majst, OneRing.CQ, OneRing.quietConsts, dif_neg h']
    norm_num

theorem majst_pos (S : Standing) : 0 < S.majst := (quiet_consts S).1

theorem CQ_nonneg (S : Standing) : 0 ≤ S.CQ := (quiet_consts S).2.2

theorem sigb_pos (S : Standing) (hS : S.Holds) : 0 < S.sigb := (standing_levels S hS).1

theorem CDuh_pos (S : Standing) (hS : S.Holds) : 0 < S.CDuh := by
  have hb := sigb_pos S hS
  have hμ := hS.one_lt_μ
  have hμ1 : 0 < S.P.μ - 1 := by linarith
  have hμ0 : 0 < S.P.μ := by linarith
  show 0 < 2 * S.P.μ / (S.sigb * (S.P.μ - 1))
  positivity

/-- `1/C_Duh = σ_b(μ-1)/(2μ)`. -/
theorem CDuh_eq (S : Standing) (hS : S.Holds) :
    S.CDuh = 1 / (S.sigb * (S.P.μ - 1) / (2 * S.P.μ)) := by
  have hb := sigb_pos S hS
  have hμ := hS.one_lt_μ
  have hμ1 : S.P.μ - 1 ≠ 0 := by linarith
  have hμ0 : S.P.μ ≠ 0 := by linarith
  show 2 * S.P.μ / (S.sigb * (S.P.μ - 1)) = _
  field_simp

theorem KO_pos (S : Standing) (hS : S.Holds) : 0 < S.KO := by
  have h1 := CM_pos S
  have h2 := CQ_nonneg S
  have h3 := CDuh_pos S hS
  show 0 < 8 * S.CM * (S.CQ * S.CDuh + 1) + 32 * S.CM * S.CQ * S.CDuh
  have : 0 ≤ S.CQ * S.CDuh := mul_nonneg h2 h3.le
  have : 0 ≤ 32 * S.CM * S.CQ * S.CDuh := by positivity
  nlinarith

/-! ### Ring parameters -/

/-- `A_j = μ^{j-i} A_i` for `1 ≤ i ≤ j`. -/
theorem A_eq_pow_mul (P : Approx) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) :
    P.A j = P.μ ^ (j - i) * P.A i := by
  simp only [Approx.A, amp]
  rw [show j - 1 = (j - i) + (i - 1) by omega, pow_add]
  ring

/-- `μ^{i-j} = (μ^{j-i})⁻¹` for `i ≤ j`. -/
theorem zpow_sub_eq (μ : ℝ) {i j : ℕ} (hij : i ≤ j) :
    μ ^ ((i : ℤ) - j) = (μ ^ (j - i))⁻¹ := by
  rw [show ((i : ℤ) - j) = -((j - i : ℕ) : ℤ) by push_cast [Nat.cast_sub hij]; ring, zpow_neg,
    zpow_natCast]

theorem s_le_sbar (P : Approx) (hP : P.Valid) (p : ℕ) : P.s p ≤ P.sbar := by
  simp only [Approx.s, ratio]
  have hμ := hP.datumParams.one_lt_μ
  have h1 : 1 ≤ (2 * P.μ) ^ p := one_le_pow₀ (by linarith)
  exact div_le_self hP.datumParams.sbar_pos.le h1

/-- `r_i = r_l ∏_{p=l}^{i-1} s_p` for `1 ≤ l ≤ i`. -/
theorem r_eq_mul_prod (P : Approx) {l i : ℕ} (hl : 1 ≤ l) (hli : l ≤ i) :
    P.r i = P.r l * ∏ p ∈ Finset.Ico l i, P.s p := by
  simp only [Approx.r, Approx.s, radius]
  exact (Finset.prod_Ico_consecutive _ hl hli).symm

theorem b_nonneg (P : Approx) (hP : P.Valid) (l i : ℕ) : 0 ≤ P.b l i := by
  rw [Approx.b_def]
  have hμ : 0 < P.μ := by linarith [hP.datumParams.one_lt_μ]
  have := hP.r_pos i
  have := hP.r_pos l
  have : 0 < P.μ ^ ((l : ℤ) - i) := zpow_pos hμ _
  positivity

/-! ### `P̃_{i,j}` -/

theorem Ptil_pos (S : Standing) (hS : S.Holds) (i j : ℕ) : 0 < S.Ptil i j :=
  Finset.prod_pos fun p _ => mul_pos (KO_pos S hS) (hS.valid.eps_pos p)

theorem Ptil_nonneg (S : Standing) (hS : S.Holds) (i j : ℕ) : 0 ≤ S.Ptil i j :=
  (Ptil_pos S hS i j).le

/-- Each factor `K_Oε_p = K_Oμs_p^{m+2} ≤ K_Oμs̄^{m+2} ≤ 1/2`. -/
theorem KO_eps_le_half (S : Standing) (hS : S.Holds) (hsm : S.OSmall) (p : ℕ) :
    S.KO * S.P.eps p ≤ 1 / 2 := by
  have h := hsm.KO_mu_sbar
  have hs := s_le_sbar S.P hS.valid p
  have hs0 := (hS.valid.s_pos p).le
  have h5 : S.P.s p ^ 5 ≤ S.P.sbar ^ 5 := pow_le_pow_left₀ hs0 hs 5
  rw [Approx.eps_def]
  have hK := (KO_pos S hS).le
  have hμ : 0 ≤ S.P.μ := by linarith [hS.one_lt_μ]
  calc S.KO * (S.P.μ * S.P.s p ^ 5) ≤ S.KO * (S.P.μ * S.P.sbar ^ 5) := by gcongr
    _ = S.KO * S.P.μ * S.P.sbar ^ (3 + 2) := by ring
    _ ≤ 1 / 2 := h

/-- `P̃_{i,j} ≤ 1/2` for `i < j` (`09_relay.tex:310-312`). -/
theorem Ptil_le_half (S : Standing) (hS : S.Holds) (hsm : S.OSmall) {i j : ℕ} (hij : i < j) :
    S.Ptil i j ≤ 1 / 2 := by
  calc S.Ptil i j ≤ ∏ _p ∈ Finset.Ico i j, (1 / 2 : ℝ) :=
        Finset.prod_le_prod (fun p _ => (mul_pos (KO_pos S hS) (hS.valid.eps_pos p)).le)
          (fun p _ => KO_eps_le_half S hS hsm p)
    _ = (1 / 2) ^ (j - i) := by rw [Finset.prod_const, Nat.card_Ico]
    _ ≤ 1 / 2 := pow_le_of_le_one (by norm_num) (by norm_num) (by omega)

/-- `∏_{p=i}^{l-1} C_Mε_p = (C_M/K_O)^{l-i} P̃_{i,l}`. -/
theorem prod_CM_eps_eq (S : Standing) (hS : S.Holds) (i l : ℕ) :
    ∏ p ∈ Finset.Ico i l, S.CM * S.P.eps p = (S.CM / S.KO) ^ (l - i) * S.Ptil i l := by
  have hK := (KO_pos S hS).ne'
  rw [Standing.Ptil_def, ← Nat.card_Ico i l, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  field_simp

/-- `b_{l,i} P̃_{l,i} = ∏_{p=l}^{i-1} K_O s_p^{2m}` for `1 ≤ l ≤ i` (`09_relay.tex:338-341`). -/
theorem b_mul_Ptil (S : Standing) (hS : S.Holds) {l i : ℕ} (hl : 1 ≤ l) (hli : l ≤ i) :
    S.P.b l i * S.Ptil l i = ∏ p ∈ Finset.Ico l i, S.KO * S.P.s p ^ 6 := by
  have hμ : 0 < S.P.μ := by linarith [hS.one_lt_μ]
  have hrl := hS.valid.r_pos l
  have hr : S.P.r i / S.P.r l = ∏ p ∈ Finset.Ico l i, S.P.s p := by
    rw [r_eq_mul_prod S.P hl hli]
    field_simp
  have hfac : ∀ p ∈ Finset.Ico l i, S.KO * S.P.s p ^ 6 =
      (S.KO * S.P.eps p) * (S.P.μ⁻¹ * S.P.s p) := by
    intro p _
    rw [Approx.eps_def]
    field_simp
  have h2 : ∏ p ∈ Finset.Ico l i, S.KO * S.P.s p ^ 6 =
      (∏ p ∈ Finset.Ico l i, S.KO * S.P.eps p) *
        ((S.P.μ ^ (i - l))⁻¹ * ∏ p ∈ Finset.Ico l i, S.P.s p) := by
    rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib (s := Finset.Ico l i)
      (f := fun p => S.KO * S.P.eps p) (g := fun p => S.P.μ⁻¹ * S.P.s p)]
    congr 1
    rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ico, inv_pow]
  rw [Approx.b_def, hr, zpow_sub_eq _ hli, Standing.Ptil_def, h2]
  ring

/-- `∏_{p=l}^{i-1} K_O s_p^{2m} ≤ (K_O s̄^{2m})^{i-l}`. -/
theorem prod_KO_s6_le (S : Standing) (hS : S.Holds) (l i : ℕ) :
    ∏ p ∈ Finset.Ico l i, S.KO * S.P.s p ^ 6 ≤ (S.KO * S.P.sbar ^ 6) ^ (i - l) := by
  have hK := (KO_pos S hS).le
  calc ∏ p ∈ Finset.Ico l i, S.KO * S.P.s p ^ 6 ≤ ∏ _p ∈ Finset.Ico l i, S.KO * S.P.sbar ^ 6 := by
        refine Finset.prod_le_prod (fun p _ => ?_) (fun p _ => ?_)
        · have := (hS.valid.s_pos p).le
          positivity
        · have hs := s_le_sbar S.P hS.valid p
          have hs0 := (hS.valid.s_pos p).le
          gcongr
    _ = (S.KO * S.P.sbar ^ 6) ^ (i - l) := by rw [Finset.prod_const, Nat.card_Ico]

/-! ### Finite geometric sums -/

/-- `Σ_{l=1}^{i-1} q^{i-l} ≤ (4/3) q` for `0 ≤ q ≤ 1/4`. -/
theorem geom_outer_le {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 4) (i : ℕ) :
    ∑ l ∈ Finset.Ico 1 i, q ^ (i - l) ≤ 4 / 3 * q := by
  rw [Finset.sum_Ico_reflect (fun k => q ^ k) 1 (Nat.le_succ i)]
  rw [show i + 1 - i = 1 by omega, show i + 1 - 1 = i by omega]
  have h := geom_sum_Ico_le_of_lt_one (m := 1) (n := i) hq0 (by linarith)
  have h1 : 0 < 1 - q := by linarith
  have h2 : q ^ 1 / (1 - q) ≤ 4 / 3 * q := by
    rw [pow_one, div_le_iff₀ h1]
    nlinarith
  linarith

/-- `Σ_{i=1}^{j-1} q^{j-1-i} ≤ 4/3` for `0 ≤ q ≤ 1/4` and `j ≥ 1`. -/
theorem geom_theta_le {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 4) {j : ℕ} (hj : 1 ≤ j) :
    ∑ i ∈ Finset.Ico 1 j, q ^ (j - 1 - i) ≤ 4 / 3 := by
  rw [Finset.sum_Ico_reflect (fun k => q ^ k) 1 (show j ≤ j - 1 + 1 by omega)]
  rw [show j - 1 + 1 - j = 0 by omega, show j - 1 + 1 - 1 = j - 1 by omega]
  have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := j - 1) hq0 (by linarith)
  have h1 : 0 < 1 - q := by linarith
  have h2 : q ^ 0 / (1 - q) ≤ 4 / 3 := by
    rw [pow_zero, div_le_iff₀ h1]
    nlinarith
  linarith

/-- `Σ_{l=i+1}^{j} X^{l-i} ≤ (8/7) X` for `0 ≤ X ≤ 1/8`. -/
theorem geom_inner_le {X : ℝ} (hX0 : 0 ≤ X) (hX : X ≤ 1 / 8) (i j : ℕ) :
    ∑ l ∈ Finset.Ico (i + 1) (j + 1), X ^ (l - i) ≤ 8 / 7 * X := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hterm : ∀ k ∈ Finset.range (j + 1 - (i + 1)), X ^ (i + 1 + k - i) = X * X ^ k := by
    intro k _
    rw [show i + 1 + k - i = k + 1 by omega, pow_succ, mul_comm]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.range_eq_Ico]
  have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := j + 1 - (i + 1)) hX0 (by linarith)
  have h1 : 0 < 1 - X := by linarith
  have h2 : X ^ 0 / (1 - X) ≤ 8 / 7 := by
    rw [pow_zero, div_le_iff₀ h1]
    nlinarith
  have h3 := mul_le_mul_of_nonneg_left (h.trans h2) hX0
  linarith

/-! ### The numerical inequality of `lem:O` -/

/-- `C_M/K_O ≤ 1/8` and `(C_M/K_O)(C_QC_Duh + 1) ≤ 1/8` (`K_O ≥ 8C_M(C_QC_Duh + 1)`). -/
theorem CM_div_KO_le (S : Standing) (hS : S.Holds) :
    0 ≤ S.CM / S.KO ∧ S.CM / S.KO ≤ 1 / 8 ∧ S.CM / S.KO * (S.CQ * S.CDuh + 1) ≤ 1 / 8 := by
  have hK := KO_pos S hS
  have hM := CM_pos S
  have hQ := CQ_nonneg S
  have hD := CDuh_pos S hS
  have hQD : 0 ≤ S.CQ * S.CDuh := mul_nonneg hQ hD.le
  have hKdef : S.KO = 8 * S.CM * (S.CQ * S.CDuh + 1) + 32 * S.CM * S.CQ * S.CDuh := rfl
  have h32 : 0 ≤ 32 * S.CM * S.CQ * S.CDuh := by positivity
  have hmain : S.CM / S.KO * (S.CQ * S.CDuh + 1) ≤ 1 / 8 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hK]
    nlinarith
  refine ⟨div_nonneg hM.le hK.le, ?_, hmain⟩
  have : S.CM / S.KO ≤ S.CM / S.KO * (S.CQ * S.CDuh + 1) := by
    have := div_nonneg hM.le hK.le
    nlinarith
  linarith

/-- **The bracket of `lem:O` is `< 1/4`** (`09_relay.tex:352-357`): with `X = C_M/K_O`,
`a₁ = (8/7)XC_Q + (4/3)C_OC_QK_Os̄^{2m}` and `a₂ = X`, `a₁C_Duh + a₂ ≤ 1/4`. -/
theorem bracket_le (S : Standing) (hS : S.Holds) (hsm : S.OSmall) :
    (8 / 7 * (S.CM / S.KO) * S.CQ + 4 / 3 * (S.CO * S.CQ * S.KO * S.P.sbar ^ 6)) * S.CDuh +
      S.CM / S.KO ≤ 1 / 4 := by
  obtain ⟨hX0, hX, hXQ⟩ := CM_div_KO_le S hS
  have h16 := hsm.CO_KO_sbar
  have h16' : S.CO * S.CQ * S.KO * S.P.sbar ^ 6 * S.CDuh ≤ 1 / 16 := by
    have : 16 * S.CO * S.CQ * S.CDuh * S.KO * S.P.sbar ^ (2 * 3) =
        16 * (S.CO * S.CQ * S.KO * S.P.sbar ^ 6 * S.CDuh) := by ring
    linarith
  have hexp : (8 / 7 * (S.CM / S.KO) * S.CQ + 4 / 3 * (S.CO * S.CQ * S.KO * S.P.sbar ^ 6)) *
      S.CDuh + S.CM / S.KO =
      8 / 7 * (S.CM / S.KO * (S.CQ * S.CDuh + 1)) - 1 / 7 * (S.CM / S.KO) +
        4 / 3 * (S.CO * S.CQ * S.KO * S.P.sbar ^ 6 * S.CDuh) := by ring
  rw [hexp]
  nlinarith

end NonUniqueEuler.Relay.OProof
