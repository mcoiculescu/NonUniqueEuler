import NonUniqueEuler.Defs.Sec9.All
import NonUniqueEuler.I.Sec6.RegionsBasic

/-!
# Helpers for `lem:Oprime`: positivity of the constants, the ring parameters, `w_i(0) = 0`

Helper file of `P/Sec9/Oprime.lean` (`09_relay.tex:632-738`). Everything here is proved.

* positivity of the chosen constants `C_M`, `C_O` (`> 0`), `C_Q` (`≥ 0`), `C₂ ≥ 1`, `I_p ≥ 0`,
  `K_O ≥ 0` (the specifications, or the junk values, which have the same signs);
* the algebra of `A_k`, `r_k`, `s_k`, `b_{i,k}`, `P̃_{i,j}`: `b_{j,k}b_{i,j} = b_{i,k}`,
  `b_{j,j+1}ε_j = s_j^{2m}`, `b_{i,j+1}P̃_{i,j+1} = b_{i,j}P̃_{i,j}K_Os_j^{2m}`, and
  `Σ_{i<j} b_{i,j}P̃_{i,j} ≤ 1/3` when `K_Os̄^{2m} ≤ 1/4` (`09_relay.tex:651-657`);
* `w_i(0) = 0` for `1 ≤ i < n` (the rings `i < n` start at `Φ` in their units,
  `09_relay.tex:648-650`), from `eq:omega-ge` (`regions_basic_three`) and `Φ_0⁻¹ = id`
  (`maxFlow_self`: the maximal flow at its initial time is the identity, also for the junk value).
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

namespace OprimeH

open RingData Datum

/-! ### Positivity of the chosen constants -/

/-- `C^T_M > 0` (the spec of `lem:transfer`, or the junk value `1`). -/
theorem CTM_pos (χ : ℝ → ℝ) (Mh : ℕ) : 0 < Rings.CTM χ Mh := by
  classical
  by_cases h : ∃ CTM CTO : ℝ, Rings.IsTransferConst χ Mh CTM CTO
  · exact (Rings.transferConsts_spec h).CTM_pos
  · have h' : ¬ ∃ x : ℝ × ℝ, Rings.IsTransferConst χ Mh x.1 x.2 :=
      fun ⟨x, hx⟩ => h ⟨x.1, x.2, hx⟩
    rw [Rings.CTM, Rings.transferConsts, dite_eq_right h']
    norm_num

/-- `C^T_O > 0` (the spec of `lem:transfer`, or the junk value `1`). -/
theorem CTO_pos (χ : ℝ → ℝ) (Mh : ℕ) : 0 < Rings.CTO χ Mh := by
  classical
  by_cases h : ∃ CTM CTO : ℝ, Rings.IsTransferConst χ Mh CTM CTO
  · exact (Rings.transferConsts_spec h).CTO_pos
  · have h' : ¬ ∃ x : ℝ × ℝ, Rings.IsTransferConst χ Mh x.1 x.2 :=
      fun ⟨x, hx⟩ => h ⟨x.1, x.2, hx⟩
    rw [Rings.CTO, Rings.transferConsts, dite_eq_right h']
    norm_num

theorem CM_pos (S : Standing) : 0 < S.CM := by
  show 0 < Rings.CM S.P.χ S.Mh
  rw [Rings.CM_def]
  exact mul_pos (CTM_pos _ _) (lt_of_lt_of_le one_pos (le_max_left _ _))

theorem CO_pos (S : Standing) : 0 < S.CO := by
  show 0 < Rings.CO S.P.χ S.Mh
  rw [Rings.CO_def]
  exact mul_pos (CTO_pos _ _) (lt_of_lt_of_le one_pos (le_max_left _ _))

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

/-- `I_p(x) ≥ 0` (the integral of a nonnegative function, or the junk value `0`). -/
theorem Ip_nonneg (p : ℕ) (x : ℝ) : 0 ≤ Ip p x := by
  unfold Ip
  refine setIntegral_nonneg measurableSet_Ioi fun u hu => ?_
  have hu' : (0 : ℝ) < u := hu
  have : (0 : ℝ) ≤ 1 + u := by linarith
  positivity

/-- `C_Duh = 2μ/(σ_b(μ-1)) ≥ 0` and `K_O ≥ 0` when `σ_b > 0`. -/
theorem KO_nonneg (S : Standing) (hS : S.Holds) (hsb : 0 < S.sigb) : 0 ≤ S.KO := by
  have hμ := hS.one_lt_μ
  have hCM := CM_pos S
  have hCQ := CQ_nonneg S
  have hD : 0 ≤ S.CDuh := by
    unfold Standing.CDuh
    have : 0 < S.sigb * (S.P.μ - 1) := mul_pos hsb (by linarith)
    have : 0 < 2 * S.P.μ := by linarith
    positivity
  unfold Standing.KO
  positivity

/-! ### The ring parameters -/

variable {P : Approx}

theorem A_succ (P : Approx) {k : ℕ} (hk : 1 ≤ k) : P.A (k + 1) = P.μ * P.A k :=
  amp_succ _ _ hk

theorem r_succ (P : Approx) {k : ℕ} (hk : 1 ≤ k) : P.r (k + 1) = P.s k * P.r k :=
  radius_succ _ _ hk

/-- `s_k ≤ s̄/2` for `k ≥ 1`. -/
theorem s_le_half (hP : P.Valid) {k : ℕ} (hk : 1 ≤ k) : P.s k ≤ P.sbar / 2 := by
  have hμ := hP.datumParams.one_lt_μ
  have hsb := hP.datumParams.sbar_pos
  show P.sbar / (2 * P.μ) ^ k ≤ P.sbar / 2
  have h2 : (2 : ℝ) ≤ (2 * P.μ) ^ k := by
    calc (2 : ℝ) ≤ 2 * P.μ := by linarith
      _ = (2 * P.μ) ^ 1 := (pow_one _).symm
      _ ≤ (2 * P.μ) ^ k := pow_le_pow_right₀ (by linarith) hk
  exact div_le_div_of_nonneg_left hsb.le (by norm_num) h2

theorem s_le_sbar (hP : P.Valid) {k : ℕ} (hk : 1 ≤ k) : P.s k ≤ P.sbar := by
  have := s_le_half hP hk
  have := hP.datumParams.sbar_pos
  linarith

/-- `s_k ≤ a/32` for `k ≥ 1` (`s̄ ≤ a/16`). -/
theorem s_le_a (hP : P.Valid) {k : ℕ} (hk : 1 ≤ k) : P.s k ≤ a / 32 := by
  have := s_le_half hP hk
  have := hP.datumParams.sbar_le
  linarith

theorem b_nonneg (hP : P.Valid) (i k : ℕ) : 0 ≤ P.b i k := by
  rw [Approx.b_def]
  have hμ : 0 < P.μ := by linarith [hP.datumParams.one_lt_μ]
  have := hP.r_pos i
  have := hP.r_pos k
  have : 0 < P.μ ^ ((i : ℤ) - k) := zpow_pos hμ _
  positivity

theorem b_self (hP : P.Valid) (i : ℕ) : P.b i i = 1 := by
  rw [Approx.b_def, sub_self, zpow_zero, one_mul, div_self (hP.r_pos i).ne']

/-- `b_{j,k} b_{i,j} = b_{i,k}`. -/
theorem b_mul (hP : P.Valid) (i j k : ℕ) : P.b j k * P.b i j = P.b i k := by
  simp only [Approx.b_def]
  have hμ : P.μ ≠ 0 := by linarith [hP.datumParams.one_lt_μ]
  have hri := (hP.r_pos i).ne'
  have hrj := (hP.r_pos j).ne'
  have hz : P.μ ^ ((j : ℤ) - k) * P.μ ^ ((i : ℤ) - j) = P.μ ^ ((i : ℤ) - k) := by
    rw [← zpow_add₀ hμ]
    congr 1
    ring
  calc P.μ ^ ((j : ℤ) - k) * (P.r k / P.r j) * (P.μ ^ ((i : ℤ) - j) * (P.r j / P.r i))
      = (P.μ ^ ((j : ℤ) - k) * P.μ ^ ((i : ℤ) - j)) * (P.r k / P.r j * (P.r j / P.r i)) := by
        ring
    _ = P.μ ^ ((i : ℤ) - k) * (P.r k / P.r i) := by
        rw [hz]
        congr 1
        field_simp

/-- `b_{j,j+1} = μ⁻¹ s_j` for `j ≥ 1`. -/
theorem b_succ (hP : P.Valid) {j : ℕ} (hj : 1 ≤ j) : P.b j (j + 1) = P.μ⁻¹ * P.s j := by
  rw [Approx.b_def, r_succ P hj]
  have hrj := (hP.r_pos j).ne'
  have hz : ((j : ℤ) - ((j + 1 : ℕ) : ℤ)) = -1 := by push_cast; ring
  rw [hz, zpow_neg_one]
  congr 1
  field_simp

/-- `b_{j,j+1} ε_j = s_j^{2m}` (`09_relay.tex:731`). -/
theorem b_succ_mul_eps (hP : P.Valid) {j : ℕ} (hj : 1 ≤ j) :
    P.b j (j + 1) * P.eps j = P.s j ^ (2 * 3) := by
  rw [b_succ hP hj, Approx.eps_def]
  have hμ : P.μ ≠ 0 := by linarith [hP.datumParams.one_lt_μ]
  field_simp

theorem Ptil_succ (S : Standing) {i j : ℕ} (hij : i ≤ j) :
    S.Ptil i (j + 1) = S.Ptil i j * (S.KO * S.P.eps j) := by
  simp only [Standing.Ptil_def]
  exact Finset.prod_Ico_succ_top hij _

theorem Ptil_nonneg (S : Standing) (hS : S.Holds) (hsb : 0 < S.sigb) (i j : ℕ) :
    0 ≤ S.Ptil i j := by
  rw [Standing.Ptil_def]
  exact Finset.prod_nonneg fun p _ =>
    mul_nonneg (KO_nonneg S hS hsb) (hS.valid.eps_pos p).le

/-- `b_{i,j+1} P̃_{i,j+1} = b_{i,j} P̃_{i,j} · K_O s_j^{2m}` for `1 ≤ i ≤ j`
(`09_relay.tex:651-655`). -/
theorem bPtil_succ (S : Standing) (hS : S.Holds) {i j : ℕ} (hj : 1 ≤ j) (hij : i ≤ j) :
    S.P.b i (j + 1) * S.Ptil i (j + 1) =
      S.P.b i j * S.Ptil i j * (S.KO * S.P.s j ^ (2 * 3)) := by
  rw [← b_mul hS.valid i j (j + 1), Ptil_succ S hij]
  have h := b_succ_mul_eps hS.valid hj
  calc S.P.b j (j + 1) * S.P.b i j * (S.Ptil i j * (S.KO * S.P.eps j))
      = S.P.b i j * S.Ptil i j * (S.KO * (S.P.b j (j + 1) * S.P.eps j)) := by ring
    _ = _ := by rw [h]

/-- `Σ_{i<j} b_{i,j} P̃_{i,j} ≤ 1/3` if `K_O s̄^{2m} ≤ 1/4` (`09_relay.tex:651-657`:
`b_{i,j}P̃_{i,j} ≤ 4^{-(j-i)}`). -/
theorem sum_bPtil_le (S : Standing) (hS : S.Holds) (hsb : 0 < S.sigb)
    (hsmall : S.KO * S.P.sbar ^ (2 * 3) ≤ 1 / 4) :
    ∀ j : ℕ, 1 ≤ j → ∑ i ∈ Finset.Ico 1 j, S.P.b i j * S.Ptil i j ≤ 1 / 3 := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => simp
  | succ j hj ih =>
    rw [Finset.sum_Ico_succ_top hj]
    have hc0 : 0 ≤ S.KO * S.P.s j ^ (2 * 3) :=
      mul_nonneg (KO_nonneg S hS hsb) (pow_nonneg (hS.valid.s_pos j).le _)
    have hc1 : S.KO * S.P.s j ^ (2 * 3) ≤ 1 / 4 := by
      refine le_trans ?_ hsmall
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (hS.valid.s_pos j).le (s_le_sbar hS.valid hj) _)
        (KO_nonneg S hS hsb)
    have hsum : ∑ i ∈ Finset.Ico 1 j, S.P.b i (j + 1) * S.Ptil i (j + 1) =
        (∑ i ∈ Finset.Ico 1 j, S.P.b i j * S.Ptil i j) * (S.KO * S.P.s j ^ (2 * 3)) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_Ico.mp hi
      exact bPtil_succ S hS hj hi'.2.le
    have hlast : S.P.b j (j + 1) * S.Ptil j (j + 1) = S.KO * S.P.s j ^ (2 * 3) := by
      rw [bPtil_succ S hS hj le_rfl, b_self hS.valid, Standing.Ptil_self]
      ring
    rw [hsum, hlast]
    have hs0 : 0 ≤ ∑ i ∈ Finset.Ico 1 j, S.P.b i j * S.Ptil i j :=
      Finset.sum_nonneg fun i _ => mul_nonneg (b_nonneg hS.valid _ _) (Ptil_nonneg S hS hsb _ _)
    nlinarith

/-! ### `w_i(0) = 0` for the rings `i < n` -/

/-- The maximal flow at its initial time is the identity (also for the junk value). -/
theorem maxFlow_self {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : ℝ → E → E)
    (U : Set (ℝ × E)) (s : ℝ) (y : E) : Smooth.maxFlow F U s s y = y := by
  classical
  by_cases h : ∃ (J : Set ℝ) (γ : ℝ → E), Smooth.IsMaxSol F U s y J γ
  · exact (Smooth.isMaxSol_maxFlow h).init
  · rw [Smooth.maxFlow, dite_eq_right h]

/-- `Φ_0⁻¹ = id`. -/
theorem flowInv_zero (P : Approx) (x : ℂ) : P.flowInv 0 x = x :=
  maxFlow_self _ _ _ _

/-- **`w_i(0) = 0` for `1 ≤ i < n`**: the rings `i < n` start at `Φ` in their units
(`09_relay.tex:648-650`). -/
theorem w_zero (hP : P.Valid) (hN : NumericalHypothesis P.χ) {i : ℕ} (hi : 1 ≤ i)
    (hin : i < P.n) : P.w i 0 = 0 := by
  have hmem : i ∈ Finset.Icc 1 P.n := Finset.mem_Icc.mpr ⟨hi, hin.le⟩
  have h3 := (Approx.regions_basic_three P hP hN hmem le_rfl).1
  have hfun : P.omegaRing i 0 = P.term i := by
    rw [h3]
    funext x
    rw [flowInv_zero]
  have h0 : P.unitsVort i (P.term i) = ringPhi P.χ := hP.ringConfig_ring0 hi hin
  funext y
  rw [Approx.w_apply, hfun, h0]
  simp

end OprimeH

end Relay

end NonUniqueEuler
