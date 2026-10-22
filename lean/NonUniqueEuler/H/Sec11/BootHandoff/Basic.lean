import NonUniqueEuler.Defs.Sec11.Extra2Boot
import NonUniqueEuler.I.Sec10.ConstantsPos
import NonUniqueEuler.I.Sec9.Standing
import NonUniqueEuler.I.Sec6.Clock
import NonUniqueEuler.I.Sec5.ActiveT1

/-!
# Helper for `P/Sec11/BootHandoff.lean`: elementary facts

Helper of the proof of Step 3 of `prop:bootstrap` (`11_bootstrap.tex:298-388`): positivity of
`A_k`, `σ_k`, `T̂_k`; the order of the clock times around `t♯_k` (`lem:clock`(1)); rings are not
debris before their activation time; `s_k ≤ s̄`; monotonicity of `‖·‖_{H^k}` in `k`; `𝒩₋_k ⊂ N_k`;
`maj ≥ 0`; the signs of `θ_j`, `η_{b,k}`; `η_{b,k} ≤ η_b`; monotonicity of the conclusions of
`thm:active` in `η_b` ("the bounds increase with `η_b`", `11_bootstrap.tex:316-318`); and
`ρ̂_k(0) = C₀` (`11_bootstrap.tex:383`). All proved.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

namespace BootHandoffH

open RingData Datum

variable {S : Standing}

/-- The signs of the constants (`lem:nonempty`), from (SA). -/
theorem constPos (hS : S.Holds) : S.ConstPos :=
  constants_pos S hS.admissible hS.hN hS.σ'_gt hS.σ'_lt_sigma hS.δ₀_pos hS.one_lt_μ hS.Tpin_pos

theorem A_pos (hS : S.Holds) (k : ℕ) : 0 < S.P.A k := hS.valid.A_pos k

theorem s_pos (hS : S.Holds) (k : ℕ) : 0 < S.P.s k := hS.valid.s_pos k

/-- `s_k ≤ s̄`. -/
theorem s_le_sbar (hS : S.Holds) (k : ℕ) : S.P.s k ≤ S.P.sbar := by
  show S.P.sbar / (2 * S.P.μ) ^ k ≤ S.P.sbar
  have hμ := hS.one_lt_μ
  exact div_le_self hS.sbar_pos.le (one_le_pow₀ (by linarith))

/-- `s_k^5 ≤ s̄^5`. -/
theorem s_pow_le (hS : S.Holds) (k : ℕ) : S.P.s k ^ (3 + 2) ≤ S.P.sbar ^ (3 + 2) :=
  pow_le_pow_left₀ (s_pos hS k).le (s_le_sbar hS k) _

/-- `σ_i ≥ σ_b > 0` for every level `i ∈ [1, n]` (`standing_levels`). -/
theorem sigma_pos (hS : S.Holds) {i : ℕ} (hi : i ∈ Finset.Icc 1 S.P.n) : 0 < S.P.sigma i := by
  obtain ⟨hb, -, -, hlev⟩ := standing_levels S hS
  exact lt_of_lt_of_le hb (hlev i hi).2.2

/-- `σ' < σ_i` for every level `i ∈ [1, n]`. -/
theorem sigma'_lt (hS : S.Holds) {i : ℕ} (hi : i ∈ Finset.Icc 1 S.P.n) : S.σ' < S.P.sigma i := by
  obtain ⟨-, -, -, hlev⟩ := standing_levels S hS
  exact lt_of_lt_of_le hS.σ'_lt_sigb (hlev i hi).2.2

/-- `T̂_i ≥ 0` when `κ♯_i ∈ (0, δ₀)`. -/
theorem That_nonneg (hS : S.Holds) {i : ℕ} (hi : i ∈ Finset.Icc 1 S.P.n)
    (hκ : S.P.ksh i ∈ Ioo (0 : ℝ) S.P.δ₀) : 0 ≤ S.P.That i := by
  show 0 ≤ (S.P.sigma i)⁻¹ * Real.log (S.P.δ₀ / S.P.ksh i)
  have hσ := sigma_pos hS hi
  have h1 : 1 ≤ S.P.δ₀ / S.P.ksh i := by
    rw [le_div_iff₀ hκ.1]
    linarith [hκ.2]
  exact mul_nonneg (inv_nonneg.2 hσ.le) (Real.log_nonneg h1)

theorem T_eq {i : ℕ} (hin : i ≤ S.P.n) : S.P.T i = S.P.tsh i + S.P.That i / S.P.A i :=
  S.P.T_of_ne (by omega)

/-- `t♯_i ≤ T_i` when `κ♯_i ∈ (0, δ₀)`. -/
theorem tsh_le_T (hS : S.Holds) {i : ℕ} (hi : i ∈ Finset.Icc 1 S.P.n)
    (hκ : S.P.ksh i ∈ Ioo (0 : ℝ) S.P.δ₀) : S.P.tsh i ≤ S.P.T i := by
  rw [T_eq (Finset.mem_Icc.1 hi).2]
  have := div_nonneg (That_nonneg hS hi hκ) (A_pos hS i).le
  linarith

/-- A ring is not debris at a time `t ≤ t♯_i`. -/
theorem not_debris_of_le_tsh (hS : S.Holds) {i : ℕ} (hi : i ∈ Finset.Icc 1 S.P.n) {t : ℝ}
    (ht : t ≤ S.P.tsh i) : ¬ S.P.DebrisAt i t := by
  rintro ⟨hc, hT⟩
  have := tsh_le_T hS hi (hc.ksh_mem le_rfl (Finset.mem_Icc.1 hi).2)
  linarith

/-- A ring is not debris at a time `t ≤ T_i`. -/
theorem not_debris_of_le_T {i : ℕ} {t : ℝ} (ht : t ≤ S.P.T i) : ¬ S.P.DebrisAt i t :=
  fun h => absurd h.2 (not_lt.2 ht)

/-- **The order of the clock around `t♯_k`** (`lem:clock`(1), `def:clock`): for `1 ≤ k < n` with
the clock defined up to level `k+1`, `0 ≤ t♯_{k+1} ≤ T_{k+1} ≤ t♯_k`, and
`t♯_k = T_{k+1} + T_pin/A_{k+1}`. -/
theorem clock_around (hS : S.Holds) {k : ℕ} (hk : 1 ≤ k) (hkn : k < S.P.n)
    (hc : S.P.ClockUpTo (k + 1)) :
    0 ≤ S.P.tsh (k + 1) ∧ S.P.tsh (k + 1) ≤ S.P.T (k + 1) ∧ S.P.T (k + 1) ≤ S.P.tsh k ∧
      S.P.tsh k = S.P.T (k + 1) + S.P.Tpin / S.P.A (k + 1) := by
  obtain ⟨-, -, hG, -⟩ := standing_levels S hS
  obtain ⟨-, -, -, h0⟩ := Approx.clock_order S.P hS.valid hS.hN hG (by omega : 1 ≤ k + 1) hc
  have hi : k + 1 ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hi' : k + 1 ∈ Finset.Icc (k + 1) S.P.n := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
  have heq := S.P.tsh_eq_T_add hkn
  have hT := div_nonneg hS.Tpin_pos.le (A_pos hS (k + 1)).le
  refine ⟨h0 _ hi', tsh_le_T hS hi (hc.ksh_mem le_rfl (by omega)), by linarith, heq⟩

/-- `0 ≤ t♯_k` (from `clock_around`). -/
theorem tsh_nonneg (hS : S.Holds) {k : ℕ} (hk : 1 ≤ k) (hkn : k < S.P.n)
    (hc : S.P.ClockUpTo (k + 1)) : 0 ≤ S.P.tsh k := by
  obtain ⟨h1, h2, h3, -⟩ := clock_around hS hk hkn hc
  linarith

/-- `t̄♯_k / A_k = t♯_k`. -/
theorem tash_div (hS : S.Holds) (k : ℕ) : S.P.tash k / S.P.A k = S.P.tsh k := by
  rw [Approx.tash_def, mul_div_cancel_left₀ _ (A_pos hS k).ne']

/-- `A_k (τ / A_k) = τ`. -/
theorem A_mul_div (hS : S.Holds) (k : ℕ) (τ : ℝ) : S.P.A k * (τ / S.P.A k) = τ := by
  rw [mul_div_cancel₀ _ (A_pos hS k).ne']

/-- `‖f‖_{H^k} ≤ ‖f‖_{H^{k'}}` for `k ≤ k'` (the sum defining the norm only gains terms). -/
theorem normH_mono {k k' : ℕ} (hk : k ≤ k') (f : ℂ → ℂ) : Sob.normH k f ≤ Sob.normH k' f := by
  unfold Sob.normH Sob.normHOn
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro γ hγ
    simp only [Sob.multiIdx, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hγ ⊢
    omega
  · intro _ _ _
    exact sq_nonneg _

/-- `s ≤ s_h = M - 1` (`M ≥ s + 4`). -/
theorem s_le_sh (S : Standing) : S.s ≤ S.sh := by
  have h4 := OneRing.add_four_le_Mact S.P.χ S.s
  simp only [Standing.sh, Standing.M]
  omega

/-- `𝒩₋_k = r_k 𝒩₋ ⊂ r_k N = N_k`. -/
theorem Nmk_subset_Nk (k : ℕ) : S.P.Nmk k ⊆ S.P.Nk k := by
  intro x hx
  have hx' : ((S.P.r k : ℂ)⁻¹ * x) ∈ annNm := hx
  show ((S.P.r k : ℂ)⁻¹ * x) ∈ annN
  rw [mem_annNm] at hx'
  rw [mem_annN]
  have ha := zero_lt_a
  constructor <;> linarith [hx'.1, hx'.2]

/-- `maj_k(τ) ≥ 0` for `τ ≥ 0`. -/
theorem maj_nonneg (k : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) : 0 ≤ S.maj k τ := by
  show 0 ≤ ∫ v in (0 : ℝ)..τ, Real.exp (S.P.sigma k * (τ - v)) * S.P.eta S.Mh k v
  exact intervalIntegral.integral_nonneg hτ fun v _ =>
    mul_nonneg (Real.exp_pos _).le (S.P.eta_nonneg _ _ _)

/-- `0 ≤ I_p(x)`. -/
theorem Ip_nonneg' (p : ℕ) (x : ℝ) : 0 ≤ Ip p x := by
  unfold Ip
  refine setIntegral_nonneg measurableSet_Ioi fun u hu => ?_
  have : 0 ≤ 1 + u := by linarith [mem_Ioi.1 hu]
  positivity

theorem theta_nonneg (hpos : S.ConstPos) (hS : S.Holds) (j : ℕ) : 0 ≤ S.theta j := by
  unfold Standing.theta
  split_ifs
  · have := hpos.CO_pos
    have := hpos.CQ_nonneg
    have := hpos.KO_pos
    have := hS.valid.s_pos (j - 1)
    positivity
  · exact le_rfl

theorem Cop_nonneg (hpos : S.ConstPos) : 0 ≤ S.Cop S.C0 S.K1 := by
  unfold Standing.Cop
  have hCO := hpos.CO_pos
  have hCQ := hpos.CQ_nonneg
  have hCM := hpos.CM_pos
  have hK1 := hpos.K1_pos
  have hC2 : 0 ≤ S.C2 := le_trans zero_le_one hpos.one_le_C2
  have hsb := hpos.sigb_pos
  have hC0 : 0 ≤ S.C0 := S.C0_pos.le
  have hCact : 0 ≤ S.Cact S.C0 := le_trans hC0 (OneRing.le_Cact _ _ _)
  have hIp := Ip_nonneg' 3 (9 * S.sigma0 / 64)
  positivity

theorem etabK_nonneg (hpos : S.ConstPos) (hS : S.Holds) (k : ℕ) :
    0 ≤ S.etabK S.C0 S.K1 k := by
  unfold Standing.etabK
  split_ifs
  · have := Cop_nonneg hpos
    have := hS.valid.s_pos (k - 1)
    have := hpos.sigb_pos
    have : 0 < S.P.μ - 1 := by linarith [hS.one_lt_μ]
    positivity
  · exact le_rfl

/-- `η_{b,k} ≤ η_b` (`s_{k-1} ≤ s̄`). -/
theorem etabK_le_etab (hpos : S.ConstPos) (hS : S.Holds) (k : ℕ) :
    S.etabK S.C0 S.K1 k ≤ S.etab S.C0 S.K1 := by
  have hCop := Cop_nonneg hpos
  have hsb := hpos.sigb_pos
  have hμ : 0 < S.P.μ - 1 := by linarith [hS.one_lt_μ]
  have hden : 0 < S.sigb * (S.P.μ - 1) := mul_pos hsb hμ
  have hetab : 0 ≤ S.etab S.C0 S.K1 := by
    unfold Standing.etab
    have := hS.sbar_pos
    positivity
  unfold Standing.etabK
  split_ifs
  · unfold Standing.etab
    apply div_le_div_of_nonneg_right _ hden.le
    apply mul_le_mul_of_nonneg_left _ hCop
    exact pow_le_pow_left₀ (s_pos hS _).le (s_le_sbar hS _) _
  · exact hetab

/-- **The conclusions of `thm:active` increase with `η_b`** (`11_bootstrap.tex:316-318`). -/
theorem activeConclAt_mono {C₀ η η' : ℝ} {k : ℕ} {u : ℝ} (hη : η ≤ η') (hC2 : 0 ≤ S.C2)
    (hC3 : 0 ≤ S.C3) (h : S.ActiveConclAt C₀ η k u) : S.ActiveConclAt C₀ η' k u where
  radial := h.radial
  supp := h.supp
  mode := by
    refine h.mode.trans ?_
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC2 (S.ahatK_nonneg k u))
    linarith
  bound := h.bound
  moment := by
    refine h.moment.trans ?_
    apply mul_le_mul_of_nonneg_left _
      (mul_nonneg (mul_nonneg (by positivity) hC3) (S.ahatK_nonneg k u))
    linarith

/-- **`ρ̂_k(0) = C₀`** (`11_bootstrap.tex:383`): `t₁(C₀, G_k) > 0` since `2^{p/2}C₀ > 1`, so
`ρ̂_k(0) = C₀⟨0⟩^p = C₀`. -/
theorem rhoHatK_zero (hS : S.Holds) {k : ℕ} (hk : k ∈ Finset.Icc 1 S.P.n) :
    S.rhoHatK S.C0 k 0 = S.C0 := by
  have hσ : S.σ' < Eig.sigma S.P.χ (S.P.G k) := sigma'_lt hS hk
  have ht := (OneRing.tOneOf_spec hσ S.one_le_C0).1
  show OneRing.rhoHatOf (Eig.sigma S.P.χ (S.P.G k)) S.σ' S.C0 0 = S.C0
  rw [OneRing.rhoHatOf_of_lt ht]
  simp

end BootHandoffH

end Relay

end NonUniqueEuler
