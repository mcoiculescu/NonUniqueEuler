import NonUniqueEuler.Defs.Sec11.Extra2Boot
import NonUniqueEuler.I.Sec10.ConstantsPos
import NonUniqueEuler.I.Sec9.Standing
import NonUniqueEuler.I.Sec6.Clock

/-!
# Helper for `P/Sec11/BootQuietSize.lean`: elementary facts

Helper of the proof of Step 5 of `prop:bootstrap` (`11_bootstrap.tex:486-530`): positivity of
`A_k`, `s_k`, `σ_k`, `T̂_k`; `A_{j+1} = μA_j`; `ε_p ≤ μs̄^{m+2}`; rings are not debris while quiet;
`t♯_i ≥ 0`; the signs of `maj`, `θ_j`, `C_*`, `C_D(T_pin)`, `C_M(2C_Q/(σ_b(μ-1)) + 1)`. All proved.
(Some of these are also proved, independently, in the helpers of other Section 11 steps; helper
files of other proofs may not be imported (import rules, `README.md`).)
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

namespace BootQuietSizeH

open RingData Datum

variable {S : Standing}

/-- The signs of the constants (`lem:nonempty`), from (SA). -/
theorem constPos (hS : S.Holds) : S.ConstPos :=
  constants_pos S hS.admissible hS.hN hS.σ'_gt hS.σ'_lt_sigma hS.δ₀_pos hS.one_lt_μ hS.Tpin_pos

theorem A_pos (hS : S.Holds) (k : ℕ) : 0 < S.P.A k := hS.valid.A_pos k

/-- `A_{j+1} = μA_j` for `j ≥ 1`. -/
theorem A_succ {j : ℕ} (hj : 1 ≤ j) : S.P.A (j + 1) = S.P.μ * S.P.A j := by
  rw [Approx.A_def, Approx.A_def, amp_succ _ _ hj]

theorem s_pos (hS : S.Holds) (k : ℕ) : 0 < S.P.s k := hS.valid.s_pos k

/-- `s_k ≤ s̄`. -/
theorem s_le_sbar (hS : S.Holds) (k : ℕ) : S.P.s k ≤ S.P.sbar := by
  show S.P.sbar / (2 * S.P.μ) ^ k ≤ S.P.sbar
  have hμ := hS.one_lt_μ
  exact div_le_self hS.sbar_pos.le (one_le_pow₀ (by linarith))

theorem eps_nonneg (hS : S.Holds) (p : ℕ) : 0 ≤ S.P.eps p := by
  show 0 ≤ S.P.μ * S.P.s p ^ (3 + 2)
  have := s_pos hS p
  have := hS.one_lt_μ
  positivity

/-- `ε_p = μs_p^{m+2} ≤ μs̄^{m+2}`. -/
theorem eps_le (hS : S.Holds) (p : ℕ) : S.P.eps p ≤ S.P.μ * S.P.sbar ^ (3 + 2) := by
  show S.P.μ * S.P.s p ^ (3 + 2) ≤ S.P.μ * S.P.sbar ^ (3 + 2)
  have hμ := hS.one_lt_μ
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (s_pos hS p).le (s_le_sbar hS p) _)
    (by linarith)

/-- `σ_i ≥ σ_b > 0` for every level `i ∈ [1, n]` (`standing_levels`). -/
theorem sigma_pos (hS : S.Holds) {i : ℕ} (hi : i ∈ Finset.Icc 1 S.P.n) : 0 < S.P.sigma i := by
  obtain ⟨hb, -, -, hlev⟩ := standing_levels S hS
  exact lt_of_lt_of_le hb (hlev i hi).2.2

/-- `T̂_i ≥ 0` when `κ♯_i ∈ (0, δ₀)`. -/
theorem That_nonneg (hS : S.Holds) {i : ℕ} (hi : i ∈ Finset.Icc 1 S.P.n)
    (hκ : S.P.ksh i ∈ Ioo (0 : ℝ) S.P.δ₀) : 0 ≤ S.P.That i := by
  show 0 ≤ (S.P.sigma i)⁻¹ * Real.log (S.P.δ₀ / S.P.ksh i)
  have hσ := sigma_pos hS hi
  have h1 : 1 ≤ S.P.δ₀ / S.P.ksh i := by
    rw [le_div_iff₀ hκ.1]
    linarith [hκ.2]
  exact mul_nonneg (inv_nonneg.2 hσ.le) (Real.log_nonneg h1)

/-- `t♯_i ≤ T_i` when `κ♯_i ∈ (0, δ₀)`. -/
theorem tsh_le_T (hS : S.Holds) {i : ℕ} (hi : i ∈ Finset.Icc 1 S.P.n)
    (hκ : S.P.ksh i ∈ Ioo (0 : ℝ) S.P.δ₀) : S.P.tsh i ≤ S.P.T i := by
  rw [S.P.T_of_ne (by have := (Finset.mem_Icc.1 hi).2; omega)]
  have := div_nonneg (That_nonneg hS hi hκ) (A_pos hS i).le
  linarith

/-- A ring that is quiet at `t'` is not debris at any `t'' ≤ t'`. -/
theorem not_debris_of_quiet (hS : S.Holds) {j : ℕ} (hj : j ∈ Finset.Icc 1 S.P.n) {t' t'' : ℝ}
    (hq : S.P.QuietAt j t') (ht : t'' ≤ t') : ¬ S.P.DebrisAt j t'' := by
  rintro ⟨hc, hT⟩
  rcases hq with hq | hq
  · exact hq (hc.mono (Nat.le_succ j))
  · have := tsh_le_T hS hj (hc.ksh_mem le_rfl (Finset.mem_Icc.1 hj).2)
    linarith

/-- `t♯_i ≥ 0` for `i ∈ [k, n]` when the clock is defined up to level `k ≥ 1` (`lem:clock`(1)). -/
theorem tsh_nonneg (hS : S.Holds) {k i : ℕ} (hk : 1 ≤ k) (hc : S.P.ClockUpTo k)
    (hi : i ∈ Finset.Icc k S.P.n) : 0 ≤ S.P.tsh i := by
  obtain ⟨-, -, hG, -⟩ := standing_levels S hS
  exact (Approx.clock_order S.P hS.valid hS.hN hG hk hc).2.2.2 i hi

/-- `maj_k(τ) ≥ 0` for `τ ≥ 0`. -/
theorem maj_nonneg (k : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) : 0 ≤ S.maj k τ := by
  show 0 ≤ ∫ v in (0 : ℝ)..τ, Real.exp (S.P.sigma k * (τ - v)) * S.P.eta S.Mh k v
  exact intervalIntegral.integral_nonneg hτ fun v _ =>
    mul_nonneg (Real.exp_pos _).le (S.P.eta_nonneg _ _ _)

theorem theta_nonneg (hpos : S.ConstPos) (hS : S.Holds) (j : ℕ) : 0 ≤ S.theta j := by
  unfold Standing.theta
  split_ifs
  · have := hpos.CO_pos
    have := hpos.CQ_nonneg
    have := hpos.KO_pos
    have := hS.valid.s_pos (j - 1)
    positivity
  · exact le_rfl

/-- `C_* ≥ 0`. -/
theorem Cstar_nonneg : 0 ≤ Cstar := by
  unfold Cstar BS.cLpLinf
  have hc : (4 : ℝ).conjExponent = 4 / 3 := by
    rw [Real.conjExponent]; norm_num
  rw [hc]
  have hb : 0 ≤ 2 * Real.pi / (2 - 4 / 3 : ℝ) := by
    have := Real.pi_pos
    have : (0 : ℝ) < 2 - 4 / 3 := by norm_num
    positivity
  have := Real.rpow_nonneg hb (1 / (4 / 3))
  have := Real.pi_pos
  have : 0 ≤ Real.sqrt Mvort := Real.sqrt_nonneg _
  positivity

/-- `C_D(T) ≥ 0` for `T ≥ 0`. -/
theorem CD_nonneg {T : ℝ} (hT : 0 ≤ T) : 0 ≤ CD T := by
  rw [CD_def]
  have := Cstar_nonneg
  positivity

/-- `C_M(2C_Q/(σ_b(μ-1)) + 1) ≥ 0`. -/
theorem Crelay_nonneg (hpos : S.ConstPos) (hS : S.Holds) : 0 ≤ S.Crelay := by
  unfold Standing.Crelay
  have := hpos.CM_pos
  have := hpos.CQ_nonneg
  have := hpos.sigb_pos
  have : 0 < S.P.μ - 1 := by linarith [hS.one_lt_μ]
  positivity

end BootQuietSizeH

end Relay

end NonUniqueEuler
