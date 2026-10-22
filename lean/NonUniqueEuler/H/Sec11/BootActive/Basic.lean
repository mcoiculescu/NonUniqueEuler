import NonUniqueEuler.Defs.Sec11.Extra2Boot
import NonUniqueEuler.I.Sec10.ConstantsPos

/-!
# Helper for `P/Sec11/BootActive.lean`: elementary facts

Helper of the proof of Step 4 of `prop:bootstrap` (`11_bootstrap.tex:390-484`): the active time
`ū = A_k(t' - t♯_k) ∈ (0, T̂_k]`, the times `t'' = t♯_k + u/A_k`, the signs of `θ_j`, `η_{b,k}`,
`C_*`, the Japanese bracket, and the algebraic inequality of `eq:boot-inner`
(`2 + 2C_*(T_pin + μu) ≤ (2 + 2C_*T_pin)(1 + 2C_*)⟨u⟩`, `11_bootstrap.tex:425-428`).
All proved.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

namespace BootActiveH

open RingData Datum

variable {S : Standing}

/-- The signs of the constants (`lem:nonempty`), from (SA). -/
theorem constPos (hS : S.Holds) : S.ConstPos :=
  constants_pos S hS.admissible hS.hN hS.σ'_gt hS.σ'_lt_sigma hS.δ₀_pos hS.one_lt_μ hS.Tpin_pos

theorem A_pos (hS : S.Holds) (k : ℕ) : 0 < S.P.A k := hS.valid.A_pos k

theorem T_eq {k : ℕ} (hkn : k ≤ S.P.n) : S.P.T k = S.P.tsh k + S.P.That k / S.P.A k :=
  S.P.T_of_ne (by omega)

theorem activeTime_pos (hS : S.Holds) {k : ℕ} {t' : ℝ} (htsh : S.P.tsh k < t') :
    0 < S.P.activeTime k t' :=
  mul_pos (A_pos hS k) (sub_pos.2 htsh)

theorem activeTime_le_That (hS : S.Holds) {k : ℕ} (hkn : k ≤ S.P.n) {t' : ℝ}
    (ht' : t' ≤ S.P.T k) : S.P.activeTime k t' ≤ S.P.That k := by
  have hA := A_pos hS k
  rw [T_eq hkn] at ht'
  have h1 : t' - S.P.tsh k ≤ S.P.That k / S.P.A k := by linarith
  have h2 := mul_le_mul_of_nonneg_left h1 hA.le
  rw [mul_div_cancel₀ _ hA.ne'] at h2
  exact h2

theorem activeTime_tsh_add (hS : S.Holds) (k : ℕ) (u : ℝ) :
    S.P.activeTime k (S.P.tsh k + u / S.P.A k) = u := by
  have hA := A_pos hS k
  simp only [Approx.activeTime]
  field_simp
  ring

theorem A_mul_tsh_add (hS : S.Holds) (k : ℕ) (u : ℝ) :
    S.P.A k * (S.P.tsh k + u / S.P.A k) = S.P.tash k + u := by
  have hA := A_pos hS k
  rw [Approx.tash_def]
  field_simp

/-- For `u ∈ [0, A_k(t' - t♯_k)]`, the real time `t♯_k + u/A_k` lies in `[t♯_k, t']`. -/
theorem tsh_add_mem (hS : S.Holds) {k : ℕ} {t' u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) (S.P.activeTime k t')) :
    S.P.tsh k + u / S.P.A k ∈ Icc (S.P.tsh k) t' := by
  have hA := A_pos hS k
  have h0 : 0 ≤ u / S.P.A k := div_nonneg hu.1 hA.le
  refine ⟨by linarith, ?_⟩
  have h1 : u / S.P.A k ≤ t' - S.P.tsh k := by
    rw [div_le_iff₀ hA]
    have := hu.2
    simp only [Approx.activeTime] at this
    linarith
  linarith

/-- Conversely, a time `t'' ∈ [t♯_k, t']` is `t♯_k + u/A_k` with `u = A_k(t'' - t♯_k)`. -/
theorem eq_tsh_add (hS : S.Holds) (k : ℕ) (t'' : ℝ) :
    S.P.tsh k + S.P.activeTime k t'' / S.P.A k = t'' := by
  have hA := A_pos hS k
  simp only [Approx.activeTime]
  field_simp
  ring

/-- `0 ≤ I_p(x)` (the integrand is nonnegative on `(0, ∞)`). -/
theorem Ip_nonneg (p : ℕ) (x : ℝ) : 0 ≤ Ip p x := by
  unfold Ip
  refine setIntegral_nonneg measurableSet_Ioi fun u hu => ?_
  have : 0 ≤ 1 + u := by linarith [mem_Ioi.1 hu]
  positivity

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
  have hIp := Ip_nonneg 3 (9 * S.sigma0 / 64)
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

theorem etab_nonneg (hpos : S.ConstPos) (hS : S.Holds) : 0 ≤ S.etab S.C0 S.K1 := by
  unfold Standing.etab
  have := Cop_nonneg hpos
  have := hS.sbar_pos
  have := hpos.sigb_pos
  have : 0 < S.P.μ - 1 := by linarith [hS.one_lt_μ]
  positivity

/-! ### The Japanese bracket -/

theorem one_le_jap (u : ℝ) : 1 ≤ Prelim.jap u := by
  unfold Prelim.jap
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (1 + u ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg u])

theorem jap_nonneg (u : ℝ) : 0 ≤ Prelim.jap u := le_trans zero_le_one (one_le_jap u)

theorem le_jap (u : ℝ) : u ≤ Prelim.jap u := by
  unfold Prelim.jap
  rcases le_or_gt u 0 with h | h
  · exact le_trans h (Real.sqrt_nonneg _)
  · calc u = Real.sqrt (u ^ 2) := (Real.sqrt_sq h.le).symm
      _ ≤ Real.sqrt (1 + u ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg u])

/-- The algebraic step of `eq:boot-inner` (`11_bootstrap.tex:425-428`): for `C ≥ 0`, `T ≥ 0`,
`0 ≤ μ ≤ 2`, `u ≥ 0`: `2 + 2C(T + μu) ≤ (2 + 2CT)(1 + 2C)⟨u⟩`. -/
theorem inner_alg {C T μ u : ℝ} (hC : 0 ≤ C) (hT : 0 ≤ T) (hμ0 : 0 ≤ μ) (hμ : μ ≤ 2)
    (hu : 0 ≤ u) : 2 + 2 * C * (T + μ * u) ≤ (2 + 2 * C * T) * (1 + 2 * C) * Prelim.jap u := by
  have hj1 := one_le_jap u
  have hju := le_jap u
  have hCT : 0 ≤ C * T := mul_nonneg hC hT
  have hCμu : 0 ≤ C * μ * u := mul_nonneg (mul_nonneg hC hμ0) hu
  -- `2 + 2CT + 2Cμu ≤ (2 + 2CT)(1 + Cμu)`
  have h1 : 2 + 2 * C * (T + μ * u) ≤ (2 + 2 * C * T) * (1 + C * μ * u) := by
    nlinarith [mul_nonneg hCT hCμu]
  -- `1 + Cμu ≤ 1 + 2Cu ≤ (1 + 2C)⟨u⟩`
  have h2 : 1 + C * μ * u ≤ (1 + 2 * C) * Prelim.jap u := by
    have h3 : C * μ * u ≤ 2 * C * u := by
      have := mul_le_mul_of_nonneg_left hμ (mul_nonneg hC hu)
      nlinarith
    have h4 : 2 * C * u ≤ 2 * C * Prelim.jap u :=
      mul_le_mul_of_nonneg_left hju (by linarith)
    nlinarith
  calc 2 + 2 * C * (T + μ * u) ≤ (2 + 2 * C * T) * (1 + C * μ * u) := h1
    _ ≤ (2 + 2 * C * T) * ((1 + 2 * C) * Prelim.jap u) :=
        mul_le_mul_of_nonneg_left h2 (by linarith)
    _ = (2 + 2 * C * T) * (1 + 2 * C) * Prelim.jap u := by ring

end BootActiveH

end Relay

end NonUniqueEuler
