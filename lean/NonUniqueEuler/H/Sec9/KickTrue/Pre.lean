import NonUniqueEuler.I.Sec9.Prehistory
import NonUniqueEuler.H.Sec9.KickTrue.Setup

/-!
# Helpers for `P/Sec9/KickTrue`: hypothesis (Kick4) of `prop:kick`

Helper file of `P/Sec9/KickTrue.lean` (`lem:kicktrue`, steps (Q2), (Kick4),
`09_relay.tex:1373-1397`), with `Q_pre = |q_{k+1}|`:
* `qKick_shift`: `q_{k+1}(v + τ₀) = q_{k+1}(v/A_{k+1})` in kick time (`τ₀ = -t̄♯_{k+1} - T_g`);
* `pre_bound` (`k+1 < n`): `Err_pre ≤ δ₀ C_qr(4μC_{L1}C_Q/(3σ(μ-1)) + 1)K₁(κ/δ₀)^{ϑ_μ}`
  (`lem:prehistory` with `σ_o = x`, `maj_{k+1}(t̄♯_{k+1}) ≤ K₁κ`, `eq:Rew`);
* `pre_seeded` (the seeded level `k+1 = n`, generic): for `q` continuous on `[-T_g, 0]` and `B > 0`
  there is `T'_g ∈ [17T_g/24, T_g)` with `∫_{-T_g}^{-T'_g} e^{-xτ}|q| ≤ B`.
Everything here is proved.
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler

namespace Relay

namespace KickTrueAux

open RingData Datum

variable (S : Standing)

/-- `maj_k(τ) ≥ 0` for `τ ≥ 0` (`η_k ≥ 0`). -/
theorem maj_nonneg' (k : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) : 0 ≤ S.maj k τ := by
  show 0 ≤ ∫ v in (0 : ℝ)..τ, Real.exp (S.P.sigma k * (τ - v)) * S.P.eta S.Mh k v
  exact intervalIntegral.integral_nonneg hτ fun v _ =>
    mul_nonneg (Real.exp_pos _).le (S.P.eta_nonneg _ _ _)

/-- In kick time, `q_{k+1}(v + τ₀) = q_{k+1}(v/A_{k+1})` (`09_relay.tex:1378-1380`). -/
theorem qKick_shift (hS : S.Holds) {k : ℕ} (hk : 1 ≤ k) (hkn : k < S.P.n)
    (hc : S.P.ClockUpTo (k + 1)) (v : ℝ) :
    S.P.qKick k (v + S.P.tau0 k) = S.P.q (k + 1) (v / S.P.A (k + 1)) := by
  obtain ⟨hT, hτ₀, -, -, -⟩ := clock_facts S hS hk hkn hc
  have hA := (hS.valid.A_pos (k + 1)).ne'
  simp only [Approx.qKick]
  congr 1
  rw [hT, hτ₀]
  simp only [Approx.tash]
  field_simp
  ring

/-- **(Kick4) for `k + 1 < n`** (`09_relay.tex:1374-1386`): with `Q_pre = |q_{k+1}|`,
`Err_pre ≤ δ₀ · C_qr(4μC_{L1}C_Q/(3σ(μ-1)) + 1)K₁(κ/δ₀)^{ϑ_μ}`. -/
theorem pre_bound (hS : S.Holds) (hDet : S.Det) {C₀ K₁ : ℝ} (hK₁ : 0 < K₁) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k < S.P.n) (hc : S.P.ClockUpTo (k + 1)) (h : S.KickTrueHyp C₀ K₁ k)
    (hlt : k + 1 < S.P.n) :
    Kick.errPre (S.P.xk k) (S.P.tau0 k) (S.P.That (k + 1)) (fun τ => ‖S.P.qKick k τ‖) ≤
      S.P.δ₀ * (Cqr * (4 * S.P.μ * Rings.CL1 * S.CQ / (3 * S.sigma0 * (S.P.μ - 1)) + 1) * K₁ *
        (S.P.ksh (k + 1) / S.P.δ₀) ^ S.varthetaMu) := by
  obtain ⟨hpre, hmaj, -, -⟩ := h.deeper hlt
  obtain ⟨hσp, -, -, hlow, -, hvt, -, hxlt, -⟩ := rew_facts S hS hDet hk hkn
  obtain ⟨-, -, hσ, -⟩ := sigma_facts S hS
  obtain ⟨hκ, hκδ, -, -, hTg, -⟩ := kappa_facts S hS hDet hk hkn hc h.ineqC
  obtain ⟨-, hτ₀, htash0, -, -⟩ := clock_facts S hS hk hkn hc
  obtain ⟨-, hbound⟩ := (prehistory S hS hpre).2 (S.P.xk k) hxlt
  have hμ := hS.one_lt_μ
  set x := S.P.xk k
  set Tg := S.P.That (k + 1)
  set ta := S.P.tash (k + 1)
  set κ := S.P.ksh (k + 1)
  set σp := S.P.sigma (k + 1)
  have hσp0 : 0 < σp := lt_of_lt_of_le (by positivity) hσp
  -- the substitution `τ = v + τ₀`
  have hsub : Kick.errPre x (S.P.tau0 k) Tg (fun τ => ‖S.P.qKick k τ‖) =
      Real.exp (x * Tg) * ∫ v in (0 : ℝ)..ta,
        Real.exp (x * (ta - v)) * ‖S.P.q (k + 1) (v / S.P.A (k + 1))‖ := by
    unfold Kick.errPre
    have hfun : ∀ v : ℝ, (fun τ => Real.exp (-(x * τ)) * ‖S.P.qKick k τ‖) (v + S.P.tau0 k) =
        Real.exp (x * Tg) * (Real.exp (x * (ta - v)) * ‖S.P.q (k + 1) (v / S.P.A (k + 1))‖) := by
      intro v
      simp only
      rw [qKick_shift S hS hk hkn hc v, ← mul_assoc, ← Real.exp_add, hτ₀]
      congr 2
      ring
    have h1 := intervalIntegral.integral_comp_add_right
      (fun τ => Real.exp (-(x * τ)) * ‖S.P.qKick k τ‖) (a := 0) (b := ta) (S.P.tau0 k)
    simp only [hfun, zero_add, intervalIntegral.integral_const_mul] at h1
    rw [show ta + S.P.tau0 k = -Tg by rw [hτ₀]; ring] at h1
    rw [← h1]
  rw [hsub]
  -- the bound of `lem:prehistory`, then `maj ≤ K₁κ`, `1/(σ₊-x) ≤ 4μ/(3σ(μ-1))`
  have hinv := inv_le_of_rew hσ hμ hlow
  have hCL1 := Rings.CL1_nonneg
  have hCQ := CQ_nonneg S.P.χ S.sh S.NQ
  have hm0 := maj_nonneg' S (k + 1) htash0
  have hA1 : Rings.CL1 * S.CQ / (σp - x) + 1 ≤
      4 * S.P.μ * Rings.CL1 * S.CQ / (3 * S.sigma0 * (S.P.μ - 1)) + 1 := by
    have hcq : 0 ≤ Rings.CL1 * S.CQ := mul_nonneg hCL1 hCQ
    have := mul_le_mul_of_nonneg_left hinv hcq
    have e1 : Rings.CL1 * S.CQ / (σp - x) = Rings.CL1 * S.CQ * (1 / (σp - x)) := by ring
    have e2 : 4 * S.P.μ * Rings.CL1 * S.CQ / (3 * S.sigma0 * (S.P.μ - 1)) =
        Rings.CL1 * S.CQ * (4 * S.P.μ / (3 * S.sigma0 * (S.P.μ - 1))) := by ring
    linarith
  have hCqr := Cqr_pos
  set Ap := 4 * S.P.μ * Rings.CL1 * S.CQ / (3 * S.sigma0 * (S.P.μ - 1)) + 1 with hAp
  have hAp0 : 0 ≤ Ap := by
    have : 0 ≤ Rings.CL1 * S.CQ / (σp - x) := by
      apply div_nonneg (mul_nonneg hCL1 hCQ)
      linarith
    linarith
  have h2 : Cqr * (Rings.CL1 * S.CQ / (σp - x) + 1) * S.maj (k + 1) ta ≤ Cqr * Ap * (K₁ * κ) := by
    apply mul_le_mul (mul_le_mul_of_nonneg_left hA1 hCqr.le) hmaj hm0
    exact mul_nonneg hCqr.le hAp0
  have hke : κ * Real.exp (x * Tg) ≤ S.P.δ₀ * (κ / S.P.δ₀) ^ S.varthetaMu := by
    rw [hTg]; exact kappa_mul_exp_le x hκ hκδ hσp0.ne' hvt
  have hE := Real.exp_pos (x * Tg)
  calc Real.exp (x * Tg) * ∫ v in (0 : ℝ)..ta,
        Real.exp (x * (ta - v)) * ‖S.P.q (k + 1) (v / S.P.A (k + 1))‖
      ≤ Real.exp (x * Tg) * (Cqr * Ap * (K₁ * κ)) :=
        mul_le_mul_of_nonneg_left (hbound.trans h2) hE.le
    _ = Cqr * Ap * K₁ * (κ * Real.exp (x * Tg)) := by ring
    _ ≤ Cqr * Ap * K₁ * (S.P.δ₀ * (κ / S.P.δ₀) ^ S.varthetaMu) :=
        mul_le_mul_of_nonneg_left hke (by positivity)
    _ = S.P.δ₀ * (Cqr * Ap * K₁ * (κ / S.P.δ₀) ^ S.varthetaMu) := by ring

/-- **(Kick4) at the seeded level** (`09_relay.tex:1391-1395`), generic: for `q` continuous on
`[-T_g, 0]`, `x ≥ 0`, `T_g > 0` and `B > 0`, there is `T'_g ∈ [17T_g/24, T_g)` with
`∫_{-T_g}^{-T'_g} e^{-xτ}|q(τ)| dτ ≤ B`. -/
theorem pre_seeded {q : ℝ → ℂ} {x Tg B : ℝ} (hx : 0 ≤ x) (hTg : 0 < Tg) (hB : 0 < B)
    (hq : ContinuousOn q (Icc (-Tg) 0)) :
    ∃ Tg' : ℝ, 17 / 24 * Tg ≤ Tg' ∧ Tg' < Tg ∧
      Kick.errPre x (-Tg) Tg' (fun τ => ‖q τ‖) ≤ B := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hq
  set K := Real.exp (x * Tg) * (|M| + 1) with hK
  have hK0 : 0 < K := by positivity
  set d := min (7 / 24 * Tg) (B / K) with hd
  have hd0 : 0 < d := lt_min (by positivity) (div_pos hB hK0)
  have hd1 : d ≤ 7 / 24 * Tg := min_le_left _ _
  have hd2 : d ≤ B / K := min_le_right _ _
  refine ⟨Tg - d, by linarith, by linarith, ?_⟩
  unfold Kick.errPre
  have hle : -Tg ≤ -(Tg - d) := by linarith
  have hsub : Icc (-Tg) (-(Tg - d)) ⊆ Icc (-Tg) 0 := Icc_subset_Icc le_rfl (by linarith)
  have hint : IntervalIntegrable (fun τ => Real.exp (-(x * τ)) * ‖q τ‖) volume (-Tg) (-(Tg - d)) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hle]
    exact ((by fun_prop : Continuous fun τ : ℝ => Real.exp (-(x * τ))).continuousOn).mul
      ((hq.mono hsub).norm)
  have hpt : ∀ τ ∈ Icc (-Tg) (-(Tg - d)), Real.exp (-(x * τ)) * ‖q τ‖ ≤ K := by
    intro τ hτ
    have h1 : Real.exp (-(x * τ)) ≤ Real.exp (x * Tg) := by
      apply Real.exp_le_exp.2
      nlinarith [hτ.1]
    have h2 : ‖q τ‖ ≤ |M| + 1 := by
      have := hM τ (hsub hτ)
      have := le_abs_self M
      linarith
    exact mul_le_mul h1 h2 (norm_nonneg _) (Real.exp_pos _).le
  have hmono := intervalIntegral.integral_mono_on hle hint intervalIntegrable_const hpt
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  refine hmono.trans ?_
  have : (-(Tg - d) - -Tg) * K = d * K := by ring
  rw [this]
  calc d * K ≤ B / K * K := mul_le_mul_of_nonneg_right hd2 hK0.le
    _ = B := by field_simp

end KickTrueAux

end Relay

end NonUniqueEuler
