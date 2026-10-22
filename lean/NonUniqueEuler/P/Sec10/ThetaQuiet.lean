import NonUniqueEuler.Defs.Sec10.Lists
import NonUniqueEuler.I.Sec9.QuietTime
import NonUniqueEuler.I.Sec10.ConstantsPos

/-!
# Proof: `lem:theta-quiet` (the outer feedback over a quiet phase)

Proof of `I/Sec10/ThetaQuiet.lean` (`10_parameters.tex:233-273`).

* The first claim is `Relay.quiet_time_bound` (`I/Sec9/QuietTime.lean`), rewritten from
  `C_τ[…]/(μ-1)` to `(C_τ/(μ-1))[…]`.
* `j = 1`: `θ_1 = 0`, and the right side is positive (`K₁, C_ls > 0`, `constants_pos`).
* `2 ≤ j < n`: `θ_j = 4C_OC_QK_Os_{j-1}^6 ≥ 0`, `log(1/s_j) = log(1/s_{j-1}) + log(2μ) ≤
  2 log(1/s_{j-1})` (`s_{j-1} · 2μ ≤ (1/16)(17/8) < 1`), and the monotonicity
  `g(s_{j-1}) ≤ g(s̄)` of `g(s) = s⁶[B₀ + 2 log(1/s)]` (`g_mono`, `B₀ = T_z + 1/(μ-1) ≥ 2`).
  `eq:E22` concludes (if `C_Q = 0`, then `θ_j = 0`).

**Deviation.** The monotonicity of `g` is proved without derivatives (`g_mono`): for
`0 < s ≤ t ≤ 1` and `B = B₀ + 2 log(1/t) ≥ 2`, `log(t/s) ≤ t/s - 1` gives
`s⁶ log(t/s) ≤ s⁵t - s⁶ ≤ t⁶ - s⁶`, so `g(s) = s⁶B + 2s⁶ log(t/s) ≤ s⁶B + B(t⁶ - s⁶) = g(t)`.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

open RingData Datum

namespace ThetaQuietAux

/-- `s⁶ log(t/s) ≤ t⁶ - s⁶` for `0 < s ≤ t`. -/
theorem pow_six_mul_log_le {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    s ^ 6 * Real.log (t / s) ≤ t ^ 6 - s ^ 6 := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have hlog : Real.log (t / s) ≤ t / s - 1 := Real.log_le_sub_one_of_pos (div_pos ht hs)
  have h1 : s ^ 6 * Real.log (t / s) ≤ s ^ 6 * (t / s - 1) :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  have h2 : s ^ 6 * (t / s - 1) = s ^ 5 * t - s ^ 6 := by
    field_simp
  have h3 : s ^ 5 * t ≤ t ^ 6 := by
    have : s ^ 5 ≤ t ^ 5 := pow_le_pow_left₀ hs.le hst 5
    calc s ^ 5 * t ≤ t ^ 5 * t := mul_le_mul_of_nonneg_right this ht.le
      _ = t ^ 6 := by ring
  linarith

/-- **Monotonicity of `g(s) = s⁶[B₀ + 2 log(1/s)]`** (`10_parameters.tex:262-268`): for
`0 < s ≤ t ≤ 1` and `B₀ ≥ 2`, `g(s) ≤ g(t)`. -/
theorem g_mono {s t B₀ : ℝ} (hs : 0 < s) (hst : s ≤ t) (ht1 : t ≤ 1) (hB : 2 ≤ B₀) :
    s ^ 6 * (B₀ + 2 * Real.log (1 / s)) ≤ t ^ 6 * (B₀ + 2 * Real.log (1 / t)) := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have hsplit : Real.log (1 / s) = Real.log (1 / t) + Real.log (t / s) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  have hlt : 0 ≤ Real.log (1 / t) := Real.log_nonneg (by rw [le_div_iff₀ ht]; linarith)
  set B := B₀ + 2 * Real.log (1 / t) with hBdef
  have hB2 : 2 ≤ B := by linarith
  have hkey := pow_six_mul_log_le hs hst
  have hst6 : s ^ 6 ≤ t ^ 6 := pow_le_pow_left₀ hs.le hst 6
  have hdiff : 0 ≤ t ^ 6 - s ^ 6 := by linarith
  have hBd : 2 * (t ^ 6 - s ^ 6) ≤ B * (t ^ 6 - s ^ 6) :=
    mul_le_mul_of_nonneg_right hB2 hdiff
  calc s ^ 6 * (B₀ + 2 * Real.log (1 / s))
      = s ^ 6 * B + 2 * (s ^ 6 * Real.log (t / s)) := by rw [hsplit, hBdef]; ring
    _ ≤ s ^ 6 * B + 2 * (t ^ 6 - s ^ 6) := by linarith
    _ ≤ s ^ 6 * B + B * (t ^ 6 - s ^ 6) := by linarith
    _ = t ^ 6 * B := by ring

end ThetaQuietAux

open ThetaQuietAux in
/-- **`lem:theta-quiet`** (`10_parameters.tex:233-243`). Assume (SA) and (B7). For every level
`1 ≤ j < n`: `τ̄♯_j ≤ (C_τ/(μ-1))[T_z + log(1/s_j) + 1/(μ-1)]`, and
`θ_j τ̄♯_j ≤ min{1/2, 1/(4 C_ls K₁)}`. -/
theorem theta_quiet (S : Standing) (hS : S.Holds) (hB7 : S.CondB7) {j : ℕ} (hj : 1 ≤ j)
    (hjn : j < S.P.n) :
    S.tauBarSh j ≤ S.Ctau / (S.P.μ - 1) * (S.Tz + Real.log (1 / S.P.s j) + 1 / (S.P.μ - 1)) ∧
      S.theta j * S.tauBarSh j ≤ min (1 / 2) (1 / (4 * Eig.Cls S.P.χ * S.K1)) := by
  -- the first claim
  have hfirst : S.tauBarSh j ≤
      S.Ctau / (S.P.μ - 1) * (S.Tz + Real.log (1 / S.P.s j) + 1 / (S.P.μ - 1)) := by
    have h := quiet_time_bound S hS hj hjn
    rwa [div_mul_eq_mul_div]
  refine ⟨hfirst, ?_⟩
  -- signs
  have hpos : S.ConstPos := constants_pos S hS.valid.admissible hS.hN hS.σ'_gt hS.σ'_lt_sigma
    hS.valid.δ₀_pos hS.valid.datumParams.one_lt_μ hS.valid.Tpin_pos
  set M : ℝ := min (1 / 2) (1 / (4 * Eig.Cls S.P.χ * S.K1)) with hMdef
  have hM : 0 < M := by
    have h4 : 0 < 4 * Eig.Cls S.P.χ * S.K1 := by
      have := hpos.Cls_pos
      have := hpos.K1_pos
      positivity
    exact lt_min (by norm_num) (one_div_pos.2 h4)
  -- `j = 1`
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · rw [S.theta_of_le_one (by omega), zero_mul]
    exact hM.le
  -- `2 ≤ j < n`
  have hμ1 : 1 < S.P.μ := hS.valid.datumParams.one_lt_μ
  have hμle : S.P.μ ≤ 17 / 16 := hS.μ_le
  have hμ0 : 0 < S.P.μ - 1 := by linarith
  have hsb : 0 < S.P.sbar := hS.valid.datumParams.sbar_pos
  have hsble : S.P.sbar ≤ a / 16 := hS.valid.datumParams.sbar_le
  have hsb1 : S.P.sbar < 1 / 16 := by linarith [a_lt_one]
  set s' : ℝ := S.P.s (j - 1) with hs'def
  have hs' : 0 < s' := hS.valid.s_pos (j - 1)
  have h2μ : 1 ≤ 2 * S.P.μ := by linarith
  have hs'le : s' ≤ S.P.sbar := by
    rw [hs'def, Approx.s_def, ratio]
    exact div_le_self hsb.le (one_le_pow₀ h2μ)
  -- `s_j = s_{j-1}/(2μ)`, so `log(1/s_j) = log(1/s_{j-1}) + log(2μ) ≤ 2 log(1/s_{j-1})`
  have hsj : S.P.s j = s' / (2 * S.P.μ) := by
    rw [hs'def, Approx.s_def, Approx.s_def, ratio, ratio, div_div]
    congr 1
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]
  have hlogj : Real.log (1 / S.P.s j) ≤ 2 * Real.log (1 / s') := by
    have hsplit : Real.log (1 / S.P.s j) = Real.log (1 / s') + Real.log (2 * S.P.μ) := by
      rw [← Real.log_mul (by positivity) (by positivity), hsj]
      congr 1
      field_simp
    have hle : Real.log (2 * S.P.μ) ≤ Real.log (1 / s') := by
      apply Real.log_le_log (by positivity)
      rw [le_div_iff₀ hs']
      nlinarith
    linarith
  -- `θ_j ≥ 0`
  have hθ : S.theta j = 4 * S.CO * S.CQ * S.KO * s' ^ 6 := by
    rw [S.theta_of_two_le hj2]
  have hθ0 : 0 ≤ S.theta j := by
    rw [hθ]
    have := hpos.CO_pos
    have := hpos.CQ_nonneg
    have := hpos.KO_pos
    positivity
  have hCτ : 0 ≤ S.Ctau / (S.P.μ - 1) := div_nonneg (by linarith [S.three_le_Ctau]) hμ0.le
  -- the bound by `g(s_{j-1})`
  set B₀ : ℝ := S.Tz + 1 / (S.P.μ - 1) with hB₀def
  have hB₀ : 2 ≤ B₀ := by
    have h16 : 16 ≤ 1 / (S.P.μ - 1) := by
      rw [le_div_iff₀ hμ0]
      linarith
    linarith [hpos.Tz_pos]
  have hτ : S.tauBarSh j ≤ S.Ctau / (S.P.μ - 1) * (B₀ + 2 * Real.log (1 / s')) := by
    refine hfirst.trans ?_
    apply mul_le_mul_of_nonneg_left _ hCτ
    rw [hB₀def]
    linarith
  have hg : s' ^ 6 * (B₀ + 2 * Real.log (1 / s')) ≤
      S.P.sbar ^ 6 * (B₀ + 2 * Real.log (1 / S.P.sbar)) :=
    g_mono hs' hs'le (by linarith) hB₀
  -- `eq:E22`
  rcases (hpos.CQ_nonneg).eq_or_lt with hCQ | hCQ
  · -- `C_Q = 0`: `θ_j = 0`
    rw [hθ, ← hCQ]
    simp only [mul_zero, zero_mul]
    exact hM.le
  have hD : 0 < 4 * S.CO * S.CQ * S.Ctau := by
    have := hpos.CO_pos
    have := S.three_le_Ctau
    have h3 : 0 < S.Ctau := by linarith
    positivity
  have hE : S.KO * (S.P.sbar ^ 6 * (B₀ + 2 * Real.log (1 / S.P.sbar))) ≤
      (S.P.μ - 1) / (4 * S.CO * S.CQ * S.Ctau) * M := by
    have : S.KO * (S.P.sbar ^ 6 * (B₀ + 2 * Real.log (1 / S.P.sbar))) =
        S.KO * S.P.sbar ^ (2 * 3) * (S.Tz + 2 * Real.log (1 / S.P.sbar) + 1 / (S.P.μ - 1)) := by
      rw [hB₀def]
      norm_num
      ring
    rw [this]
    exact (S.condE22_iff_div hD).1 hB7.e22
  have hKO := hpos.KO_pos
  calc S.theta j * S.tauBarSh j
      ≤ S.theta j * (S.Ctau / (S.P.μ - 1) * (B₀ + 2 * Real.log (1 / s'))) :=
        mul_le_mul_of_nonneg_left hτ hθ0
    _ = 4 * S.CO * S.CQ * S.Ctau / (S.P.μ - 1) *
          (S.KO * (s' ^ 6 * (B₀ + 2 * Real.log (1 / s')))) := by
        rw [hθ]
        ring
    _ ≤ 4 * S.CO * S.CQ * S.Ctau / (S.P.μ - 1) *
          (S.KO * (S.P.sbar ^ 6 * (B₀ + 2 * Real.log (1 / S.P.sbar)))) := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg hD.le hμ0.le)
        exact mul_le_mul_of_nonneg_left hg hKO.le
    _ ≤ 4 * S.CO * S.CQ * S.Ctau / (S.P.μ - 1) *
          ((S.P.μ - 1) / (4 * S.CO * S.CQ * S.Ctau) * M) :=
        mul_le_mul_of_nonneg_left hE (div_nonneg hD.le hμ0.le)
    _ = M := by
        have hCO : S.CO ≠ 0 := hpos.CO_pos.ne'
        have hCt : S.Ctau ≠ 0 := (by linarith [S.three_le_Ctau] : (0 : ℝ) < S.Ctau).ne'
        have hCQ' : S.CQ ≠ 0 := hCQ.ne'
        field_simp

end Relay

end NonUniqueEuler
