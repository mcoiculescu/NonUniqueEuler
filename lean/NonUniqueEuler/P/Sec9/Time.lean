import NonUniqueEuler.Defs.Sec9.All
import NonUniqueEuler.I.Sec9.Detuning
import NonUniqueEuler.I.Sec4.Uniform

/-!
# Proof: `lem:time` (the saturation time `T₁` is bounded independently of `n`)

Proof of `I/Sec9/Time.lean` (`09_relay.tex:1465-1474`, proof `:1476-1494`).

The manuscript proof bounds each increment `T_k - T_{k+1} ≤ A_k⁻¹[T_z + (m+2)σ'⁻¹log(1/s_k)]`
(`k < n`) and `T_n ≤ σ'⁻¹log(2δ₀/κ_seed)/A₁`, then telescopes and sums two geometric series.
Here the telescoping and the two geometric sums are replaced by an equivalent downward induction
(`TimeAux.rec_bound`): with `a = T_z + (m+2)σ'⁻¹log(1/s̄)`, `b = (m+2)σ'⁻¹log(2μ)`,
`c = σ'⁻¹log(2δ₀/κ_seed)` and
`F(j) = aμ/(μ-1) + b(j + 1/(μ-1))μ/(μ-1) + c`, one has `T_j ≤ F(j)/A_j` for `1 ≤ j ≤ n`, because
`a + bj + F(j+1)/μ ≤ F(j)` (an identity up to `c(μ-1)/μ ≥ 0`). At `j = 1`,
`F(1) = aμ/(μ-1) + bμ²/(μ-1)² + c = A₁T_* - 1`.

The positivity `K_lo > 0` (used implicitly by the manuscript) comes from `c_N > 0`
(`lem:uniform`, `Eig.uniform_constants`) and `|z| ≥ Re z = σ(0) > 0` ((SA1)).
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

open RingData Datum

namespace TimeAux

/-- The key algebraic inequality of the downward induction:
`F(j+1)/μ + a + b j ≤ F(j)` with `F(j) = aμ/(μ-1) + b(j + 1/(μ-1))μ/(μ-1) + c`. -/
theorem step_ineq {μ a b c x : ℝ} (hμ : 1 < μ) (hc : 0 ≤ c) :
    (a * (μ / (μ - 1)) + b * ((x + 1 + 1 / (μ - 1)) * (μ / (μ - 1))) + c) / μ + (a + b * x) ≤
      a * (μ / (μ - 1)) + b * ((x + 1 / (μ - 1)) * (μ / (μ - 1))) + c := by
  have hm : μ - 1 ≠ 0 := by linarith
  have hμ0 : μ ≠ 0 := by linarith
  have key : a * (μ / (μ - 1)) + b * ((x + 1 / (μ - 1)) * (μ / (μ - 1))) + c -
      ((a * (μ / (μ - 1)) + b * ((x + 1 + 1 / (μ - 1)) * (μ / (μ - 1))) + c) / μ + (a + b * x)) =
      c * ((μ - 1) / μ) := by
    field_simp
    ring
  have hpos : 0 ≤ c * ((μ - 1) / μ) := mul_nonneg hc (div_nonneg (by linarith) (by linarith))
  linarith

/-- **The downward induction** replacing the telescoping sum of `lem:time`. If
`T_k ≤ T_{k+1} + (a + bk)/A_k` for `1 ≤ k < n`, `T_n ≤ c/A_n`, `A_{k+1} = μA_k > 0`, then
`T_j ≤ F(j)/A_j` for `1 ≤ j ≤ n` (stated with `j + d = n`). -/
theorem rec_bound {μ a b c : ℝ} (hμ : 1 < μ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    {A T : ℕ → ℝ} {n : ℕ} (hA : ∀ k, 1 ≤ k → 0 < A k)
    (hAs : ∀ k, 1 ≤ k → A (k + 1) = μ * A k)
    (hstep : ∀ k, 1 ≤ k → k < n → T k ≤ T (k + 1) + (a + b * k) / A k)
    (hbase : T n ≤ c / A n) :
    ∀ d j : ℕ, j + d = n → 1 ≤ j →
      T j ≤ (a * (μ / (μ - 1)) + b * ((j + 1 / (μ - 1)) * (μ / (μ - 1))) + c) / A j := by
  have hm : 0 < μ - 1 := by linarith
  have hq : 0 ≤ μ / (μ - 1) := div_nonneg (by linarith) hm.le
  intro d
  induction d with
  | zero =>
    intro j hj h1
    have hjn : j = n := by omega
    subst hjn
    have hAj := hA j h1
    refine hbase.trans (div_le_div_of_nonneg_right ?_ hAj.le)
    have h1' : 0 ≤ a * (μ / (μ - 1)) := mul_nonneg ha hq
    have hx : 0 ≤ ((j : ℝ) + 1 / (μ - 1)) * (μ / (μ - 1)) :=
      mul_nonneg (add_nonneg (Nat.cast_nonneg _) (div_nonneg zero_le_one hm.le)) hq
    have h2' : 0 ≤ b * (((j : ℝ) + 1 / (μ - 1)) * (μ / (μ - 1))) := mul_nonneg hb hx
    linarith
  | succ d ih =>
    intro j hj h1
    have hjn : j < n := by omega
    have hAj := hA j h1
    have hIH := ih (j + 1) (by omega) (by omega)
    rw [hAs j h1] at hIH
    push_cast at hIH
    have hs := hstep j h1 hjn
    have hμ0 : 0 < μ := by linarith
    have hsplit : (a * (μ / (μ - 1)) + b * (((j : ℝ) + 1 + 1 / (μ - 1)) * (μ / (μ - 1))) + c) /
        (μ * A j) + (a + b * j) / A j =
        ((a * (μ / (μ - 1)) + b * (((j : ℝ) + 1 + 1 / (μ - 1)) * (μ / (μ - 1))) + c) / μ +
          (a + b * j)) / A j := by
      field_simp
    have hkey := step_ineq (a := a) (b := b) (x := (j : ℝ)) hμ hc
    calc T j ≤ T (j + 1) + (a + b * j) / A j := hs
      _ ≤ (a * (μ / (μ - 1)) + b * (((j : ℝ) + 1 + 1 / (μ - 1)) * (μ / (μ - 1))) + c) /
            (μ * A j) + (a + b * j) / A j := by linarith
      _ = _ := hsplit
      _ ≤ _ := div_le_div_of_nonneg_right hkey hAj.le

/-- `F(1) + 1` is the bracket of `T_*`. -/
theorem F_one {μ a b c : ℝ} (hμ : 1 < μ) :
    a * (μ / (μ - 1)) + b * (((1 : ℕ) : ℝ) + 1 / (μ - 1)) * (μ / (μ - 1)) + c + 1 =
      μ / (μ - 1) * a + b * (μ ^ 2 / (μ - 1) ^ 2) + 1 + c := by
  have hm : μ - 1 ≠ 0 := by linarith
  push_cast
  field_simp
  ring

end TimeAux

open TimeAux in
/-- **`lem:time`** (`09_relay.tex:1465-1474`). Assume (SA), (Det), the clock defined up to level
`1`, `κ♯_k ≥ K_lo s_k⁵` for `1 ≤ k < n` and `κ♯_n ≥ ½κ_seed`. Then `T_1 ≤ T_*`. -/
theorem time (S : Standing) (hS : S.Holds) (hDet : S.Det) (hc : S.P.ClockUpTo 1)
    (hκ : ∀ k ∈ Finset.Ico 1 S.P.n, S.Klo * S.P.s k ^ (3 + 2) ≤ S.P.ksh k)
    (hκn : 1 / 2 * S.P.κs ≤ S.P.ksh S.P.n) : S.P.T 1 ≤ S.Tstar := by
  -- basic positivity
  have hA₁ : 0 < S.P.A₁ := hS.valid.datumParams.A₁_pos
  have hμ : 1 < S.P.μ := hS.one_lt_μ
  have hμ0 : 0 < S.P.μ := by linarith
  have hσ' : 0 < S.σ' := by linarith [hS.σ'_gt]
  have hδ₀ : 0 < S.P.δ₀ := hS.δ₀_pos
  have hTpin : 0 < S.P.Tpin := hS.Tpin_pos
  have hκs : 0 < S.P.κs := hS.kseed_pos
  have hsbar : 0 < S.P.sbar := hS.sbar_pos
  have hsbar2 : S.P.sbar ≤ 1 / 2 := by simpa using hS.sbar_pow_le
  have hn2 : 2 ≤ S.P.n := hS.two_le_n
  have hA : ∀ k, 1 ≤ k → 0 < S.P.A k := fun k _ => amp_pos hA₁ hμ0 k
  have hAs : ∀ k, 1 ≤ k → S.P.A (k + 1) = S.P.μ * S.P.A k := fun k hk =>
    amp_succ S.P.A₁ S.P.μ hk
  -- `K_lo > 0`: `c_N > 0` (`lem:uniform`) and `|z| ≥ σ(0) > 0`
  have hcN : 0 < Eig.cN S.P.χ :=
    (Eig.uniform_constants S.P.χ hS.admissible hS.hN).2.2.2.2.2.2.1
  have hz : 0 < ‖S.z‖ := by
    have h1 : S.z.re = S.sigma0 := rfl
    have h2 : S.σ' < 3 / 4 * S.sigma0 := hS.σ'_lt_sigma
    have h3 := Complex.re_le_norm S.z
    linarith
  have hKlo : 0 < S.Klo := by
    rw [Standing.Klo_def]
    have : 0 < 22 * ‖S.z‖ * (S.P.μ - 1) := by
      have : 0 < S.P.μ - 1 := by linarith
      positivity
    positivity
  -- `σ_k > σ'` for every level (`lem:detuning`)
  have hσk : ∀ k, 1 ≤ k → k ≤ S.P.n → S.σ' < S.P.sigma k := by
    intro k h1 h2
    have hd := ((detuning S hS hDet).2.2 k (Finset.mem_Icc.mpr ⟨h1, h2⟩))
    linarith [hd.2.1, hd.2.2.1]
  -- `T̂_k ≤ σ'⁻¹ log(δ₀/κ♯_k)` and `log(δ₀/κ♯_k) ≥ 0`
  have hThat : ∀ k, 1 ≤ k → k ≤ S.P.n →
      0 ≤ Real.log (S.P.δ₀ / S.P.ksh k) ∧
        S.P.That k ≤ S.σ'⁻¹ * Real.log (S.P.δ₀ / S.P.ksh k) := by
    intro k h1 h2
    have hk := hc.ksh_mem h1 h2
    have hlog : 0 ≤ Real.log (S.P.δ₀ / S.P.ksh k) :=
      Real.log_nonneg ((one_le_div hk.1).mpr hk.2.le)
    refine ⟨hlog, ?_⟩
    have hinv : (S.P.sigma k)⁻¹ ≤ S.σ'⁻¹ := inv_anti₀ hσ' (hσk k h1 h2).le
    exact mul_le_mul_of_nonneg_right hinv hlog
  -- `log(1/s_k) = log(1/s̄) + k log(2μ)`
  have hlogs : ∀ k : ℕ, Real.log (1 / S.P.s k) =
      Real.log (1 / S.P.sbar) + k * Real.log (2 * S.P.μ) := by
    intro k
    have h2μ : (0 : ℝ) < 2 * S.P.μ := by linarith
    have : 1 / S.P.s k = (1 / S.P.sbar) * (2 * S.P.μ) ^ k := by
      simp only [Approx.s, ratio]
      field_simp
    rw [this, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  -- the three constants
  set a : ℝ := S.Tz + (3 + 2) / S.σ' * Real.log (1 / S.P.sbar) with ha_def
  set b : ℝ := (3 + 2) * Real.log (2 * S.P.μ) / S.σ' with hb_def
  set c : ℝ := 1 / S.σ' * Real.log (2 * S.P.δ₀ / S.P.κs) with hc_def
  have hlsbar : 0 ≤ Real.log (1 / S.P.sbar) :=
    Real.log_nonneg ((le_div_iff₀ hsbar).mpr (by linarith))
  have hl2μ : 0 ≤ Real.log (2 * S.P.μ) := Real.log_nonneg (by linarith)
  have hTz : 0 ≤ S.Tz := by
    rw [Standing.Tz_def]
    have : 0 ≤ S.σ'⁻¹ * Real.posLog (S.P.δ₀ / S.Klo) :=
      mul_nonneg (inv_nonneg.mpr hσ'.le) Real.posLog_nonneg
    linarith
  have ha : 0 ≤ a := by
    have : 0 ≤ (3 + 2) / S.σ' * Real.log (1 / S.P.sbar) :=
      mul_nonneg (div_nonneg (by norm_num) hσ'.le) hlsbar
    linarith
  have hb : 0 ≤ b := div_nonneg (mul_nonneg (by norm_num) hl2μ) hσ'.le
  -- the last level: `T_n = T̂_n/A_n ≤ c/A_n`
  have hknpos : 0 < S.P.ksh S.P.n := (hc.ksh_mem (by omega) le_rfl).1
  have hln : Real.log (S.P.δ₀ / S.P.ksh S.P.n) ≤ Real.log (2 * S.P.δ₀ / S.P.κs) := by
    apply Real.log_le_log (div_pos hδ₀ hknpos)
    have h2 : 2 * S.P.δ₀ / S.P.κs = S.P.δ₀ / (1 / 2 * S.P.κs) := by
      field_simp
    rw [h2]
    exact div_le_div_of_nonneg_left hδ₀.le (by positivity) hκn
  have hThn := hThat S.P.n (by omega) le_rfl
  have hc0 : 0 ≤ c := by
    rw [hc_def]
    exact mul_nonneg (div_nonneg zero_le_one hσ'.le) (hThn.1.trans hln)
  have hbase : S.P.T S.P.n ≤ c / S.P.A S.P.n := by
    rw [Approx.T_of_ne S.P (by omega), Approx.tsh_n, zero_add]
    refine div_le_div_of_nonneg_right ?_ (hA _ (by omega)).le
    calc S.P.That S.P.n ≤ S.σ'⁻¹ * Real.log (S.P.δ₀ / S.P.ksh S.P.n) := hThn.2
      _ ≤ S.σ'⁻¹ * Real.log (2 * S.P.δ₀ / S.P.κs) :=
          mul_le_mul_of_nonneg_left hln (inv_nonneg.mpr hσ'.le)
      _ = c := by rw [hc_def, one_div]
  -- the levels `k < n`: `T_k ≤ T_{k+1} + (a + bk)/A_k`
  have hstep : ∀ k, 1 ≤ k → k < S.P.n →
      S.P.T k ≤ S.P.T (k + 1) + (a + b * k) / S.P.A k := by
    intro k h1 h2
    have hAk := hA k h1
    have hAk1 : S.P.A k ≤ S.P.A (k + 1) := by
      rw [hAs k h1]
      nlinarith
    have hsk : 0 < S.P.s k := ratio_pos hsbar hμ0 k
    have hkk := hκ k (Finset.mem_Ico.mpr ⟨h1, h2⟩)
    have hkpos : 0 < S.P.ksh k := (hc.ksh_mem h1 h2.le).1
    -- `log(δ₀/κ♯_k) ≤ log₊(δ₀/K_lo) + 5 log(1/s_k)`
    have hlogk : Real.log (S.P.δ₀ / S.P.ksh k) ≤
        Real.posLog (S.P.δ₀ / S.Klo) + 5 * Real.log (1 / S.P.s k) := by
      have hle : Real.log (S.P.δ₀ / S.P.ksh k) ≤
          Real.log (S.P.δ₀ / (S.Klo * S.P.s k ^ (3 + 2))) :=
        Real.log_le_log (div_pos hδ₀ hkpos)
          (div_le_div_of_nonneg_left hδ₀.le (by positivity) hkk)
      have heq : S.P.δ₀ / (S.Klo * S.P.s k ^ (3 + 2)) = (S.P.δ₀ / S.Klo) * (1 / S.P.s k) ^ 5 := by
        field_simp
      rw [heq, Real.log_mul (by positivity) (by positivity), Real.log_pow] at hle
      have hpl : Real.log (S.P.δ₀ / S.Klo) ≤ Real.posLog (S.P.δ₀ / S.Klo) := by
        rw [Real.posLog_apply]
        exact le_max_right _ _
      push_cast at hle
      linarith
    have hThk : S.P.That k ≤
        S.σ'⁻¹ * (Real.posLog (S.P.δ₀ / S.Klo) + 5 * Real.log (1 / S.P.s k)) :=
      (hThat k h1 h2.le).2.trans (mul_le_mul_of_nonneg_left hlogk (inv_nonneg.mpr hσ'.le))
    have hTk : S.P.T k = S.P.T (k + 1) + S.P.Tpin / S.P.A (k + 1) + S.P.That k / S.P.A k := by
      rw [Approx.T_of_ne S.P (by omega), Approx.tsh_eq_T_add S.P h2]
    have hpin : S.P.Tpin / S.P.A (k + 1) ≤ S.P.Tpin / S.P.A k :=
      div_le_div_of_nonneg_left hTpin.le hAk hAk1
    have hnum : S.P.Tpin + S.σ'⁻¹ * (Real.posLog (S.P.δ₀ / S.Klo) + 5 * Real.log (1 / S.P.s k)) ≤
        a + b * k := by
      rw [hlogs k, ha_def, hb_def, Standing.Tz_def]
      have : S.P.Tpin + S.σ'⁻¹ * (Real.posLog (S.P.δ₀ / S.Klo) +
          5 * (Real.log (1 / S.P.sbar) + k * Real.log (2 * S.P.μ))) + 1 =
          S.P.Tpin + 1 + S.σ'⁻¹ * Real.posLog (S.P.δ₀ / S.Klo) +
            (3 + 2) / S.σ' * Real.log (1 / S.P.sbar) +
            (3 + 2) * Real.log (2 * S.P.μ) / S.σ' * k := by
        ring
      linarith
    have hfrac : S.P.That k / S.P.A k ≤
        S.σ'⁻¹ * (Real.posLog (S.P.δ₀ / S.Klo) + 5 * Real.log (1 / S.P.s k)) / S.P.A k :=
      div_le_div_of_nonneg_right hThk hAk.le
    have hsum : S.P.Tpin / S.P.A k +
        S.σ'⁻¹ * (Real.posLog (S.P.δ₀ / S.Klo) + 5 * Real.log (1 / S.P.s k)) / S.P.A k ≤
        (a + b * k) / S.P.A k := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right hnum hAk.le
    rw [hTk]
    linarith
  -- the downward induction, at `j = 1`
  have hmain := rec_bound hμ ha hb hc0 hA hAs hstep hbase (S.P.n - 1) 1 (by omega) le_rfl
  have hA1 : S.P.A 1 = S.P.A₁ := amp_one S.P.A₁ S.P.μ
  rw [hA1] at hmain
  have hF := F_one (a := a) (b := b) (c := c) hμ
  have hTstar : S.Tstar = S.P.A₁⁻¹ *
      (S.P.μ / (S.P.μ - 1) * a + b * (S.P.μ ^ 2 / (S.P.μ - 1) ^ 2) + 1 + c) := rfl
  rw [hTstar]
  refine hmain.trans ?_
  rw [div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hA₁.le)
  have : a * (S.P.μ / (S.P.μ - 1)) + b * (((1 : ℕ) : ℝ) + 1 / (S.P.μ - 1)) * (S.P.μ / (S.P.μ - 1))
      + c = a * (S.P.μ / (S.P.μ - 1)) + b * ((((1 : ℕ) : ℝ) + 1 / (S.P.μ - 1)) *
        (S.P.μ / (S.P.μ - 1))) + c := by ring
  linarith

end Relay

end NonUniqueEuler
