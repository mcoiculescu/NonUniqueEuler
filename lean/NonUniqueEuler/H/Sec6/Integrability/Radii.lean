import NonUniqueEuler.Defs.Sec6.Datum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Helpers for `prop:integrability`: the radii and the amplitudes

Helper of `P/Sec6/Integrability.lean` (`06_datum.tex:35-60`).

* `IntegrabilityH.radius_lt_of_lt`: `r_l < a r_k` for `1 ≤ k < l` (`06_datum.tex:36-39`);
* `IntegrabilityH.annuli_disjoint`: the annuli `{a r_k ≤ |x| ≤ r_k}` are pairwise disjoint;
* `IntegrabilityH.log_inv_radius`: `log(1/r_k) = (k-1) log(1/s̄) + k(k-1)/2 · log(2μ)`;
* `IntegrabilityH.summable_amp_rpow_mul_radius_sq`: `Σ_k A_k^q r_k² < ∞` (`06_datum.tex:52-59`),
  by the ratio test: `A_{k+1}^q r_{k+1}² = μ^q s_k² · A_k^q r_k²` and `s_k → 0`.
-/

noncomputable section

open Filter Topology

namespace NonUniqueEuler.Datum.IntegrabilityH

open RingData

/-- `a > 0`. -/
theorem a_pos : 0 < a := Real.exp_pos _

/-- `s_k = s̄(2μ)^{-k} ≤ s̄`. -/
theorem ratio_le_sbar {sbar μ : ℝ} (hs : 0 ≤ sbar) (hμ : 1 ≤ 2 * μ) (k : ℕ) :
    ratio sbar μ k ≤ sbar :=
  div_le_self hs (one_le_pow₀ hμ)

/-- `s̄ < 1` (indeed `s̄ ≤ a/16` and `a = e^{ξL - ξR} < 1`). -/
theorem sbar_lt_one {A₁ μ sbar : ℝ} (hp : DatumParams A₁ μ sbar) : sbar < 1 := by
  have ha : a < 1 := by
    unfold a
    rw [Real.exp_lt_one_iff]
    unfold ξL ξR
    norm_num
  linarith [hp.sbar_le]

/-- `r_{k+1} ≤ r_k` for every `k` (for `k = 0` both are `1`). -/
theorem radius_succ_le {sbar μ : ℝ} (hs : 0 < sbar) (hs1 : sbar ≤ 1) (hμ : 1 ≤ 2 * μ) (k : ℕ) :
    radius sbar μ (k + 1) ≤ radius sbar μ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [radius]
  · rw [radius_succ sbar μ hk]
    have hr : 0 < radius sbar μ k := radius_pos hs (by linarith) k
    have : ratio sbar μ k ≤ 1 := (ratio_le_sbar hs.le hμ k).trans hs1
    nlinarith

theorem radius_antitone {sbar μ : ℝ} (hs : 0 < sbar) (hs1 : sbar ≤ 1) (hμ : 1 ≤ 2 * μ) :
    Antitone (radius sbar μ) :=
  antitone_nat_of_succ_le (radius_succ_le hs hs1 hμ)

/-- `r_{k+1} < a r_k` for `k ≥ 1` (`06_datum.tex:36-38`). -/
theorem radius_succ_lt {A₁ sbar μ : ℝ} (hp : DatumParams A₁ μ sbar) {k : ℕ}
    (hk : 1 ≤ k) : radius sbar μ (k + 1) < a * radius sbar μ k := by
  rw [radius_succ sbar μ hk]
  have hr : 0 < radius sbar μ k := radius_pos hp.sbar_pos (by linarith [hp.one_lt_μ]) k
  have h1 : ratio sbar μ k ≤ sbar := ratio_le_sbar hp.sbar_pos.le (by linarith [hp.one_lt_μ]) k
  have h2 : ratio sbar μ k < a := by linarith [hp.sbar_le, a_pos]
  exact mul_lt_mul_of_pos_right h2 hr

/-- `r_l < a r_k` for `1 ≤ k < l`: the annulus of index `l` lies in the open disk `B_{a r_k}`
(`06_datum.tex:36-39`). -/
theorem radius_lt_of_lt {A₁ sbar μ : ℝ} (hp : DatumParams A₁ μ sbar) {k l : ℕ} (hk : 1 ≤ k)
    (hkl : k < l) : radius sbar μ l < a * radius sbar μ k :=
  lt_of_le_of_lt
    (radius_antitone hp.sbar_pos (sbar_lt_one hp).le (by linarith [hp.one_lt_μ]) hkl)
    (radius_succ_lt hp hk)

/-- The annuli `{a r_k ≤ |x| ≤ r_k}`, `k ≥ 1`, are pairwise disjoint (`06_datum.tex:36-40`). -/
theorem annuli_disjoint {A₁ μ sbar : ℝ} (hp : DatumParams A₁ μ sbar) :
    ∀ k l : ℕ, 1 ≤ k → 1 ≤ l → k ≠ l →
      Disjoint {x : ℂ | a * radius sbar μ k ≤ ‖x‖ ∧ ‖x‖ ≤ radius sbar μ k}
        {x : ℂ | a * radius sbar μ l ≤ ‖x‖ ∧ ‖x‖ ≤ radius sbar μ l} := by
  intro k l hk hl hkl
  rw [Set.disjoint_left]
  rintro x ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
  rcases lt_or_gt_of_ne hkl with h | h
  · have := radius_lt_of_lt hp hk h
    linarith
  · have := radius_lt_of_lt hp hl h
    linarith

/-- `log(1/r_k) = (k-1) log(1/s̄) + k(k-1)/2 · log(2μ)` for `k ≥ 1` (`06_datum.tex:40-41`). -/
theorem log_inv_radius {sbar μ : ℝ} (hs : 0 < sbar) (hμ : 0 < μ) :
    ∀ k : ℕ, 1 ≤ k → Real.log (1 / radius sbar μ k) =
      ((k : ℝ) - 1) * Real.log (1 / sbar) + (k : ℝ) * ((k : ℝ) - 1) / 2 * Real.log (2 * μ) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have hr : radius sbar μ k ≠ 0 := (radius_pos hs hμ k).ne'
    have hq : ratio sbar μ k ≠ 0 := (ratio_pos hs hμ k).ne'
    have hpow : (2 * μ) ^ k ≠ 0 := pow_ne_zero _ (by positivity)
    have h1 : Real.log (radius sbar μ (k + 1)) =
        Real.log sbar - (k : ℝ) * Real.log (2 * μ) + Real.log (radius sbar μ k) := by
      rw [radius_succ sbar μ hk, Real.log_mul hq hr, ratio, Real.log_div hs.ne' hpow,
        Real.log_pow]
    simp only [one_div, Real.log_inv] at ih ⊢
    rw [h1]
    push_cast
    linear_combination ih

/-- `s_k → 0`. -/
theorem tendsto_ratio {sbar μ : ℝ} (hμ : 1 < μ) :
    Tendsto (fun k : ℕ => ratio sbar μ k) atTop (𝓝 0) := by
  have h : Tendsto (fun k : ℕ => (2 * μ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by linarith)
  exact tendsto_const_nhds.div_atTop h

/-- One step of the ratio test: `A_{k+1}^q r_{k+1}² = (μ^q s_k²) · A_k^q r_k²` for `k ≥ 1`. -/
theorem amp_rpow_mul_radius_sq_succ {A₁ μ sbar : ℝ} (hp : DatumParams A₁ μ sbar) (q : ℝ)
    {k : ℕ} (hk : 1 ≤ k) :
    amp A₁ μ (k + 1) ^ q * radius sbar μ (k + 1) ^ 2 =
      (μ ^ q * ratio sbar μ k ^ 2) * (amp A₁ μ k ^ q * radius sbar μ k ^ 2) := by
  have hμ0 : 0 ≤ μ := by linarith [hp.one_lt_μ]
  have hA : 0 ≤ amp A₁ μ k := (amp_pos hp.A₁_pos (by linarith [hp.one_lt_μ]) k).le
  rw [amp_succ A₁ μ hk, Real.mul_rpow hμ0 hA, radius_succ sbar μ hk]
  ring

/-- `Σ_{k ≥ 1} A_k^q r_k² < ∞` for every real `q` (`06_datum.tex:52-59`; the manuscript states
it for `q ≥ 1`). Ratio test: the ratio `μ^q s_k²` of consecutive terms tends to `0`. -/
theorem summable_amp_rpow_mul_radius_sq {A₁ μ sbar : ℝ} (hp : DatumParams A₁ μ sbar) (q : ℝ) :
    Summable fun j : ℕ => amp A₁ μ (j + 1) ^ q * radius sbar μ (j + 1) ^ 2 := by
  have hμ0 : 0 < μ := by linarith [hp.one_lt_μ]
  have hnn : ∀ j : ℕ, 0 ≤ amp A₁ μ (j + 1) ^ q * radius sbar μ (j + 1) ^ 2 := fun j =>
    mul_nonneg (Real.rpow_nonneg (amp_pos hp.A₁_pos hμ0 _).le _) (sq_nonneg _)
  have hlim : Tendsto (fun j : ℕ => μ ^ q * ratio sbar μ (j + 1) ^ 2) atTop (𝓝 0) := by
    have h := ((tendsto_ratio (sbar := sbar) hp.one_lt_μ).comp (tendsto_add_atTop_nat 1)).pow 2
    simpa using h.const_mul (μ ^ q)
  refine summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num) ?_
  filter_upwards [hlim.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)] with j hj
  rw [Real.norm_of_nonneg (hnn _), Real.norm_of_nonneg (hnn _),
    amp_rpow_mul_radius_sq_succ hp q (by omega : 1 ≤ j + 1)]
  exact mul_le_mul_of_nonneg_right hj (hnn j)

end NonUniqueEuler.Datum.IntegrabilityH
