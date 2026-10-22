import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Sec5.Majorant
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Helpers for `quiet_approx`: the scalar integrals of `eq:Q-hier`

Helper of `P/Sec5/Quiet/Approx.lean` (fully proved). Namespace `NonUniqueEuler.OneRing.QAppH`.
Manuscript `05_single_ring.tex:481-492`: by (M1) `e^{σ(t-τ)} maj(τ)^j ≤ e^{-(j-1)σ(t-τ)} maj(t)^j`,
whose integral over `[0,t]` is `≤ maj(t)^j/((j-1)σ)`, and `e^{σ(t-τ)} η(τ) maj(τ)^{j-1} ≤
η(τ) maj(t)^{j-1}`, whose integral is `≤ maj(t)^j` by (M2).

* `integral_exp_sub` (copied from `H/Sec5/LinearPart/Integrals.lean`), `integral_exp_neg_le`;
* `maj_nonneg`, `maj_le_of`: elementary facts on the majorant;
* `hier_pointwise`: the pointwise bound (with `n = j - 1 ≥ 1`);
* `hier_integral`: the integral of the right side.
-/

noncomputable section

open MeasureTheory Set intervalIntegral

namespace NonUniqueEuler.OneRing.QAppH

/-- `∫₀ᵘ e^{c(u-v)} dv = (e^{cu} - 1)/c`. -/
theorem integral_exp_sub {c : ℝ} (hc : c ≠ 0) (u : ℝ) :
    ∫ v in (0 : ℝ)..u, Real.exp (c * (u - v)) = (Real.exp (c * u) - 1) / c := by
  have hd : ∀ v ∈ uIcc (0 : ℝ) u, HasDerivAt (fun v => -Real.exp (c * (u - v)) / c)
      (Real.exp (c * (u - v))) v := by
    intro v _
    have h1 : HasDerivAt (fun v => c * (u - v)) (c * (-1)) v := by
      simpa using ((hasDerivAt_id v).const_sub u).const_mul c
    have h2 : HasDerivAt (fun v => -Real.exp (c * (u - v)) / c)
        (-(Real.exp (c * (u - v)) * (c * -1)) / c) v := (h1.exp.neg).div_const c
    exact h2.congr_deriv (by field_simp)
  rw [integral_eq_sub_of_hasDerivAt hd]
  · simp only [sub_self, mul_zero, Real.exp_zero, sub_zero]
    ring
  · exact (by fun_prop : Continuous fun v => Real.exp (c * (u - v))).intervalIntegrable _ _

/-- `∫₀ᵗ e^{-c(t-τ)} dτ ≤ 1/c` for `c > 0`. -/
theorem integral_exp_neg_le {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ∫ τ in (0 : ℝ)..t, Real.exp (-c * (t - τ)) ≤ 1 / c := by
  rw [integral_exp_sub (by linarith : -c ≠ 0)]
  have h1 : 0 < Real.exp (-c * t) := Real.exp_pos _
  have e : (Real.exp (-c * t) - 1) / -c = (1 - Real.exp (-c * t)) / c := by
    field_simp
    ring
  rw [e]
  exact div_le_div_of_nonneg_right (by linarith) hc.le

/-- `maj ≥ 0` on `[0,T]` (from (M1) at `τ = 0`). -/
theorem maj_nonneg {σ T : ℝ} (hσ : 0 < σ) {η : ℝ → ℝ} (hη : IntegrableOn η (Icc 0 T))
    (hη0 : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ η t) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    0 ≤ maj σ η t := by
  have h := ((majorant_of_pos hσ hη hη0).1 0 t le_rfl ht.1 ht.2).1
  rw [maj_zero, mul_zero] at h
  exact h

/-- The pointwise bound of `eq:Q-hier`: for `a = e^{σ(t-τ)} ≥ 1`, `0 ≤ m_τ`, `a m_τ ≤ m_t`,
`n ≥ 1`: `a (P m_τ^{n+1} + Q η m_τ^n) ≤ P e^{-nσ(t-τ)} m_t^{n+1} + Q η m_t^n`. -/
theorem hier_pointwise {σ t τ mτ mt P Q e : ℝ} {n : ℕ} (hn : 1 ≤ n) (hτt : τ ≤ t)
    (hσ : 0 ≤ σ) (hmτ : 0 ≤ mτ) (hM1 : Real.exp (σ * (t - τ)) * mτ ≤ mt) (hP : 0 ≤ P)
    (hQ : 0 ≤ Q) (he : 0 ≤ e) :
    Real.exp (σ * (t - τ)) * (P * mτ ^ (n + 1) + Q * e * mτ ^ n) ≤
      P * Real.exp (-(n * σ) * (t - τ)) * mt ^ (n + 1) + Q * e * mt ^ n := by
  set a := Real.exp (σ * (t - τ)) with ha
  have ha1 : 1 ≤ a := Real.one_le_exp (mul_nonneg hσ (by linarith))
  have ha0 : 0 < a := by linarith
  have hexp : Real.exp (-(n * σ) * (t - τ)) = (a ^ n)⁻¹ := by
    rw [ha, ← Real.exp_nat_mul, ← Real.exp_neg]
    congr 1
    ring
  have hamt : a * mτ ≤ mt := hM1
  have hmt : 0 ≤ mt := le_trans (mul_nonneg ha0.le hmτ) hamt
  -- first term
  have h1 : a * mτ ^ (n + 1) ≤ (a ^ n)⁻¹ * mt ^ (n + 1) := by
    have han : 0 < a ^ n := pow_pos ha0 n
    rw [le_inv_mul_iff₀ han]
    calc a ^ n * (a * mτ ^ (n + 1)) = (a * mτ) ^ (n + 1) := by ring
      _ ≤ mt ^ (n + 1) := pow_le_pow_left₀ (mul_nonneg ha0.le hmτ) hamt _
  -- second term
  have h2 : a * mτ ^ n ≤ mt ^ n := by
    have han : a ≤ a ^ n := by
      calc a = a ^ 1 := (pow_one a).symm
        _ ≤ a ^ n := pow_le_pow_right₀ ha1 hn
    calc a * mτ ^ n ≤ a ^ n * mτ ^ n := mul_le_mul_of_nonneg_right han (pow_nonneg hmτ n)
      _ = (a * mτ) ^ n := by ring
      _ ≤ mt ^ n := pow_le_pow_left₀ (mul_nonneg ha0.le hmτ) hamt _
  rw [hexp]
  have e1 : a * (P * mτ ^ (n + 1) + Q * e * mτ ^ n) =
      P * (a * mτ ^ (n + 1)) + Q * e * (a * mτ ^ n) := by ring
  rw [e1]
  have e2 : P * (a ^ n)⁻¹ * mt ^ (n + 1) = P * ((a ^ n)⁻¹ * mt ^ (n + 1)) := by ring
  rw [e2]
  exact add_le_add (mul_le_mul_of_nonneg_left h1 hP)
    (mul_le_mul_of_nonneg_left h2 (mul_nonneg hQ he))

/-- The integral of the right side of `hier_pointwise`:
`∫₀ᵗ (P e^{-nσ(t-τ)} m_t^{n+1} + Q η(τ) m_t^n) dτ ≤ (P/(nσ) + Q) m_t^{n+1}` when `∫₀ᵗ η ≤ m_t`. -/
theorem hier_integral {σ t mt P Q : ℝ} {n : ℕ} (hn : 1 ≤ n) (hσ : 0 < σ)
    (hmt : 0 ≤ mt) (hP : 0 ≤ P) (hQ : 0 ≤ Q) {η : ℝ → ℝ} (hηi : IntervalIntegrable η volume 0 t)
    (hM2 : ∫ τ in (0 : ℝ)..t, η τ ≤ mt) :
    ∫ τ in (0 : ℝ)..t, (P * Real.exp (-(n * σ) * (t - τ)) * mt ^ (n + 1) + Q * η τ * mt ^ n) ≤
      (P / (n * σ) + Q) * mt ^ (n + 1) := by
  have hnσ : 0 < (n : ℝ) * σ := mul_pos (by exact_mod_cast hn) hσ
  have hi1 : IntervalIntegrable (fun τ => P * Real.exp (-(n * σ) * (t - τ)) * mt ^ (n + 1))
      volume 0 t := (by fun_prop : Continuous fun τ =>
        P * Real.exp (-(n * σ) * (t - τ)) * mt ^ (n + 1)).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun τ => Q * η τ * mt ^ n) volume 0 t := by
    have := (hηi.const_mul Q).mul_const (mt ^ n)
    simpa [mul_assoc] using this
  rw [integral_add hi1 hi2]
  have e1 : ∫ τ in (0 : ℝ)..t, P * Real.exp (-(n * σ) * (t - τ)) * mt ^ (n + 1) =
      P * mt ^ (n + 1) * ∫ τ in (0 : ℝ)..t, Real.exp (-(n * σ) * (t - τ)) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext τ
    ring
  have e2 : ∫ τ in (0 : ℝ)..t, Q * η τ * mt ^ n = Q * mt ^ n * ∫ τ in (0 : ℝ)..t, η τ := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext τ
    ring
  rw [e1, e2]
  have hI := integral_exp_neg_le hnσ t
  have hPm : 0 ≤ P * mt ^ (n + 1) := mul_nonneg hP (pow_nonneg hmt _)
  have hQm : 0 ≤ Q * mt ^ n := mul_nonneg hQ (pow_nonneg hmt _)
  calc P * mt ^ (n + 1) * (∫ τ in (0 : ℝ)..t, Real.exp (-(n * σ) * (t - τ))) +
        Q * mt ^ n * ∫ τ in (0 : ℝ)..t, η τ
      ≤ P * mt ^ (n + 1) * (1 / (n * σ)) + Q * mt ^ n * mt :=
        add_le_add (mul_le_mul_of_nonneg_left hI hPm) (mul_le_mul_of_nonneg_left hM2 hQm)
    _ = (P / (n * σ) + Q) * mt ^ (n + 1) := by
        rw [pow_succ]
        field_simp

end NonUniqueEuler.OneRing.QAppH
