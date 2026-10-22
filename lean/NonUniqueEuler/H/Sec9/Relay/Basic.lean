import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import NonUniqueEuler.Defs.Sec9.All

/-!
# Helpers for `prop:relay`: generic real and interval-integral lemmas

Helper file of `P/Sec9/Relay.lean` (`09_relay.tex:440-593`). Everything here is proved and
independent of the standing data.

* `integral_le_of_le`: comparison of interval integrals when only the larger integrand is known
  to be integrable (the smaller integral is then bounded or the junk value `0`);
* `integral_le_mul_of_le`: an integrand bounded by a constant `C ≥ 0`;
* `integral_exp_neg_le`: `∫_a^b e^{-c(T-v)} dv ≤ 1/c` for `c > 0`, `a ≤ b ≤ T`;
* `integral_split3`, `integral_exp_shift` (the Duhamel integral over `[0,τ_a]` is
  `e^{σ(τ-τ_a)} maj(τ_a)`);
* the Japanese bracket: `jap_le_jap`, `self_le_jap`, `That_jap_le` (`T̂⟨T̂⟩^m ≤
  ⟨L⟩^{m+1}/(σ_b min(1,σ_b)^m)` for `T̂ = σ_k⁻¹L`, `σ_k ≥ σ_b > 0`, `09_relay.tex:566-570`);
* `mul_exp_log_eq`: `κ e^{γ log(δ₀/κ)} = δ₀ (κ/δ₀)^{1-γ}` (`eq:relay-id`).
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler

namespace Relay

namespace RelayH

/-- Comparison of interval integrals with only the larger integrand integrable. -/
theorem integral_le_of_le {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b) (hfg : ∀ x ∈ Icc a b, f x ≤ g x)
    (hg0 : 0 ≤ ∫ x in a..b, g x) : (∫ x in a..b, f x) ≤ ∫ x in a..b, g x := by
  by_cases hf : IntervalIntegrable f volume a b
  · exact intervalIntegral.integral_mono_on hab hf hg hfg
  · rw [intervalIntegral.integral_undef hf]
    exact hg0

/-- An integrand bounded by a constant `C ≥ 0` on `[a,b]` has integral at most `(b-a)C`. -/
theorem integral_le_mul_of_le {f : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b) (hC : 0 ≤ C)
    (hf : ∀ x ∈ Icc a b, f x ≤ C) : (∫ x in a..b, f x) ≤ (b - a) * C := by
  have h0 : 0 ≤ ∫ _ in a..b, C := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    exact mul_nonneg (by linarith) hC
  have := integral_le_of_le hab intervalIntegrable_const hf h0
  rwa [intervalIntegral.integral_const, smul_eq_mul] at this

/-- `∫_a^b e^{-c(T-v)} dv ≤ 1/c` for `c > 0` and `a ≤ b ≤ T`. -/
theorem integral_exp_neg_le {c a b T : ℝ} (hc : 0 < c) (hab : a ≤ b) (hbT : b ≤ T) :
    (∫ v in a..b, Real.exp (-(c * (T - v)))) ≤ 1 / c := by
  have hderiv : ∀ x ∈ uIcc a b, HasDerivAt (fun v => Real.exp (-(c * (T - v))) / c)
      (Real.exp (-(c * (T - x)))) x := by
    intro x _
    have h1 : HasDerivAt (fun v => -(c * (T - v))) c x := by
      have h := (((hasDerivAt_id x).const_sub T).const_mul c).neg
      simp only [id, mul_neg, mul_one, neg_neg] at h
      exact h
    refine (h1.exp.div_const c).congr_deriv ?_
    exact mul_div_cancel_right₀ _ hc.ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun v => Real.exp (-(c * (T - v)))).intervalIntegrable _ _)]
  have hb : Real.exp (-(c * (T - b))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ c * (T - b) := mul_nonneg hc.le (by linarith)
    linarith
  have ha : 0 < Real.exp (-(c * (T - a))) := Real.exp_pos _
  rw [div_sub_div_same]
  exact div_le_div_of_nonneg_right (by linarith) hc.le

/-- Splitting an interval integral into three adjacent pieces. -/
theorem integral_split3 {F : ℝ → ℝ} {a₀ a₁ a₂ a₃ : ℝ} (h01 : a₀ ≤ a₁) (h12 : a₁ ≤ a₂)
    (h23 : a₂ ≤ a₃) (hF : IntervalIntegrable F volume a₀ a₃) :
    (∫ x in a₀..a₃, F x) = (∫ x in a₀..a₁, F x) + (∫ x in a₁..a₂, F x) + ∫ x in a₂..a₃, F x := by
  have hsub : ∀ {u v : ℝ}, a₀ ≤ u → u ≤ v → v ≤ a₃ → IntervalIntegrable F volume u v := by
    intro u v hu huv hv
    refine hF.mono_set ?_
    rw [uIcc_of_le huv, uIcc_of_le (by linarith)]
    exact Icc_subset_Icc hu hv
  have i01 := hsub le_rfl h01 (by linarith)
  have i12 := hsub h01 h12 (by linarith)
  have i23 := hsub (by linarith) h23 le_rfl
  rw [intervalIntegral.integral_add_adjacent_intervals i01 i12,
    intervalIntegral.integral_add_adjacent_intervals (i01.trans i12) i23]

/-- The Duhamel integral over `[0,τ_a]` at the time `τ`: `e^{σ(τ-τ_a)} maj(τ_a)`. -/
theorem integral_exp_shift (σ τ τa : ℝ) (η : ℝ → ℝ) :
    (∫ v in (0 : ℝ)..τa, Real.exp (σ * (τ - v)) * η v) =
      Real.exp (σ * (τ - τa)) * OneRing.maj σ η τa := by
  unfold OneRing.maj
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun v _ => ?_
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- `0 ≤ maj(τ)` for `τ ≥ 0` and `η ≥ 0` on `[0,τ]`. -/
theorem maj_nonneg_of {σ : ℝ} {η : ℝ → ℝ} {τ : ℝ} (hτ : 0 ≤ τ)
    (hη : ∀ v ∈ Icc (0 : ℝ) τ, 0 ≤ η v) : 0 ≤ OneRing.maj σ η τ := by
  unfold OneRing.maj
  exact intervalIntegral.integral_nonneg hτ fun v hv =>
    mul_nonneg (Real.exp_pos _).le (hη v hv)

/-! ### The Japanese bracket -/

theorem jap_le_jap {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : Prelim.jap x ≤ Prelim.jap y := by
  unfold Prelim.jap
  apply Real.sqrt_le_sqrt
  nlinarith

theorem self_le_jap (x : ℝ) : x ≤ Prelim.jap x := by
  unfold Prelim.jap
  rcases le_or_gt x 0 with hx | hx
  · exact hx.trans (Real.sqrt_nonneg _)
  · rw [Real.le_sqrt hx.le (by positivity)]
    linarith

/-- `⟨L/σ⟩ ≤ ⟨L⟩/min(1,σ)` for `σ > 0`. -/
theorem jap_div_le {L σ : ℝ} (hσ : 0 < σ) : Prelim.jap (L / σ) ≤ Prelim.jap L / min 1 σ := by
  set m := min 1 σ with hm
  have hm0 : 0 < m := lt_min one_pos hσ
  have hm1 : m ≤ 1 := min_le_left _ _
  have hmσ : m ≤ σ := min_le_right _ _
  rw [le_div_iff₀ hm0]
  have h0 : 0 ≤ Prelim.jap (L / σ) * m := mul_nonneg (Prelim.jap_nonneg _) hm0.le
  have hsq : (Prelim.jap (L / σ) * m) ^ 2 ≤ Prelim.jap L ^ 2 := by
    rw [mul_pow, Prelim.jap_sq, Prelim.jap_sq, div_pow]
    have hm2 : m ^ 2 ≤ 1 := by nlinarith
    have hσ2 : 0 < σ ^ 2 := by positivity
    have hmσ2 : m ^ 2 ≤ σ ^ 2 := by nlinarith
    have hL2 : 0 ≤ L ^ 2 := sq_nonneg L
    have : L ^ 2 / σ ^ 2 * m ^ 2 ≤ L ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hσ2]
      nlinarith
    nlinarith
  exact (pow_le_pow_iff_left₀ h0 (Prelim.jap_nonneg _) two_ne_zero).1 hsq

/-- **`T̂⟨T̂⟩^m ≤ ⟨L⟩^{m+1}/(σ_b min(1,σ_b)^m)`** for `T̂ = σ_k⁻¹ L`, `L ≥ 0`, `σ_k ≥ σ_b > 0`
(`09_relay.tex:566-570`, `m = 3`). -/
theorem That_jap_le {L σk σb : ℝ} (hL : 0 ≤ L) (hb : 0 < σb) (hbk : σb ≤ σk) :
    σk⁻¹ * L * Prelim.jap (σk⁻¹ * L) ^ 3 ≤ Prelim.jap L ^ (3 + 1) / (σb * min 1 σb ^ 3) := by
  have hk : 0 < σk := lt_of_lt_of_le hb hbk
  have hm0 : 0 < min 1 σb := lt_min one_pos hb
  have hTh0 : 0 ≤ σk⁻¹ * L := mul_nonneg (inv_nonneg.2 hk.le) hL
  have hTh : σk⁻¹ * L ≤ L / σb := by
    rw [inv_mul_eq_div]
    exact div_le_div_of_nonneg_left hL hb hbk
  have hJ1 : Prelim.jap (σk⁻¹ * L) ≤ Prelim.jap L / min 1 σb :=
    (jap_le_jap hTh0 hTh).trans (jap_div_le hb)
  have hJ2 : L / σb ≤ Prelim.jap L / σb := div_le_div_of_nonneg_right (self_le_jap L) hb.le
  have hJ0 : 0 ≤ Prelim.jap (σk⁻¹ * L) := Prelim.jap_nonneg _
  calc σk⁻¹ * L * Prelim.jap (σk⁻¹ * L) ^ 3
      ≤ (Prelim.jap L / σb) * (Prelim.jap L / min 1 σb) ^ 3 :=
        mul_le_mul (hTh.trans hJ2) (pow_le_pow_left₀ hJ0 hJ1 3) (pow_nonneg hJ0 3)
          (div_nonneg (Prelim.jap_nonneg _) hb.le)
    _ = Prelim.jap L ^ (3 + 1) / (σb * min 1 σb ^ 3) := by
        field_simp

/-- `κ e^{γ log(δ₀/κ)} = δ₀ (κ/δ₀)^{1-γ}` for `κ, δ₀ > 0` (`eq:relay-id`). -/
theorem mul_exp_log_eq {κ δ γ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ) :
    κ * Real.exp (γ * Real.log (δ / κ)) = δ * (κ / δ) ^ (1 - γ) := by
  rw [Real.rpow_def_of_pos (div_pos hκ hδ), Real.log_div hκ.ne' hδ.ne',
    Real.log_div hδ.ne' hκ.ne']
  have e1 : κ * Real.exp (γ * (Real.log δ - Real.log κ)) =
      Real.exp (Real.log κ + γ * (Real.log δ - Real.log κ)) := by
    rw [Real.exp_add, Real.exp_log hκ]
  have e2 : δ * Real.exp ((Real.log κ - Real.log δ) * (1 - γ)) =
      Real.exp (Real.log δ + (Real.log κ - Real.log δ) * (1 - γ)) := by
    rw [Real.exp_add, Real.exp_log hδ]
  rw [e1, e2]
  congr 1
  ring

end RelayH

end Relay

end NonUniqueEuler
