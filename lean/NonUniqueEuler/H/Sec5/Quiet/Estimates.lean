import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Helpers for `thm:quiet`: the scalar estimates of the comparison step

Helper of `P/Sec5/Quiet.lean` (fully proved). Real-variable lemmas behind `eq:Q-v` and the
radial displacement bound (`05_single_ring.tex:521-549`):

* `exp_mul_pow_le`: `e^{Λ d} x^n ≤ y^n` from `e^{σ d} x ≤ y`, `Λ ≤ nσ`, `d ≥ 0`
  (`05_single_ring.tex:526-528`);
* `energy_integral_le`: `∫₀^τ e^{Λ(τ-τ')} R(τ') dτ' ≤ C (1 + σ_b⁻¹) maj(τ)^{n+1}` from
  `R ≤ C(maj^{n+1} + η maj^n)` and (M1)–(M3) (`eq:Q-v`);
* `radial_integral_le`: `|∫₀^τ f| ≤ (1 + A/σ_b) maj(τ)` from `|f| ≤ η + A maj` and (M2), (M3)
  (`05_single_ring.tex:544-547`).
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler.OneRing.QuietH

/-- `e^{Λd} x^n ≤ y^n` when `e^{σd} x ≤ y`, `Λ ≤ nσ`, `d ≥ 0`, `x ≥ 0`. -/
theorem exp_mul_pow_le {Λ σ d x y : ℝ} {n : ℕ} (hd : 0 ≤ d) (hΛ : Λ ≤ n * σ) (hx : 0 ≤ x)
    (h1 : Real.exp (σ * d) * x ≤ y) : Real.exp (Λ * d) * x ^ n ≤ y ^ n := by
  have he : Real.exp (Λ * d) ≤ Real.exp (σ * d) ^ n := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_right hΛ hd
    linarith
  have hxn : 0 ≤ x ^ n := pow_nonneg hx n
  calc Real.exp (Λ * d) * x ^ n ≤ Real.exp (σ * d) ^ n * x ^ n :=
        mul_le_mul_of_nonneg_right he hxn
    _ = (Real.exp (σ * d) * x) ^ n := (mul_pow _ _ _).symm
    _ ≤ y ^ n := pow_le_pow_left₀ (mul_nonneg (Real.exp_pos _).le hx) h1 n

/-- **The integral of `eq:Q-v`** (`05_single_ring.tex:521-533`). -/
theorem energy_integral_le {Λ σ σb C τ : ℝ} {n : ℕ} {m η R : ℝ → ℝ}
    (hσb : 0 < σb) (hσ : σb ≤ σ) (hΛ : Λ ≤ n * σ) (hC : 0 ≤ C) (hτ : 0 ≤ τ)
    (hm0 : ∀ t ∈ Icc (0 : ℝ) τ, 0 ≤ m t) (hη0 : ∀ t ∈ Icc (0 : ℝ) τ, 0 ≤ η t)
    (hM1 : ∀ t ∈ Icc (0 : ℝ) τ, Real.exp (σ * (τ - t)) * m t ≤ m τ)
    (hM2 : (∫ v in (0 : ℝ)..τ, η v) ≤ m τ) (hM3 : (∫ v in (0 : ℝ)..τ, m v) ≤ m τ / σ)
    (hmi : IntervalIntegrable m volume 0 τ) (hηi : IntervalIntegrable η volume 0 τ)
    (hR : ∀ t ∈ Icc (0 : ℝ) τ, R t ≤ C * (m t ^ (n + 1) + η t * m t ^ n)) :
    (∫ t in (0 : ℝ)..τ, Real.exp (Λ * (τ - t)) * R t) ≤ C * (1 + σb⁻¹) * m τ ^ (n + 1) := by
  have hmτ : 0 ≤ m τ := hm0 τ ⟨hτ, le_rfl⟩
  have hpt : ∀ t ∈ Icc (0 : ℝ) τ,
      Real.exp (Λ * (τ - t)) * R t ≤ C * m τ ^ n * (m t + η t) := by
    intro t ht
    have hd : 0 ≤ τ - t := by linarith [ht.2]
    have hkey := exp_mul_pow_le (n := n) hd hΛ (hm0 t ht) (hM1 t ht)
    have hmt := hm0 t ht
    have hηt := hη0 t ht
    calc Real.exp (Λ * (τ - t)) * R t
        ≤ Real.exp (Λ * (τ - t)) * (C * (m t ^ (n + 1) + η t * m t ^ n)) :=
          mul_le_mul_of_nonneg_left (hR t ht) (Real.exp_pos _).le
      _ = C * (Real.exp (Λ * (τ - t)) * m t ^ n) * (m t + η t) := by ring
      _ ≤ C * m τ ^ n * (m t + η t) := by
          apply mul_le_mul_of_nonneg_right _ (add_nonneg hmt hηt)
          exact mul_le_mul_of_nonneg_left hkey hC
  have hint : IntervalIntegrable (fun t => C * m τ ^ n * (m t + η t)) volume 0 τ :=
    (hmi.add hηi).const_mul _
  have hle : (∫ t in (0 : ℝ)..τ, Real.exp (Λ * (τ - t)) * R t) ≤
      ∫ t in (0 : ℝ)..τ, C * m τ ^ n * (m t + η t) := by
    by_cases hi : IntervalIntegrable (fun t => Real.exp (Λ * (τ - t)) * R t) volume 0 τ
    · exact intervalIntegral.integral_mono_on hτ hi hint hpt
    · rw [intervalIntegral.integral_undef hi]
      refine intervalIntegral.integral_nonneg hτ fun t ht => ?_
      exact mul_nonneg (mul_nonneg hC (pow_nonneg hmτ n)) (add_nonneg (hm0 t ht) (hη0 t ht))
  have heq : (∫ t in (0 : ℝ)..τ, C * m τ ^ n * (m t + η t)) =
      C * m τ ^ n * ((∫ t in (0 : ℝ)..τ, m t) + ∫ t in (0 : ℝ)..τ, η t) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hmi hηi]
  have hdiv : m τ / σ ≤ m τ / σb := div_le_div_of_nonneg_left hmτ hσb hσ
  have hsum : (∫ t in (0 : ℝ)..τ, m t) + (∫ t in (0 : ℝ)..τ, η t) ≤ (1 + σb⁻¹) * m τ := by
    have : m τ / σb = σb⁻¹ * m τ := by rw [div_eq_inv_mul]
    linarith
  calc (∫ t in (0 : ℝ)..τ, Real.exp (Λ * (τ - t)) * R t)
      ≤ C * m τ ^ n * ((∫ t in (0 : ℝ)..τ, m t) + ∫ t in (0 : ℝ)..τ, η t) := hle.trans heq.le
    _ ≤ C * m τ ^ n * ((1 + σb⁻¹) * m τ) :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg hC (pow_nonneg hmτ n))
    _ = C * (1 + σb⁻¹) * m τ ^ (n + 1) := by ring

/-- **The radial displacement integral** (`05_single_ring.tex:544-547`). -/
theorem radial_integral_le {σ σb A τ : ℝ} {m η f : ℝ → ℝ} (hσb : 0 < σb) (hσ : σb ≤ σ)
    (hA : 0 ≤ A) (hτ : 0 ≤ τ) (hmτ : 0 ≤ m τ)
    (hM2 : (∫ v in (0 : ℝ)..τ, η v) ≤ m τ) (hM3 : (∫ v in (0 : ℝ)..τ, m v) ≤ m τ / σ)
    (hmi : IntervalIntegrable m volume 0 τ) (hηi : IntervalIntegrable η volume 0 τ)
    (hf : ∀ t ∈ Ioc (0 : ℝ) τ, |f t| ≤ η t + A * m t) :
    |∫ t in (0 : ℝ)..τ, f t| ≤ (1 + A / σb) * m τ := by
  have hint : IntervalIntegrable (fun t => η t + A * m t) volume 0 τ :=
    hηi.add (hmi.const_mul A)
  have h1 : ‖∫ t in (0 : ℝ)..τ, f t‖ ≤ ∫ t in (0 : ℝ)..τ, (η t + A * m t) := by
    refine intervalIntegral.norm_integral_le_of_norm_le hτ ?_ hint
    exact Filter.Eventually.of_forall fun t ht => by
      rw [Real.norm_eq_abs]; exact hf t ht
  have h2 : (∫ t in (0 : ℝ)..τ, (η t + A * m t)) =
      (∫ t in (0 : ℝ)..τ, η t) + A * ∫ t in (0 : ℝ)..τ, m t := by
    rw [intervalIntegral.integral_add hηi (hmi.const_mul A), intervalIntegral.integral_const_mul]
  have hdiv : m τ / σ ≤ m τ / σb := div_le_div_of_nonneg_left hmτ hσb hσ
  have h3 : A * (∫ t in (0 : ℝ)..τ, m t) ≤ A * (m τ / σb) :=
    mul_le_mul_of_nonneg_left (hM3.trans hdiv) hA
  rw [Real.norm_eq_abs] at h1
  have : A * (m τ / σb) = A / σb * m τ := by ring
  nlinarith
