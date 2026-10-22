import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Sec5.ActiveT1
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Helpers for `thm:active`: elementary facts (`⟨·⟩`, small `κ`)

Helper of `P/Sec5/Active.lean` (fully proved). Manuscript `05_single_ring.tex:941-952`,
`:1037-1047`. The facts on `t₁` are `tOneOf_spec`, `active_tOne` (`I/Sec5/ActiveT1.lean`).

* `poly_exp_eventually_le`: `K(1+x)^n e^{-bx} ≤ 1` for large `x` (`b > 0`);
* `jap_add_pow_le` (Peetre): `⟨t+u⟩^3 ≤ 2^{3/2}⟨t⟩^3⟨u⟩^3`;
* `jap_mono`: `⟨·⟩` is monotone on `[0,∞)`;
* `small_sqrt`: `Aκ ≤ ½√κ` for small `κ`; `small_varsigma`: `Bκς(κ)^N ≤ ½√κ` for small `κ`.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace NonUniqueEuler.OneRing.ActiveH

open RingData

/-- `K (1 + x)^n e^{-bx} ≤ 1` for all large `x`, if `b > 0`. -/
theorem poly_exp_eventually_le (n : ℕ) {b : ℝ} (hb : 0 < b) (K : ℝ) :
    ∃ X : ℝ, 0 ≤ X ∧ ∀ x : ℝ, X ≤ x → K * (1 + x) ^ n * Real.exp (-(b * x)) ≤ 1 := by
  have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) b hb
  have h2 : Tendsto (fun x : ℝ => 1 + x) atTop atTop := tendsto_atTop_add_const_left _ _ tendsto_id
  have h3 := (h1.comp h2).const_mul (|K| * Real.exp b)
  rw [mul_zero] at h3
  have h4 := h3.eventually (gt_mem_nhds (zero_lt_one : (0 : ℝ) < 1))
  obtain ⟨X, hX⟩ := eventually_atTop.1 (h4.and (eventually_ge_atTop 0))
  refine ⟨max X 0, le_max_right _ _, fun x hx => ?_⟩
  have hxX : X ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 ≤ x := (le_max_right _ _).trans hx
  have hlt := (hX x hxX).1
  simp only [Function.comp] at hlt
  have hpos : 0 ≤ 1 + x := by linarith
  rw [Real.rpow_natCast] at hlt
  have heq : Real.exp (-(b * x)) = Real.exp b * Real.exp (-b * (1 + x)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc K * (1 + x) ^ n * Real.exp (-(b * x))
      ≤ |K| * (1 + x) ^ n * Real.exp (-(b * x)) := by
        gcongr
        exact le_abs_self K
    _ = |K| * Real.exp b * ((1 + x) ^ n * Real.exp (-b * (1 + x))) := by rw [heq]; ring
    _ ≤ 1 := hlt.le

/-- `⟨·⟩` is monotone on `[0,∞)`. -/
theorem jap_mono {t u : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) : Prelim.jap t ≤ Prelim.jap u := by
  rw [Prelim.jap, Prelim.jap]
  apply Real.sqrt_le_sqrt
  nlinarith

/-- Peetre's inequality in the form used in `thm:active` (`05_single_ring.tex:1040`):
`⟨t + u⟩ ≤ √2 ⟨t⟩⟨u⟩`, hence `⟨t+u⟩^3 ≤ 2^{3/2}⟨t⟩^3⟨u⟩^3`. -/
theorem jap_add_pow_le (t u : ℝ) :
    Prelim.jap (t + u) ^ pW ≤ (2 : ℝ) ^ ((pW : ℝ) / 2) * Prelim.jap t ^ pW * Prelim.jap u ^ pW := by
  have hsq : Prelim.jap (t + u) ^ 2 ≤ 2 * (Prelim.jap t ^ 2 * Prelim.jap u ^ 2) := by
    rw [Prelim.jap_sq, Prelim.jap_sq, Prelim.jap_sq]
    nlinarith [sq_nonneg (t - u), sq_nonneg (t * u)]
  have h1 : Prelim.jap (t + u) ≤ Real.sqrt 2 * (Prelim.jap t * Prelim.jap u) := by
    have ht := Prelim.jap_nonneg t
    have hu := Prelim.jap_nonneg u
    calc Prelim.jap (t + u) = Real.sqrt (Prelim.jap (t + u) ^ 2) :=
          (Real.sqrt_sq (Prelim.jap_nonneg _)).symm
      _ ≤ Real.sqrt (2 * (Prelim.jap t ^ 2 * Prelim.jap u ^ 2)) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt 2 * (Prelim.jap t * Prelim.jap u) := by
          rw [Real.sqrt_mul (by norm_num), ← mul_pow, Real.sqrt_sq (by positivity)]
  have h2 : (2 : ℝ) ^ ((pW : ℝ) / 2) = Real.sqrt 2 ^ pW := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [h2, ← mul_pow, ← mul_pow, mul_assoc]
  exact pow_le_pow_left₀ (Prelim.jap_nonneg _) h1 _

/-- `1 < 2^{p/2}`. -/
theorem one_lt_two_rpow : (1 : ℝ) < (2 : ℝ) ^ ((pW : ℝ) / 2) :=
  Real.one_lt_rpow (by norm_num) (by norm_num)

/-- For `A ≥ 0` there is `ε ∈ (0,1]` with `Aκ ≤ ½√κ` on `(0,ε]`. -/
theorem small_sqrt {A : ℝ} (hA : 0 ≤ A) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ ε → A * κ ≤ Real.sqrt κ / 2 := by
  refine ⟨1 / (4 * (A + 1) ^ 2), by positivity, ?_, fun κ hκ hκε => ?_⟩
  · rw [div_le_one (by positivity)]
    nlinarith
  · have hs : Real.sqrt κ ≤ 1 / (2 * (A + 1)) := by
      rw [Real.sqrt_le_left (by positivity)]
      calc κ ≤ 1 / (4 * (A + 1) ^ 2) := hκε
        _ = (1 / (2 * (A + 1))) ^ 2 := by field_simp; ring
    have hsq : κ = Real.sqrt κ * Real.sqrt κ := (Real.mul_self_sqrt hκ.le).symm
    have hs0 : 0 ≤ Real.sqrt κ := Real.sqrt_nonneg κ
    have h2 : 2 * (A + 1) * Real.sqrt κ ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at hs
      linarith
    calc A * κ = A * Real.sqrt κ * Real.sqrt κ := by rw [mul_assoc, Real.mul_self_sqrt hκ.le]
      _ ≤ (A + 1) * Real.sqrt κ * Real.sqrt κ := by gcongr; linarith
      _ ≤ Real.sqrt κ / 2 := by nlinarith

/-- For `B ≥ 0`, `σ_b > 0` and `N : ℕ` there is `ε ∈ (0,1]` with
`Bκ(1 + σ_b⁻¹ log(1/κ))^N ≤ ½√κ` on `(0,ε]` (`05_single_ring.tex:945-946`, (L3)). -/
theorem small_varsigma {B σb : ℝ} (hB : 0 ≤ B) (hσb : 0 < σb) (N : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ ε →
      B * κ * (1 + σb⁻¹ * Real.log (1 / κ)) ^ N ≤ Real.sqrt κ / 2 := by
  obtain ⟨X, hX0, hX⟩ := poly_exp_eventually_le N (by norm_num : (0 : ℝ) < 1 / 2)
    (2 * B * (1 + σb⁻¹) ^ N)
  refine ⟨Real.exp (-X), Real.exp_pos _, ?_, fun κ hκ hκε => ?_⟩
  · rw [Real.exp_le_one_iff]; linarith
  · set x := Real.log (1 / κ) with hx
    have hκx : κ = Real.exp (-x) := by
      rw [hx, Real.log_div one_ne_zero hκ.ne', Real.log_one, zero_sub, neg_neg,
        Real.exp_log hκ]
    have hxX : X ≤ x := by
      have : Real.log κ ≤ -X := by
        rw [← Real.exp_le_exp, Real.exp_log hκ]; exact hκε
      rw [hx, Real.log_div one_ne_zero hκ.ne', Real.log_one]; linarith
    have hx0 : 0 ≤ x := hX0.trans hxX
    have hsqrt : Real.sqrt κ = Real.exp (-(1 / 2 * x)) := by
      rw [hκx, Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le,
        ← Real.exp_add]
      congr 1; ring
    have hvs0 : 0 ≤ 1 + σb⁻¹ * x := by have := inv_pos.2 hσb; positivity
    have hvs : 1 + σb⁻¹ * x ≤ (1 + σb⁻¹) * (1 + x) := by
      have := inv_pos.2 hσb; nlinarith
    have hpow : (1 + σb⁻¹ * x) ^ N ≤ (1 + σb⁻¹) ^ N * (1 + x) ^ N := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hvs0 hvs N
    have hmain : 2 * B * (Real.sqrt κ * (1 + σb⁻¹ * x) ^ N) ≤ 1 := by
      calc 2 * B * (Real.sqrt κ * (1 + σb⁻¹ * x) ^ N)
          ≤ 2 * B * (Real.exp (-(1 / 2 * x)) * ((1 + σb⁻¹) ^ N * (1 + x) ^ N)) := by
            rw [hsqrt]; gcongr
        _ = 2 * B * (1 + σb⁻¹) ^ N * (1 + x) ^ N * Real.exp (-(1 / 2 * x)) := by ring
        _ ≤ 1 := hX x hxX
    have hsq : κ = Real.sqrt κ * Real.sqrt κ := (Real.mul_self_sqrt hκ.le).symm
    have hs0 : 0 ≤ Real.sqrt κ := Real.sqrt_nonneg κ
    calc B * κ * (1 + σb⁻¹ * x) ^ N
        = (2 * B * (Real.sqrt κ * (1 + σb⁻¹ * x) ^ N)) * (Real.sqrt κ / 2) := by
          nth_rewrite 1 [hsq]; ring
      _ ≤ 1 * (Real.sqrt κ / 2) := by gcongr
      _ = Real.sqrt κ / 2 := one_mul _

end NonUniqueEuler.OneRing.ActiveH
