import NonUniqueEuler.Defs.Infra.ConvMinkowski
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Proof of `I/Infra/ConvMinkowski/YoungGeneral.lean`: Young's inequality, general exponents

For `convAbs K g x = ∫⁻ ‖K(x-y)‖ ‖g(y)‖ dy` on `ℂ` and real exponents `1 ≤ s, p, r` with
`1/s + 1/p = 1 + 1/r`: `‖|K| ⋆ |g|‖_r ≤ ‖K‖_s ‖g‖_p`
(manuscript `lem:velocity`(a),(b), `02_prelim.tex:323-381`).

The classical three-factor Hölder argument, entirely in `ℝ≥0∞` (so no degenerate case needs a
separate treatment). Put `k = ‖K‖ₑ`, `h = ‖g‖ₑ`, `a = 1/r`, `b = 1 - 1/p`, `c = 1 - 1/s`
(`a, b, c ≥ 0`, `a + b + c = 1`), `A = ∫ k^s`, `B = ∫ h^p`, `Φ(x) = ∫ k(x-y)^s h(y)^p dy`.
1. Pointwise: `k(x-y) h(y) = (k(x-y)^s h(y)^p)^a (k(x-y)^s)^b (h(y)^p)^c` (because
   `s(a + b) = 1` and `p(a + c) = 1`), so the three-factor Hölder inequality
   (`ENNReal.lintegral_mul_prod_norm_pow_le`) and translation invariance give
   `(|K| ⋆ |g|)(x) ≤ Φ(x)^a A^b B^c`.
2. Tonelli and translation invariance: `∫ Φ = A B`.
3. Since `a r = 1`: `∫ (|K| ⋆ |g|)^r ≤ A^{br} B^{cr} A B`, and taking the `r`-th root,
   `(b r + 1)/r = 1/s`, `(c r + 1)/r = 1/p` give `A^{1/s} B^{1/p} = ‖K‖_s ‖g‖_p`.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal

namespace NonUniqueEuler.Conv

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

/-! ### Helpers -/

/-- Three-factor Hölder inequality for `ℝ≥0∞`-valued functions, with weights summing to `1`. -/
private theorem lintegral_three_rpow_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f₁ f₂ f₃ : α → ℝ≥0∞} (h₁ : AEMeasurable f₁ μ) (h₂ : AEMeasurable f₂ μ)
    (h₃ : AEMeasurable f₃ μ) {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c = 1) :
    ∫⁻ y, f₁ y ^ a * f₂ y ^ b * f₃ y ^ c ∂μ ≤
      (∫⁻ y, f₁ y ∂μ) ^ a * (∫⁻ y, f₂ y ∂μ) ^ b * (∫⁻ y, f₃ y ∂μ) ^ c := by
  have h := ENNReal.lintegral_mul_prod_norm_pow_le (μ := μ) (Finset.univ : Finset (Fin 2))
    (g := f₁) (f := ![f₂, f₃]) h₁ (by intro i _; fin_cases i <;> simpa) a (p := ![b, c])
    (by simp [Fin.sum_univ_two]; linarith) ha (by intro i _; fin_cases i <;> simpa)
  simpa [Fin.prod_univ_two, mul_assoc] using h

/-- The pointwise factorization `k h = (k^s h^p)^a (k^s)^b (h^p)^c` when `s (a + b) = 1` and
`p (a + c) = 1`. -/
private theorem mul_eq_three_rpow (k h : ℝ≥0∞) {s p a b c : ℝ} (hs : 0 ≤ s) (hp : 0 ≤ p)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsab : s * a + s * b = 1)
    (hpac : p * a + p * c = 1) :
    k * h = (k ^ s * h ^ p) ^ a * (k ^ s) ^ b * (h ^ p) ^ c := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ ha, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  calc k * h = k ^ (s * a + s * b) * h ^ (p * a + p * c) := by
        rw [hsab, hpac, ENNReal.rpow_one, ENNReal.rpow_one]
    _ = k ^ (s * a) * h ^ (p * a) * k ^ (s * b) * h ^ (p * c) := by
        rw [ENNReal.rpow_add_of_nonneg _ _ (mul_nonneg hs ha) (mul_nonneg hs hb),
          ENNReal.rpow_add_of_nonneg _ _ (mul_nonneg hp ha) (mul_nonneg hp hc)]
        ring

/-- Joint measurability of `(x, y) ↦ ‖K (x - y)‖^s ‖g y‖^p`. -/
private theorem aemeasurable_prod_conv_rpow {K : ℂ → E} {g : ℂ → F}
    (hK : AEStronglyMeasurable K volume) (hg : AEStronglyMeasurable g volume) (s p : ℝ) :
    AEMeasurable (fun q : ℂ × ℂ => ‖K (q.1 - q.2)‖ₑ ^ s * ‖g q.2‖ₑ ^ p)
      ((volume : Measure ℂ).prod volume) :=
  ((hK.enorm.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub volume volume)).pow_const
    s).mul (hg.enorm.comp_snd.pow_const p)

/-- For fixed `x`, `y ↦ ‖K (x - y)‖ₑ` is a.e.-measurable. -/
private theorem aemeasurable_enorm_sub_left {K : ℂ → E} (hK : AEStronglyMeasurable K volume)
    (x : ℂ) : AEMeasurable (fun y => ‖K (x - y)‖ₑ) volume :=
  hK.enorm.comp_quasiMeasurePreserving
    (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving

/-- Tonelli: `∫∫ ‖K (x - y)‖^s ‖g y‖^p dy dx = (∫ ‖K‖^s) (∫ ‖g‖^p)`. -/
private theorem lintegral_lintegral_conv_rpow {K : ℂ → E} {g : ℂ → F}
    (hK : AEStronglyMeasurable K volume) (hg : AEStronglyMeasurable g volume) (s p : ℝ) :
    ∫⁻ x, ∫⁻ y, ‖K (x - y)‖ₑ ^ s * ‖g y‖ₑ ^ p =
      (∫⁻ z, ‖K z‖ₑ ^ s) * ∫⁻ y, ‖g y‖ₑ ^ p := by
  rw [lintegral_lintegral_swap (aemeasurable_prod_conv_rpow hK hg s p)]
  have hm : ∀ y : ℂ, AEMeasurable (fun x => ‖K (x - y)‖ₑ ^ s) volume := fun y =>
    (hK.enorm.comp_quasiMeasurePreserving
      (measurePreserving_sub_right volume y).quasiMeasurePreserving).pow_const s
  have h2 : ∀ y : ℂ, ∫⁻ x, ‖K (x - y)‖ₑ ^ s = ∫⁻ z, ‖K z‖ₑ ^ s := fun y =>
    lintegral_sub_right_eq_self (fun z => ‖K z‖ₑ ^ s) y
  calc ∫⁻ y, ∫⁻ x, ‖K (x - y)‖ₑ ^ s * ‖g y‖ₑ ^ p
      = ∫⁻ y, (∫⁻ z, ‖K z‖ₑ ^ s) * ‖g y‖ₑ ^ p := by
        refine lintegral_congr fun y => ?_
        rw [lintegral_mul_const'' _ (hm y), h2 y]
    _ = (∫⁻ z, ‖K z‖ₑ ^ s) * ∫⁻ y, ‖g y‖ₑ ^ p :=
        lintegral_const_mul'' _ (hg.enorm.pow_const p)

/-- Step 1: `(|K| ⋆ |g|)(x) ≤ Φ(x)^a (∫ ‖K‖^s)^b (∫ ‖g‖^p)^c`. -/
private theorem convAbs_le_three_rpow {K : ℂ → E} {g : ℂ → F}
    (hK : AEStronglyMeasurable K volume) (hg : AEStronglyMeasurable g volume)
    {s p a b c : ℝ} (hs : 0 ≤ s) (hp : 0 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c = 1) (hsab : s * a + s * b = 1) (hpac : p * a + p * c = 1) (x : ℂ) :
    convAbs K g x ≤ (∫⁻ y, ‖K (x - y)‖ₑ ^ s * ‖g y‖ₑ ^ p) ^ a *
      (∫⁻ z, ‖K z‖ₑ ^ s) ^ b * (∫⁻ y, ‖g y‖ₑ ^ p) ^ c := by
  have hk := aemeasurable_enorm_sub_left hK x
  have hgm : AEMeasurable (fun y => ‖g y‖ₑ) volume := hg.enorm
  have htr : ∫⁻ y, ‖K (x - y)‖ₑ ^ s = ∫⁻ z, ‖K z‖ₑ ^ s :=
    lintegral_sub_left_eq_self (fun z => ‖K z‖ₑ ^ s) x
  rw [← htr, convAbs]
  calc ∫⁻ y, ‖K (x - y)‖ₑ * ‖g y‖ₑ
      = ∫⁻ y, (‖K (x - y)‖ₑ ^ s * ‖g y‖ₑ ^ p) ^ a * (‖K (x - y)‖ₑ ^ s) ^ b *
          (‖g y‖ₑ ^ p) ^ c :=
        lintegral_congr fun y => mul_eq_three_rpow _ _ hs hp ha hb hc hsab hpac
    _ ≤ _ := lintegral_three_rpow_le ((hk.pow_const s).mul (hgm.pow_const p))
        (hk.pow_const s) (hgm.pow_const p) ha hb hc habc

/-! ### Young's inequality -/

/-- **Young's convolution inequality**: `‖|K| ⋆ |g|‖_r ≤ ‖K‖_s ‖g‖_p` for
`1 ≤ s, p, r < ∞` with `1/s + 1/p = 1 + 1/r`. -/
theorem eLpNorm_convAbs_le_young {K : ℂ → E} {g : ℂ → F} (hK : AEStronglyMeasurable K volume)
    (hg : AEStronglyMeasurable g volume) {s p r : ℝ} (hs : 1 ≤ s) (hp : 1 ≤ p) (hr : 1 ≤ r)
    (hspr : 1 / s + 1 / p = 1 + 1 / r) :
    eLpNorm (convAbs K g) (ENNReal.ofReal r) volume ≤
      eLpNorm K (ENNReal.ofReal s) volume * eLpNorm g (ENNReal.ofReal p) volume := by
  have hs0 : 0 < s := by linarith
  have hp0 : 0 < p := by linarith
  have hr0 : 0 < r := by linarith
  -- exponents
  set a : ℝ := 1 / r with ha_def
  set b : ℝ := 1 - 1 / p with hb_def
  set c : ℝ := 1 - 1 / s with hc_def
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by
    rw [hb_def, sub_nonneg, div_le_one hp0]; exact hp
  have hc : 0 ≤ c := by
    rw [hc_def, sub_nonneg, div_le_one hs0]; exact hs
  have habc : a + b + c = 1 := by rw [ha_def, hb_def, hc_def]; linarith
  have hab : a + b = 1 / s := by rw [ha_def, hb_def]; linarith
  have hac : a + c = 1 / p := by rw [ha_def, hc_def]; linarith
  have hsab : s * a + s * b = 1 := by rw [← mul_add, hab]; field_simp
  have hpac : p * a + p * c = 1 := by rw [← mul_add, hac]; field_simp
  have har : a * r = 1 := by rw [ha_def]; field_simp
  -- the integrals
  set A : ℝ≥0∞ := ∫⁻ z, ‖K z‖ₑ ^ s with hA_def
  set B : ℝ≥0∞ := ∫⁻ y, ‖g y‖ₑ ^ p with hB_def
  set Φ : ℂ → ℝ≥0∞ := fun x => ∫⁻ y, ‖K (x - y)‖ₑ ^ s * ‖g y‖ₑ ^ p with hΦ_def
  have hΦm : AEMeasurable Φ volume := (aemeasurable_prod_conv_rpow hK hg s p).lintegral_prod_right'
  have hΦint : ∫⁻ x, Φ x = A * B := lintegral_lintegral_conv_rpow hK hg s p
  -- Step 3: the `r`-th power
  have h3 : ∫⁻ x, convAbs K g x ^ r ≤ A * B * (A ^ (b * r) * B ^ (c * r)) := by
    calc ∫⁻ x, convAbs K g x ^ r
        ≤ ∫⁻ x, (Φ x ^ a * A ^ b * B ^ c) ^ r := by
          refine lintegral_mono fun x => ?_
          exact ENNReal.rpow_le_rpow
            (convAbs_le_three_rpow hK hg hs0.le hp0.le ha hb hc habc hsab hpac x) hr0.le
      _ = ∫⁻ x, Φ x * (A ^ (b * r) * B ^ (c * r)) := by
          refine lintegral_congr fun x => ?_
          rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le, ENNReal.mul_rpow_of_nonneg _ _ hr0.le,
            ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, har, ENNReal.rpow_one,
            mul_assoc]
      _ = A * B * (A ^ (b * r) * B ^ (c * r)) := by
          rw [lintegral_mul_const'' _ hΦm, hΦint]
  -- Step 4: the `r`-th root
  have hr_ne : ENNReal.ofReal r ≠ 0 := by simp [hr0]
  have hs_ne : ENNReal.ofReal s ≠ 0 := by simp [hs0]
  have hp_ne : ENNReal.ofReal p ≠ 0 := by simp [hp0]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hr_ne ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hs_ne ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hr0.le, ENNReal.toReal_ofReal hs0.le, ENNReal.toReal_ofReal hp0.le]
  simp only [enorm_eq_self]
  rw [← hA_def, ← hB_def]
  have hbr : 0 ≤ b * r := mul_nonneg hb hr0.le
  have hcr : 0 ≤ c * r := mul_nonneg hc hr0.le
  have hexpA : (b * r + 1) * (1 / r) = 1 / s := by rw [← hab, ha_def]; field_simp; ring
  have hexpB : (c * r + 1) * (1 / r) = 1 / p := by rw [← hac, ha_def]; field_simp; ring
  have hprod : A * B * (A ^ (b * r) * B ^ (c * r)) = A ^ (b * r + 1) * B ^ (c * r + 1) := by
    rw [ENNReal.rpow_add_of_nonneg _ _ hbr zero_le_one,
      ENNReal.rpow_add_of_nonneg _ _ hcr zero_le_one, ENNReal.rpow_one, ENNReal.rpow_one]
    ring
  calc (∫⁻ x, convAbs K g x ^ r) ^ (1 / r)
      ≤ (A * B * (A ^ (b * r) * B ^ (c * r))) ^ (1 / r) :=
        ENNReal.rpow_le_rpow h3 (by positivity)
    _ = A ^ (1 / s) * B ^ (1 / p) := by
        rw [hprod, ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul, hexpA, hexpB]

end NonUniqueEuler.Conv
