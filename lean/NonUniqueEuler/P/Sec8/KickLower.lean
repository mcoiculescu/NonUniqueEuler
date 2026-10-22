import NonUniqueEuler.Defs.Sec8.All
import NonUniqueEuler.I.Sec8.Pinning
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Proof: `lem:kick-lower` (the amplitude is close to the resonant kick `𝖪`)

Proof of `NonUniqueEuler/I/Sec8/KickLower.lean` (`08_kick.tex:193-212`, proof `:213-227`).

Uses `lem:pinning` (`I/Sec8/Pinning.lean`: `Kick.pinning` with `0` and `τ` in place of `τ` and
`τ'`), and Mathlib: `intervalIntegral.integral_add_adjacent_intervals`,
`intervalIntegral.norm_integral_le_of_norm_le`, `integral_exp_mul_complex`, `Complex.norm_exp`.

The proof follows the manuscript:
1. `|e^{-wT_g}| = e^{-Re w T_g}`, so `|1 - e^{-wT_g}| ≥ 1 - e^{-Re w T_g}` (`kickK_norm_lower`).
2. `A(0) = β∫_{τ₀}^{-T_g} e^{-ζ₀s}q + β∫_{-T_g}^0 e^{-ζ₀s}q` (`amp_zero_split`), and
   `A(τ) - 𝖪 = β∫_{τ₀}^{-T_g} e^{-ζ₀s}q + (β∫_{-T_g}^0 e^{-ζ₀s}q - 𝖪) + (A(τ) - A(0))`.
3. The first term is `≤ |β|Err_pre` (Q2, `norm_integral_pre_le`); the second is `≤ |β|Err_g`
   (Q1, `norm_integral_g_sub_le`, using `∫_{-T_g}^0 q_s e^{ws}ds = q_s(1 - e^{-wT_g})/w`); the
   third is `≤ |β|Q̄I_p(x)` (Q3, `lem:pinning`).
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler

namespace Kick

/-! Helper lemmas, in the namespace `Kick.KickLowerAux` to avoid name clashes. -/

namespace KickLowerAux

/-- `|e^{-ζ₀ s}| = e^{-(Re ζ₀) s}` for real `s`. -/
theorem norm_cexp_neg_mul_ofReal (ζ₀ : ℂ) (s : ℝ) :
    ‖Complex.exp (-(ζ₀ * s))‖ = Real.exp (-(ζ₀.re * s)) := by
  rw [Complex.norm_exp]
  congr 1
  simp

/-- Step 1 of `lem:kick-lower`: `|𝖪| ≥ |β||q_s|(1 - e^{-Re w T_g})/|w|`. -/
theorem kickK_norm_lower (β qs w : ℂ) (Tg : ℝ) :
    ‖β‖ * ‖qs‖ * (1 - Real.exp (-(w.re * Tg))) / ‖w‖ ≤ ‖kickK β qs w Tg‖ := by
  have h1 : 1 - Real.exp (-(w.re * Tg)) ≤ ‖1 - Complex.exp (-(w * Tg))‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (Complex.exp (-(w * Tg)))
    have he : ‖Complex.exp (-(w * Tg))‖ = Real.exp (-(w.re * Tg)) := by
      rw [Complex.norm_exp]
      congr 1
      simp
    rw [he, norm_one] at h
    exact h
  rw [kickK, norm_div, norm_mul, norm_mul]
  have hβq : 0 ≤ ‖β‖ * ‖qs‖ := by positivity
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hβq) (norm_nonneg _)

/-- The integrand `e^{-ζ₀ s} q(s)` of `A` is continuous on `[τ₀, 0]` when `τ₁ > 0`. -/
theorem continuousOn_integrand_Icc {ζ₀ β : ℂ} {τ₀ : ℝ} {τ₁ : EReal} {q : ℝ → ℂ}
    (h : IsSetting ζ₀ β τ₀ τ₁ q) (hτ₁ : (0 : EReal) < τ₁) :
    ContinuousOn (fun s : ℝ => Complex.exp (-(ζ₀ * s)) * q s) (Icc τ₀ 0) := by
  have hsub : Icc τ₀ 0 ⊆ interval τ₀ τ₁ := fun s hs =>
    ⟨hs.1, le_trans (by exact_mod_cast hs.2) hτ₁.le⟩
  have hexp : Continuous (fun s : ℝ => Complex.exp (-(ζ₀ * s))) := by fun_prop
  exact hexp.continuousOn.mul (h.continuousOn.mono hsub)

/-- Step 2 of `lem:kick-lower`: `A(0) = β∫_{τ₀}^{-T_g} e^{-ζ₀s}q + β∫_{-T_g}^0 e^{-ζ₀s}q`. -/
theorem amp_zero_split {ζ₀ β : ℂ} {τ₀ : ℝ} {τ₁ : EReal} {q : ℝ → ℂ}
    (h : IsSetting ζ₀ β τ₀ τ₁ q) (hτ₁ : (0 : EReal) < τ₁) {Tg : ℝ} (hTg : 0 < Tg)
    (hτ₀ : τ₀ < -Tg) :
    amp ζ₀ β τ₀ q 0 = β * (∫ s in τ₀..(-Tg), Complex.exp (-(ζ₀ * s)) * q s) +
      β * (∫ s in (-Tg)..0, Complex.exp (-(ζ₀ * s)) * q s) := by
  have hc := continuousOn_integrand_Icc h hτ₁
  have hTg' : -Tg ≤ 0 := by linarith
  have hi1 : IntervalIntegrable (fun s : ℝ => Complex.exp (-(ζ₀ * s)) * q s) volume τ₀ (-Tg) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hτ₀.le]
    exact hc.mono (Icc_subset_Icc le_rfl hTg')
  have hi2 : IntervalIntegrable (fun s : ℝ => Complex.exp (-(ζ₀ * s)) * q s) volume (-Tg) 0 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hTg']
    exact hc.mono (Icc_subset_Icc hτ₀.le le_rfl)
  rw [amp, ← mul_add, intervalIntegral.integral_add_adjacent_intervals hi1 hi2]

/-- Step 3a of `lem:kick-lower` (Q2): `|∫_{τ₀}^{-T_g} e^{-ζ₀s}q| ≤ Err_pre`. -/
theorem norm_integral_pre_le {ζ₀ : ℂ} {τ₀ Tg : ℝ} {q : ℝ → ℂ} {Qpre : ℝ → ℝ}
    (hτ₀ : τ₀ < -Tg) (h2 : Q2 q τ₀ Tg Qpre) :
    ‖∫ s in τ₀..(-Tg), Complex.exp (-(ζ₀ * s)) * q s‖ ≤ errPre ζ₀.re τ₀ Tg Qpre := by
  obtain ⟨hQI, -, hQB⟩ := h2
  apply intervalIntegral.norm_integral_le_of_norm_le hτ₀.le
  · refine Filter.Eventually.of_forall (fun s hs => ?_)
    rw [norm_mul, norm_cexp_neg_mul_ofReal]
    exact mul_le_mul_of_nonneg_left (hQB s (Ioc_subset_Icc_self hs)) (Real.exp_pos _).le
  · have hQ' : IntervalIntegrable Qpre volume τ₀ (-Tg) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hτ₀.le).mpr hQI
    have hexp : Continuous (fun s : ℝ => Real.exp (-(ζ₀.re * s))) := by fun_prop
    exact hQ'.continuousOn_mul hexp.continuousOn

/-- `∫_{-T_g}^0 q_s e^{ws} ds = q_s(1 - e^{-wT_g})/w` for `w ≠ 0`. -/
theorem integral_qs_cexp (qs w : ℂ) (hw : w ≠ 0) (Tg : ℝ) :
    ∫ s in (-Tg)..0, qs * Complex.exp (w * s) = qs * (1 - Complex.exp (-(w * Tg))) / w := by
  rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hw]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, Complex.ofReal_neg, mul_neg]
  rw [mul_div_assoc]

/-- Step 3b of `lem:kick-lower` (Q1): `|β∫_{-T_g}^0 e^{-ζ₀s}q - 𝖪| ≤ |β|Err_g`. -/
theorem norm_integral_g_sub_le {ζ₀ β : ℂ} {τ₀ : ℝ} {τ₁ : EReal} {q : ℝ → ℂ}
    (h : IsSetting ζ₀ β τ₀ τ₁ q) (hτ₁ : (0 : EReal) < τ₁) {z' : ℂ} (hw : 0 < (z' - ζ₀).re)
    {Tg : ℝ} (hTg : 0 < Tg) (hτ₀ : τ₀ < -Tg) {qs : ℂ} {err : ℝ → ℝ}
    (h1 : Q1 q z' Tg qs err) :
    ‖β * (∫ s in (-Tg)..0, Complex.exp (-(ζ₀ * s)) * q s) - kickK β qs (z' - ζ₀) Tg‖ ≤
      ‖β‖ * errG ζ₀.re Tg err := by
  obtain ⟨-, herrI, -, herrB⟩ := h1
  have hTg' : -Tg ≤ 0 := by linarith
  have hw0 : z' - ζ₀ ≠ 0 := by
    intro h0
    rw [h0, Complex.zero_re] at hw
    exact lt_irrefl _ hw
  have hc := continuousOn_integrand_Icc h hτ₁
  have hi2 : IntervalIntegrable (fun s : ℝ => Complex.exp (-(ζ₀ * s)) * q s) volume (-Tg) 0 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hTg']
    exact hc.mono (Icc_subset_Icc hτ₀.le le_rfl)
  have hg : IntervalIntegrable (fun s : ℝ => qs * Complex.exp ((z' - ζ₀) * s)) volume (-Tg) 0 :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have hK : kickK β qs (z' - ζ₀) Tg =
      β * ∫ s in (-Tg)..0, qs * Complex.exp ((z' - ζ₀) * s) := by
    rw [integral_qs_cexp qs (z' - ζ₀) hw0 Tg, kickK]
    ring
  have hpt : ∀ s : ℝ, Complex.exp (-(ζ₀ * s)) * q s - qs * Complex.exp ((z' - ζ₀) * s) =
      Complex.exp (-(ζ₀ * s)) * (q s - qs * Complex.exp (z' * s)) := by
    intro s
    have he : Complex.exp ((z' - ζ₀) * s) = Complex.exp (-(ζ₀ * s)) * Complex.exp (z' * s) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [he]
    ring
  rw [hK, ← mul_sub, norm_mul, ← intervalIntegral.integral_sub hi2 hg]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  apply intervalIntegral.norm_integral_le_of_norm_le hTg'
  · refine Filter.Eventually.of_forall (fun s hs => ?_)
    rw [hpt, norm_mul, norm_cexp_neg_mul_ofReal]
    exact mul_le_mul_of_nonneg_left (herrB s (Ioc_subset_Icc_self hs)) (Real.exp_pos _).le
  · have he' : IntervalIntegrable err volume (-Tg) 0 :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hTg').mpr herrI
    have hexp : Continuous (fun s : ℝ => Real.exp (-(ζ₀.re * s))) := by fun_prop
    exact he'.continuousOn_mul hexp.continuousOn

end KickLowerAux

open KickLowerAux in
/-- **`lem:kick-lower`** (`08_kick.tex:193-212`). In the setting of Section 8, let `w = z' - ζ₀`
with `Re w > 0`, `T_g > 0`, `τ₀ < -T_g`, `τ₁ > 0`, `Q̄ > 0`, `p ∈ ℕ`, and assume (Q1)–(Q3). Then
`|𝖪| ≥ |β||q_s|(1 - e^{-Re w T_g})/|w|` and `|A(τ) - 𝖪| ≤ 𝖱` for every `τ ∈ I ∩ [0,∞)`. -/
theorem kick_lower {ζ₀ β : ℂ} {τ₀ : ℝ} {τ₁ : EReal} {q : ℝ → ℂ} (h : IsSetting ζ₀ β τ₀ τ₁ q)
    {z' : ℂ} (hw : 0 < (z' - ζ₀).re) {Tg : ℝ} (hTg : 0 < Tg) (hτ₀ : τ₀ < -Tg)
    (hτ₁ : (0 : EReal) < τ₁) {Qbar : ℝ} (hQ : 0 < Qbar) {p : ℕ} {qs : ℂ} {err Qpre : ℝ → ℝ}
    (h1 : Q1 q z' Tg qs err) (h2 : Q2 q τ₀ Tg Qpre) (h3 : Q3 q τ₀ τ₁ Qbar p) :
    ‖β‖ * ‖qs‖ * (1 - Real.exp (-((z' - ζ₀).re * Tg))) / ‖z' - ζ₀‖ ≤
        ‖kickK β qs (z' - ζ₀) Tg‖ ∧
    ∀ τ ∈ interval τ₀ τ₁, 0 ≤ τ →
      ‖amp ζ₀ β τ₀ q τ - kickK β qs (z' - ζ₀) Tg‖ ≤
        kickR β ζ₀.re τ₀ Tg err Qpre Qbar p := by
  refine ⟨kickK_norm_lower β qs (z' - ζ₀) Tg, ?_⟩
  intro τ hτ hτ0
  have hτ₀0 : τ₀ < 0 := by linarith
  have h0I : (0 : ℝ) ∈ interval τ₀ τ₁ := ⟨hτ₀0.le, by exact_mod_cast hτ₁.le⟩
  -- Step 3c (Q3, `lem:pinning` with `0` and `τ`): `|A(τ) - A(0)| ≤ |β|Q̄I_p(x)`.
  have hpin := pinning h hτ₀0 hτ₁ hQ h3 0 h0I τ hτ le_rfl hτ0
  simp only [add_zero, one_pow, mul_one, mul_zero, neg_zero, Real.exp_zero] at hpin
  have hT1 := norm_integral_pre_le (ζ₀ := ζ₀) hτ₀ h2
  have hT2 := norm_integral_g_sub_le h hτ₁ hw hTg hτ₀ h1
  have hT1' : ‖β * (∫ s in τ₀..(-Tg), Complex.exp (-(ζ₀ * s)) * q s)‖ ≤
      ‖β‖ * errPre ζ₀.re τ₀ Tg Qpre := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hT1 (norm_nonneg _)
  calc ‖amp ζ₀ β τ₀ q τ - kickK β qs (z' - ζ₀) Tg‖
      = ‖β * (∫ s in τ₀..(-Tg), Complex.exp (-(ζ₀ * s)) * q s) +
          (β * (∫ s in (-Tg)..0, Complex.exp (-(ζ₀ * s)) * q s) - kickK β qs (z' - ζ₀) Tg) +
          (amp ζ₀ β τ₀ q τ - amp ζ₀ β τ₀ q 0)‖ := by
        rw [amp_zero_split h hτ₁ hTg hτ₀]
        congr 1
        ring
    _ ≤ ‖β * (∫ s in τ₀..(-Tg), Complex.exp (-(ζ₀ * s)) * q s)‖ +
          ‖β * (∫ s in (-Tg)..0, Complex.exp (-(ζ₀ * s)) * q s) - kickK β qs (z' - ζ₀) Tg‖ +
          ‖amp ζ₀ β τ₀ q τ - amp ζ₀ β τ₀ q 0‖ := norm_add₃_le
    _ ≤ ‖β‖ * errPre ζ₀.re τ₀ Tg Qpre + ‖β‖ * errG ζ₀.re Tg err + ‖β‖ * Qbar * Ip p ζ₀.re := by
        gcongr
    _ = kickR β ζ₀.re τ₀ Tg err Qpre Qbar p := by
        rw [kickR]
        ring

end Kick

end NonUniqueEuler
