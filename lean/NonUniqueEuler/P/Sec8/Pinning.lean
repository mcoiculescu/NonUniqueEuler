import NonUniqueEuler.Defs.Sec8.All
import NonUniqueEuler.I.Infra.Ip.Ip

/-!
# Proof: `lem:pinning` (the amplitude is pinned after time `0`)

Proof of `NonUniqueEuler/I/Sec8/Pinning.lean` (`08_kick.tex:173-181`, proof `:182-191`).

Uses `I/Infra/Ip/Ip.lean` (`intervalIntegral_le_mul_Ip`:
`∫_τ^{τ'} e^{-xs}(1+s)^p ds ≤ (1+τ)^p e^{-xτ} I_p(x)` for `0 ≤ τ ≤ τ'`), and Mathlib
`intervalIntegral.integral_interval_sub_left`, `intervalIntegral.norm_integral_le_of_norm_le`,
`intervalIntegral.integral_const_mul`, `Complex.norm_exp`.

The proof follows the manuscript:
1. `A(τ') - A(τ) = β∫_τ^{τ'} e^{-ζ₀s}q(s)ds` (`amp_sub_eq`; the integrand is continuous on
   `[τ₀, τ'] ⊆ I`).
2. `|e^{-ζ₀s}q(s)| ≤ Q̄e^{-xs}(1+s)^p` on `[τ, τ'] ⊆ I ∩ [0, ∞)` (Q3).
3. `∫_τ^{τ'} e^{-xs}(1+s)^p ds ≤ (1+τ)^pe^{-xτ}I_p(x)` (`intervalIntegral_le_mul_Ip`).
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler

namespace Kick

/-! Helper lemmas, in the namespace `Kick.PinningAux` to avoid name clashes. -/

namespace PinningAux

/-- `|e^{-ζ₀ s}| = e^{-(Re ζ₀) s}` for real `s`. -/
theorem norm_cexp_neg_mul_ofReal (ζ₀ : ℂ) (s : ℝ) :
    ‖Complex.exp (-(ζ₀ * s))‖ = Real.exp (-(ζ₀.re * s)) := by
  rw [Complex.norm_exp]
  congr 1
  simp

/-- `[τ₀, τ'] ⊆ I` for `τ' ∈ I`. -/
theorem Icc_subset_interval {τ₀ : ℝ} {τ₁ : EReal} {τ' : ℝ} (hτ' : τ' ∈ interval τ₀ τ₁) :
    Icc τ₀ τ' ⊆ interval τ₀ τ₁ := fun s hs =>
  ⟨hs.1, le_trans (by exact_mod_cast hs.2) hτ'.2⟩

/-- The integrand `e^{-ζ₀ s} q(s)` of `A` is interval integrable on `[τ₀, τ']` for `τ' ∈ I`. -/
theorem intervalIntegrable_integrand {ζ₀ β : ℂ} {τ₀ : ℝ} {τ₁ : EReal} {q : ℝ → ℂ}
    (h : IsSetting ζ₀ β τ₀ τ₁ q) {τ' : ℝ} (hτ' : τ' ∈ interval τ₀ τ₁) :
    IntervalIntegrable (fun s : ℝ => Complex.exp (-(ζ₀ * s)) * q s) volume τ₀ τ' := by
  have hexp : Continuous (fun s : ℝ => Complex.exp (-(ζ₀ * s))) := by fun_prop
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hτ'.1]
  exact hexp.continuousOn.mul (h.continuousOn.mono (Icc_subset_interval hτ'))

/-- Step 1: `A(τ') - A(τ) = β∫_τ^{τ'} e^{-ζ₀s}q(s)ds` for `τ, τ' ∈ I`. -/
theorem amp_sub_eq {ζ₀ β : ℂ} {τ₀ : ℝ} {τ₁ : EReal} {q : ℝ → ℂ}
    (h : IsSetting ζ₀ β τ₀ τ₁ q) {τ τ' : ℝ} (hτ : τ ∈ interval τ₀ τ₁)
    (hτ' : τ' ∈ interval τ₀ τ₁) :
    amp ζ₀ β τ₀ q τ' - amp ζ₀ β τ₀ q τ =
      β * ∫ s in τ..τ', Complex.exp (-(ζ₀ * s)) * q s := by
  rw [amp, amp, ← mul_sub,
    intervalIntegral.integral_interval_sub_left (intervalIntegrable_integrand h hτ')
      (intervalIntegrable_integrand h hτ)]

/-- Step 2: `|∫_τ^{τ'} e^{-ζ₀s}q(s)ds| ≤ Q̄∫_τ^{τ'} e^{-xs}(1+s)^p ds` for `τ, τ' ∈ I`,
`0 ≤ τ ≤ τ'` (Q3). -/
theorem norm_integral_le {ζ₀ : ℂ} {τ₀ : ℝ} {τ₁ : EReal} {q : ℝ → ℂ} {Qbar : ℝ} {p : ℕ}
    (hq : Q3 q τ₀ τ₁ Qbar p)
    {τ τ' : ℝ} (hτ : τ ∈ interval τ₀ τ₁) (hτ' : τ' ∈ interval τ₀ τ₁) (h0 : 0 ≤ τ)
    (hle : τ ≤ τ') :
    ‖∫ s in τ..τ', Complex.exp (-(ζ₀ * s)) * q s‖ ≤
      Qbar * ∫ s in τ..τ', Real.exp (-ζ₀.re * s) * (1 + s) ^ p := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.norm_integral_le_of_norm_le hle
  · refine Filter.Eventually.of_forall (fun s hs => ?_)
    have hsI : s ∈ interval τ₀ τ₁ := Icc_subset_interval hτ' ⟨le_trans hτ.1 hs.1.le, hs.2⟩
    have hs0 : 0 ≤ s := le_trans h0 hs.1.le
    rw [norm_mul, norm_cexp_neg_mul_ofReal, neg_mul]
    have hqs := hq s hsI hs0
    have hexp : 0 ≤ Real.exp (-(ζ₀.re * s)) := (Real.exp_pos _).le
    calc Real.exp (-(ζ₀.re * s)) * ‖q s‖ ≤ Real.exp (-(ζ₀.re * s)) * (Qbar * (1 + s) ^ p) :=
          mul_le_mul_of_nonneg_left hqs hexp
      _ = Qbar * (Real.exp (-(ζ₀.re * s)) * (1 + s) ^ p) := by ring
  · have hc : Continuous (fun s : ℝ => Qbar * (Real.exp (-ζ₀.re * s) * (1 + s) ^ p)) := by
      fun_prop
    exact hc.intervalIntegrable _ _

end PinningAux

open PinningAux in
/-- **`lem:pinning`** (`08_kick.tex:173-181`). In the setting of Section 8 with `τ₀ < 0 < τ₁`,
`Q̄ > 0`, `p ∈ ℕ` and `|q(τ)| ≤ Q̄(1+τ)^p` on `I ∩ [0,∞)`: for `τ, τ' ∈ I` with `0 ≤ τ ≤ τ'`,
`|A(τ') - A(τ)| ≤ |β|Q̄(1+τ)^pe^{-xτ}I_p(x)`, `x = Re ζ₀`. -/
theorem pinning {ζ₀ β : ℂ} {τ₀ : ℝ} {τ₁ : EReal} {q : ℝ → ℂ} (h : IsSetting ζ₀ β τ₀ τ₁ q)
    (hτ₀ : τ₀ < 0) (hτ₁ : (0 : EReal) < τ₁) {Qbar : ℝ} (hQ : 0 < Qbar) {p : ℕ}
    (hq : Q3 q τ₀ τ₁ Qbar p) :
    ∀ τ ∈ interval τ₀ τ₁, ∀ τ' ∈ interval τ₀ τ₁, 0 ≤ τ → τ ≤ τ' →
      ‖amp ζ₀ β τ₀ q τ' - amp ζ₀ β τ₀ q τ‖ ≤
        ‖β‖ * Qbar * (1 + τ) ^ p * Real.exp (-(ζ₀.re * τ)) * Ip p ζ₀.re := by
  intro τ hτ τ' hτ' h0 hle
  rw [amp_sub_eq h hτ hτ', norm_mul]
  have h2 := norm_integral_le (ζ₀ := ζ₀) hq hτ hτ' h0 hle
  have h3 := intervalIntegral_le_mul_Ip p h.re_pos h0 hle
  rw [neg_mul] at h3
  have hβ : 0 ≤ ‖β‖ := norm_nonneg _
  calc ‖β‖ * ‖∫ s in τ..τ', Complex.exp (-(ζ₀ * s)) * q s‖
      ≤ ‖β‖ * (Qbar * ∫ s in τ..τ', Real.exp (-ζ₀.re * s) * (1 + s) ^ p) :=
        mul_le_mul_of_nonneg_left h2 hβ
    _ ≤ ‖β‖ * (Qbar * ((1 + τ) ^ p * Real.exp (-(ζ₀.re * τ)) * Ip p ζ₀.re)) := by
        gcongr
    _ = ‖β‖ * Qbar * (1 + τ) ^ p * Real.exp (-(ζ₀.re * τ)) * Ip p ζ₀.re := by ring

end Kick

end NonUniqueEuler
