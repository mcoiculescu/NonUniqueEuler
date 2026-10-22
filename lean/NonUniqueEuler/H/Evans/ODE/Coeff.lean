import NonUniqueEuler.Statement.Evans
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Helper for `P/Evans/ODE`: the Riccati coefficient

Facts about the profile `ϖ = prof χ`, the angular velocity `Ω_G = OmegaG χ G` and the Riccati
coefficient `V = riccatiCoeff χ ℓ z G` of `04_ring.tex` (`def:sector-setting`, `lem:sector`(3),
`hyp:N`):
* `ϖ` is `C^∞` with compact support, so `ϖ'` is bounded (`exists_bound_deriv_prof`);
* `Ω_G` is `C^∞` (`contDiff_OmegaG`; the integral over `(-∞, ξ]` is a constant plus a
  primitive), and `Ω_G - Ω_{G'} = e^{-2ξ}(G - G')`;
* the denominator `den = λ + iℓΩ_G` has real part `Re λ`, hence `|den| ≥ Re λ`;
* `V` is `C^∞` (`contDiff_riccatiCoeff'`), bounded (`norm_riccatiCoeff_le`), Lipschitz in
  `(λ, G)` (`norm_riccatiCoeff_sub_le`), and complex differentiable in `λ` with derivative
  `Vdot` and a quadratic remainder (`norm_riccatiCoeff_sub_sub_le`).
-/

noncomputable section

namespace NonUniqueEuler.EvansODE

open RingData Set MeasureTheory
open scoped ContDiff

variable {χ : ℝ → ℝ}

theorem contDiff_H : ContDiff ℝ ∞ H := by
  show ContDiff ℝ ∞ (fun x : ℝ => (1 + Real.exp (-2 * x))⁻¹)
  have h : ContDiff ℝ ∞ (fun x : ℝ => 1 + Real.exp (-2 * x)) :=
    contDiff_const.add (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))
  exact h.inv fun x => by positivity

theorem contDiff_prof (hχ : IsAdmissibleCutoff χ) : ContDiff ℝ ∞ (prof χ) := by
  show ContDiff ℝ ∞ (fun ξ => χ ξ * H ((ξ - a₀) / d) * H (-ξ / d))
  have hA : ContDiff ℝ ∞ (fun ξ : ℝ => H ((ξ - a₀) / d)) :=
    contDiff_H.comp ((contDiff_id.sub contDiff_const).div_const _)
  have hB : ContDiff ℝ ∞ (fun ξ : ℝ => H (-ξ / d)) :=
    contDiff_H.comp (contDiff_id.neg.div_const _)
  exact (hχ.contDiff.mul hA).mul hB

theorem hasCompactSupport_chi (hχ : IsAdmissibleCutoff χ) : HasCompactSupport χ :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport χ) hχ.tsupport_subset

theorem hasCompactSupport_prof (hχ : IsAdmissibleCutoff χ) : HasCompactSupport (prof χ) :=
  ((hasCompactSupport_chi hχ).mul_right (f' := fun ξ => H ((ξ - a₀) / d))).mul_right
    (f' := fun ξ => H (-ξ / d))

theorem contDiff_deriv_prof (hχ : IsAdmissibleCutoff χ) : ContDiff ℝ ∞ (deriv (prof χ)) :=
  (contDiff_infty_iff_deriv.1 (contDiff_prof hχ)).2

theorem exists_bound_deriv_prof (hχ : IsAdmissibleCutoff χ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ξ, |deriv (prof χ) ξ| ≤ M := by
  obtain ⟨C, hC⟩ := (contDiff_deriv_prof hχ).continuous.bounded_above_of_compact_support
    (hasCompactSupport_prof hχ).deriv
  exact ⟨max C 0, le_max_right _ _, fun ξ => (hC ξ).trans (le_max_left _ _)⟩

/-- The integrand `ϖ(t) e^{2t}` of `Ω_G`. -/
def qInt (χ : ℝ → ℝ) (t : ℝ) : ℝ := prof χ t * Real.exp (2 * t)

theorem contDiff_qInt (hχ : IsAdmissibleCutoff χ) : ContDiff ℝ ∞ (qInt χ) :=
  (contDiff_prof hχ).mul (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))

theorem integrable_qInt (hχ : IsAdmissibleCutoff χ) : Integrable (qInt χ) :=
  (contDiff_qInt hχ).continuous.integrable_of_hasCompactSupport
    ((hasCompactSupport_prof hχ).mul_right (f' := fun t => Real.exp (2 * t)))

theorem integral_Iic_qInt (hχ : IsAdmissibleCutoff χ) (ξ : ℝ) :
    ∫ t in Iic ξ, prof χ t * Real.exp (2 * t) =
      (∫ t in Iic 0, qInt χ t) + ∫ t in (0 : ℝ)..ξ, qInt χ t := by
  rw [← intervalIntegral.integral_Iic_sub_Iic (integrable_qInt hχ).integrableOn
    (integrable_qInt hχ).integrableOn]
  simp only [qInt]
  ring

theorem contDiff_OmegaG (hχ : IsAdmissibleCutoff χ) (G : ℝ) : ContDiff ℝ ∞ (OmegaG χ G) := by
  have hq := contDiff_qInt hχ
  have hd : ∀ ξ, HasDerivAt (fun ξ => ∫ t in (0 : ℝ)..ξ, qInt χ t) (qInt χ ξ) ξ :=
    fun ξ => (hq.continuous.integral_hasStrictDerivAt 0 ξ).hasDerivAt
  have hprim : ContDiff ℝ ∞ (fun ξ => ∫ t in (0 : ℝ)..ξ, qInt χ t) := by
    rw [contDiff_infty_iff_deriv]
    refine ⟨fun ξ => (hd ξ).differentiableAt, ?_⟩
    have : deriv (fun ξ => ∫ t in (0 : ℝ)..ξ, qInt χ t) = qInt χ := funext fun ξ => (hd ξ).deriv
    rw [this]
    exact hq
  have heq : OmegaG χ G = fun ξ => Real.exp (-2 * ξ) *
      (G + ((∫ t in Iic 0, qInt χ t) + ∫ t in (0 : ℝ)..ξ, qInt χ t)) := by
    funext ξ
    simp only [OmegaG]
    rw [integral_Iic_qInt hχ ξ]
  rw [heq]
  exact (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul
    (contDiff_const.add (contDiff_const.add hprim))

theorem OmegaG_sub (χ : ℝ → ℝ) (G G' ξ : ℝ) :
    OmegaG χ G ξ - OmegaG χ G' ξ = Real.exp (-2 * ξ) * (G - G') := by
  simp only [OmegaG]
  ring

/-- The denominator `λ + iℓΩ_G(ξ)` of the Riccati coefficient. -/
def den (χ : ℝ → ℝ) (ℓ : ℕ) (z : ℂ) (G ξ : ℝ) : ℂ :=
  z + Complex.I * (ℓ : ℂ) * ((OmegaG χ G ξ : ℝ) : ℂ)

theorem re_den (χ : ℝ → ℝ) (ℓ : ℕ) (z : ℂ) (G ξ : ℝ) : (den χ ℓ z G ξ).re = z.re := by
  simp [den]

theorem re_le_norm_den (χ : ℝ → ℝ) (ℓ : ℕ) (z : ℂ) (G ξ : ℝ) : z.re ≤ ‖den χ ℓ z G ξ‖ := by
  have := Complex.re_le_norm (den χ ℓ z G ξ)
  rwa [re_den] at this

theorem den_ne_zero (χ : ℝ → ℝ) (ℓ : ℕ) {z : ℂ} (hz : 0 < z.re) (G ξ : ℝ) :
    den χ ℓ z G ξ ≠ 0 := by
  intro h
  have := re_den χ ℓ z G ξ
  rw [h, Complex.zero_re] at this
  linarith

theorem riccatiCoeff_eq (χ : ℝ → ℝ) (ℓ : ℕ) (z : ℂ) (G ξ : ℝ) :
    riccatiCoeff χ ℓ z G ξ =
      (ℓ : ℂ) ^ 2 + Complex.I * (ℓ : ℂ) * ((deriv (prof χ) ξ : ℝ) : ℂ) / den χ ℓ z G ξ := rfl

theorem norm_I_mul_deriv (χ : ℝ → ℝ) (ℓ : ℕ) (ξ : ℝ) :
    ‖Complex.I * (ℓ : ℂ) * ((deriv (prof χ) ξ : ℝ) : ℂ)‖ = ℓ * |deriv (prof χ) ξ| := by
  rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_natCast, Complex.norm_real,
    Real.norm_eq_abs, one_mul]

theorem contDiff_den (hχ : IsAdmissibleCutoff χ) (ℓ : ℕ) (z : ℂ) (G : ℝ) :
    ContDiff ℝ ∞ (fun ξ => den χ ℓ z G ξ) :=
  contDiff_const.add (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_OmegaG hχ G)))

theorem contDiff_riccatiCoeff' (hχ : IsAdmissibleCutoff χ) (ℓ : ℕ) {z : ℂ} (hz : 0 < z.re)
    (G : ℝ) : ContDiff ℝ ∞ (fun ξ => riccatiCoeff χ ℓ z G ξ) := by
  have hf : ContDiff ℝ ∞ (fun ξ => ((deriv (prof χ) ξ : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_deriv_prof hχ)
  have hinv : ContDiff ℝ ∞ (fun ξ => (den χ ℓ z G ξ)⁻¹) :=
    (contDiff_den hχ ℓ z G).inv fun ξ => den_ne_zero χ ℓ hz G ξ
  have h : ContDiff ℝ ∞ (fun ξ => (ℓ : ℂ) ^ 2 +
      Complex.I * (ℓ : ℂ) * ((deriv (prof χ) ξ : ℝ) : ℂ) * (den χ ℓ z G ξ)⁻¹) :=
    contDiff_const.add ((contDiff_const.mul hf).mul hinv)
  have heq : (fun ξ => riccatiCoeff χ ℓ z G ξ) = (fun ξ => (ℓ : ℂ) ^ 2 +
      Complex.I * (ℓ : ℂ) * ((deriv (prof χ) ξ : ℝ) : ℂ) * (den χ ℓ z G ξ)⁻¹) := by
    funext ξ
    rw [riccatiCoeff_eq, div_eq_mul_inv]
  rw [heq]
  exact h

theorem norm_riccatiCoeff_le (ℓ : ℕ) {M ρ : ℝ} (hM : ∀ ξ, |deriv (prof χ) ξ| ≤ M) (hρ : 0 < ρ)
    {z : ℂ} (hz : ρ ≤ z.re) (G ξ : ℝ) :
    ‖riccatiCoeff χ ℓ z G ξ‖ ≤ (ℓ : ℝ) ^ 2 + ℓ * M / ρ := by
  rw [riccatiCoeff_eq]
  refine (norm_add_le _ _).trans ?_
  rw [norm_div, norm_I_mul_deriv, norm_pow, Complex.norm_natCast]
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM ξ)
  have h1 : (ℓ : ℝ) * |deriv (prof χ) ξ| ≤ ℓ * M :=
    mul_le_mul_of_nonneg_left (hM ξ) (Nat.cast_nonneg _)
  have h2 : ρ ≤ ‖den χ ℓ z G ξ‖ := hz.trans (re_le_norm_den χ ℓ z G ξ)
  have := div_le_div₀ (mul_nonneg (Nat.cast_nonneg ℓ) hM0) h1 hρ h2
  linarith

theorem norm_riccatiCoeff_sub_le (ℓ : ℕ) {M ρ : ℝ} (hM : ∀ ξ, |deriv (prof χ) ξ| ≤ M)
    (hρ : 0 < ρ) {z z₀ : ℂ} (hz : ρ ≤ z.re) (hz₀ : ρ ≤ z₀.re) (G G₀ ξ : ℝ) :
    ‖riccatiCoeff χ ℓ z G ξ - riccatiCoeff χ ℓ z₀ G₀ ξ‖ ≤
      ℓ * M * (‖z - z₀‖ + ℓ * Real.exp (-2 * ξ) * |G - G₀|) / (ρ * ρ) := by
  have hD : den χ ℓ z G ξ ≠ 0 := den_ne_zero χ ℓ (hρ.trans_le hz) G ξ
  have hD₀ : den χ ℓ z₀ G₀ ξ ≠ 0 := den_ne_zero χ ℓ (hρ.trans_le hz₀) G₀ ξ
  set f : ℂ := Complex.I * (ℓ : ℂ) * ((deriv (prof χ) ξ : ℝ) : ℂ) with hf
  have key : riccatiCoeff χ ℓ z G ξ - riccatiCoeff χ ℓ z₀ G₀ ξ =
      f * (den χ ℓ z₀ G₀ ξ - den χ ℓ z G ξ) / (den χ ℓ z G ξ * den χ ℓ z₀ G₀ ξ) := by
    rw [riccatiCoeff_eq, riccatiCoeff_eq]
    field_simp
    ring
  have hdd : den χ ℓ z₀ G₀ ξ - den χ ℓ z G ξ =
      (z₀ - z) - Complex.I * (ℓ : ℂ) * (((Real.exp (-2 * ξ) * (G - G₀) : ℝ)) : ℂ) := by
    rw [← OmegaG_sub χ G G₀ ξ]
    simp only [den, Complex.ofReal_sub]
    ring
  have hnum : ‖den χ ℓ z₀ G₀ ξ - den χ ℓ z G ξ‖ ≤ ‖z - z₀‖ + ℓ * Real.exp (-2 * ξ) * |G - G₀| := by
    rw [hdd]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_sub_rev, norm_mul, norm_mul, Complex.norm_I, Complex.norm_natCast, Complex.norm_real,
      Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), one_mul, mul_assoc]
  have hden : ρ * ρ ≤ ‖den χ ℓ z G ξ * den χ ℓ z₀ G₀ ξ‖ := by
    rw [norm_mul]
    exact mul_le_mul (hz.trans (re_le_norm_den χ ℓ z G ξ)) (hz₀.trans (re_le_norm_den χ ℓ z₀ G₀ ξ))
      hρ.le (norm_nonneg _)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM ξ)
  rw [key, norm_div, norm_mul, hf, norm_I_mul_deriv]
  apply div_le_div₀ (by positivity) _ (by positivity) hden
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hM ξ) (Nat.cast_nonneg _)) hnum (norm_nonneg _)
    (by positivity)

/-- The `λ`-derivative of the Riccati coefficient: `-iℓϖ'/(λ + iℓΩ_G)²`. -/
def Vdot (χ : ℝ → ℝ) (ℓ : ℕ) (z : ℂ) (G ξ : ℝ) : ℂ :=
  -(Complex.I * (ℓ : ℂ) * ((deriv (prof χ) ξ : ℝ) : ℂ)) / den χ ℓ z G ξ ^ 2

theorem continuous_Vdot (hχ : IsAdmissibleCutoff χ) (ℓ : ℕ) {z : ℂ} (hz : 0 < z.re) (G : ℝ) :
    Continuous (fun ξ => Vdot χ ℓ z G ξ) := by
  have hf : Continuous (fun ξ => ((deriv (prof χ) ξ : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (contDiff_deriv_prof hχ).continuous
  have hD := (contDiff_den hχ ℓ z G).continuous
  exact (continuous_const.mul hf).neg.div (hD.pow 2) fun ξ => pow_ne_zero 2 (den_ne_zero χ ℓ hz G ξ)

theorem norm_riccatiCoeff_sub_sub_le (ℓ : ℕ) {M ρ : ℝ} (hM : ∀ ξ, |deriv (prof χ) ξ| ≤ M)
    (hρ : 0 < ρ) {z z₀ : ℂ} (hz : ρ ≤ z.re) (hz₀ : ρ ≤ z₀.re) (G ξ : ℝ) :
    ‖riccatiCoeff χ ℓ z G ξ - riccatiCoeff χ ℓ z₀ G ξ - (z - z₀) * Vdot χ ℓ z₀ G ξ‖ ≤
      ℓ * M * ‖z - z₀‖ ^ 2 / ρ ^ 3 := by
  have hD : den χ ℓ z G ξ ≠ 0 := den_ne_zero χ ℓ (hρ.trans_le hz) G ξ
  have hD₀ : den χ ℓ z₀ G ξ ≠ 0 := den_ne_zero χ ℓ (hρ.trans_le hz₀) G ξ
  set f : ℂ := Complex.I * (ℓ : ℂ) * ((deriv (prof χ) ξ : ℝ) : ℂ) with hf
  have hdd : den χ ℓ z G ξ = den χ ℓ z₀ G ξ + (z - z₀) := by
    simp only [den]
    ring
  have key : riccatiCoeff χ ℓ z G ξ - riccatiCoeff χ ℓ z₀ G ξ - (z - z₀) * Vdot χ ℓ z₀ G ξ =
      f * (z - z₀) ^ 2 / (den χ ℓ z G ξ * den χ ℓ z₀ G ξ ^ 2) := by
    rw [riccatiCoeff_eq, riccatiCoeff_eq, Vdot]
    rw [← hf]
    field_simp
    rw [hdd]
    ring
  have hden : ρ ^ 3 ≤ ‖den χ ℓ z G ξ * den χ ℓ z₀ G ξ ^ 2‖ := by
    rw [norm_mul, norm_pow, pow_succ']
    have h1 := hz.trans (re_le_norm_den χ ℓ z G ξ)
    have h2 := hz₀.trans (re_le_norm_den χ ℓ z₀ G ξ)
    exact mul_le_mul h1 (pow_le_pow_left₀ hρ.le h2 2) (by positivity) (norm_nonneg _)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM ξ)
  rw [key, norm_div, norm_mul, hf, norm_I_mul_deriv, norm_pow]
  apply div_le_div₀ (by positivity) _ (by positivity) hden
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hM ξ) (Nat.cast_nonneg _))
    (by positivity)

end NonUniqueEuler.EvansODE
