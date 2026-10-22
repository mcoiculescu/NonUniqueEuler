import NonUniqueEuler.Defs.Verify.Profile
import NonUniqueEuler.I.Verify.ProfileBasic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Proof: the circulation term `g`, `Ω_G`, the denominator `λ + iℓΩ_G` and `δ`

Proof of `NonUniqueEuler/I/Verify/ProfileOmega.lean`. Manuscript: proof of Proposition A.3,
steps (i) and (iii) (`A_verification.tex:364-372`, `:401-404`), proof of Lemma A.1(2)
(`:174-180`) and of Lemma A.2 (`:207-218`).

We follow the manuscript.
* The integrand `t ↦ ϖ(t) e^{2t}` is continuous, satisfies `0 ≤ ϖ e^{2·} ≤ e^{2·}` and
  vanishes on `(-∞, ξL)`. Hence it is integrable on every `Iic ξ` (domination by `e^{2t}`,
  `integrableOn_exp_mul_Iic`), `g = 0` on `(-∞, ξL]`, and `g(ξ) = ∫_{ξL}^{ξ} ϖ e^{2·}` for every
  `ξ` (`intervalIntegral.integral_Iic_sub_Iic`). The FTC
  (`Continuous.integral_hasStrictDerivAt`) gives `g' = ϖ e^{2·}`.
* `g ≤ e^{2ξ}/2` and the `g(ξa)` bound: comparison with explicit exponential integrals
  (`integral_exp_mul_Iic`), using `ϖ ≤ AB ≤ A = H((·-a₀)/d) ≤ e^{2(·-a₀)/d}`.
* The denominator: `Re(λ + iℓΩ) = Re λ`.

Helper lemmas are in the namespace `NonUniqueEuler.AppA.ProfileOmegaProof`.
-/

noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace NonUniqueEuler

namespace AppA

open RingData

namespace ProfileOmegaProof

theorem d_pos : 0 < d := by
  unfold d; positivity

theorem continuous_integrand {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) :
    Continuous (fun t => prof χ t * Real.exp (2 * t)) :=
  (contDiff_prof hχ).continuous.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))

theorem contDiff_integrand {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) :
    ContDiff ℝ ∞ (fun t => prof χ t * Real.exp (2 * t)) :=
  (contDiff_prof hχ).mul (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))

theorem integrand_nonneg {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (t : ℝ) :
    0 ≤ prof χ t * Real.exp (2 * t) :=
  mul_nonneg (prof_nonneg hχ t) (Real.exp_pos _).le

theorem prof_le_one {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (t : ℝ) : prof χ t ≤ 1 :=
  (prof_le_profW hχ t).trans (profW_le_one t)

theorem integrand_le_exp {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (t : ℝ) :
    prof χ t * Real.exp (2 * t) ≤ Real.exp (2 * t) := by
  have h := prof_le_one hχ t
  have he := Real.exp_pos (2 * t)
  nlinarith

theorem integrand_eq_zero_of_lt {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {t : ℝ} (ht : t < ξL) :
    prof χ t * Real.exp (2 * t) = 0 := by
  have : t ∉ Icc ξL ξR := fun h => absurd h.1 (not_le.2 ht)
  rw [prof_eq_zero_of_not_mem hχ this, zero_mul]

/-- `g(ξ) = ∫_{ξL}^{ξ} ϖ e^{2·}` for every `ξ` (also for `ξ < ξL`, where both sides vanish). -/
theorem gInt_eq_intervalIntegral' {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (ξ : ℝ) :
    gInt χ ξ = ∫ t in ξL..ξ, prof χ t * Real.exp (2 * t) := by
  have hint : ∀ c : ℝ, IntegrableOn (fun t => prof χ t * Real.exp (2 * t)) (Iic c) := by
    intro c
    refine Integrable.mono' (integrableOn_exp_mul_Iic two_pos c)
      (continuous_integrand hχ).aestronglyMeasurable (ae_of_all _ fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (integrand_nonneg hχ t)]
    exact integrand_le_exp hχ t
  have h0 : ∫ t in Iic ξL, prof χ t * Real.exp (2 * t) = 0 := by
    rw [integral_Iic_eq_integral_Iio]
    exact setIntegral_eq_zero_of_forall_eq_zero fun t ht => integrand_eq_zero_of_lt hχ ht
  rw [← intervalIntegral.integral_Iic_sub_Iic (hint ξL) (hint ξ), h0, sub_zero]
  rfl

theorem gInt_eq_fun {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) :
    gInt χ = fun ξ => ∫ t in ξL..ξ, prof χ t * Real.exp (2 * t) :=
  funext (gInt_eq_intervalIntegral' hχ)

/-- `A(t) ≤ e^{2(t - a₀)/d}` and `ϖ(t) ≤ A(t)`. -/
theorem prof_le_exp_profA {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (t : ℝ) :
    prof χ t ≤ Real.exp (2 * ((t - a₀) / d)) := by
  have h1 := prof_le_profW hχ t
  have hA : 0 < profA t := H_pos _
  have hB : profB t ≤ 1 := H_le_one _
  have hAe : profA t ≤ Real.exp (2 * ((t - a₀) / d)) := H_le_exp _
  have hW : profW t ≤ profA t := by
    unfold profW
    nlinarith
  linarith

end ProfileOmegaProof

open ProfileOmegaProof

/-! ### `g` -/

theorem integrableOn_prof_exp {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (ξ : ℝ) :
    IntegrableOn (fun t => prof χ t * Real.exp (2 * t)) (Iic ξ) := by
  refine Integrable.mono' (integrableOn_exp_mul_Iic two_pos ξ)
    (continuous_integrand hχ).aestronglyMeasurable (ae_of_all _ fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (integrand_nonneg hχ t)]
  exact integrand_le_exp hχ t

/-- `g' = ϖ e^{2ξ}`. -/
theorem hasDerivAt_gInt {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (ξ : ℝ) :
    HasDerivAt (gInt χ) (prof χ ξ * Real.exp (2 * ξ)) ξ := by
  rw [gInt_eq_fun hχ]
  exact ((continuous_integrand hχ).integral_hasStrictDerivAt ξL ξ).hasDerivAt

theorem contDiff_gInt {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) : ContDiff ℝ ∞ (gInt χ) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun ξ => (hasDerivAt_gInt hχ ξ).differentiableAt, ?_⟩
  have : deriv (gInt χ) = fun t => prof χ t * Real.exp (2 * t) :=
    funext fun ξ => (hasDerivAt_gInt hχ ξ).deriv
  rw [this]
  exact contDiff_integrand hχ

theorem monotone_gInt {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) : Monotone (gInt χ) := by
  intro a b hab
  have h := intervalIntegral.integral_Iic_sub_Iic (integrableOn_prof_exp hχ a)
    (integrableOn_prof_exp hχ b)
  have hnn : 0 ≤ ∫ t in a..b, prof χ t * Real.exp (2 * t) :=
    intervalIntegral.integral_nonneg hab fun t _ => integrand_nonneg hχ t
  change (∫ t in Iic a, prof χ t * Real.exp (2 * t)) ≤ ∫ t in Iic b, prof χ t * Real.exp (2 * t)
  linarith

theorem gInt_nonneg {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (ξ : ℝ) : 0 ≤ gInt χ ξ :=
  setIntegral_nonneg measurableSet_Iic fun t _ => integrand_nonneg hχ t

theorem gInt_le {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (ξ : ℝ) :
    gInt χ ξ ≤ Real.exp (2 * ξ) / 2 := by
  rw [← integral_exp_mul_Iic two_pos ξ]
  exact setIntegral_mono_on (integrableOn_prof_exp hχ ξ) (integrableOn_exp_mul_Iic two_pos ξ)
    measurableSet_Iic fun t _ => integrand_le_exp hχ t

theorem gInt_eq_zero_of_le {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {ξ : ℝ} (hξ : ξ ≤ ξL) :
    gInt χ ξ = 0 := by
  change (∫ t in Iic ξ, prof χ t * Real.exp (2 * t)) = 0
  rw [integral_Iic_eq_integral_Iio]
  exact setIntegral_eq_zero_of_forall_eq_zero fun t ht =>
    integrand_eq_zero_of_lt hχ (lt_of_lt_of_le ht hξ)

theorem gInt_eq_intervalIntegral {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {ξ : ℝ}
    (hξ : ξL ≤ ξ) : gInt χ ξ = ∫ t in ξL..ξ, prof χ t * Real.exp (2 * t) := by
  exact (fun _ => gInt_eq_intervalIntegral' hχ ξ) hξ

/-- The bound on `g(ξa)` used for `γ₀ = hull(0, e^{2x_a + 2ξa}/(2/d + 2))` in step (i). -/
theorem gInt_ξa_bound {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) :
    gInt χ ξa ≤ Real.exp (2 * xa + 2 * ξa) / (2 / d + 2) := by
  have hd := d_pos
  have hc : 0 < 2 / d + 2 := by positivity
  set K : ℝ := Real.exp (-(2 * a₀ / d)) with hK
  have hint : IntegrableOn (fun t => Real.exp ((2 / d + 2) * t) * K) (Iic ξa) :=
    (integrableOn_exp_mul_Iic hc ξa).mul_const K
  have hval : ∫ t in Iic ξa, Real.exp ((2 / d + 2) * t) * K =
      Real.exp (2 * xa + 2 * ξa) / (2 / d + 2) := by
    rw [integral_mul_const, integral_exp_mul_Iic hc ξa, hK, div_mul_eq_mul_div,
      ← Real.exp_add]
    congr 2
    unfold xa
    ring
  rw [← hval]
  refine setIntegral_mono_on (integrableOn_prof_exp hχ ξa) hint measurableSet_Iic
    fun t _ => ?_
  have h1 := prof_le_exp_profA hχ t
  have he : 0 < Real.exp (2 * t) := Real.exp_pos _
  have hprod : Real.exp (2 * ((t - a₀) / d)) * Real.exp (2 * t) =
      Real.exp ((2 / d + 2) * t) * K := by
    rw [hK, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc prof χ t * Real.exp (2 * t) ≤ Real.exp (2 * ((t - a₀) / d)) * Real.exp (2 * t) :=
        mul_le_mul_of_nonneg_right h1 he.le
    _ = Real.exp ((2 / d + 2) * t) * K := hprod

/-! ### `Ω_G` -/

theorem contDiff_OmegaG {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (G : ℝ) :
    ContDiff ℝ ∞ (OmegaG χ G) := by
  have : OmegaG χ G = fun ξ => Real.exp (-2 * ξ) * (G + gInt χ ξ) :=
    funext (OmegaG_eq χ G)
  rw [this]
  exact (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul
    (contDiff_const.add (contDiff_gInt hχ))

theorem OmegaG_nonneg {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {G : ℝ} (hG : 0 ≤ G)
    (ξ : ℝ) : 0 ≤ OmegaG χ G ξ := by
  rw [OmegaG_eq]
  exact mul_nonneg (Real.exp_pos _).le (add_nonneg hG (gInt_nonneg hχ ξ))

theorem OmegaG_le {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (G ξ : ℝ) :
    OmegaG χ G ξ ≤ 1 / 2 + G * Real.exp (-2 * ξ) := by
  rw [OmegaG_eq]
  have he : 0 < Real.exp (-2 * ξ) := Real.exp_pos _
  have hprod : Real.exp (-2 * ξ) * Real.exp (2 * ξ) = 1 := by
    rw [← Real.exp_add]; simp
  have h := mul_le_mul_of_nonneg_left (add_le_add (le_refl G) (gInt_le hχ ξ)) he.le
  calc Real.exp (-2 * ξ) * (G + gInt χ ξ)
      ≤ Real.exp (-2 * ξ) * (G + Real.exp (2 * ξ) / 2) := h
    _ = 1 / 2 + G * Real.exp (-2 * ξ) := by
        rw [mul_add, mul_div_assoc', hprod]; ring

theorem OmegaG_le_OmegaMax {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {G : ℝ}
    (hG : G ∈ Icc (0 : ℝ) d) {ξ : ℝ} (hξ : ξL ≤ ξ) : OmegaG χ G ξ ≤ OmegaMax := by
  have h1 := OmegaG_le hχ G ξ
  have hexp : Real.exp (-2 * ξ) ≤ Real.exp (-2 * ξL) := Real.exp_le_exp.2 (by linarith)
  have h2 : G * Real.exp (-2 * ξ) ≤ d * Real.exp (-2 * ξL) :=
    mul_le_mul hG.2 hexp (Real.exp_pos _).le d_pos.le
  unfold OmegaMax
  linarith

/-! ### The denominator `λ + iℓΩ_G` and `δ = iℓϖ'/(λ + iℓΩ_G)` -/

theorem re_add_I_mul_ofReal (z : ℂ) (ℓ : ℕ) (r : ℝ) :
    (z + Complex.I * (ℓ : ℂ) * (r : ℂ)).re = z.re := by
  simp [Complex.add_re, Complex.mul_re]

theorem re_le_norm_add_I_mul_ofReal (z : ℂ) (ℓ : ℕ) (r : ℝ) :
    z.re ≤ ‖z + Complex.I * (ℓ : ℂ) * (r : ℂ)‖ := by
  rw [← re_add_I_mul_ofReal z ℓ r]
  exact Complex.re_le_norm _

theorem add_I_mul_ofReal_ne_zero {z : ℂ} (hz : 0 < z.re) (ℓ : ℕ) (r : ℝ) :
    z + Complex.I * (ℓ : ℂ) * (r : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [re_add_I_mul_ofReal, Complex.zero_re] at this
  linarith

theorem contDiff_evansDenom {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (z : ℂ) (ℓ : ℕ)
    (G : ℝ) :
    ContDiff ℝ ∞ (fun ξ => z + Complex.I * (ℓ : ℂ) * ((OmegaG χ G ξ : ℝ) : ℂ)) :=
  contDiff_const.add (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_OmegaG hχ G)))

theorem contDiff_evansDelta {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (ℓ : ℕ) {z : ℂ}
    (hz : 0 < z.re) (G : ℝ) : ContDiff ℝ ∞ (evansDelta χ ℓ z G) := by
  have hderiv : ContDiff ℝ ∞ (deriv (prof χ)) :=
    (contDiff_infty_iff_deriv.1 (contDiff_prof hχ)).2
  have hnum : ContDiff ℝ ∞ (fun ξ => Complex.I * (ℓ : ℂ) * ((deriv (prof χ) ξ : ℝ) : ℂ)) :=
    contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hderiv)
  have hinv : ContDiff ℝ ∞
      (fun ξ => (z + Complex.I * (ℓ : ℂ) * ((OmegaG χ G ξ : ℝ) : ℂ))⁻¹) :=
    (contDiff_evansDenom hχ z ℓ G).fun_inv fun ξ => add_I_mul_ofReal_ne_zero hz ℓ _
  have : evansDelta χ ℓ z G = fun ξ => Complex.I * (ℓ : ℂ) * ((deriv (prof χ) ξ : ℝ) : ℂ) *
      (z + Complex.I * (ℓ : ℂ) * ((OmegaG χ G ξ : ℝ) : ℂ))⁻¹ := by
    funext ξ
    simp only [evansDelta, div_eq_mul_inv]
  rw [this]
  exact hnum.mul hinv

/-- `|δ|/ℓ = |ϖ'|/|λ + iℓΩ_G|` (this is `b` of the proof of Lemma A.1(2)). -/
theorem norm_evansDelta_div {χ : ℝ → ℝ} {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (z : ℂ) (G ξ : ℝ) :
    ‖evansDelta χ ℓ z G ξ‖ / ℓ =
      |deriv (prof χ) ξ| / ‖z + Complex.I * (ℓ : ℂ) * ((OmegaG χ G ξ : ℝ) : ℂ)‖ := by
  have hℓ0 : (ℓ : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    linarith
  unfold evansDelta
  rw [norm_div, norm_mul, norm_mul, Complex.norm_I, Complex.norm_natCast, Complex.norm_real,
    Real.norm_eq_abs, one_mul, div_div, mul_comm _ (ℓ : ℝ)]
  exact mul_div_mul_left _ _ hℓ0

/-- `|δ|/ℓ ≤ |ϖ'|/Re λ`. -/
theorem norm_evansDelta_div_le {χ : ℝ → ℝ} (ℓ : ℕ) {z : ℂ} (hz : 0 < z.re) (G ξ : ℝ) :
    ‖evansDelta χ ℓ z G ξ‖ / ℓ ≤ |deriv (prof χ) ξ| / z.re := by
  rcases Nat.eq_zero_or_pos ℓ with h0 | hpos
  · subst h0
    simp only [Nat.cast_zero, div_zero]
    exact div_nonneg (abs_nonneg _) hz.le
  · rw [norm_evansDelta_div hpos]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hz (re_le_norm_add_I_mul_ofReal z ℓ _)

theorem evansDelta_eq_zero_of_not_mem {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (ℓ : ℕ)
    (z : ℂ) (G : ℝ) {ξ : ℝ} (hξ : ξ ∉ Icc ξL ξR) : evansDelta χ ℓ z G ξ = 0 := by
  unfold evansDelta
  rw [deriv_prof_eq_zero_of_not_mem hχ hξ]
  simp

end AppA

end NonUniqueEuler
