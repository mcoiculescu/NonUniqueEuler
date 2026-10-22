import NonUniqueEuler.Defs.Sec4.RingSetting
import NonUniqueEuler.I.Sec4.EvansBasic
import NonUniqueEuler.H.Sec4.ClosedForm.Sign
import NonUniqueEuler.H.Sec4.ClosedForm.Integrals
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Proof: `lem:closed-form` (sign of `ϖ'` and the closed-form bound on `Z_ℓ`)

Proof of the interface `NonUniqueEuler/I/Sec4/ClosedForm.lean` (same declarations, statements
copied verbatim). Manuscript `04_ring.tex:771-827`.

* (1) `prof_deriv_sign`: `ϖ' = χ'AB + χAB(2/d)(Ā - B̄)` and the monotonicity of `χ`
  (`H/Sec4/ClosedForm/Sign.lean`). `ringRefSetting_edgeSplit`: `r ω̄_c'(r) = ϖ'(log r)`
  (`ringRefSetting_fxi`, `I/Sec4/EvansBasic.lean`) and `ϖ'(a₀/2) = 0`, so
  `{ω̄_c' > 0} ⊆ (0, e^{a₀/2})` and `{ω̄_c' < 0} ⊆ (e^{a₀/2}, ∞)`.
* (2) The substitution `r = e^ξ` (`integral_image_eq_integral_abs_deriv_smul`) and the
  factorization of the double integral (no integrability needed: the inner integral is a
  constant multiple of a fixed integral). The bounds: the pointwise bounds `bound_A`, `bound_B`
  (`Sign.lean`), `∫χ' = 1` and the `sech²` integral (`Integrals.lean`, `SechIntegral.lean`).

**Deviation.** The `sech²` identity is proved with the substitution `v = H(x)` and Mathlib's Beta
integral on `(0, 1)` instead of `t = e^{2x}` and the Beta integral on `(0, ∞)`
(`SechIntegral.lean`). The order facts of the data are checked by `norm_num` (in particular the
strict inequalities `ξa < a₀/2 < ξb`, which give `ϖ'(a₀/2) = 0`).
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler

open RingData

namespace ClosedFormAux

variable {χ : ℝ → ℝ}

/-- `e^ξ ω̄_c'(e^ξ) = ϖ'(ξ)`. -/
theorem exp_mul_dom (hχ : IsAdmissibleCutoff χ) (ξ : ℝ) :
    Real.exp ξ * (ringRefSetting χ).dom (Real.exp ξ) = deriv (prof χ) ξ :=
  ringRefSetting_fxi hχ ξ

/-- `r ω̄_c'(r) = ϖ'(log r)` for `r > 0`. -/
theorem mul_dom_eq (hχ : IsAdmissibleCutoff χ) {r : ℝ} (hr : 0 < r) :
    r * (ringRefSetting χ).dom r = deriv (prof χ) (Real.log r) := by
  have h := exp_mul_dom hχ (Real.log r)
  rwa [Real.exp_log hr] at h

theorem Upos_eq (hχ : IsAdmissibleCutoff χ) :
    {r : ℝ | 0 < r ∧ 0 < (ringRefSetting χ).dom r} =
      Real.exp '' {ξ : ℝ | 0 < deriv (prof χ) ξ} := by
  ext r
  constructor
  · rintro ⟨hr, h⟩
    refine ⟨Real.log r, ?_, Real.exp_log hr⟩
    show 0 < deriv (prof χ) (Real.log r)
    rw [← mul_dom_eq hχ hr]
    exact mul_pos hr h
  · rintro ⟨ξ, hξ, rfl⟩
    have hξ' : 0 < deriv (prof χ) ξ := hξ
    refine ⟨Real.exp_pos ξ, ?_⟩
    rw [← exp_mul_dom hχ ξ] at hξ'
    exact pos_of_mul_pos_right hξ' (Real.exp_pos ξ).le

theorem Uneg_eq (hχ : IsAdmissibleCutoff χ) :
    {ρ : ℝ | 0 < ρ ∧ (ringRefSetting χ).dom ρ < 0} =
      Real.exp '' {ξ : ℝ | deriv (prof χ) ξ < 0} := by
  ext r
  constructor
  · rintro ⟨hr, h⟩
    refine ⟨Real.log r, ?_, Real.exp_log hr⟩
    show deriv (prof χ) (Real.log r) < 0
    rw [← mul_dom_eq hχ hr]
    exact mul_neg_of_pos_of_neg hr h
  · rintro ⟨ξ, hξ, rfl⟩
    have hξ' : deriv (prof χ) ξ < 0 := hξ
    refine ⟨Real.exp_pos ξ, ?_⟩
    rw [← exp_mul_dom hχ ξ] at hξ'
    exact lt_of_not_ge fun h => absurd (mul_nonneg (Real.exp_pos ξ).le h) (not_le.2 hξ')

theorem measurableSet_pos (hχ : IsAdmissibleCutoff χ) :
    MeasurableSet {ξ : ℝ | 0 < deriv (prof χ) ξ} :=
  (isOpen_lt continuous_const (continuous_deriv_prof hχ)).measurableSet

theorem measurableSet_neg (hχ : IsAdmissibleCutoff χ) :
    MeasurableSet {ξ : ℝ | deriv (prof χ) ξ < 0} :=
  (isOpen_lt (continuous_deriv_prof hχ) continuous_const).measurableSet

/-- The substitution `r = e^ξ`. -/
theorem integral_exp_image {s : Set ℝ} (hs : MeasurableSet s) (g : ℝ → ℝ) :
    ∫ r in Real.exp '' s, g r = ∫ ξ in s, Real.exp ξ * g (Real.exp ξ) := by
  rw [integral_image_eq_integral_abs_deriv_smul hs
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn]
  congr 1
  funext ξ
  rw [smul_eq_mul, abs_of_pos (Real.exp_pos ξ)]

theorem exp_pow_two_mul (ℓ : ℕ) (ξ : ℝ) :
    Real.exp ξ ^ (2 * ℓ) = Real.exp (2 * ℓ * ξ) := by
  rw [← Real.exp_nat_mul]
  push_cast
  ring_nf

/-- `∫_{𝒰₊} r^{2ℓ} |ω̄_c'(r)| dr = ∫_{\{ϖ'>0\}} e^{2ℓξ} |ϖ'(ξ)| dξ`. -/
theorem integral_Upos (hχ : IsAdmissibleCutoff χ) (ℓ : ℕ) :
    ∫ r in {r : ℝ | 0 < r ∧ 0 < (ringRefSetting χ).dom r},
        r ^ (2 * ℓ) * |(ringRefSetting χ).dom r| =
      ∫ ξ in {ξ : ℝ | 0 < deriv (prof χ) ξ}, Real.exp (2 * ℓ * ξ) * |deriv (prof χ) ξ| := by
  rw [Upos_eq hχ, integral_exp_image (measurableSet_pos hχ)]
  congr 1
  funext ξ
  rw [← exp_mul_dom hχ ξ, abs_mul, abs_of_pos (Real.exp_pos ξ), exp_pow_two_mul]
  ring

/-- `∫_{𝒰₋} ρ^{-2ℓ} |ω̄_c'(ρ)| dρ = ∫_{\{ϖ'<0\}} e^{-2ℓξ} |ϖ'(ξ)| dξ`. -/
theorem integral_Uneg (hχ : IsAdmissibleCutoff χ) (ℓ : ℕ) :
    ∫ ρ in {ρ : ℝ | 0 < ρ ∧ (ringRefSetting χ).dom ρ < 0},
        (ρ ^ (2 * ℓ))⁻¹ * |(ringRefSetting χ).dom ρ| =
      ∫ ξ in {ξ : ℝ | deriv (prof χ) ξ < 0}, Real.exp (-(2 * ℓ * ξ)) * |deriv (prof χ) ξ| := by
  rw [Uneg_eq hχ, integral_exp_image (measurableSet_neg hχ)]
  congr 1
  funext ξ
  rw [← exp_mul_dom hχ ξ, abs_mul, abs_of_pos (Real.exp_pos ξ), exp_pow_two_mul,
    Real.exp_neg]
  ring

/-- `Z_ℓ = (∫_{\{ϖ'>0\}} e^{2ℓξ} |ϖ'|) (∫_{\{ϖ'<0\}} e^{-2ℓξ} |ϖ'|)`. -/
theorem Zedge_eq (hχ : IsAdmissibleCutoff χ) (ℓ : ℕ) :
    (ringRefSetting χ).Zedge ℓ =
      (∫ ξ in {ξ : ℝ | 0 < deriv (prof χ) ξ}, Real.exp (2 * ℓ * ξ) * |deriv (prof χ) ξ|) *
        ∫ ξ in {ξ : ℝ | deriv (prof χ) ξ < 0}, Real.exp (-(2 * ℓ * ξ)) * |deriv (prof χ) ξ| := by
  rw [← integral_Upos hχ, ← integral_Uneg hχ, ← integral_mul_const]
  simp only [SectorSetting.Zedge]
  congr 1
  funext r
  rw [← integral_const_mul]
  congr 1
  funext ρ
  rw [div_pow]
  ring

theorem ZedgeA_eq (hχ : IsAdmissibleCutoff χ) (ℓ : ℕ) :
    ZedgeA χ ℓ = Real.exp (-(2 * ℓ * ξc)) *
      ∫ ξ in {ξ : ℝ | 0 < deriv (prof χ) ξ}, Real.exp (2 * ℓ * ξ) * |deriv (prof χ) ξ| := by
  rw [ZedgeA, ← integral_const_mul]
  refine setIntegral_congr_fun (measurableSet_pos hχ) (fun ξ hξ => ?_)
  have hξ' : 0 < deriv (prof χ) ξ := hξ
  rw [abs_of_pos hξ', ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem ZedgeB_eq (ℓ : ℕ) :
    ZedgeB χ ℓ = Real.exp (2 * ℓ * ξc) *
      ∫ ξ in {ξ : ℝ | deriv (prof χ) ξ < 0}, Real.exp (-(2 * ℓ * ξ)) * |deriv (prof χ) ξ| := by
  rw [ZedgeB, ← integral_const_mul]
  congr 1
  funext ξ
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- `Z^a_ℓ ≤ e^{ℓa₀}Θ_ℓ + H((ξa-a₀)/d)`. -/
theorem ZedgeA_le (hχ : IsAdmissibleCutoff χ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hd : (ℓ : ℝ) * d < 1) :
    ZedgeA χ ℓ ≤ Real.exp (ℓ * a₀) * Θ ℓ + H ((ξa - a₀) / d) := by
  set s := {ξ : ℝ | 0 < deriv (prof χ) ξ} with hs_def
  have hs : MeasurableSet s := measurableSet_pos hχ
  set εa := H ((ξa - a₀) / d)
  have hεa : 0 ≤ εa := (AppA.H_pos _).le
  have hsub : s ⊆ Icc (ξL - 1) ξc := by
    intro ξ hξ
    have h1 := lt_c_of_deriv_prof_pos hχ hξ
    have h2 := mem_Icc_of_deriv_prof_ne_zero hχ (ne_of_gt hξ)
    exact ⟨by linarith [h2.1], h1.le⟩
  have hχi : IntegrableOn (deriv χ) (Icc (ξL - 1) ξc) :=
    (continuous_deriv_chi hχ).continuousOn.integrableOn_Icc
  have hkA := integrable_kA hℓ hd
  have hgi : IntegrableOn (fun ξ => εa * deriv χ ξ + kA ℓ ξ) s :=
    ((hχi.mono_set hsub).const_mul εa).add hkA.integrableOn
  have step1 : ZedgeA χ ℓ ≤ ∫ ξ in s, (εa * deriv χ ξ + kA ℓ ξ) := by
    rw [ZedgeA]
    refine integral_mono_of_nonneg ?_ hgi ?_
    · refine (ae_restrict_iff' hs).2 (Filter.Eventually.of_forall fun ξ hξ => ?_)
      exact (mul_pos (Real.exp_pos _) hξ).le
    · refine (ae_restrict_iff' hs).2 (Filter.Eventually.of_forall fun ξ hξ => ?_)
      exact bound_A hχ ℓ (lt_c_of_deriv_prof_pos hχ hξ).le
  have step2 : ∫ ξ in s, (εa * deriv χ ξ + kA ℓ ξ) =
      εa * (∫ ξ in s, deriv χ ξ) + ∫ ξ in s, kA ℓ ξ := by
    rw [integral_add ((hχi.mono_set hsub).const_mul εa) hkA.integrableOn, integral_const_mul]
  have step3 : ∫ ξ in s, deriv χ ξ ≤ 1 := by
    rw [← integral_deriv_chi_left hχ]
    refine setIntegral_mono_set hχi ?_ hsub.eventuallyLE
    refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun ξ hξ => ?_)
    exact deriv_chi_nonneg hχ (hξ.2.trans_lt ξc_lt_ξb)
  have step4 : ∫ ξ in s, kA ℓ ξ ≤ Real.exp (ℓ * a₀) * Θ ℓ := by
    rw [← integral_kA hℓ hd]
    exact setIntegral_le_integral hkA (Filter.Eventually.of_forall (kA_nonneg ℓ))
  have step5 : εa * (∫ ξ in s, deriv χ ξ) ≤ εa := by
    calc εa * (∫ ξ in s, deriv χ ξ) ≤ εa * 1 := mul_le_mul_of_nonneg_left step3 hεa
      _ = εa := mul_one _
  linarith

/-- `Z^b_ℓ ≤ e^{ℓa₀}Θ_ℓ + H(-ξb/d)`. -/
theorem ZedgeB_le (hχ : IsAdmissibleCutoff χ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hd : (ℓ : ℝ) * d < 1) :
    ZedgeB χ ℓ ≤ Real.exp (ℓ * a₀) * Θ ℓ + H (-ξb / d) := by
  set s := {ξ : ℝ | deriv (prof χ) ξ < 0} with hs_def
  have hs : MeasurableSet s := measurableSet_neg hχ
  set εb := H (-ξb / d)
  have hεb : 0 ≤ εb := (AppA.H_pos _).le
  have hsub : s ⊆ Icc ξc (ξR + 1) := by
    intro ξ hξ
    have h1 := c_lt_of_deriv_prof_neg hχ hξ
    have h2 := mem_Icc_of_deriv_prof_ne_zero hχ (ne_of_lt hξ)
    exact ⟨h1.le, by linarith [h2.2]⟩
  have hχi : IntegrableOn (fun ξ => -deriv χ ξ) (Icc ξc (ξR + 1)) :=
    (continuous_deriv_chi hχ).neg.continuousOn.integrableOn_Icc
  have hkB := integrable_kB hℓ hd
  have hgi : IntegrableOn (fun ξ => εb * (-deriv χ ξ) + kB ℓ ξ) s :=
    ((hχi.mono_set hsub).const_mul εb).add hkB.integrableOn
  have step1 : ZedgeB χ ℓ ≤ ∫ ξ in s, (εb * (-deriv χ ξ) + kB ℓ ξ) := by
    rw [ZedgeB]
    refine integral_mono_of_nonneg ?_ hgi ?_
    · exact Filter.Eventually.of_forall fun ξ => by positivity
    · refine (ae_restrict_iff' hs).2 (Filter.Eventually.of_forall fun ξ hξ => ?_)
      have hξ' : deriv (prof χ) ξ < 0 := hξ
      beta_reduce
      rw [abs_of_neg hξ']
      exact bound_B hχ ℓ (c_lt_of_deriv_prof_neg hχ hξ').le
  have step2 : ∫ ξ in s, (εb * (-deriv χ ξ) + kB ℓ ξ) =
      εb * (∫ ξ in s, -deriv χ ξ) + ∫ ξ in s, kB ℓ ξ := by
    rw [integral_add ((hχi.mono_set hsub).const_mul εb) hkB.integrableOn, integral_const_mul]
  have step3 : ∫ ξ in s, -deriv χ ξ ≤ 1 := by
    rw [← integral_deriv_chi_right hχ]
    refine setIntegral_mono_set hχi ?_ hsub.eventuallyLE
    refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun ξ hξ => ?_)
    exact neg_nonneg.2 (deriv_chi_nonpos hχ (ξa_lt_ξc.trans_le hξ.1))
  have step4 : ∫ ξ in s, kB ℓ ξ ≤ Real.exp (ℓ * a₀) * Θ ℓ := by
    rw [← integral_kB hℓ hd]
    exact setIntegral_le_integral hkB (Filter.Eventually.of_forall (kB_nonneg ℓ))
  have step5 : εb * (∫ ξ in s, -deriv χ ξ) ≤ εb := by
    calc εb * (∫ ξ in s, -deriv χ ξ) ≤ εb * 1 := mul_le_mul_of_nonneg_left step3 hεb
      _ = εb := mul_one _
  linarith

end ClosedFormAux

open ClosedFormAux

/-- `lem:closed-form`(1): `ϖ' ≥ 0` on `(-∞, a₀/2)` and `ϖ' ≤ 0` on `(a₀/2, ∞)`. -/
theorem prof_deriv_sign {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) :
    (∀ ξ : ℝ, ξ < a₀ / 2 → 0 ≤ deriv (prof χ) ξ) ∧
      (∀ ξ : ℝ, a₀ / 2 < ξ → deriv (prof χ) ξ ≤ 0) :=
  ⟨fun _ h => deriv_prof_nonneg hχ h, fun _ h => deriv_prof_nonpos hχ h⟩

/-- `lem:closed-form`(1): `ω̄_c` satisfies the hypothesis of `lem:edge`. -/
theorem ringRefSetting_edgeSplit {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) :
    (ringRefSetting χ).EdgeSplit := by
  intro r ρ hr hρ h1 h2
  have e1 : 0 < deriv (prof χ) (Real.log r) := by
    rw [← mul_dom_eq hχ hr]
    exact mul_pos hr h1
  have e2 : deriv (prof χ) (Real.log ρ) < 0 := by
    rw [← mul_dom_eq hχ hρ]
    exact mul_neg_of_pos_of_neg hρ h2
  have := (lt_c_of_deriv_prof_pos hχ e1).trans (c_lt_of_deriv_prof_neg hχ e2)
  exact (Real.log_lt_log_iff hr hρ).1 this

/-- `lem:closed-form`(2): for every integer `ℓ ≥ 1` with `ℓd < 1`, `Z_ℓ = Z^a_ℓ Z^b_ℓ` and
`Z^a_ℓ, Z^b_ℓ ≤ e^{ℓa₀}Θ_ℓ + ε_*`, `Θ_ℓ = πℓd/sin(πℓd)`,
`ε_* = max{H((ξa-a₀)/d), H(-ξb/d)}`. -/
theorem closedForm_Zedge {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hd : (ℓ : ℝ) * d < 1) :
    (ringRefSetting χ).Zedge ℓ = ZedgeA χ ℓ * ZedgeB χ ℓ ∧
      ZedgeA χ ℓ ≤ Real.exp (ℓ * a₀) * Θ ℓ + εstar ∧
      ZedgeB χ ℓ ≤ Real.exp (ℓ * a₀) * Θ ℓ + εstar := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Zedge_eq hχ, ZedgeA_eq hχ, ZedgeB_eq]
    have : Real.exp (-(2 * ℓ * ξc)) * Real.exp (2 * ℓ * ξc) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc _ = (Real.exp (-(2 * ℓ * ξc)) * Real.exp (2 * ℓ * ξc)) *
          ((∫ ξ in {ξ : ℝ | 0 < deriv (prof χ) ξ},
              Real.exp (2 * ℓ * ξ) * |deriv (prof χ) ξ|) *
            ∫ ξ in {ξ : ℝ | deriv (prof χ) ξ < 0},
              Real.exp (-(2 * ℓ * ξ)) * |deriv (prof χ) ξ|) := by
          rw [this, one_mul]
      _ = _ := by ring
  · exact (ZedgeA_le hχ hℓ hd).trans (by gcongr; exact le_max_left _ _)
  · exact (ZedgeB_le hχ hℓ hd).trans (by gcongr; exact le_max_right _ _)

end NonUniqueEuler
