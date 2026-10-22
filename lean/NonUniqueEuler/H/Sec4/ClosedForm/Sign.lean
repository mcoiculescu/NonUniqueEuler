import NonUniqueEuler.I.Verify.ProfileBasic
import NonUniqueEuler.Defs.Sec4.Ring
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Helper for `lem:closed-form`: the derivative of `ϖ`, its sign, and the pointwise bounds

Manuscript `04_ring.tex:789-827`. With `A, Ā, B, B̄` of `Defs/Verify/Profile.lean`
(`A(ξ) = H((ξ-a₀)/d)`, `Ā = H((a₀-ξ)/d)`, `B = H(-ξ/d)`, `B̄ = H(ξ/d)`) and `P = AB`:

* `hasDerivAt_prof`: `ϖ' = χ'AB + χAB(2/d)(Ā - B̄)` (from `A' = (2/d)AĀ`, `B' = -(2/d)BB̄`;
  this is `(log P)' = (2/d)[Ā - B̄]`);
* `χ` is nondecreasing on `(-∞, ξ_b]` and nonincreasing on `[ξ_a, ∞)`, so `χ' ≥ 0` on
  `(-∞, ξ_b)` and `χ' ≤ 0` on `(ξ_a, ∞)`;
* `Ā - B̄ > 0` iff `ξ < a₀/2`; hence the sign of `ϖ'` (`lem:closed-form`(1)), and `ϖ'(a₀/2) = 0`;
* the pointwise bounds of the proof of (2): on `ξ ≤ a₀/2`,
  `e^{2ℓ(ξ-ξc)} ϖ' ≤ H((ξa-a₀)/d) χ' + e^{2ℓ(ξ-ξc)} (2/d) AĀ`, and the mirror image.
-/

noncomputable section

open Set Real

namespace NonUniqueEuler

namespace ClosedFormAux

open RingData AppA

/-! ### Order facts of the pinned data (`04_ring.tex:78-86`) -/

theorem d_pos : 0 < d := by norm_num [d]

theorem a₀_neg : a₀ < 0 := by norm_num [a₀]

theorem ξa_lt_ξc : ξa < a₀ / 2 := by norm_num [ξa, a₀]

theorem ξc_lt_ξb : a₀ / 2 < ξb := by norm_num [ξb, a₀]

theorem ξL_lt_ξa : ξL < ξa := by norm_num [ξL, ξa]

theorem ξb_lt_ξR : ξb < ξR := by norm_num [ξb, ξR]

theorem ξL_lt_ξc : ξL < a₀ / 2 := ξL_lt_ξa.trans ξa_lt_ξc

theorem ξc_lt_ξR : a₀ / 2 < ξR := ξc_lt_ξb.trans ξb_lt_ξR

/-! ### Monotonicity of the cutoff -/

variable {χ : ℝ → ℝ}

theorem chi_monotoneOn (hχ : IsAdmissibleCutoff χ) : MonotoneOn χ (Iic ξb) := by
  intro x _ y hy hxy
  rcases le_or_gt y ξa with h | h
  · exact hχ.monotoneOn (show x ∈ Iic ξa from hxy.trans h) (show y ∈ Iic ξa from h) hxy
  · rw [hχ.eq_one y ⟨h.le, hy⟩]
    exact (hχ.mem_Icc x).2

theorem chi_antitoneOn (hχ : IsAdmissibleCutoff χ) : AntitoneOn χ (Ici ξa) := by
  intro x hx y _ hxy
  rcases le_or_gt ξb x with h | h
  · exact hχ.antitoneOn (show x ∈ Ici ξb from h) (show y ∈ Ici ξb from h.trans hxy) hxy
  · rw [hχ.eq_one x ⟨hx, h.le⟩]
    exact (hχ.mem_Icc y).2

theorem deriv_chi_nonneg (hχ : IsAdmissibleCutoff χ) {ξ : ℝ} (h : ξ < ξb) :
    0 ≤ deriv χ ξ := by
  have := ((chi_monotoneOn hχ).mono Iio_subset_Iic_self).derivWithin_nonneg (x := ξ)
  rwa [derivWithin_of_isOpen isOpen_Iio h] at this

theorem deriv_chi_nonpos (hχ : IsAdmissibleCutoff χ) {ξ : ℝ} (h : ξa < ξ) :
    deriv χ ξ ≤ 0 := by
  have := ((chi_antitoneOn hχ).mono Ioi_subset_Ici_self).derivWithin_nonpos (x := ξ)
  rwa [derivWithin_of_isOpen isOpen_Ioi h] at this

theorem deriv_chi_eq_zero (hχ : IsAdmissibleCutoff χ) {ξ : ℝ} (h₁ : ξa < ξ) (h₂ : ξ < ξb) :
    deriv χ ξ = 0 :=
  le_antisymm (deriv_chi_nonpos hχ h₁) (deriv_chi_nonneg hχ h₂)

/-! ### The derivative of `ϖ` -/

/-- `ϖ' = χ'AB + χAB(2/d)(Ā - B̄)`. -/
theorem hasDerivAt_prof (hχ : IsAdmissibleCutoff χ) (ξ : ℝ) :
    HasDerivAt (prof χ) (deriv χ ξ * (profA ξ * profB ξ) +
      χ ξ * (profA ξ * profB ξ) * ((2 / d) * (profAbar ξ - profBbar ξ))) ξ := by
  have hχd : HasDerivAt χ (deriv χ ξ) ξ :=
    ((hχ.contDiff.differentiable (by simp)) ξ).hasDerivAt
  have h : HasDerivAt (fun t => χ t * profA t * profB t)
      ((deriv χ ξ * profA ξ + χ ξ * (2 / d * (profA ξ * profAbar ξ))) * profB ξ +
        χ ξ * profA ξ * (-(2 / d) * (profB ξ * profBbar ξ))) ξ :=
    (hχd.mul (hasDerivAt_profA ξ)).mul (hasDerivAt_profB ξ)
  have hf : prof χ = fun t => χ t * profA t * profB t := rfl
  rw [hf]
  convert h using 1
  ring

theorem deriv_prof_eq (hχ : IsAdmissibleCutoff χ) (ξ : ℝ) :
    deriv (prof χ) ξ = deriv χ ξ * (profA ξ * profB ξ) +
      χ ξ * (profA ξ * profB ξ) * ((2 / d) * (profAbar ξ - profBbar ξ)) :=
  (hasDerivAt_prof hχ ξ).deriv

theorem continuous_deriv_prof (hχ : IsAdmissibleCutoff χ) : Continuous (deriv (prof χ)) :=
  (contDiff_prof hχ).continuous_deriv (by simp)

/-! ### The sign of `Ā - B̄` -/

theorem profAbar_sub_profBbar_pos {ξ : ℝ} (h : ξ < a₀ / 2) : 0 < profAbar ξ - profBbar ξ := by
  have hlt : ξ / d < (a₀ - ξ) / d := div_lt_div_of_pos_right (by linarith) d_pos
  have := strictMono_H hlt
  simp only [profAbar, profBbar]
  linarith

theorem profAbar_sub_profBbar_neg {ξ : ℝ} (h : a₀ / 2 < ξ) : profAbar ξ - profBbar ξ < 0 := by
  have hlt : (a₀ - ξ) / d < ξ / d := div_lt_div_of_pos_right (by linarith) d_pos
  have := strictMono_H hlt
  simp only [profAbar, profBbar]
  linarith

theorem profAbar_sub_profBbar_c : profAbar (a₀ / 2) - profBbar (a₀ / 2) = 0 := by
  simp only [profAbar, profBbar]
  rw [show a₀ - a₀ / 2 = a₀ / 2 by ring, sub_self]

theorem profA_pos (ξ : ℝ) : 0 < profA ξ := H_pos _
theorem profB_pos (ξ : ℝ) : 0 < profB ξ := H_pos _
theorem profAbar_pos (ξ : ℝ) : 0 < profAbar ξ := H_pos _
theorem profBbar_pos (ξ : ℝ) : 0 < profBbar ξ := H_pos _
theorem profA_le_one (ξ : ℝ) : profA ξ ≤ 1 := H_le_one _
theorem profB_le_one (ξ : ℝ) : profB ξ ≤ 1 := H_le_one _
theorem profAbar_le_one (ξ : ℝ) : profAbar ξ ≤ 1 := H_le_one _
theorem profBbar_le_one (ξ : ℝ) : profBbar ξ ≤ 1 := H_le_one _

/-! ### `lem:closed-form`(1): the sign of `ϖ'` -/

theorem deriv_prof_nonneg (hχ : IsAdmissibleCutoff χ) {ξ : ℝ} (h : ξ < a₀ / 2) :
    0 ≤ deriv (prof χ) ξ := by
  rw [deriv_prof_eq hχ]
  have h1 := deriv_chi_nonneg hχ (h.trans ξc_lt_ξb)
  have h2 := (hχ.mem_Icc ξ).1
  have h3 := profAbar_sub_profBbar_pos h
  have hA := profA_pos ξ
  have hB := profB_pos ξ
  have hd := d_pos
  positivity

theorem deriv_prof_nonpos (hχ : IsAdmissibleCutoff χ) {ξ : ℝ} (h : a₀ / 2 < ξ) :
    deriv (prof χ) ξ ≤ 0 := by
  rw [deriv_prof_eq hχ]
  have h1 := deriv_chi_nonpos hχ (ξa_lt_ξc.trans h)
  have h2 := (hχ.mem_Icc ξ).1
  have h3 := profAbar_sub_profBbar_neg h
  have hAB : 0 < profA ξ * profB ξ := mul_pos (profA_pos ξ) (profB_pos ξ)
  have hd : 0 < 2 / d := div_pos two_pos d_pos
  have e1 : deriv χ ξ * (profA ξ * profB ξ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h1 hAB.le
  have e2 : χ ξ * (profA ξ * profB ξ) * ((2 / d) * (profAbar ξ - profBbar ξ)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg h2 hAB.le)
      (mul_nonpos_of_nonneg_of_nonpos hd.le h3.le)
  linarith

theorem deriv_prof_c (hχ : IsAdmissibleCutoff χ) : deriv (prof χ) (a₀ / 2) = 0 := by
  rw [deriv_prof_eq hχ, deriv_chi_eq_zero hχ ξa_lt_ξc ξc_lt_ξb, profAbar_sub_profBbar_c]
  ring

theorem lt_c_of_deriv_prof_pos (hχ : IsAdmissibleCutoff χ) {ξ : ℝ}
    (h : 0 < deriv (prof χ) ξ) : ξ < a₀ / 2 := by
  by_contra hc
  rcases (not_lt.1 hc).lt_or_eq with hc | hc
  · exact absurd (deriv_prof_nonpos hχ hc) (not_le.2 h)
  · rw [← hc, deriv_prof_c hχ] at h
    exact lt_irrefl _ h

theorem c_lt_of_deriv_prof_neg (hχ : IsAdmissibleCutoff χ) {ξ : ℝ}
    (h : deriv (prof χ) ξ < 0) : a₀ / 2 < ξ := by
  by_contra hc
  rcases (not_lt.1 hc).lt_or_eq with hc | hc
  · exact absurd (deriv_prof_nonneg hχ hc) (not_le.2 h)
  · rw [hc, deriv_prof_c hχ] at h
    exact lt_irrefl _ h

theorem mem_Icc_of_deriv_prof_ne_zero (hχ : IsAdmissibleCutoff χ) {ξ : ℝ}
    (h : deriv (prof χ) ξ ≠ 0) : ξ ∈ Icc ξL ξR := by
  by_contra hc
  exact h (deriv_prof_eq_zero_of_not_mem hχ hc)

/-! ### The pointwise bounds of `lem:closed-form`(2) -/

/-- On `ξ ≤ a₀/2`: `e^{2ℓ(ξ-ξc)} ϖ' ≤ H((ξa-a₀)/d) χ' + e^{2ℓ(ξ-ξc)} (2/d) AĀ`. -/
theorem bound_A (hχ : IsAdmissibleCutoff χ) (ℓ : ℕ) {ξ : ℝ} (hξ : ξ ≤ a₀ / 2) :
    Real.exp (2 * ℓ * (ξ - ξc)) * deriv (prof χ) ξ ≤
      H ((ξa - a₀) / d) * deriv χ ξ +
        Real.exp (2 * ℓ * (ξ - ξc)) * ((2 / d) * (profA ξ * profAbar ξ)) := by
  set E := Real.exp (2 * ℓ * (ξ - ξc)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := by
    rw [hE, Real.exp_le_one_iff]
    have : ξ - ξc ≤ 0 := by simp only [ξc]; linarith
    have hl : (0 : ℝ) ≤ 2 * ℓ := by positivity
    exact mul_nonpos_of_nonneg_of_nonpos hl this
  set εa := H ((ξa - a₀) / d)
  have hA := profA_pos ξ
  have hA1 := profA_le_one ξ
  have hB := profB_pos ξ
  have hB1 := profB_le_one ξ
  have hAb := profAbar_pos ξ
  have hBb := profBbar_pos ξ
  have hχ0 := (hχ.mem_Icc ξ).1
  have hχ1 := (hχ.mem_Icc ξ).2
  have hd : 0 < 2 / d := div_pos two_pos d_pos
  -- the cutoff term
  have h1 : deriv χ ξ * (E * profA ξ * profB ξ) ≤ εa * deriv χ ξ := by
    rcases le_or_gt ξ ξa with hξa | hξa
    · have hc := deriv_chi_nonneg hχ (hξ.trans_lt ξc_lt_ξb)
      have hAa : profA ξ ≤ εa := strictMono_profA.monotone hξa
      have : E * profA ξ * profB ξ ≤ εa := by
        calc E * profA ξ * profB ξ ≤ 1 * profA ξ * 1 := by gcongr
          _ = profA ξ := by ring
          _ ≤ εa := hAa
      rw [mul_comm εa]
      exact mul_le_mul_of_nonneg_left this hc
    · rw [deriv_chi_eq_zero hχ hξa (hξ.trans_lt ξc_lt_ξb)]
      simp
  -- the profile term
  have h2 : χ ξ * profB ξ * profAbar ξ ≤ profAbar ξ := by
    have : χ ξ * profB ξ ≤ 1 := by
      calc χ ξ * profB ξ ≤ 1 * 1 := by gcongr
        _ = 1 := by ring
    calc χ ξ * profB ξ * profAbar ξ ≤ 1 * profAbar ξ := by gcongr
      _ = profAbar ξ := one_mul _
  have h3 : 0 ≤ χ ξ * profB ξ * profBbar ξ := by positivity
  have hc : 0 ≤ E * (2 / d) * profA ξ := by positivity
  have key : (εa * deriv χ ξ + E * ((2 / d) * (profA ξ * profAbar ξ))) -
      E * deriv (prof χ) ξ =
      (εa * deriv χ ξ - deriv χ ξ * (E * profA ξ * profB ξ)) +
        E * (2 / d) * profA ξ * (profAbar ξ - χ ξ * profB ξ * profAbar ξ) +
        E * (2 / d) * profA ξ * (χ ξ * profB ξ * profBbar ξ) := by
    rw [deriv_prof_eq hχ]
    ring
  have : 0 ≤ (εa * deriv χ ξ + E * ((2 / d) * (profA ξ * profAbar ξ))) -
      E * deriv (prof χ) ξ := by
    rw [key]
    have k1 : 0 ≤ εa * deriv χ ξ - deriv χ ξ * (E * profA ξ * profB ξ) := by linarith
    have k2 : 0 ≤ E * (2 / d) * profA ξ * (profAbar ξ - χ ξ * profB ξ * profAbar ξ) :=
      mul_nonneg hc (by linarith)
    have k3 : 0 ≤ E * (2 / d) * profA ξ * (χ ξ * profB ξ * profBbar ξ) := mul_nonneg hc h3
    linarith
  linarith

/-- On `ξ ≥ a₀/2`: `e^{-2ℓ(ξ-ξc)} (-ϖ') ≤ H(-ξb/d) (-χ') + e^{-2ℓ(ξ-ξc)} (2/d) BB̄`. -/
theorem bound_B (hχ : IsAdmissibleCutoff χ) (ℓ : ℕ) {ξ : ℝ} (hξ : a₀ / 2 ≤ ξ) :
    Real.exp (-(2 * ℓ * (ξ - ξc))) * (-deriv (prof χ) ξ) ≤
      H (-ξb / d) * (-deriv χ ξ) +
        Real.exp (-(2 * ℓ * (ξ - ξc))) * ((2 / d) * (profB ξ * profBbar ξ)) := by
  set E := Real.exp (-(2 * ℓ * (ξ - ξc))) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := by
    rw [hE, Real.exp_le_one_iff, neg_nonpos]
    have : 0 ≤ ξ - ξc := by simp only [ξc]; linarith
    have hl : (0 : ℝ) ≤ 2 * ℓ := by positivity
    exact mul_nonneg hl this
  set εb := H (-ξb / d)
  have hA := profA_pos ξ
  have hA1 := profA_le_one ξ
  have hB := profB_pos ξ
  have hAb := profAbar_pos ξ
  have hBb := profBbar_pos ξ
  have hχ0 := (hχ.mem_Icc ξ).1
  have hχ1 := (hχ.mem_Icc ξ).2
  have hd : 0 < 2 / d := div_pos two_pos d_pos
  -- the cutoff term
  have h1 : -deriv χ ξ * (E * profA ξ * profB ξ) ≤ εb * (-deriv χ ξ) := by
    rcases le_or_gt ξb ξ with hξb | hξb
    · have hc : 0 ≤ -deriv χ ξ :=
        neg_nonneg.2 (deriv_chi_nonpos hχ (ξa_lt_ξc.trans_le hξ))
      have hBb' : profB ξ ≤ εb := strictAnti_profB.antitone hξb
      have : E * profA ξ * profB ξ ≤ εb := by
        calc E * profA ξ * profB ξ ≤ 1 * 1 * profB ξ := by gcongr
          _ = profB ξ := by ring
          _ ≤ εb := hBb'
      rw [mul_comm εb]
      exact mul_le_mul_of_nonneg_left this hc
    · rw [deriv_chi_eq_zero hχ (ξa_lt_ξc.trans_le hξ) hξb]
      simp
  have h2 : χ ξ * profA ξ * profBbar ξ ≤ profBbar ξ := by
    have : χ ξ * profA ξ ≤ 1 := by
      calc χ ξ * profA ξ ≤ 1 * 1 := by gcongr
        _ = 1 := by ring
    calc χ ξ * profA ξ * profBbar ξ ≤ 1 * profBbar ξ := by gcongr
      _ = profBbar ξ := one_mul _
  have h3 : 0 ≤ χ ξ * profA ξ * profAbar ξ := by positivity
  have hc : 0 ≤ E * (2 / d) * profB ξ := by positivity
  have key : (εb * (-deriv χ ξ) + E * ((2 / d) * (profB ξ * profBbar ξ))) -
      E * (-deriv (prof χ) ξ) =
      (εb * (-deriv χ ξ) - (-deriv χ ξ) * (E * profA ξ * profB ξ)) +
        E * (2 / d) * profB ξ * (profBbar ξ - χ ξ * profA ξ * profBbar ξ) +
        E * (2 / d) * profB ξ * (χ ξ * profA ξ * profAbar ξ) := by
    rw [deriv_prof_eq hχ]
    ring
  have : 0 ≤ (εb * (-deriv χ ξ) + E * ((2 / d) * (profB ξ * profBbar ξ))) -
      E * (-deriv (prof χ) ξ) := by
    rw [key]
    have k1 : 0 ≤ εb * (-deriv χ ξ) - (-deriv χ ξ) * (E * profA ξ * profB ξ) := by linarith
    have k2 : 0 ≤ E * (2 / d) * profB ξ * (profBbar ξ - χ ξ * profA ξ * profBbar ξ) :=
      mul_nonneg hc (by linarith)
    have k3 : 0 ≤ E * (2 / d) * profB ξ * (χ ξ * profA ξ * profAbar ξ) := mul_nonneg hc h3
    linarith
  linarith

end ClosedFormAux

end NonUniqueEuler
