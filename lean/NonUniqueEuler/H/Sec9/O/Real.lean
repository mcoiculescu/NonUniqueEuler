import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Helpers for `P/Sec9/O`: the Duhamel comparisons of `lem:O` on the real line

Generic real-analysis steps of the proof of `lem:O` (`09_relay.tex:264-300`), over named real
functions:
* `OProof.duh_subst`: the substitution `v = v'/c` of `eq:O-duh`;
* `OProof.integral_exp_decay_le`: `∫₀^{τ'} e^{-δ(τ'-v)} dv ≤ 1/δ`;
* `OProof.duhamel_compare`: `eq:O-fast` and `eq:O-same` combined: if
  `f ≤ P(a₁m + a₂g)` on `[0,τ']`, `m` satisfies (M1) at rate `σ`, `0 ≤ g ≤ e`, and `σ̂ ≤ σ - δ`,
  then `c⁻¹∫₀^{τ'} e^{σ̂(τ'-v)} f ≤ P(a₁ m(τ')/δ + a₂∫₀^{τ'} e^{σ(τ'-v)} e)` for `c ≥ 1`.
-/

noncomputable section

open Set MeasureTheory

namespace NonUniqueEuler.Relay.OProof

/-- The substitution `v = v'/c` of `eq:O-duh` (`09_relay.tex:271-274`):
`∫₀^{τ'/c} e^{σ(τ'/c-v)} η(v) dv = c⁻¹ ∫₀^{τ'} e^{(σ/c)(τ'-v')} η(v'/c) dv'`. -/
theorem duh_subst {c : ℝ} (hc : c ≠ 0) (σ τ' : ℝ) (η : ℝ → ℝ) :
    ∫ v in (0 : ℝ)..τ' / c, Real.exp (σ * (τ' / c - v)) * η v =
      c⁻¹ * ∫ v in (0 : ℝ)..τ', Real.exp (σ / c * (τ' - v)) * η (v / c) := by
  have h := intervalIntegral.integral_comp_div
    (fun v => Real.exp (σ * (τ' / c - v)) * η v) hc (a := 0) (b := τ')
  simp only [zero_div, smul_eq_mul] at h
  have h2 : (∫ x in (0 : ℝ)..τ', Real.exp (σ / c * (τ' - x)) * η (x / c)) =
      ∫ x in (0 : ℝ)..τ', Real.exp (σ * (τ' / c - x / c)) * η (x / c) := by
    congr 1
    funext x
    congr 2
    field_simp
  rw [h2, h, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/-- `∫₀^{τ'} e^{-δ(τ'-v)} dv ≤ 1/δ` for `δ > 0`. -/
theorem integral_exp_decay_le {δ : ℝ} (hδ : 0 < δ) (τ' : ℝ) :
    ∫ v in (0 : ℝ)..τ', Real.exp (-(δ * (τ' - v))) ≤ 1 / δ := by
  have h : (fun v => Real.exp (-(δ * (τ' - v)))) = fun v => Real.exp (δ * v + -(δ * τ')) := by
    funext v
    congr 1
    ring
  rw [h, intervalIntegral.integral_comp_mul_add (fun x => Real.exp x) hδ.ne', integral_exp]
  simp only [mul_zero, zero_add, smul_eq_mul]
  rw [show δ * τ' + -(δ * τ') = 0 by ring, Real.exp_zero, one_div]
  have h1 := Real.exp_pos (-(δ * τ'))
  have hδi : 0 < δ⁻¹ := inv_pos.mpr hδ
  nlinarith

private theorem contOn_exp_mul {σ τ' : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 τ')) :
    ContinuousOn (fun v => Real.exp (σ * (τ' - v)) * f v) (Icc 0 τ') :=
  ((Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))).continuousOn).mul hf

private theorem ii_of_contOn {τ' : ℝ} (hτ : 0 ≤ τ') {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 τ')) :
    IntervalIntegrable f volume 0 τ' :=
  (uIcc_of_le hτ ▸ hf).intervalIntegrable

/-- **`eq:O-fast` and `eq:O-same`** (`09_relay.tex:276-287`), combined with the pointwise bound
of the forcing. Let `τ' ≥ 0`, `c ≥ 1`, `δ > 0`, `σ̂ ≤ σ - δ`, `P, a₁, a₂ ≥ 0`, and let `f, m, g, e`
be continuous on `[0,τ']` with `f ≤ P(a₁m + a₂g)`, `m ≥ 0`, `e^{σ(τ'-v)}m(v) ≤ m(τ')`,
`0 ≤ g ≤ e` there. Then
`c⁻¹∫₀^{τ'} e^{σ̂(τ'-v)} f(v) dv ≤ P(a₁ m(τ')/δ + a₂∫₀^{τ'} e^{σ(τ'-v)} e(v) dv)`. -/
theorem duhamel_compare {τ' c σh σ δ P a1 a2 : ℝ} (hτ : 0 ≤ τ') (hc : 1 ≤ c) (hδ : 0 < δ)
    (hσh : σh ≤ σ - δ) (hP : 0 ≤ P) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2)
    {f m g e : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 τ')) (hm : ContinuousOn m (Icc 0 τ'))
    (hg : ContinuousOn g (Icc 0 τ')) (he : ContinuousOn e (Icc 0 τ'))
    (hfb : ∀ v ∈ Icc 0 τ', f v ≤ P * (a1 * m v + a2 * g v))
    (hm0 : ∀ v ∈ Icc 0 τ', 0 ≤ m v)
    (hm1 : ∀ v ∈ Icc 0 τ', Real.exp (σ * (τ' - v)) * m v ≤ m τ')
    (hg0 : ∀ v ∈ Icc 0 τ', 0 ≤ g v) (hge : ∀ v ∈ Icc 0 τ', g v ≤ e v) :
    c⁻¹ * ∫ v in (0 : ℝ)..τ', Real.exp (σh * (τ' - v)) * f v ≤
      P * (a1 * (m τ' / δ) + a2 * ∫ v in (0 : ℝ)..τ', Real.exp (σ * (τ' - v)) * e v) := by
  have hiEf := ii_of_contOn hτ (contOn_exp_mul (σ := σh) hf)
  have hiEm := ii_of_contOn hτ (contOn_exp_mul (σ := σh) hm)
  have hiEg := ii_of_contOn hτ (contOn_exp_mul (σ := σh) hg)
  have hiEe := ii_of_contOn hτ (contOn_exp_mul (σ := σ) he)
  have hiD : IntervalIntegrable (fun v => Real.exp (-(δ * (τ' - v))) * m τ') volume 0 τ' :=
    ii_of_contOn hτ (((Real.continuous_exp.comp
      ((continuous_const.mul (continuous_const.sub continuous_id)).neg)).mul
        continuous_const).continuousOn)
  -- the pointwise bound of the forcing
  have h1 : (∫ v in (0 : ℝ)..τ', Real.exp (σh * (τ' - v)) * f v) ≤
      ∫ v in (0 : ℝ)..τ', P * a1 * (Real.exp (σh * (τ' - v)) * m v) +
        P * a2 * (Real.exp (σh * (τ' - v)) * g v) := by
    refine intervalIntegral.integral_mono_on hτ hiEf
      ((hiEm.const_mul _).add (hiEg.const_mul _)) fun v hv => ?_
    have := hfb v hv
    have hE := Real.exp_pos (σh * (τ' - v))
    have : Real.exp (σh * (τ' - v)) * f v ≤
        Real.exp (σh * (τ' - v)) * (P * (a1 * m v + a2 * g v)) :=
      mul_le_mul_of_nonneg_left this hE.le
    linarith
  rw [intervalIntegral.integral_add (hiEm.const_mul _) (hiEg.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h1
  -- `eq:O-fast`
  have h2 : (∫ v in (0 : ℝ)..τ', Real.exp (σh * (τ' - v)) * m v) ≤ m τ' / δ := by
    have hmono : (∫ v in (0 : ℝ)..τ', Real.exp (σh * (τ' - v)) * m v) ≤
        ∫ v in (0 : ℝ)..τ', Real.exp (-(δ * (τ' - v))) * m τ' := by
      refine intervalIntegral.integral_mono_on hτ hiEm hiD fun v hv => ?_
      have hv' : 0 ≤ τ' - v := by linarith [hv.2]
      have hsplit : Real.exp (σh * (τ' - v)) =
          Real.exp ((σh - σ) * (τ' - v)) * Real.exp (σ * (τ' - v)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hle : Real.exp ((σh - σ) * (τ' - v)) ≤ Real.exp (-(δ * (τ' - v))) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      have hpos : 0 ≤ Real.exp (σ * (τ' - v)) * m v :=
        mul_nonneg (Real.exp_pos _).le (hm0 v hv)
      rw [hsplit, mul_assoc]
      calc Real.exp ((σh - σ) * (τ' - v)) * (Real.exp (σ * (τ' - v)) * m v)
          ≤ Real.exp (-(δ * (τ' - v))) * (Real.exp (σ * (τ' - v)) * m v) :=
            mul_le_mul_of_nonneg_right hle hpos
        _ ≤ Real.exp (-(δ * (τ' - v))) * m τ' :=
            mul_le_mul_of_nonneg_left (hm1 v hv) (Real.exp_pos _).le
    have hm0' : 0 ≤ m τ' := hm0 τ' ⟨hτ, le_rfl⟩
    rw [intervalIntegral.integral_mul_const] at hmono
    have hI := integral_exp_decay_le hδ τ'
    calc _ ≤ _ := hmono
      _ ≤ 1 / δ * m τ' := mul_le_mul_of_nonneg_right hI hm0'
      _ = m τ' / δ := by ring
  -- `eq:O-same`
  have h3 : (∫ v in (0 : ℝ)..τ', Real.exp (σh * (τ' - v)) * g v) ≤
      ∫ v in (0 : ℝ)..τ', Real.exp (σ * (τ' - v)) * e v := by
    refine intervalIntegral.integral_mono_on hτ hiEg hiEe fun v hv => ?_
    have hv' : 0 ≤ τ' - v := by linarith [hv.2]
    have hle : Real.exp (σh * (τ' - v)) ≤ Real.exp (σ * (τ' - v)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    calc Real.exp (σh * (τ' - v)) * g v ≤ Real.exp (σ * (τ' - v)) * g v :=
          mul_le_mul_of_nonneg_right hle (hg0 v hv)
      _ ≤ Real.exp (σ * (τ' - v)) * e v :=
          mul_le_mul_of_nonneg_left (hge v hv) (Real.exp_pos _).le
  -- assemble
  have hR0 : 0 ≤ ∫ v in (0 : ℝ)..τ', Real.exp (σ * (τ' - v)) * e v := by
    refine intervalIntegral.integral_nonneg hτ fun v hv => ?_
    exact mul_nonneg (Real.exp_pos _).le ((hg0 v hv).trans (hge v hv))
  have hm0' : 0 ≤ m τ' := hm0 τ' ⟨hτ, le_rfl⟩
  have hR : 0 ≤ P * (a1 * (m τ' / δ) + a2 * ∫ v in (0 : ℝ)..τ', Real.exp (σ * (τ' - v)) * e v) := by
    have : 0 ≤ m τ' / δ := div_nonneg hm0' hδ.le
    positivity
  have hI : (∫ v in (0 : ℝ)..τ', Real.exp (σh * (τ' - v)) * f v) ≤
      P * (a1 * (m τ' / δ) + a2 * ∫ v in (0 : ℝ)..τ', Real.exp (σ * (τ' - v)) * e v) := by
    have hPa1 : 0 ≤ P * a1 := mul_nonneg hP ha1
    have hPa2 : 0 ≤ P * a2 := mul_nonneg hP ha2
    have := mul_le_mul_of_nonneg_left h2 hPa1
    have := mul_le_mul_of_nonneg_left h3 hPa2
    nlinarith
  have hc0 : 0 ≤ c⁻¹ := inv_nonneg.mpr (by linarith)
  have hc1 : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc
  calc c⁻¹ * ∫ v in (0 : ℝ)..τ', Real.exp (σh * (τ' - v)) * f v
      ≤ c⁻¹ * (P * (a1 * (m τ' / δ) + a2 * ∫ v in (0 : ℝ)..τ', Real.exp (σ * (τ' - v)) * e v)) :=
        mul_le_mul_of_nonneg_left hI hc0
    _ ≤ _ := by nlinarith

end NonUniqueEuler.Relay.OProof
