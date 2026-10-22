import NonUniqueEuler.Defs.Sec2.Multipole
import NonUniqueEuler.Defs.Infra.Polar
import NonUniqueEuler.I.Infra.Multipole.LogPotential
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Proof: the multipole coefficients and the angular sectors of the stream function

Proof of `I/Sec2/MultipoleStream.lean` (manuscript `02_prelim.tex:460-468`, the paragraph after
`def:multipole`). Both identities are the I-MULT lemmas
`Multipole.angularSector_logPotential_exterior_pos` (with `ρ = ρ₂`) and
`Multipole.angularSector_logPotential_interior_pos` (with `ρ = ρ₁`), rewritten with the bridges
`BS.pout_eq_conjMoment`, `BS.pin_eq_moment`. The interior identity needs the integrability of
`log|y| g(y)`, proved here (`integrable_log_norm_mul_of_annulus`) from
`|log|y|| ≤ max(|log ρ₁|, |log ρ₂|)` on the support of `g`.
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler.BS

/-- On the annulus `ρ₁ ≤ ‖y‖ ≤ ρ₂` (`0 < ρ₁`), `|log ‖y‖| ≤ max |log ρ₁| |log ρ₂|`. -/
private theorem abs_log_le_of_annulus {ρ₁ ρ₂ t : ℝ} (hρ₁ : 0 < ρ₁) (h₁ : ρ₁ ≤ t) (h₂ : t ≤ ρ₂) :
    |Real.log t| ≤ max |Real.log ρ₁| |Real.log ρ₂| :=
  abs_le_max_abs_abs (Real.log_le_log hρ₁ h₁) (Real.log_le_log (hρ₁.trans_le h₁) h₂)

/-- If `g ∈ L¹` vanishes a.e. off the annulus `ρ₁ ≤ ‖y‖ ≤ ρ₂` (`0 < ρ₁`), then
`log ‖y‖ · g(y) ∈ L¹`. -/
private theorem integrable_log_norm_mul_of_annulus {g : ℂ → ℂ} (hg : Integrable g volume)
    {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁)
    (hsupp : ∀ᵐ y, (‖y‖ < ρ₁ ∨ ρ₂ < ‖y‖) → g y = 0) :
    Integrable (fun y => (Real.log ‖y‖ : ℂ) * g y) volume := by
  have hmeas : AEStronglyMeasurable (fun y : ℂ => (Real.log ‖y‖ : ℂ) * g y) volume := by
    have hlog : Measurable fun y : ℂ => (Real.log ‖y‖ : ℂ) :=
      Complex.measurable_ofReal.comp (Real.measurable_log.comp measurable_norm)
    exact hlog.aestronglyMeasurable.mul hg.aestronglyMeasurable
  refine Integrable.mono' (hg.norm.const_mul (max |Real.log ρ₁| |Real.log ρ₂|)) hmeas ?_
  filter_upwards [hsupp] with y hy
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  by_cases hgy : g y = 0
  · rw [hgy, norm_zero, mul_zero, mul_zero]
  · have h₁ : ρ₁ ≤ ‖y‖ := by
      by_contra h
      exact hgy (hy (Or.inl (lt_of_not_ge h)))
    have h₂ : ‖y‖ ≤ ρ₂ := by
      by_contra h
      exact hgy (hy (Or.inr (lt_of_not_ge h)))
    exact mul_le_mul_of_nonneg_right (abs_log_le_of_annulus hρ₁ h₁ h₂) (norm_nonneg _)

/-- Exterior sectors (`02_prelim.tex:465-466`): for `r > ρ₂` the angular sector `m` of the
stream function of `g` is `-(2m)⁻¹ pout_m[g] r^{-m}`. -/
theorem angularSector_stream_exterior {m : ℕ} (hm : 1 ≤ m) {g : ℂ → ℂ} (hg : Integrable g volume)
    {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (hρ₁₂ : ρ₁ ≤ ρ₂)
    (hsupp : ∀ᵐ y, (‖y‖ < ρ₁ ∨ ρ₂ < ‖y‖) → g y = 0) {r : ℝ} (hr : ρ₂ < r) :
    Polar.angularSector (Multipole.logPotential g) m r =
      -((2 * (m : ℂ))⁻¹ * pout m g * ((r : ℂ) ^ m)⁻¹) := by
  have hsupp' : ∀ᵐ y, ρ₂ < ‖y‖ → g y = 0 := by
    filter_upwards [hsupp] with y hy h using hy (Or.inr h)
  rw [Multipole.angularSector_logPotential_exterior_pos hg (hρ₁.le.trans hρ₁₂) hsupp' hm hr,
    pout_eq_conjMoment, div_eq_mul_inv]

/-- Interior sectors (`02_prelim.tex:466-467`): for `0 < r < ρ₁` the angular sector `m` of the
stream function of `g` is `-(2m)⁻¹ pin_m[g] r^m`. -/
theorem angularSector_stream_interior {m : ℕ} (hm : 1 ≤ m) {g : ℂ → ℂ} (hg : Integrable g volume)
    {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (hρ₁₂ : ρ₁ ≤ ρ₂)
    (hsupp : ∀ᵐ y, (‖y‖ < ρ₁ ∨ ρ₂ < ‖y‖) → g y = 0) {r : ℝ} (hr0 : 0 < r) (hr : r < ρ₁) :
    Polar.angularSector (Multipole.logPotential g) m r =
      -((2 * (m : ℂ))⁻¹ * pin m g * (r : ℂ) ^ m) := by
  have hsupp' : ∀ᵐ y, ‖y‖ < ρ₁ → g y = 0 := by
    filter_upwards [hsupp] with y hy h using hy (Or.inl h)
  rw [Multipole.angularSector_logPotential_interior_pos hg hsupp'
    (integrable_log_norm_mul_of_annulus hg hρ₁ hsupp) hm hr0.le hr, pin_eq_moment]

end NonUniqueEuler.BS
