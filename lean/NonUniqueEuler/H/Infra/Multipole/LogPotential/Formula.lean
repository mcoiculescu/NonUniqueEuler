import NonUniqueEuler.H.Infra.Multipole.LogPotential.Kernel

/-!
# Helper: reduction of the sectors of the logarithmic potential to integrals against `g`
(for `P/Infra/Multipole/LogPotential`)

* Exterior (`g = 0` a.e. on `{|y| > ρ}`, `0 ≤ ρ < r`): `|log|r e^{iθ} - y|| ≤ |log r| -
  log(1 - ρ/r)` on the support, so Fubini applies and
  `ψ_ℓ(r) = (2π)⁻¹ (2π)⁻¹ ∫ g(y) c(y) dy` whenever `c(y)` is the kernel sector for `|y| < r`.
* Interior (`g = 0` a.e. on `{|y| < ρ}`, `0 ≤ r < ρ`, `log|y| g ∈ L¹`):
  `|log|r e^{iθ} - y|| ≤ |log|y|| - log(1 - r/ρ)` on the support, and the same reduction.
-/

noncomputable section

open MeasureTheory Set Metric Real ComplexConjugate

namespace NonUniqueEuler.Multipole.LogPotentialH

open NonUniqueEuler.Polar

/-- `-log(1 - t)` is monotone on `[0, 1)`. -/
theorem neg_log_one_sub_le {s t : ℝ} (hst : s ≤ t) (ht : t < 1) :
    -Real.log (1 - s) ≤ -Real.log (1 - t) := by
  have h1 : 0 < 1 - t := by linarith
  have := Real.log_le_log h1 (by linarith : 1 - t ≤ 1 - s)
  linarith

/-- Exterior bound on the support. -/
theorem abs_log_norm_sub_le_ext {ρ r : ℝ} (hρ : 0 ≤ ρ) (hr : ρ < r) {y : ℂ} (hy : ‖y‖ ≤ ρ)
    (θ : ℝ) :
    |Real.log ‖(r : ℂ) * Complex.exp (θ * Complex.I) - y‖| ≤
      |Real.log r| + -Real.log (1 - ρ / r) := by
  have hr0 : 0 < r := lt_of_le_of_lt hρ hr
  have hyr : ‖y‖ < r := lt_of_le_of_lt hy hr
  have hna : ‖conj y / r * Complex.exp (θ * Complex.I)‖ = ‖y‖ / r := by
    rw [norm_mul_exp_I, norm_div, Complex.norm_conj, Complex.norm_real,
      Real.norm_of_nonneg hr0.le]
  have hρr : ρ / r < 1 := (div_lt_one hr0).2 hr
  have ha : ‖conj y / r * Complex.exp (θ * Complex.I)‖ < 1 := by
    rw [hna]; exact (div_lt_one hr0).2 hyr
  rw [log_norm_sub_eq_of_lt hr0 hyr θ]
  refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
  refine (abs_log_norm_one_sub_le ha).trans ?_
  rw [hna]
  exact neg_log_one_sub_le (div_le_div_of_nonneg_right hy hr0.le) hρr

/-- Interior bound on the support. -/
theorem abs_log_norm_sub_le_int {ρ r : ℝ} (hr0 : 0 ≤ r) (hr : r < ρ) {y : ℂ} (hy : ρ ≤ ‖y‖)
    (θ : ℝ) :
    |Real.log ‖(r : ℂ) * Complex.exp (θ * Complex.I) - y‖| ≤
      |Real.log ‖y‖| + -Real.log (1 - r / ρ) := by
  have hρ0 : 0 < ρ := lt_of_le_of_lt hr0 hr
  have hry : r < ‖y‖ := lt_of_lt_of_le hr hy
  have hy0 : 0 < ‖y‖ := lt_of_lt_of_le hρ0 hy
  have hna : ‖(r : ℂ) / y * Complex.exp (θ * Complex.I)‖ = r / ‖y‖ := by
    rw [norm_mul_exp_I, norm_div, Complex.norm_real, Real.norm_of_nonneg hr0]
  have hrρ : r / ρ < 1 := (div_lt_one hρ0).2 hr
  have ha : ‖(r : ℂ) / y * Complex.exp (θ * Complex.I)‖ < 1 := by
    rw [hna]; exact (div_lt_one hy0).2 hry
  rw [log_norm_sub_eq_of_gt hr0 hry θ]
  refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
  refine (abs_log_norm_one_sub_le ha).trans ?_
  rw [hna]
  exact neg_log_one_sub_le (div_le_div_of_nonneg_left hr0 hρ0 hy) hrρ

/-- Exterior reduction: `ψ_ℓ(r) = (2π)⁻¹ (2π)⁻¹ ∫ g(y) c(y) dy` when `c(y)` is the sector of
`θ ↦ log|r e^{iθ} - y|` for every `|y| < r`. -/
theorem angularSector_logPotential_ext {g : ℂ → ℂ} (hg : Integrable g) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hsupp : ∀ᵐ y, ρ < ‖y‖ → g y = 0) {r : ℝ} (hr : ρ < r) (ℓ : ℤ)
    (c : ℂ → ℂ)
    (hc : ∀ y : ℂ, ‖y‖ < r →
      ∫ θ in (0 : ℝ)..2 * π, (Real.log ‖(r : ℂ) * Complex.exp (θ * Complex.I) - y‖ : ℂ) *
        Complex.exp (-((ℓ : ℂ) * θ * Complex.I)) = c y) :
    angularSector (logPotential g) ℓ r =
      (2 * π : ℂ)⁻¹ * ((2 * π : ℂ)⁻¹ * ∫ y, g y * c y) := by
  set C : ℝ := |Real.log r| + -Real.log (1 - ρ / r)
  have hbound : ∀ᵐ y, ∀ θ : ℝ,
      ‖(Real.log ‖(r : ℂ) * Complex.exp (θ * Complex.I) - y‖ : ℂ) * g y‖ ≤ C * ‖g y‖ := by
    filter_upwards [hsupp] with y hy θ
    by_cases hyρ : ρ < ‖y‖
    · rw [hy hyρ]; simp
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        (abs_log_norm_sub_le_ext hρ hr (not_lt.1 hyρ) θ) (norm_nonneg _)
  rw [angularSector_logPotential_eq hg.aestronglyMeasurable ℓ r (hg.norm.const_mul C) hbound]
  congr 2
  refine integral_congr_ae ?_
  filter_upwards [hsupp] with y hy
  by_cases hyρ : ρ < ‖y‖
  · rw [hy hyρ, zero_mul, zero_mul]
  · rw [hc y (lt_of_le_of_lt (not_lt.1 hyρ) hr)]

/-- Interior reduction: `ψ_ℓ(r) = (2π)⁻¹ (2π)⁻¹ ∫ g(y) c(y) dy` when `c(y)` is the sector of
`θ ↦ log|r e^{iθ} - y|` for every `|y| > r`. -/
theorem angularSector_logPotential_int {g : ℂ → ℂ} (hg : Integrable g) {ρ : ℝ}
    (hsupp : ∀ᵐ y, ‖y‖ < ρ → g y = 0)
    (hlog : Integrable fun y => (Real.log ‖y‖ : ℂ) * g y) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r < ρ) (ℓ : ℤ) (c : ℂ → ℂ)
    (hc : ∀ y : ℂ, r < ‖y‖ →
      ∫ θ in (0 : ℝ)..2 * π, (Real.log ‖(r : ℂ) * Complex.exp (θ * Complex.I) - y‖ : ℂ) *
        Complex.exp (-((ℓ : ℂ) * θ * Complex.I)) = c y) :
    angularSector (logPotential g) ℓ r =
      (2 * π : ℂ)⁻¹ * ((2 * π : ℂ)⁻¹ * ∫ y, g y * c y) := by
  set C : ℝ := -Real.log (1 - r / ρ)
  have hbound : ∀ᵐ y, ∀ θ : ℝ,
      ‖(Real.log ‖(r : ℂ) * Complex.exp (θ * Complex.I) - y‖ : ℂ) * g y‖ ≤
        ‖(Real.log ‖y‖ : ℂ) * g y‖ + C * ‖g y‖ := by
    filter_upwards [hsupp] with y hy θ
    by_cases hyρ : ‖y‖ < ρ
    · rw [hy hyρ]; simp
    · rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, ← add_mul]
      exact mul_le_mul_of_nonneg_right
        (abs_log_norm_sub_le_int hr0 hr (not_lt.1 hyρ) θ) (norm_nonneg _)
  rw [angularSector_logPotential_eq hg.aestronglyMeasurable ℓ r
    (hlog.norm.add (hg.norm.const_mul C)) hbound]
  congr 2
  refine integral_congr_ae ?_
  filter_upwards [hsupp] with y hy
  by_cases hyρ : ‖y‖ < ρ
  · rw [hy hyρ, zero_mul, zero_mul]
  · rw [hc y (lt_of_lt_of_le hr (not_lt.1 hyρ))]

end NonUniqueEuler.Multipole.LogPotentialH
