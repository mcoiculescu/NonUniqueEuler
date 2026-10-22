import NonUniqueEuler.H.Infra.Multipole.LogPotential.Fourier
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Helper: angular sectors of `x ↦ log|x - y|` and Fubini (for `P/Infra/Multipole/LogPotential`)

* Factorizations (`02_prelim.tex:461-469`): for `x = r e^{iθ}`,
  `log|x - y| = log r + log|1 - (ȳ/r) e^{iθ}|` if `|y| < r`, and
  `log|x - y| = log|y| + log|1 - (r/y) e^{iθ}|` if `r < |y|`.
* The bound `|log|1 - w|| ≤ -log(1 - |w|)` for `|w| < 1`.
* The sectors `∫₀^{2π} log|r e^{iθ} - y| e^{-iℓθ} dθ` for `ℓ = 0, m, -m` in both regimes.
* Fubini: `ψ_ℓ(r) = (2π)⁻¹ (2π)⁻¹ ∫ g(y) ∫₀^{2π} log|r e^{iθ} - y| e^{-iℓθ} dθ dy` under a
  uniform integrable bound for `log|r e^{iθ} - y| g(y)`.
-/

noncomputable section

open MeasureTheory Set Metric Real ComplexConjugate

namespace NonUniqueEuler.Multipole.LogPotentialH

open NonUniqueEuler.Polar

theorem exp_mul_conj_exp (θ : ℝ) :
    Complex.exp (θ * Complex.I) * conj (Complex.exp (θ * Complex.I)) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
  simp

theorem log_norm_one_sub_ne {w : ℂ} (hw : ‖w‖ < 1) : ‖1 - w‖ ≠ 0 := by
  intro h
  rw [norm_eq_zero, sub_eq_zero] at h
  rw [← h, norm_one] at hw
  exact lt_irrefl _ hw

/-- Exterior factorization: `|r e^{iθ} - y| = r |1 - (ȳ/r) e^{iθ}|`. -/
theorem log_norm_sub_eq_of_lt {r : ℝ} (hr : 0 < r) {y : ℂ} (hy : ‖y‖ < r) (θ : ℝ) :
    Real.log ‖(r : ℂ) * Complex.exp (θ * Complex.I) - y‖ =
      Real.log r + Real.log ‖1 - (conj y / r) * Complex.exp (θ * Complex.I)‖ := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  set e := Complex.exp (θ * Complex.I) with he_def
  have he : e * conj e = 1 := exp_mul_conj_exp θ
  have hne : ‖e‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have hw : ‖conj y / r * e‖ < 1 := by
    rw [norm_mul, hne, mul_one, norm_div, Complex.norm_conj, Complex.norm_real,
      Real.norm_of_nonneg hr.le, div_lt_one hr]
    exact hy
  have hcancel : (r : ℂ) * (conj y / r * e) = conj y * e := by field_simp
  have heq : ‖(r : ℂ) * e - y‖ = r * ‖1 - conj y / r * e‖ := by
    calc ‖(r : ℂ) * e - y‖ = ‖conj ((r : ℂ) * e - y)‖ := (Complex.norm_conj _).symm
      _ = ‖e‖ * ‖conj ((r : ℂ) * e - y)‖ := by rw [hne, one_mul]
      _ = ‖e * conj ((r : ℂ) * e - y)‖ := (norm_mul _ _).symm
      _ = ‖(r : ℂ) * (1 - conj y / r * e)‖ := by
          congr 1
          rw [map_sub, map_mul, Complex.conj_ofReal, mul_sub, mul_sub, mul_one, hcancel]
          linear_combination (r : ℂ) * he
      _ = r * ‖1 - conj y / r * e‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le]
  rw [heq, Real.log_mul hr.ne' (log_norm_one_sub_ne hw)]

/-- Interior factorization: `|r e^{iθ} - y| = |y| |1 - (r/y) e^{iθ}|`. -/
theorem log_norm_sub_eq_of_gt {r : ℝ} (hr : 0 ≤ r) {y : ℂ} (hy : r < ‖y‖) (θ : ℝ) :
    Real.log ‖(r : ℂ) * Complex.exp (θ * Complex.I) - y‖ =
      Real.log ‖y‖ + Real.log ‖1 - ((r : ℂ) / y) * Complex.exp (θ * Complex.I)‖ := by
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, norm_zero] at hy
    linarith
  have hw : ‖(r : ℂ) / y * Complex.exp (θ * Complex.I)‖ < 1 := by
    rw [norm_mul_exp_I, norm_div, Complex.norm_real, Real.norm_of_nonneg hr,
      div_lt_one (by linarith)]
    exact hy
  have heq : ‖(r : ℂ) * Complex.exp (θ * Complex.I) - y‖ =
      ‖y‖ * ‖1 - (r : ℂ) / y * Complex.exp (θ * Complex.I)‖ := by
    rw [← norm_neg y, ← norm_mul]
    congr 1
    field_simp
    ring
  rw [heq, Real.log_mul (norm_ne_zero_iff.mpr hy0) (log_norm_one_sub_ne hw)]

/-- `|log|1 - w|| ≤ -log(1 - |w|)` for `|w| < 1`. -/
theorem abs_log_norm_one_sub_le {w : ℂ} (hw : ‖w‖ < 1) :
    |Real.log ‖1 - w‖| ≤ -Real.log (1 - ‖w‖) := by
  have h0 : 0 < 1 - ‖w‖ := by linarith
  have hlow : 1 - ‖w‖ ≤ ‖1 - w‖ := by
    have := norm_sub_norm_le (1 : ℂ) w
    rwa [norm_one] at this
  have hup : ‖1 - w‖ ≤ 1 + ‖w‖ := by
    have := norm_sub_le (1 : ℂ) w
    rwa [norm_one] at this
  have hpos : 0 < ‖1 - w‖ := lt_of_lt_of_le h0 hlow
  have hprod : Real.log (1 + ‖w‖) + Real.log (1 - ‖w‖) ≤ 0 := by
    rw [← Real.log_mul (by positivity) h0.ne']
    apply Real.log_nonpos (by nlinarith [norm_nonneg w])
    nlinarith [norm_nonneg w]
  rw [abs_le]
  constructor
  · rw [neg_neg]
    exact Real.log_le_log h0 hlow
  · have := Real.log_le_log hpos hup
    linarith

theorem integral_exp_neg_int_mul (ℓ : ℤ) :
    ∫ θ in (0 : ℝ)..2 * π, Complex.exp (-((ℓ : ℂ) * θ * Complex.I)) =
      if ℓ = 0 then 2 * (π : ℂ) else 0 := by
  have h : ∀ θ : ℝ, Complex.exp (-((ℓ : ℂ) * θ * Complex.I)) =
      Complex.exp (((-ℓ : ℤ) : ℂ) * θ * Complex.I) := fun θ => by
    congr 1
    push_cast
    ring
  simp_rw [h]
  rw [integral_exp_int_mul]
  simp only [neg_eq_zero]

/-- The sector of `θ ↦ log|r e^{iθ} - y|` from a factorization
`log|r e^{iθ} - y| = c + log|1 - a e^{iθ}|` with `|a| < 1`. -/
theorem integral_log_norm_sub_of_factor {r : ℝ} {y a : ℂ} {c : ℝ} (ha : ‖a‖ < 1)
    (hfac : ∀ θ : ℝ, Real.log ‖(r : ℂ) * Complex.exp (θ * Complex.I) - y‖ =
      c + Real.log ‖1 - a * Complex.exp (θ * Complex.I)‖) (ℓ : ℤ) :
    ∫ θ in (0 : ℝ)..2 * π, (Real.log ‖(r : ℂ) * Complex.exp (θ * Complex.I) - y‖ : ℂ) *
        Complex.exp (-((ℓ : ℂ) * θ * Complex.I)) =
      (c : ℂ) * (if ℓ = 0 then 2 * (π : ℂ) else 0) +
        ∫ θ in (0 : ℝ)..2 * π, (Real.log ‖1 - a * Complex.exp (θ * Complex.I)‖ : ℂ) *
          Complex.exp (-((ℓ : ℂ) * θ * Complex.I)) := by
  have hcont : Continuous fun θ : ℝ => (Real.log ‖1 - a * Complex.exp (θ * Complex.I)‖ : ℂ) *
      Complex.exp (-((ℓ : ℂ) * θ * Complex.I)) := by
    refine (Complex.continuous_ofReal.comp ?_).mul (by fun_prop)
    refine Continuous.log (by fun_prop) fun θ => log_norm_one_sub_ne ?_
    rw [norm_mul_exp_I]
    exact ha
  simp_rw [hfac, Complex.ofReal_add, add_mul]
  rw [intervalIntegral.integral_add ((by fun_prop : Continuous fun θ : ℝ =>
      (c : ℂ) * Complex.exp (-((ℓ : ℂ) * θ * Complex.I))).intervalIntegrable _ _)
    (hcont.intervalIntegrable _ _), intervalIntegral.integral_const_mul,
    integral_exp_neg_int_mul]

/-! ### Exterior sectors (`|y| < r`) -/

theorem kernel_ext_zero {r : ℝ} (hr : 0 < r) {y : ℂ} (hy : ‖y‖ < r) :
    ∫ θ in (0 : ℝ)..2 * π, (Real.log ‖(r : ℂ) * Complex.exp (θ * Complex.I) - y‖ : ℂ) *
        Complex.exp (-(((0 : ℤ) : ℂ) * θ * Complex.I)) = (Real.log r : ℂ) * (2 * π) := by
  have ha : ‖conj y / r‖ < 1 := by
    rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hr.le,
      div_lt_one hr]
    exact hy
  rw [integral_log_norm_sub_of_factor ha (log_norm_sub_eq_of_lt hr hy),
    integral_log_norm_one_sub_zero ha]
  simp

theorem kernel_ext_pos {r : ℝ} (hr : 0 < r) {y : ℂ} (hy : ‖y‖ < r) {m : ℕ} (hm : 1 ≤ m) :
    ∫ θ in (0 : ℝ)..2 * π, (Real.log ‖(r : ℂ) * Complex.exp (θ * Complex.I) - y‖ : ℂ) *
        Complex.exp (-(((m : ℤ) : ℂ) * θ * Complex.I)) = -(π * (conj y / r) ^ m / m) := by
  have ha : ‖conj y / r‖ < 1 := by
    rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hr.le,
      div_lt_one hr]
    exact hy
  rw [integral_log_norm_sub_of_factor ha (log_norm_sub_eq_of_lt hr hy),
    integral_log_norm_one_sub_pos ha hm]
  have : m ≠ 0 := by omega
  simp [this]

theorem kernel_ext_neg {r : ℝ} (hr : 0 < r) {y : ℂ} (hy : ‖y‖ < r) {m : ℕ} (hm : 1 ≤ m) :
    ∫ θ in (0 : ℝ)..2 * π, (Real.log ‖(r : ℂ) * Complex.exp (θ * Complex.I) - y‖ : ℂ) *
        Complex.exp (-(((-(m : ℤ) : ℤ) : ℂ) * θ * Complex.I)) = -(π * (y / r) ^ m / m) := by
  have ha : ‖conj y / r‖ < 1 := by
    rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hr.le,
      div_lt_one hr]
    exact hy
  rw [integral_log_norm_sub_of_factor ha (log_norm_sub_eq_of_lt hr hy),
    integral_log_norm_one_sub_neg ha hm]
  have : m ≠ 0 := by omega
  simp [this, map_div₀, Complex.conj_ofReal]

/-! ### Interior sectors (`r < |y|`) -/

theorem kernel_int_zero {r : ℝ} (hr : 0 ≤ r) {y : ℂ} (hy : r < ‖y‖) :
    ∫ θ in (0 : ℝ)..2 * π, (Real.log ‖(r : ℂ) * Complex.exp (θ * Complex.I) - y‖ : ℂ) *
        Complex.exp (-(((0 : ℤ) : ℂ) * θ * Complex.I)) = (Real.log ‖y‖ : ℂ) * (2 * π) := by
  have ha : ‖(r : ℂ) / y‖ < 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hr, div_lt_one (by linarith)]
    exact hy
  rw [integral_log_norm_sub_of_factor ha (log_norm_sub_eq_of_gt hr hy),
    integral_log_norm_one_sub_zero ha]
  simp

theorem kernel_int_pos {r : ℝ} (hr : 0 ≤ r) {y : ℂ} (hy : r < ‖y‖) {m : ℕ} (hm : 1 ≤ m) :
    ∫ θ in (0 : ℝ)..2 * π, (Real.log ‖(r : ℂ) * Complex.exp (θ * Complex.I) - y‖ : ℂ) *
        Complex.exp (-(((m : ℤ) : ℂ) * θ * Complex.I)) = -(π * ((r : ℂ) / y) ^ m / m) := by
  have ha : ‖(r : ℂ) / y‖ < 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hr, div_lt_one (by linarith)]
    exact hy
  rw [integral_log_norm_sub_of_factor ha (log_norm_sub_eq_of_gt hr hy),
    integral_log_norm_one_sub_pos ha hm]
  have : m ≠ 0 := by omega
  simp [this]

theorem kernel_int_neg {r : ℝ} (hr : 0 ≤ r) {y : ℂ} (hy : r < ‖y‖) {m : ℕ} (hm : 1 ≤ m) :
    ∫ θ in (0 : ℝ)..2 * π, (Real.log ‖(r : ℂ) * Complex.exp (θ * Complex.I) - y‖ : ℂ) *
        Complex.exp (-(((-(m : ℤ) : ℤ) : ℂ) * θ * Complex.I)) =
      -(π * ((r : ℂ) / conj y) ^ m / m) := by
  have ha : ‖(r : ℂ) / y‖ < 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hr, div_lt_one (by linarith)]
    exact hy
  rw [integral_log_norm_sub_of_factor ha (log_norm_sub_eq_of_gt hr hy),
    integral_log_norm_one_sub_neg ha hm]
  have : m ≠ 0 := by omega
  simp [this, map_div₀, Complex.conj_ofReal]

/-! ### Fubini -/

/-- Fubini for the angular sector of the logarithmic potential, under a uniform integrable
bound for `log|r e^{iθ} - y| g(y)`. -/
theorem angularSector_logPotential_eq {g : ℂ → ℂ} (hg : AEStronglyMeasurable g) (ℓ : ℤ) (r : ℝ)
    {G : ℂ → ℝ} (hG : Integrable G)
    (hbound : ∀ᵐ y, ∀ θ : ℝ,
      ‖(Real.log ‖(r : ℂ) * Complex.exp (θ * Complex.I) - y‖ : ℂ) * g y‖ ≤ G y) :
    angularSector (logPotential g) ℓ r =
      (2 * π : ℂ)⁻¹ * ((2 * π : ℂ)⁻¹ * ∫ y, g y *
        ∫ θ in (0 : ℝ)..2 * π, (Real.log ‖(r : ℂ) * Complex.exp (θ * Complex.I) - y‖ : ℂ) *
          Complex.exp (-((ℓ : ℂ) * θ * Complex.I))) := by
  unfold angularSector logPotential
  congr 1
  have h1 : ∀ θ : ℝ, (2 * π : ℂ)⁻¹ * (∫ y, (Real.log ‖(r : ℂ) * Complex.exp (θ * Complex.I) -
      y‖ : ℂ) * g y) * Complex.exp (-((ℓ : ℂ) * θ * Complex.I)) =
      (2 * π : ℂ)⁻¹ * ∫ y, (Real.log ‖(r : ℂ) * Complex.exp (θ * Complex.I) - y‖ : ℂ) * g y *
        Complex.exp (-((ℓ : ℂ) * θ * Complex.I)) := fun θ => by
    rw [mul_assoc, integral_mul_const]
  simp_rw [h1]
  rw [intervalIntegral.integral_const_mul]
  congr 1
  have hint : Integrable (Function.uncurry fun (θ : ℝ) (y : ℂ) =>
      (Real.log ‖(r : ℂ) * Complex.exp (θ * Complex.I) - y‖ : ℂ) * g y *
        Complex.exp (-((ℓ : ℂ) * θ * Complex.I)))
      ((volume.restrict (Ioc 0 (2 * π))).prod volume) := by
    refine Integrable.mono' (hG.comp_snd _) ?_ ?_
    · refine AEStronglyMeasurable.mul (AEStronglyMeasurable.mul ?_ hg.comp_snd) ?_
      · exact (Complex.measurable_ofReal.comp (Real.measurable_log.comp
          (by fun_prop : Continuous fun p : ℝ × ℂ =>
            ‖(r : ℂ) * Complex.exp (p.1 * Complex.I) - p.2‖).measurable)).aestronglyMeasurable
      · exact (by fun_prop : Continuous fun p : ℝ × ℂ =>
          Complex.exp (-((ℓ : ℂ) * p.1 * Complex.I))).aestronglyMeasurable
    · refine (Measure.quasiMeasurePreserving_snd.ae hbound).mono fun p hp => ?_
      simp only [Function.uncurry]
      rw [norm_mul, norm_exp_neg_int_mul, mul_one]
      exact hp p.1
  rw [intervalIntegral.integral_of_le (by positivity), integral_integral_swap hint]
  congr 1
  funext y
  rw [intervalIntegral.integral_of_le (by positivity), ← integral_const_mul]
  congr 1
  funext θ
  ring

end NonUniqueEuler.Multipole.LogPotentialH
