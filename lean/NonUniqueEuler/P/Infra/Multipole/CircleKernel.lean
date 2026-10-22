import NonUniqueEuler.Defs.Infra.Multipole
import NonUniqueEuler.H.Infra.Multipole.CircleKernel.Fourier
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Proof: the angular Fourier coefficients of `log|r - ρe^{iθ}|` and of `ρ sin θ/|r - ρe^{iθ}|²`

Proof of `I/Infra/Multipole/CircleKernel.lean`.

* First formula. `|r - ρe^{iθ}| = |ρ - re^{iθ}|` (`norm_ofReal_sub_circleMap_comm`), so we may
  assume `ρ < r`; then `|r - ρe^{iθ}| = r|1 - (ρ/r)e^{iθ}|`, the constant `log r` integrates to
  `0` against `e^{iℓθ}` (`ℓ ≠ 0`), and the Fourier coefficients of `log|1 - a e^{iθ}|` are those
  of the helper `H/Infra/Multipole/CircleKernel/Fourier.lean`.
* Second formula. `F(θ) = log|r - ρe^{iθ}| = ½ log(r² - 2rρ cos θ + ρ²)` has
  `F'(θ) = rρ sin θ/|r - ρe^{iθ}|²`; integration by parts against `e^{iℓθ}` (the boundary terms
  cancel by periodicity) gives `r ∫ ρ sin θ/|·|² e^{iℓθ} = -iℓ ∫ F e^{iℓθ}`, and the first formula
  concludes (for `ℓ = 0` both sides vanish).
-/

noncomputable section

open MeasureTheory Set Real ComplexConjugate

namespace NonUniqueEuler.Multipole

namespace CircleKernelP

/-- `|r - ρe^{iθ}| = |ρ - re^{iθ}|` for real `r, ρ, θ`. -/
theorem norm_ofReal_sub_circleMap_comm (r ρ θ : ℝ) :
    ‖(r : ℂ) - circleMap 0 ρ θ‖ = ‖(ρ : ℂ) - circleMap 0 r θ‖ := by
  have h : Complex.exp (θ * Complex.I) * Complex.exp (θ * -Complex.I) = 1 := by
    rw [← Complex.exp_add, show (θ : ℂ) * Complex.I + θ * -Complex.I = 0 by ring,
      Complex.exp_zero]
  have key : (ρ : ℂ) - circleMap 0 r θ =
      -Complex.exp (θ * Complex.I) * conj ((r : ℂ) - circleMap 0 ρ θ) := by
    rw [circleMap_zero, circleMap_zero, map_sub, map_mul, Complex.conj_ofReal,
      Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    linear_combination (-(ρ : ℂ)) * h
  rw [key, norm_mul, norm_neg, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_conj]

/-- `R - s e^{iθ} = R (1 - (s/R) e^{iθ})` for `R ≠ 0`. -/
theorem ofReal_sub_circleMap_eq {R : ℝ} (hR : R ≠ 0) (s θ : ℝ) :
    (R : ℂ) - circleMap 0 s θ = R * (1 - ((s / R : ℝ) : ℂ) * Complex.exp (θ * Complex.I)) := by
  have hR' : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR
  rw [circleMap_zero]
  push_cast
  field_simp

/-- `log|R - s e^{iθ}| = log R + log|1 - (s/R) e^{iθ}|` for `0 ≤ s < R`. -/
theorem log_norm_ofReal_sub_circleMap {R s : ℝ} (hs : 0 ≤ s) (hsR : s < R) (θ : ℝ) :
    Real.log ‖(R : ℂ) - circleMap 0 s θ‖ =
      Real.log R + Real.log ‖1 - ((s / R : ℝ) : ℂ) * Complex.exp (θ * Complex.I)‖ := by
  have hR : 0 < R := lt_of_le_of_lt hs hsR
  have ha : ‖((s / R : ℝ) : ℂ) * Complex.exp (θ * Complex.I)‖ < 1 := by
    rw [CircleKernelH.norm_mul_exp_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hs hR.le), div_lt_one hR]
    exact hsR
  have hne : ‖1 - ((s / R : ℝ) : ℂ) * Complex.exp (θ * Complex.I)‖ ≠ 0 := by
    rw [norm_ne_zero_iff, sub_ne_zero]
    intro h
    rw [← h, norm_one] at ha
    exact lt_irrefl _ ha
  rw [ofReal_sub_circleMap_eq hR.ne' s θ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hR, Real.log_mul hR.ne' hne]

theorem continuous_log_norm_one_sub {a : ℝ} (ha : |a| < 1) :
    Continuous fun θ : ℝ => Real.log ‖1 - (a : ℂ) * Complex.exp (θ * Complex.I)‖ := by
  refine Continuous.log (by fun_prop) fun θ => ?_
  rw [norm_ne_zero_iff, sub_ne_zero]
  intro h
  have := congrArg norm h
  rw [norm_one, CircleKernelH.norm_mul_exp_I, Complex.norm_real, Real.norm_eq_abs] at this
  rw [← this] at ha
  exact lt_irrefl _ ha

/-- The first formula for `0 < s < R`. -/
theorem integral_log_norm_sub_circleMap_lt {R s : ℝ} (hs : 0 < s) (hsR : s < R) {ℓ : ℤ}
    (hℓ : ℓ ≠ 0) :
    ∫ θ in (0 : ℝ)..2 * π, (Real.log ‖(R : ℂ) - circleMap 0 s θ‖ : ℂ) *
        Complex.exp ((ℓ : ℂ) * θ * Complex.I) =
      -((π / ℓ.natAbs * (s / R) ^ ℓ.natAbs : ℝ) : ℂ) := by
  have hR : 0 < R := hs.trans hsR
  have ha : |s / R| < 1 := by
    rw [abs_of_pos (div_pos hs hR), div_lt_one hR]
    exact hsR
  have hfun : (fun θ : ℝ => (Real.log ‖(R : ℂ) - circleMap 0 s θ‖ : ℂ) *
        Complex.exp ((ℓ : ℂ) * θ * Complex.I)) =
      fun θ : ℝ => (Real.log R : ℂ) * Complex.exp ((ℓ : ℂ) * θ * Complex.I) +
        (Real.log ‖1 - ((s / R : ℝ) : ℂ) * Complex.exp (θ * Complex.I)‖ : ℂ) *
          Complex.exp ((ℓ : ℂ) * θ * Complex.I) := by
    funext θ
    rw [log_norm_ofReal_sub_circleMap hs.le hsR θ]
    push_cast
    ring
  have hc1 : Continuous fun θ : ℝ =>
      (Real.log R : ℂ) * Complex.exp ((ℓ : ℂ) * θ * Complex.I) := by fun_prop
  have hc2 : Continuous fun θ : ℝ =>
      (Real.log ‖1 - ((s / R : ℝ) : ℂ) * Complex.exp (θ * Complex.I)‖ : ℂ) *
        Complex.exp ((ℓ : ℂ) * θ * Complex.I) :=
    (Complex.continuous_ofReal.comp (continuous_log_norm_one_sub ha)).mul (by fun_prop)
  rw [hfun, intervalIntegral.integral_add (hc1.intervalIntegrable _ _)
    (hc2.intervalIntegrable _ _), intervalIntegral.integral_const_mul,
    CircleKernelH.integral_exp_int_mul, ite_eq_right hℓ, mul_zero, zero_add]
  exact CircleKernelH.integral_log_norm_one_sub_ofReal_mul_exp ha hℓ

/-- `|r - ρe^{iθ}|² = r² - 2rρ cos θ + ρ²`. -/
theorem sq_norm_ofReal_sub_circleMap (r ρ θ : ℝ) :
    ‖(r : ℂ) - circleMap 0 ρ θ‖ ^ 2 = r ^ 2 - 2 * r * ρ * Real.cos θ + ρ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, circleMap_zero]
  have hre : ((r : ℂ) - ρ * Complex.exp (θ * Complex.I)).re = r - ρ * Real.cos θ := by
    simp [Complex.exp_ofReal_mul_I_re]
  have him : ((r : ℂ) - ρ * Complex.exp (θ * Complex.I)).im = -(ρ * Real.sin θ) := by
    simp [Complex.exp_ofReal_mul_I_im]
  rw [hre, him]
  linear_combination ρ ^ 2 * Real.sin_sq_add_cos_sq θ

theorem norm_ofReal_sub_circleMap_pos {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r ≠ ρ)
    (θ : ℝ) : 0 < ‖(r : ℂ) - circleMap 0 ρ θ‖ := by
  refine norm_pos_iff.mpr (sub_ne_zero.mpr fun h => hrρ ?_)
  have := congrArg norm h
  rw [norm_circleMap_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
    abs_of_pos hρ] at this
  exact this

theorem continuous_norm_ofReal_sub_circleMap (r ρ : ℝ) :
    Continuous fun θ : ℝ => ‖(r : ℂ) - circleMap 0 ρ θ‖ := by
  have hcm : Continuous fun θ : ℝ => circleMap 0 ρ θ := by
    simp only [circleMap_zero]
    fun_prop
  exact (continuous_const.sub hcm).norm

/-- `d/dθ log|r - ρe^{iθ}| = rρ sin θ/|r - ρe^{iθ}|²` (`r, ρ > 0`, `r ≠ ρ`). -/
theorem hasDerivAt_log_norm_ofReal_sub_circleMap {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (hrρ : r ≠ ρ) (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => Real.log ‖(r : ℂ) - circleMap 0 ρ θ‖)
      (r * (ρ * Real.sin θ / ‖(r : ℂ) - circleMap 0 ρ θ‖ ^ 2)) θ := by
  have hfun : (fun θ : ℝ => Real.log ‖(r : ℂ) - circleMap 0 ρ θ‖) =
      fun θ : ℝ => Real.log (r ^ 2 - 2 * r * ρ * Real.cos θ + ρ ^ 2) / 2 := by
    funext θ
    rw [← sq_norm_ofReal_sub_circleMap, Real.log_pow]
    push_cast
    ring
  have hQ : HasDerivAt (fun θ : ℝ => r ^ 2 - 2 * r * ρ * Real.cos θ + ρ ^ 2)
      (2 * r * ρ * Real.sin θ) θ := by
    exact ((((Real.hasDerivAt_cos θ).const_mul (2 * r * ρ)).const_sub (r ^ 2)).add_const
      (ρ ^ 2)).congr_deriv (by ring)
  have hpos := norm_ofReal_sub_circleMap_pos hr hρ hrρ θ
  have hQ0 : r ^ 2 - 2 * r * ρ * Real.cos θ + ρ ^ 2 ≠ 0 := by
    rw [← sq_norm_ofReal_sub_circleMap]
    exact pow_ne_zero 2 hpos.ne'
  rw [hfun]
  refine ((hQ.log hQ0).div_const 2).congr_deriv ?_
  rw [← sq_norm_ofReal_sub_circleMap]
  field_simp

/-- Integration by parts: `r ∫ ρ sin θ/|r - ρe^{iθ}|² e^{iℓθ} = -iℓ ∫ log|r - ρe^{iθ}| e^{iℓθ}`. -/
theorem integral_sin_div_eq_integral_log {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r ≠ ρ)
    (ℓ : ℤ) :
    (r : ℂ) * ∫ θ in (0 : ℝ)..2 * π,
        ((ρ * Real.sin θ / ‖(r : ℂ) - circleMap 0 ρ θ‖ ^ 2 : ℝ) : ℂ) *
          Complex.exp ((ℓ : ℂ) * θ * Complex.I) =
      -((ℓ : ℂ) * Complex.I * ∫ θ in (0 : ℝ)..2 * π,
        (Real.log ‖(r : ℂ) - circleMap 0 ρ θ‖ : ℂ) * Complex.exp ((ℓ : ℂ) * θ * Complex.I)) := by
  have hu : ∀ x ∈ uIcc (0 : ℝ) (2 * π),
      HasDerivAt (fun θ : ℝ => ((Real.log ‖(r : ℂ) - circleMap 0 ρ θ‖ : ℝ) : ℂ))
        (((r * (ρ * Real.sin x / ‖(r : ℂ) - circleMap 0 ρ x‖ ^ 2)) : ℝ) : ℂ) x :=
    fun x _ => (hasDerivAt_log_norm_ofReal_sub_circleMap hr hρ hrρ x).ofReal_comp
  have hv : ∀ x ∈ uIcc (0 : ℝ) (2 * π),
      HasDerivAt (fun θ : ℝ => Complex.exp ((ℓ : ℂ) * θ * Complex.I))
        (Complex.exp ((ℓ : ℂ) * x * Complex.I) * ((ℓ : ℂ) * Complex.I)) x := by
    intro x _
    have h1 : HasDerivAt (fun θ : ℝ => (ℓ : ℂ) * (θ : ℂ) * Complex.I) ((ℓ : ℂ) * Complex.I) x := by
      exact (((hasDerivAt_id' x).ofReal_comp.const_mul (ℓ : ℂ)).mul_const Complex.I).congr_deriv
        (by push_cast; ring)
    exact h1.cexp
  have hcont : Continuous fun x : ℝ =>
      r * (ρ * Real.sin x / ‖(r : ℂ) - circleMap 0 ρ x‖ ^ 2) :=
    continuous_const.mul ((continuous_const.mul Real.continuous_sin).div
      ((continuous_norm_ofReal_sub_circleMap r ρ).pow 2)
      fun x => pow_ne_zero 2 (norm_ofReal_sub_circleMap_pos hr hρ hrρ x).ne')
  have hu' : IntervalIntegrable
      (fun x : ℝ => (((r * (ρ * Real.sin x / ‖(r : ℂ) - circleMap 0 ρ x‖ ^ 2)) : ℝ) : ℂ))
      volume 0 (2 * π) :=
    (Complex.continuous_ofReal.comp hcont).intervalIntegrable _ _
  have hv' : IntervalIntegrable
      (fun x : ℝ => Complex.exp ((ℓ : ℂ) * x * Complex.I) * ((ℓ : ℂ) * Complex.I))
      volume 0 (2 * π) :=
    (by fun_prop : Continuous fun x : ℝ =>
      Complex.exp ((ℓ : ℂ) * x * Complex.I) * ((ℓ : ℂ) * Complex.I)).intervalIntegrable _ _
  have ibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  have hv2 : Complex.exp ((ℓ : ℂ) * ((2 * π : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_int_mul_two_pi_mul_I ℓ]
    congr 1
    push_cast
    ring
  have hv0 : Complex.exp ((ℓ : ℂ) * ((0 : ℝ) : ℂ) * Complex.I) = 1 := by simp
  have hu2 : circleMap 0 ρ (2 * π) = circleMap 0 ρ 0 := (periodic_circleMap 0 ρ).eq
  simp only [hv2, hv0, hu2, mul_one, sub_self, zero_sub] at ibp
  have hL : (∫ x in (0 : ℝ)..2 * π, ((Real.log ‖(r : ℂ) - circleMap 0 ρ x‖ : ℝ) : ℂ) *
      (Complex.exp ((ℓ : ℂ) * x * Complex.I) * ((ℓ : ℂ) * Complex.I))) =
      (ℓ : ℂ) * Complex.I * ∫ θ in (0 : ℝ)..2 * π,
        (Real.log ‖(r : ℂ) - circleMap 0 ρ θ‖ : ℂ) * Complex.exp ((ℓ : ℂ) * θ * Complex.I) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext x
    ring
  have hR : (∫ x in (0 : ℝ)..2 * π,
      (((r * (ρ * Real.sin x / ‖(r : ℂ) - circleMap 0 ρ x‖ ^ 2)) : ℝ) : ℂ) *
        Complex.exp ((ℓ : ℂ) * x * Complex.I)) =
      (r : ℂ) * ∫ θ in (0 : ℝ)..2 * π,
        ((ρ * Real.sin θ / ‖(r : ℂ) - circleMap 0 ρ θ‖ ^ 2 : ℝ) : ℂ) *
          Complex.exp ((ℓ : ℂ) * θ * Complex.I) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext x
    push_cast
    ring
  rw [hL, hR] at ibp
  rw [ibp, neg_neg]

end CircleKernelP

open CircleKernelP in
/-- `∫₀^{2π} log|r - ρe^{iθ}| e^{iℓθ} dθ = -(π/|ℓ|) (min(r,ρ)/max(r,ρ))^{|ℓ|}` for `r, ρ > 0`,
`r ≠ ρ`, `ℓ ≠ 0`. -/
theorem intervalIntegral_log_norm_sub_circleMap_mul_exp {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (hrρ : r ≠ ρ) {ℓ : ℤ} (hℓ : ℓ ≠ 0) :
    ∫ θ in (0 : ℝ)..2 * π, (Real.log ‖(r : ℂ) - circleMap 0 ρ θ‖ : ℂ) *
        Complex.exp ((ℓ : ℂ) * θ * Complex.I) =
      -((π / ℓ.natAbs * (min r ρ / max r ρ) ^ ℓ.natAbs : ℝ) : ℂ) := by
  rcases lt_or_gt_of_ne hrρ with h | h
  · rw [min_eq_left h.le, max_eq_right h.le]
    simp_rw [norm_ofReal_sub_circleMap_comm r ρ]
    exact integral_log_norm_sub_circleMap_lt hr h hℓ
  · rw [min_eq_right h.le, max_eq_left h.le]
    exact integral_log_norm_sub_circleMap_lt hρ h hℓ

open CircleKernelP in
/-- `∫₀^{2π} ρ sin θ/|r - ρe^{iθ}|² · e^{iℓθ} dθ = iπ sgn(ℓ) (min(r,ρ)/max(r,ρ))^{|ℓ|} / r` for
`r, ρ > 0`, `r ≠ ρ` and every `ℓ` (both sides vanish for `ℓ = 0`). -/
theorem intervalIntegral_sin_div_norm_sub_circleMap_sq_mul_exp {r ρ : ℝ} (hr : 0 < r)
    (hρ : 0 < ρ) (hrρ : r ≠ ρ) (ℓ : ℤ) :
    ∫ θ in (0 : ℝ)..2 * π, ((ρ * Real.sin θ / ‖(r : ℂ) - circleMap 0 ρ θ‖ ^ 2 : ℝ) : ℂ) *
        Complex.exp ((ℓ : ℂ) * θ * Complex.I) =
      Complex.I * π * (Int.sign ℓ : ℂ) * (((min r ρ / max r ρ) ^ ℓ.natAbs / r : ℝ) : ℂ) := by
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have key := integral_sin_div_eq_integral_log hr hρ hrρ ℓ
  refine mul_left_cancel₀ hr' ?_
  rw [key]
  by_cases hℓ : ℓ = 0
  · subst hℓ
    simp
  · rw [intervalIntegral_log_norm_sub_circleMap_mul_exp hr hρ hrρ hℓ]
    have hs : (ℓ : ℂ) = (Int.sign ℓ : ℂ) * (ℓ.natAbs : ℂ) := by
      have h := congrArg (fun z : ℤ => (z : ℂ)) (Int.sign_mul_natAbs ℓ).symm
      simp only [Int.cast_mul, Int.cast_natCast] at h
      exact h
    have hn : (ℓ.natAbs : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Int.natAbs_ne_zero.mpr hℓ)
    rw [hs]
    push_cast
    field_simp

end NonUniqueEuler.Multipole
