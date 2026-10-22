import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Helper: Fourier coefficients of `θ ↦ log|1 - a e^{iθ}|` (for `P/Infra/Multipole/CircleKernel`)

Adapted from `H/Infra/Multipole/LogPotential/Fourier.lean` (helper files may not be
imported across proofs, so the computation is repeated here in its own namespace).

For `‖a‖ < 1`, `log(1 - a e^{iθ}) = -∑_{k ≥ 1} a^k e^{ikθ}/k` uniformly in `θ`; termwise
integration against `e^{-inθ}` gives `∫₀^{2π} log(1 - a e^{iθ}) e^{-inθ} dθ = -2π a^n/n` for
`n ≥ 1` and `0` for `n ≤ 0`. Taking real parts (`log|z| = Re log z = (log z + conj log z)/2`):
* `∫₀^{2π} log|1 - a e^{iθ}| e^{-imθ} dθ = -π a^m/m` (`m ≥ 1`);
* `∫₀^{2π} log|1 - a e^{iθ}| e^{imθ} dθ = -π ā^m/m` (`m ≥ 1`);
* for real `a`, `|a| < 1`, `ℓ ≠ 0`: `∫₀^{2π} log|1 - a e^{iθ}| e^{iℓθ} dθ = -(π/|ℓ|) a^{|ℓ|}`.
This is the computation of the text after `def:multipole` (`02_prelim.tex:461-469`).
-/

noncomputable section

open MeasureTheory Set Real ComplexConjugate

namespace NonUniqueEuler.Multipole.CircleKernelH

/-- `∫₀^{2π} e^{ijθ} dθ = 2π [j = 0]`. -/
theorem integral_exp_int_mul (j : ℤ) :
    ∫ θ in (0 : ℝ)..2 * π, Complex.exp ((j : ℂ) * θ * Complex.I) =
      if j = 0 then 2 * (π : ℂ) else 0 := by
  by_cases hj : j = 0
  · subst hj
    simp
  · rw [ite_eq_right hj]
    have hc : (j : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (Int.cast_ne_zero.mpr hj) Complex.I_ne_zero
    have hfun : (fun θ : ℝ => Complex.exp ((j : ℂ) * θ * Complex.I)) =
        fun θ : ℝ => Complex.exp ((j : ℂ) * Complex.I * θ) := by
      funext θ; ring_nf
    rw [hfun, integral_exp_mul_complex hc]
    have h1 : Complex.exp ((j : ℂ) * Complex.I * ((2 * π : ℝ) : ℂ)) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I j]
      congr 1
      push_cast
      ring
    rw [h1]
    simp

theorem norm_exp_neg_int_mul (ℓ : ℤ) (θ : ℝ) :
    ‖Complex.exp (-((ℓ : ℂ) * θ * Complex.I))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- `log(1 - w) = -∑_{k ≥ 0} w^{k+1}/(k+1)` for `‖w‖ < 1`. -/
theorem hasSum_log_one_sub {w : ℂ} (hw : ‖w‖ < 1) :
    HasSum (fun k : ℕ => -(w ^ (k + 1) / (k + 1))) (Complex.log (1 - w)) := by
  simpa using (Complex.hasSum_taylorSeries_neg_log' hw).neg

theorem one_sub_mem_slitPlane {w : ℂ} (hw : ‖w‖ < 1) : 1 - w ∈ Complex.slitPlane := by
  have := Complex.mem_slitPlane_of_norm_lt_one (z := -w) (by simpa using hw)
  simpa [sub_eq_add_neg] using this

theorem norm_mul_exp_I (a : ℂ) (θ : ℝ) : ‖a * Complex.exp (θ * Complex.I)‖ = ‖a‖ := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

theorem continuous_log_one_sub {a : ℂ} (ha : ‖a‖ < 1) :
    Continuous fun θ : ℝ => Complex.log (1 - a * Complex.exp (θ * Complex.I)) := by
  refine Continuous.clog (by fun_prop) fun θ => one_sub_mem_slitPlane ?_
  rw [norm_mul_exp_I]
  exact ha

/-- The term of the termwise-integrated series. -/
theorem term_eq (a : ℂ) (n : ℤ) (k : ℕ) (θ : ℝ) :
    -((a * Complex.exp (θ * Complex.I)) ^ (k + 1) / (k + 1)) *
        Complex.exp (-((n : ℂ) * θ * Complex.I)) =
      -(a ^ (k + 1) / (k + 1)) *
        Complex.exp ((((k : ℤ) + 1 - n : ℤ) : ℂ) * θ * Complex.I) := by
  rw [mul_pow, ← Complex.exp_nat_mul]
  have : Complex.exp ((((k : ℤ) + 1 - n : ℤ) : ℂ) * θ * Complex.I) =
      Complex.exp (((k + 1 : ℕ) : ℂ) * (θ * Complex.I)) *
        Complex.exp (-((n : ℂ) * θ * Complex.I)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [this]
  push_cast
  ring

/-- Termwise integration: the Fourier coefficients of `θ ↦ log(1 - a e^{iθ})`. -/
theorem hasSum_integral_log_one_sub_mul_exp {a : ℂ} (ha : ‖a‖ < 1) (n : ℤ) :
    HasSum (fun k : ℕ => -(a ^ (k + 1) / (k + 1)) *
        (if (k : ℤ) + 1 - n = 0 then 2 * (π : ℂ) else 0))
      (∫ θ in (0 : ℝ)..2 * π, Complex.log (1 - a * Complex.exp (θ * Complex.I)) *
        Complex.exp (-((n : ℂ) * θ * Complex.I))) := by
  have key := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (a := 0) (b := 2 * π)
    (F := fun (k : ℕ) (θ : ℝ) => -((a * Complex.exp (θ * Complex.I)) ^ (k + 1) / (k + 1)) *
        Complex.exp (-((n : ℂ) * θ * Complex.I)))
    (f := fun θ : ℝ => Complex.log (1 - a * Complex.exp (θ * Complex.I)) *
        Complex.exp (-((n : ℂ) * θ * Complex.I)))
    (fun k _ => ‖a‖ ^ (k + 1)) ?_ ?_ ?_ ?_ ?_
  · have hfun : ∀ k : ℕ, (∫ θ in (0 : ℝ)..2 * π,
        -((a * Complex.exp (θ * Complex.I)) ^ (k + 1) / (k + 1)) *
          Complex.exp (-((n : ℂ) * θ * Complex.I))) =
        -(a ^ (k + 1) / (k + 1)) * (if (k : ℤ) + 1 - n = 0 then 2 * (π : ℂ) else 0) := by
      intro k
      simp_rw [term_eq a n k]
      rw [intervalIntegral.integral_const_mul, integral_exp_int_mul]
    simp_rw [hfun] at key
    exact key
  · intro k
    exact (by fun_prop : Continuous fun θ : ℝ =>
      -((a * Complex.exp (θ * Complex.I)) ^ (k + 1) / (k + 1)) *
        Complex.exp (-((n : ℂ) * θ * Complex.I))).aestronglyMeasurable
  · intro k
    refine ae_of_all _ fun θ _ => ?_
    rw [norm_mul, norm_exp_neg_int_mul, mul_one, norm_neg, norm_div, norm_pow, norm_mul_exp_I]
    have h1 : (1 : ℝ) ≤ ‖((k : ℂ) + 1)‖ := by
      have : ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_natCast]
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    exact div_le_self (by positivity) h1
  · exact ae_of_all _ fun θ _ =>
      ((summable_geometric_of_lt_one (norm_nonneg a) ha).mul_left ‖a‖).congr fun k => by ring
  · exact intervalIntegrable_const
  · refine ae_of_all _ fun θ _ => ?_
    have hw : ‖a * Complex.exp (θ * Complex.I)‖ < 1 := by rw [norm_mul_exp_I]; exact ha
    exact (hasSum_log_one_sub hw).mul_right _

/-- `∫₀^{2π} log(1 - a e^{iθ}) e^{-imθ} dθ = -2π a^m/m` for `m ≥ 1`. -/
theorem integral_log_one_sub_mul_exp_pos {a : ℂ} (ha : ‖a‖ < 1) {m : ℕ} (hm : 1 ≤ m) :
    ∫ θ in (0 : ℝ)..2 * π, Complex.log (1 - a * Complex.exp (θ * Complex.I)) *
        Complex.exp (-(((m : ℤ) : ℂ) * θ * Complex.I)) =
      -(a ^ m / m) * (2 * π) := by
  refine (hasSum_integral_log_one_sub_mul_exp ha m).unique ?_
  have hfun : (fun k : ℕ => -(a ^ (k + 1) / (k + 1)) *
      (if (k : ℤ) + 1 - (m : ℤ) = 0 then 2 * (π : ℂ) else 0)) =
      fun k => if k = m - 1 then -(a ^ m / m) * (2 * π) else 0 := by
    funext k
    by_cases hk : k = m - 1
    · have h1 : (k : ℤ) + 1 - (m : ℤ) = 0 := by omega
      have h2 : k + 1 = m := by omega
      rw [ite_eq_left h1, ite_eq_left hk]
      subst h2
      push_cast
      ring
    · have h1 : ¬ ((k : ℤ) + 1 - (m : ℤ) = 0) := by omega
      rw [ite_eq_right h1, ite_eq_right hk, mul_zero]
  rw [hfun]
  exact hasSum_ite_eq (m - 1) _

/-- `∫₀^{2π} log(1 - a e^{iθ}) e^{-inθ} dθ = 0` for `n ≤ 0`. -/
theorem integral_log_one_sub_mul_exp_nonpos {a : ℂ} (ha : ‖a‖ < 1) {n : ℤ} (hn : n ≤ 0) :
    ∫ θ in (0 : ℝ)..2 * π, Complex.log (1 - a * Complex.exp (θ * Complex.I)) *
        Complex.exp (-((n : ℂ) * θ * Complex.I)) = 0 := by
  refine (hasSum_integral_log_one_sub_mul_exp ha n).unique ?_
  have hfun : (fun k : ℕ => -(a ^ (k + 1) / (k + 1)) *
      (if (k : ℤ) + 1 - n = 0 then 2 * (π : ℂ) else 0)) = fun _ => 0 := by
    funext k
    have h1 : ¬ ((k : ℤ) + 1 - n = 0) := by omega
    rw [ite_eq_right h1, mul_zero]
  rw [hfun]
  exact hasSum_zero

/-- `log|z| = (log z + conj (log z))/2` as complex numbers. -/
theorem ofReal_log_norm (z : ℂ) :
    (Real.log ‖z‖ : ℂ) = (Complex.log z + conj (Complex.log z)) / 2 := by
  rw [← Complex.log_re, Complex.re_eq_add_conj]

/-- `∫₀^{2π} log|1 - a e^{iθ}| e^{-iℓθ} dθ` in terms of the Fourier coefficients of
`log(1 - a e^{iθ})` of orders `ℓ` and `-ℓ`. -/
theorem integral_log_norm_one_sub_mul_exp {a : ℂ} (ha : ‖a‖ < 1) (ℓ : ℤ) :
    ∫ θ in (0 : ℝ)..2 * π, (Real.log ‖1 - a * Complex.exp (θ * Complex.I)‖ : ℂ) *
        Complex.exp (-((ℓ : ℂ) * θ * Complex.I)) =
      ((∫ θ in (0 : ℝ)..2 * π, Complex.log (1 - a * Complex.exp (θ * Complex.I)) *
          Complex.exp (-((ℓ : ℂ) * θ * Complex.I))) +
        conj (∫ θ in (0 : ℝ)..2 * π, Complex.log (1 - a * Complex.exp (θ * Complex.I)) *
          Complex.exp (-(((-ℓ : ℤ) : ℂ) * θ * Complex.I)))) / 2 := by
  have hL := continuous_log_one_sub ha
  have hc1 : Continuous fun θ : ℝ => Complex.log (1 - a * Complex.exp (θ * Complex.I)) *
      Complex.exp (-((ℓ : ℂ) * θ * Complex.I)) := hL.mul (by fun_prop)
  have hc2 : Continuous fun θ : ℝ => conj (Complex.log (1 - a * Complex.exp (θ * Complex.I))) *
      Complex.exp (-((ℓ : ℂ) * θ * Complex.I)) :=
    (Complex.continuous_conj.comp hL).mul (by fun_prop)
  have hconj : ∀ θ : ℝ, conj (Complex.log (1 - a * Complex.exp (θ * Complex.I))) *
      Complex.exp (-((ℓ : ℂ) * θ * Complex.I)) =
      conj (Complex.log (1 - a * Complex.exp (θ * Complex.I)) *
        Complex.exp (-(((-ℓ : ℤ) : ℂ) * θ * Complex.I))) := by
    intro θ
    rw [map_mul, ← Complex.exp_conj]
    congr 2
    simp [Complex.conj_ofReal]
  simp_rw [ofReal_log_norm, div_mul_eq_mul_div, add_mul]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)]
  simp_rw [hconj]
  rw [intervalIntegral.intervalIntegral_conj]

/-- `∫₀^{2π} log|1 - a e^{iθ}| e^{-imθ} dθ = -π a^m/m` for `m ≥ 1`. -/
theorem integral_log_norm_one_sub_pos {a : ℂ} (ha : ‖a‖ < 1) {m : ℕ} (hm : 1 ≤ m) :
    ∫ θ in (0 : ℝ)..2 * π, (Real.log ‖1 - a * Complex.exp (θ * Complex.I)‖ : ℂ) *
        Complex.exp (-(((m : ℤ) : ℂ) * θ * Complex.I)) = -(π * a ^ m / m) := by
  rw [integral_log_norm_one_sub_mul_exp ha, integral_log_one_sub_mul_exp_pos ha hm,
    integral_log_one_sub_mul_exp_nonpos ha (by omega)]
  simp only [map_zero, add_zero]
  ring

/-- `∫₀^{2π} log|1 - a e^{iθ}| e^{imθ} dθ = -π ā^m/m` for `m ≥ 1`. -/
theorem integral_log_norm_one_sub_neg {a : ℂ} (ha : ‖a‖ < 1) {m : ℕ} (hm : 1 ≤ m) :
    ∫ θ in (0 : ℝ)..2 * π, (Real.log ‖1 - a * Complex.exp (θ * Complex.I)‖ : ℂ) *
        Complex.exp (-(((-(m : ℤ) : ℤ) : ℂ) * θ * Complex.I)) = -(π * conj a ^ m / m) := by
  rw [integral_log_norm_one_sub_mul_exp ha, neg_neg, integral_log_one_sub_mul_exp_pos ha hm,
    integral_log_one_sub_mul_exp_nonpos ha (by omega)]
  simp only [map_neg, map_mul, map_div₀, map_pow, map_natCast, Complex.conj_ofReal, map_ofNat,
    zero_add]
  ring

/-- For real `a` with `|a| < 1` and `ℓ ≠ 0`:
`∫₀^{2π} log|1 - a e^{iθ}| e^{iℓθ} dθ = -(π/|ℓ|) a^{|ℓ|}`. -/
theorem integral_log_norm_one_sub_ofReal_mul_exp {a : ℝ} (ha : |a| < 1) {ℓ : ℤ} (hℓ : ℓ ≠ 0) :
    ∫ θ in (0 : ℝ)..2 * π, (Real.log ‖1 - (a : ℂ) * Complex.exp (θ * Complex.I)‖ : ℂ) *
        Complex.exp ((ℓ : ℂ) * θ * Complex.I) =
      -((π / ℓ.natAbs * a ^ ℓ.natAbs : ℝ) : ℂ) := by
  have ha' : ‖(a : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_eq_abs]
  have hm : 1 ≤ ℓ.natAbs := Int.natAbs_pos.mpr hℓ
  rcases lt_or_gt_of_ne hℓ with hneg | hpos
  · have hℓm : ℓ = -((ℓ.natAbs : ℕ) : ℤ) := by omega
    calc ∫ θ in (0 : ℝ)..2 * π, (Real.log ‖1 - (a : ℂ) * Complex.exp (θ * Complex.I)‖ : ℂ) *
          Complex.exp ((ℓ : ℂ) * θ * Complex.I)
        = ∫ θ in (0 : ℝ)..2 * π,
            (Real.log ‖1 - (a : ℂ) * Complex.exp (θ * Complex.I)‖ : ℂ) *
              Complex.exp (-((((ℓ.natAbs : ℕ) : ℤ) : ℂ) * θ * Complex.I)) := by
          congr 1
          funext θ
          congr 2
          conv_lhs => rw [hℓm]
          push_cast
          ring
      _ = -(π * (a : ℂ) ^ ℓ.natAbs / ℓ.natAbs) := integral_log_norm_one_sub_pos ha' hm
      _ = -((π / ℓ.natAbs * a ^ ℓ.natAbs : ℝ) : ℂ) := by
          push_cast
          ring
  · have hℓm : ℓ = ((ℓ.natAbs : ℕ) : ℤ) := by omega
    calc ∫ θ in (0 : ℝ)..2 * π, (Real.log ‖1 - (a : ℂ) * Complex.exp (θ * Complex.I)‖ : ℂ) *
          Complex.exp ((ℓ : ℂ) * θ * Complex.I)
        = ∫ θ in (0 : ℝ)..2 * π,
            (Real.log ‖1 - (a : ℂ) * Complex.exp (θ * Complex.I)‖ : ℂ) *
              Complex.exp (-(((-((ℓ.natAbs : ℕ) : ℤ) : ℤ) : ℂ) * θ * Complex.I)) := by
          congr 1
          funext θ
          congr 2
          conv_lhs => rw [hℓm]
          push_cast
          ring
      _ = -(π * conj (a : ℂ) ^ ℓ.natAbs / ℓ.natAbs) := integral_log_norm_one_sub_neg ha' hm
      _ = -((π / ℓ.natAbs * a ^ ℓ.natAbs : ℝ) : ℂ) := by
          rw [Complex.conj_ofReal]
          push_cast
          ring

end NonUniqueEuler.Multipole.CircleKernelH
