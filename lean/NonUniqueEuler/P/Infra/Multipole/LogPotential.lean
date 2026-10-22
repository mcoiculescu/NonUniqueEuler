import NonUniqueEuler.Defs.Infra.Multipole
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
import NonUniqueEuler.H.Infra.Multipole.LogPotential.Formula

/-!
# Proof: expansions of `log|x - y|` and angular sectors of the logarithmic potential (I-MULT)

Proof of `NonUniqueEuler/I/Infra/Multipole/LogPotential.lean` (`02_prelim.tex:461-469`).

* Expansions: `log|x - y| = log|x| + Re log(1 - y/x)` and the Taylor series of `-log(1 - w)`
  (`Complex.hasSum_taylorSeries_neg_log'`), mapped by `Re`.
* Sectors: Fubini (`LogPotentialH.angularSector_logPotential_ext/_int`, helper
  `H/Infra/Multipole/LogPotential/Formula.lean`) reduces `ψ_ℓ(r)` to
  `(2π)⁻¹ (2π)⁻¹ ∫ g(y) S_ℓ(y) dy`, with `S_ℓ(y) = ∫₀^{2π} log|r e^{iθ} - y| e^{-iℓθ} dθ`
  computed in `H/Infra/Multipole/LogPotential/Kernel.lean` (factorization
  `log|r e^{iθ} - y| = log r + log|1 - (ȳ/r) e^{iθ}|`, resp. `log|y| + log|1 - (r/y) e^{iθ}|`,
  and the Fourier coefficients of `log|1 - a e^{iθ}|` from
  `H/Infra/Multipole/LogPotential/Fourier.lean`).
-/

noncomputable section

open MeasureTheory Set Metric Real ComplexConjugate

namespace NonUniqueEuler.Multipole

open NonUniqueEuler.Polar

theorem hasSum_log_norm_sub_of_norm_lt {x y : ℂ} (h : ‖y‖ < ‖x‖) :
    HasSum (fun k : ℕ => ((y / x) ^ (k + 1)).re / (k + 1))
      (Real.log ‖x‖ - Real.log ‖x - y‖) := by
  have hx : x ≠ 0 := by
    intro hx
    rw [hx, norm_zero] at h
    exact absurd h (not_lt.2 (norm_nonneg y))
  have hw : ‖y / x‖ < 1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.2 hx)]
    exact h
  have hxy : x - y ≠ 0 := by
    intro e
    rw [sub_eq_zero] at e
    rw [e] at h
    exact lt_irrefl _ h
  have h1 := Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log' hw)
  have hval : (-Complex.log (1 - y / x)).re = Real.log ‖x‖ - Real.log ‖x - y‖ := by
    rw [Complex.neg_re, Complex.log_re, one_sub_div hx, norm_div,
      Real.log_div (norm_ne_zero_iff.2 hxy) (norm_ne_zero_iff.2 hx)]
    ring
  have hfun : ∀ k : ℕ, ((y / x) ^ (k + 1) / ((k : ℂ) + 1)).re =
      ((y / x) ^ (k + 1)).re / ((k : ℝ) + 1) := by
    intro k
    have : ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.div_ofReal_re]
  simp only [hfun, hval] at h1
  exact h1

theorem hasSum_log_norm_sub_of_norm_gt {x y : ℂ} (h : ‖x‖ < ‖y‖) :
    HasSum (fun k : ℕ => ((x / y) ^ (k + 1)).re / (k + 1))
      (Real.log ‖y‖ - Real.log ‖x - y‖) := by
  have := hasSum_log_norm_sub_of_norm_lt h
  rwa [norm_sub_rev] at this

/-- Exterior sectors `ℓ = m ≥ 1`: `ψ_m(r) = -(2m)⁻¹ pout_m r^{-m}`. -/
theorem angularSector_logPotential_exterior_pos {g : ℂ → ℂ} (hg : Integrable g) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hsupp : ∀ᵐ y, ρ < ‖y‖ → g y = 0) {m : ℕ} (hm : 1 ≤ m) {r : ℝ}
    (hr : ρ < r) :
    angularSector (logPotential g) m r =
      -((2 * (m : ℂ))⁻¹ * ((2 * π : ℂ)⁻¹ * conjMoment g m) / (r : ℂ) ^ m) := by
  have hr0 : 0 < r := lt_of_le_of_lt hρ hr
  rw [LogPotentialH.angularSector_logPotential_ext hg hρ hsupp hr (m : ℤ)
    (fun y => -(π * (conj y / r) ^ m / m))
    (fun y hy => LogPotentialH.kernel_ext_pos hr0 hy hm)]
  have hint : ∫ y, g y * -(π * (conj y / r) ^ m / m) =
      -(π / (m * (r : ℂ) ^ m)) * conjMoment g m := by
    rw [conjMoment, ← integral_const_mul]
    congr 1
    funext y
    rw [zpow_natCast, div_pow]
    ring
  rw [hint]
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  field_simp

/-- Exterior sectors `ℓ = -m ≤ -1`: `ψ_{-m}(r) = -(2m)⁻¹ (2π)⁻¹ Q_m r^{-m}`. -/
theorem angularSector_logPotential_exterior_neg {g : ℂ → ℂ} (hg : Integrable g) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hsupp : ∀ᵐ y, ρ < ‖y‖ → g y = 0) {m : ℕ} (hm : 1 ≤ m) {r : ℝ}
    (hr : ρ < r) :
    angularSector (logPotential g) (-(m : ℤ)) r =
      -((2 * (m : ℂ))⁻¹ * ((2 * π : ℂ)⁻¹ * moment g m) / (r : ℂ) ^ m) := by
  have hr0 : 0 < r := lt_of_le_of_lt hρ hr
  rw [LogPotentialH.angularSector_logPotential_ext hg hρ hsupp hr (-(m : ℤ))
    (fun y => -(π * (y / r) ^ m / m))
    (fun y hy => LogPotentialH.kernel_ext_neg hr0 hy hm)]
  have hint : ∫ y, g y * -(π * (y / r) ^ m / m) =
      -(π / (m * (r : ℂ) ^ m)) * moment g m := by
    rw [moment, ← integral_const_mul]
    congr 1
    funext y
    rw [zpow_natCast, div_pow]
    ring
  rw [hint]
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  field_simp

/-- Exterior sector `0`: `ψ_0(r) = (2π)⁻¹ (∫ g) log r`. -/
theorem angularSector_logPotential_exterior_zero {g : ℂ → ℂ} (hg : Integrable g) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hsupp : ∀ᵐ y, ρ < ‖y‖ → g y = 0) {r : ℝ} (hr : ρ < r) :
    angularSector (logPotential g) 0 r = (2 * π : ℂ)⁻¹ * (∫ y, g y) * (Real.log r : ℂ) := by
  have hr0 : 0 < r := lt_of_le_of_lt hρ hr
  have h := LogPotentialH.angularSector_logPotential_ext hg hρ hsupp hr (0 : ℤ)
    (fun _ => (Real.log r : ℂ) * (2 * π))
    (fun y hy => LogPotentialH.kernel_ext_zero hr0 hy)
  rw [h, integral_mul_const]
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- Interior sectors `ℓ = m ≥ 1`: `ψ_m(r) = -(2m)⁻¹ pin_m r^m`. -/
theorem angularSector_logPotential_interior_pos {g : ℂ → ℂ} (hg : Integrable g) {ρ : ℝ}
    (hsupp : ∀ᵐ y, ‖y‖ < ρ → g y = 0)
    (hlog : Integrable fun y => (Real.log ‖y‖ : ℂ) * g y) {m : ℕ} (hm : 1 ≤ m) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r < ρ) :
    angularSector (logPotential g) m r =
      -((2 * (m : ℂ))⁻¹ * ((2 * π : ℂ)⁻¹ * moment g (-(m : ℤ))) * (r : ℂ) ^ m) := by
  rw [LogPotentialH.angularSector_logPotential_int hg hsupp hlog hr0 hr (m : ℤ)
    (fun y => -(π * ((r : ℂ) / y) ^ m / m))
    (fun y hy => LogPotentialH.kernel_int_pos hr0 hy hm)]
  have hint : ∫ y, g y * -(π * ((r : ℂ) / y) ^ m / m) =
      -(π * (r : ℂ) ^ m / m) * moment g (-(m : ℤ)) := by
    rw [moment, ← integral_const_mul]
    congr 1
    funext y
    rw [zpow_neg, zpow_natCast, div_pow]
    ring
  rw [hint]
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  field_simp

/-- Interior sectors `ℓ = -m ≤ -1`: `ψ_{-m}(r) = -(2m)⁻¹ (2π)⁻¹ (∫ g ȳ^{-m}) r^m`. -/
theorem angularSector_logPotential_interior_neg {g : ℂ → ℂ} (hg : Integrable g) {ρ : ℝ}
    (hsupp : ∀ᵐ y, ‖y‖ < ρ → g y = 0)
    (hlog : Integrable fun y => (Real.log ‖y‖ : ℂ) * g y) {m : ℕ} (hm : 1 ≤ m) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r < ρ) :
    angularSector (logPotential g) (-(m : ℤ)) r =
      -((2 * (m : ℂ))⁻¹ * ((2 * π : ℂ)⁻¹ * conjMoment g (-(m : ℤ))) * (r : ℂ) ^ m) := by
  rw [LogPotentialH.angularSector_logPotential_int hg hsupp hlog hr0 hr (-(m : ℤ))
    (fun y => -(π * ((r : ℂ) / conj y) ^ m / m))
    (fun y hy => LogPotentialH.kernel_int_neg hr0 hy hm)]
  have hint : ∫ y, g y * -(π * ((r : ℂ) / conj y) ^ m / m) =
      -(π * (r : ℂ) ^ m / m) * conjMoment g (-(m : ℤ)) := by
    rw [conjMoment, ← integral_const_mul]
    congr 1
    funext y
    rw [zpow_neg, zpow_natCast, div_pow]
    ring
  rw [hint]
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  field_simp

/-- Interior sector `0`: `ψ_0(r) = (2π)⁻¹ ∫ g(y) log|y| dy`. -/
theorem angularSector_logPotential_interior_zero {g : ℂ → ℂ} (hg : Integrable g) {ρ : ℝ}
    (hsupp : ∀ᵐ y, ‖y‖ < ρ → g y = 0)
    (hlog : Integrable fun y => (Real.log ‖y‖ : ℂ) * g y) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < ρ) :
    angularSector (logPotential g) 0 r =
      (2 * π : ℂ)⁻¹ * ∫ y, (Real.log ‖y‖ : ℂ) * g y := by
  rw [LogPotentialH.angularSector_logPotential_int hg hsupp hlog hr0 hr (0 : ℤ)
    (fun y => (Real.log ‖y‖ : ℂ) * (2 * π))
    (fun y hy => LogPotentialH.kernel_int_zero hr0 hy)]
  have hint : ∫ y, g y * ((Real.log ‖y‖ : ℂ) * (2 * π)) =
      (2 * π) * ∫ y, (Real.log ‖y‖ : ℂ) * g y := by
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  rw [hint]
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

end NonUniqueEuler.Multipole
