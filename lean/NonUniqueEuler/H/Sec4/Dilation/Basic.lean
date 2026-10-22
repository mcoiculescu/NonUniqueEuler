import NonUniqueEuler.Defs.Sec4.Evans
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Helpers for `lem:dilation`: the elementary scaling identities

Helper of `P/Sec4/Dilation.lean` (`lem:dilation`, `04_ring.tex:653-712`). All lemmas are
pointwise identities or changes of variables that hold unconditionally (Lean's Bochner integral
is `0` for non-integrable functions on both sides).

* `DilationH.dilate_dom`: `ω̄_R'(r) = R ω̄'(Rr)`;
* `DilationH.circ_dilate`: `Circ_{ω̄_R}(r) = R⁻² Circ_{ω̄}(Rr)`;
* `DilationH.Omega_dilate`: `Ω^{ω̄_R}(r;G) = Ω^{ω̄}(Rr;R²G)`;
* `DilationH.kcoef_dilate`: `k^{ω̄_R}_ℓ(r) = R² k^{ω̄}_ℓ(Rr)`;
* `DilationH.green_comp_mul`: `𝒢_ℓ(g(R·))(r) = R⁻² (𝒢_ℓ g)(Rr)`;
* `DilationH.fxi_dilate`, `Vric_dilate`, `Mres_dilate`, `bfun_dilate`;
* `DilationH.integral_Ioi_comp_mul`: `∫_0^∞ f(Rρ) dρ = R⁻¹ ∫_0^∞ f`;
* `DilationH.l2_comp_mul`: `‖f(R·)‖_{L²(ℝ²)} = R⁻¹ ‖f‖_{L²(ℝ²)}`;
* `DilationH.biotSavartKernel_mul`: `K(Rz) = R⁻¹ K(z)`.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace DilationH

open SectorSetting

variable (S : SectorSetting)

theorem dilate_omR (R r : ℝ) : (S.dilate R).omR r = S.omR (R * r) := by
  simp only [omR, dilate, Complex.ofReal_mul]

theorem dilate_dom (R r : ℝ) : (S.dilate R).dom r = R * S.dom (R * r) := by
  have h : (S.dilate R).omR = fun r => S.omR (R * r) := funext (dilate_omR S R)
  simp only [dom, h]
  rw [deriv_comp_mul_left R S.omR r, smul_eq_mul]

theorem circ_dilate {R : ℝ} (hR : 0 < R) (r : ℝ) :
    Polar.circ (S.dilate R).om r = (R ^ 2)⁻¹ * Polar.circ S.om (R * r) := by
  simp only [Polar.circ, dilate]
  have h1 : (fun y : ℂ => S.om ((R : ℂ) * y)) = fun y => S.om (R • y) := by
    funext y
    rw [Complex.real_smul]
  rw [h1, Measure.setIntegral_comp_smul_of_pos volume (fun y => S.om y) (ball (0 : ℂ) r) hR,
    _root_.smul_ball hR.ne', smul_zero, Real.norm_eq_abs, abs_of_pos hR, Complex.finrank_real_complex,
    smul_eq_mul]

theorem Omega_dilate {R : ℝ} (hR : 0 < R) (G r : ℝ) :
    (S.dilate R).Omega G r = S.Omega (R ^ 2 * G) (R * r) := by
  simp only [Omega, circ_dilate S hR]
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  have hR0 : R ≠ 0 := hR.ne'
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

theorem kcoef_dilate {R : ℝ} (hR : 0 < R) (ℓ : ℤ) (r : ℝ) :
    (S.dilate R).kcoef ℓ r = ((R ^ 2 : ℝ) : ℂ) * S.kcoef ℓ (R * r) := by
  simp only [kcoef, dilate_dom]
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  have hR0 : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR.ne'
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr
  push_cast
  field_simp

theorem minmax_mul {R : ℝ} (hR : 0 < R) (r ρ : ℝ) :
    min (R * r) (R * ρ) / max (R * r) (R * ρ) = min r ρ / max r ρ := by
  rw [← mul_min_of_nonneg _ _ hR.le, ← mul_max_of_nonneg _ _ hR.le,
    mul_div_mul_left _ _ hR.ne']

/-- `∫_0^∞ f(Rρ) dρ = R⁻¹ ∫_0^∞ f` for complex-valued `f` (unconditional). -/
theorem integral_Ioi_comp_mul (f : ℝ → ℂ) {R : ℝ} (hR : 0 < R) :
    ∫ ρ in Ioi (0 : ℝ), f (R * ρ) = ((R⁻¹ : ℝ) : ℂ) * ∫ u in Ioi (0 : ℝ), f u := by
  rw [integral_comp_mul_left_Ioi f 0 hR, mul_zero, Complex.real_smul]

theorem green_comp_mul (ℓ : ℤ) (g : ℝ → ℂ) {R : ℝ} (hR : 0 < R) (r : ℝ) :
    green ℓ (fun ρ => g (R * ρ)) r = (((R ^ 2)⁻¹ : ℝ) : ℂ) * green ℓ g (R * r) := by
  simp only [green]
  have hR0 : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR.ne'
  have h1 : (fun ρ : ℝ => (((min r ρ / max r ρ) ^ ℓ.natAbs : ℝ) : ℂ) * g (R * ρ) * (ρ : ℂ)) =
      fun ρ => ((R⁻¹ : ℝ) : ℂ) *
        ((((min (R * r) (R * ρ) / max (R * r) (R * ρ)) ^ ℓ.natAbs : ℝ) : ℂ) * g (R * ρ) *
          ((R * ρ : ℝ) : ℂ)) := by
    funext ρ
    rw [minmax_mul hR]
    push_cast
    field_simp
  rw [h1, integral_const_mul,
    integral_Ioi_comp_mul
      (fun u => (((min (R * r) u / max (R * r) u) ^ ℓ.natAbs : ℝ) : ℂ) * g u * (u : ℂ)) hR]
  push_cast
  ring

theorem fxi_dilate {R : ℝ} (hR : 0 < R) (ξ : ℝ) :
    (S.dilate R).fxi ξ = S.fxi (ξ + Real.log R) := by
  simp only [fxi, dilate_dom, Real.exp_add, Real.exp_log hR]
  ring_nf

theorem Vric_dilate {R : ℝ} (hR : 0 < R) (ℓ : ℕ) (z : ℂ) (G ξ : ℝ) :
    (S.dilate R).Vric ℓ z G ξ = S.Vric ℓ z (R ^ 2 * G) (ξ + Real.log R) := by
  simp only [Vric, fxi_dilate S hR, Omega_dilate S hR, Real.exp_add, Real.exp_log hR, mul_comm R]

theorem Mres_dilate {R : ℝ} (hR : 0 < R) (ℓ : ℤ) (z : ℂ) (G r : ℝ) :
    (S.dilate R).Mres ℓ z G r = S.Mres ℓ z (R ^ 2 * G) (R * r) := by
  simp only [Mres, Omega_dilate S hR]

theorem bfun_dilate {R : ℝ} (hR : 0 < R) (ℓ : ℕ) {r : ℝ} (hr : 0 < r) :
    (S.dilate R).bfun ℓ r = ((R ^ (ℓ + 2) : ℝ) : ℂ) * S.bfun ℓ (R * r) := by
  simp only [bfun, dilate_dom]
  have hR0 : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR.ne'
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  have e : ((R * r : ℝ) : ℂ) ^ (-(ℓ : ℤ) - 1) =
      ((R : ℂ) ^ (ℓ + 1))⁻¹ * (r : ℂ) ^ (-(ℓ : ℤ) - 1) := by
    rw [Complex.ofReal_mul, mul_zpow]
    congr 1
    rw [show -(ℓ : ℤ) - 1 = -((ℓ + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  rw [e]
  push_cast
  field_simp
  ring

/-- The `L²(ℝ²)` norm under the dilation `x ↦ Rx`: `‖f(R·)‖ = R⁻¹ ‖f‖` (unconditional). -/
theorem l2_comp_mul (f : ℂ → ℂ) {R : ℝ} (hR : 0 < R) :
    Sob.l2 (fun x => f ((R : ℂ) * x)) = R⁻¹ * Sob.l2 f := by
  have hR0 : R ≠ 0 := hR.ne'
  have hT : MeasurableEmbedding (fun x : ℂ => R • x) := measurableEmbedding_const_smul₀ hR0
  have hmap := Measure.map_addHaar_smul (volume : Measure ℂ) hR0
  rw [Complex.finrank_real_complex] at hmap
  set ν : ENNReal := ENNReal.ofReal |(R ^ 2)⁻¹| with hν
  have hν0 : ν ≠ 0 := by
    rw [hν, Ne, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have h1 := hT.eLpNorm_map_measure (g := f) (p := 2) (μ := volume)
  rw [hmap, eLpNorm_smul_measure_of_ne_zero hν0] at h1
  have h2 : (fun x => f ((R : ℂ) * x)) = f ∘ fun x : ℂ => R • x := by
    funext x
    simp [Complex.real_smul]
  have hsq : (ν ^ (1 / (2 : ENNReal)).toReal) = ENNReal.ofReal R⁻¹ := by
    rw [hν, abs_of_pos (by positivity), show (1 / (2 : ENNReal)).toReal = (1 / 2 : ℝ) by
      norm_num, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    congr 1
    rw [← Real.sqrt_eq_rpow, Real.sqrt_inv, Real.sqrt_sq hR.le]
  unfold Sob.l2
  rw [h2, ← h1, hsq, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

/-- `K(Rz) = R⁻¹ K(z)` for `R ≠ 0` real. -/
theorem biotSavartKernel_mul {R : ℝ} (hR : R ≠ 0) (z : ℂ) :
    biotSavartKernel ((R : ℂ) * z) = (R : ℂ)⁻¹ * biotSavartKernel z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [biotSavartKernel]
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
  have hR0 : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hn' : ((‖z‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hn
  simp only [biotSavartKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have habs : ((|R| : ℝ) : ℂ) ^ 2 = (R : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, sq_abs, Complex.ofReal_pow]
  push_cast
  rw [mul_pow, habs]
  field_simp

end DilationH

end NonUniqueEuler
