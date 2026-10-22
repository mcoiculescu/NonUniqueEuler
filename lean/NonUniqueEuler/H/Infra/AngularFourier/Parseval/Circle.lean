import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.Prod
import NonUniqueEuler.Defs.Infra.Polar

/-!
# Helper for `P/Infra/AngularFourier/Parseval`: Parseval on one circle

For a fixed radius `r`, the angular sectors `g_ℓ(r)` are the Fourier coefficients on `[0, 2π]`
of `θ ↦ g(r e^{iθ})` (`angularSector_eq_fourierCoeffOn`), so Mathlib's Parseval identity
`hasSum_sq_fourierCoeffOn` gives `∫₀^{2π} |g(re^{iθ})|² dθ = 2π ∑_ℓ |g_ℓ(r)|²`
(`lintegral_circle_eq_tsum`, in `ℝ≥0∞`).

Also: strong measurability of `r ↦ g_ℓ(r)` for strongly measurable `g`.
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace NonUniqueEuler.Ang.ParsevalH

/-- The angular sector `g_ℓ(r)` is the `ℓ`-th Fourier coefficient of `θ ↦ g(r e^{iθ})` on
`[0, 2π]`. -/
theorem angularSector_eq_fourierCoeffOn (g : ℂ → ℂ) (ℓ : ℤ) (r : ℝ) :
    Polar.angularSector g ℓ r =
      fourierCoeffOn two_pi_pos (fun θ : ℝ => g (circleMap 0 r θ)) ℓ := by
  rw [fourierCoeffOn_eq_integral, Polar.angularSector, Complex.real_smul]
  congr 1
  · push_cast
    simp
  · refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [fourier_coe_apply, smul_eq_mul, circleMap_zero]
    rw [mul_comm]
    congr 2
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    push_cast
    field_simp
    ring

/-- `‖‖z‖ ^ 2‖ₑ = ‖z‖ₑ ^ 2`. -/
theorem enorm_norm_sq (z : ℂ) : ‖‖z‖ ^ 2‖ₑ = ‖z‖ₑ ^ 2 := by
  rw [enorm_pow, enorm_norm]

/-- `MemLp` with exponent `2` from finiteness of `∫⁻ ‖f‖ₑ²`. -/
theorem memLp_two_of_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : AEStronglyMeasurable f μ) (hfin : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ ≠ ∞) : MemLp f 2 μ := by
  refine ⟨hf, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
  simpa using hfin.lt_top

/-- **Parseval on one circle**, in `ℝ≥0∞`:
`∫_{(0,2π]} ‖g(re^{iθ})‖² dθ = 2π ∑_ℓ ‖g_ℓ(r)‖²` when the left side is finite. -/
theorem lintegral_circle_eq_tsum {g : ℂ → ℂ} {r : ℝ}
    (hm : AEStronglyMeasurable (fun θ : ℝ => g (circleMap 0 r θ))
      (volume.restrict (Ioc 0 (2 * π))))
    (hfin : ∫⁻ θ in Ioc 0 (2 * π), ‖g (circleMap 0 r θ)‖ₑ ^ 2 ≠ ∞) :
    ∫⁻ θ in Ioc 0 (2 * π), ‖g (circleMap 0 r θ)‖ₑ ^ 2 =
      ENNReal.ofReal (2 * π) * ∑' ℓ : ℤ, ‖Polar.angularSector g ℓ r‖ₑ ^ 2 := by
  set u : ℝ → ℂ := fun θ => g (circleMap 0 r θ) with hu
  have hL2 : MemLp u 2 (volume.restrict (Ioc 0 (2 * π))) := memLp_two_of_lintegral hm hfin
  have hS := hasSum_sq_fourierCoeffOn two_pi_pos hL2
  have hcoef : ∀ ℓ : ℤ, fourierCoeffOn two_pi_pos u ℓ = Polar.angularSector g ℓ r :=
    fun ℓ => (angularSector_eq_fourierCoeffOn g ℓ r).symm
  simp only [hcoef, sub_zero, smul_eq_mul] at hS
  -- the integral of `‖u‖²`
  have hint : Integrable (fun θ => ‖u θ‖ ^ 2) (volume.restrict (Ioc 0 (2 * π))) :=
    (memLp_two_iff_integrable_sq_norm hm).1 hL2
  have hI : ENNReal.ofReal (∫ θ in (0 : ℝ)..2 * π, ‖u θ‖ ^ 2) =
      ∫⁻ θ in Ioc 0 (2 * π), ‖u θ‖ₑ ^ 2 := by
    rw [intervalIntegral.integral_of_le two_pi_pos.le,
      ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun _ => by positivity)]
    refine lintegral_congr fun θ => ?_
    rw [← enorm_norm_sq, Real.enorm_eq_ofReal (by positivity)]
  have hT : ENNReal.ofReal (∑' ℓ : ℤ, ‖Polar.angularSector g ℓ r‖ ^ 2) =
      ∑' ℓ : ℤ, ‖Polar.angularSector g ℓ r‖ₑ ^ 2 := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hS.summable]
    refine tsum_congr fun ℓ => ?_
    rw [← enorm_norm_sq, Real.enorm_eq_ofReal (by positivity)]
  rw [← hI, ← hT, hS.tsum_eq, ← ENNReal.ofReal_mul two_pi_pos.le, ← mul_assoc,
    mul_inv_cancel₀ two_pi_pos.ne', one_mul]

/-- `(r, θ) ↦ r e^{iθ}` is continuous. -/
theorem continuous_circleMap_zero_uncurried :
    Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by
  simp only [circleMap_zero]
  fun_prop

/-- For strongly measurable `g`, `r ↦ g_ℓ(r)` is strongly measurable. -/
theorem stronglyMeasurable_angularSector {g : ℂ → ℂ} (hg : StronglyMeasurable g) (ℓ : ℤ) :
    StronglyMeasurable (Polar.angularSector g ℓ) := by
  have hF : StronglyMeasurable (fun p : ℝ × ℝ =>
      g ((p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)) *
        Complex.exp (-((ℓ : ℂ) * p.2 * Complex.I))) := by
    refine StronglyMeasurable.mul ?_ ?_
    · refine hg.comp_measurable ?_
      have : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)) := by
        fun_prop
      exact this.measurable
    · refine Continuous.stronglyMeasurable ?_
      fun_prop
  have h2 := hF.integral_prod_right' (ν := volume.restrict (Ioc 0 (2 * π)))
  have : Polar.angularSector g ℓ = fun r : ℝ => (2 * π : ℂ)⁻¹ *
      ∫ θ, g ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
        Complex.exp (-((ℓ : ℂ) * θ * Complex.I)) ∂(volume.restrict (Ioc 0 (2 * π))) := by
    funext r
    rw [Polar.angularSector, intervalIntegral.integral_of_le two_pi_pos.le]
  rw [this]
  exact h2.const_mul _

end NonUniqueEuler.Ang.ParsevalH
