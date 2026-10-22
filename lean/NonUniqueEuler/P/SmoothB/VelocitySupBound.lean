import NonUniqueEuler.Statement.Plane
import NonUniqueEuler.I.Sec2.BSBasic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Proof: `‖K_BS ∗ g‖_{L^∞} ≤ √2 ρ ‖g‖_{L^∞}` for `g` vanishing outside `B_ρ`

Proof of `I/SmoothB/VelocitySupBound.lean` (the bound inside the proof of `prop:iter-limit`,
`B_global_smooth.tex:422-424`).

1. `‖g‖₁ ≤ |B_ρ| ‖g‖_∞ = πρ² ‖g‖_∞` (`eLpNorm_one_le_pi_mul_sq_mul_eLpNorm_top`): bound
   `‖g y‖ₑ` a.e. by `1_{B_ρ}(y) ‖g‖_∞` and integrate (`Complex.volume_ball`).
2. `lem:BS-basic`(b) (`BS.integrable_and_norm_velocity_le_sqrt_L1_Linf`) and
   `(2‖g‖₁‖g‖_∞/π)^{1/2} ≤ (2πρ²‖g‖_∞²/π)^{1/2} = √2 ρ ‖g‖_∞`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace NonUniqueEuler.Smooth

/-- `‖g‖₁ ≤ πρ² ‖g‖_∞` for `g` vanishing (a.e.) outside `B_ρ`. -/
theorem eLpNorm_one_le_pi_mul_sq_mul_eLpNorm_top {g : ℂ → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hsupp : ∀ᵐ y, y ∉ ball (0 : ℂ) ρ → g y = 0) :
    eLpNorm g 1 volume ≤ ENNReal.ofReal (Real.pi * ρ ^ 2) * eLpNorm g ⊤ volume := by
  rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_exponent_top]
  calc ∫⁻ y, ‖g y‖ₑ
      ≤ ∫⁻ y, (ball (0 : ℂ) ρ).indicator (fun _ => eLpNormEssSup g volume) y := by
        apply lintegral_mono_ae
        filter_upwards [hsupp, ae_le_eLpNormEssSup (f := g) (μ := volume)] with y hy hle
        by_cases hyb : y ∈ ball (0 : ℂ) ρ
        · simpa [indicator_of_mem hyb] using hle
        · simp [indicator_of_notMem hyb, hy hyb]
    _ = eLpNormEssSup g volume * volume (ball (0 : ℂ) ρ) :=
        lintegral_indicator_const measurableSet_ball _
    _ = ENNReal.ofReal (Real.pi * ρ ^ 2) * eLpNormEssSup g volume := by
        rw [mul_comm, Complex.volume_ball, ENNReal.ofReal_mul Real.pi_pos.le,
          ENNReal.ofReal_pow hρ.le, mul_comm (ENNReal.ofReal Real.pi)]
        congr 2
        rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]

/-- For a bounded measurable real `g` vanishing outside `B_ρ`, the Biot–Savart integral
converges absolutely at every `x` and `|K_BS ∗ g(x)| ≤ √2 ρ ‖g‖_{L^∞}`
(`B_global_smooth.tex:422-424`). -/
theorem norm_velocity_le_sqrt_two_mul_radius {g : ℂ → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hg : MemLp g ⊤ volume) (hsupp : ∀ᵐ y, y ∉ ball (0 : ℂ) ρ → g y = 0) (x : ℂ) :
    Integrable (fun y => biotSavartKernel (x - y) * (g y : ℂ)) volume ∧
      ‖velocity g x‖ ≤ Real.sqrt 2 * ρ * (eLpNorm g ⊤ volume).toReal := by
  have h1 := eLpNorm_one_le_pi_mul_sq_mul_eLpNorm_top hρ hsupp
  have htop : eLpNorm g ⊤ volume ≠ ⊤ := hg.2.ne
  have hg1 : MemLp g 1 volume :=
    ⟨hg.1, lt_of_le_of_lt h1 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg.2)⟩
  obtain ⟨hint, hle⟩ := BS.integrable_and_norm_velocity_le_sqrt_L1_Linf hg1 hg x
  refine ⟨hint, hle.trans ?_⟩
  set a := (eLpNorm g 1 volume).toReal with ha_def
  set b := (eLpNorm g ⊤ volume).toReal with hb_def
  have hb : 0 ≤ b := ENNReal.toReal_nonneg
  have ha : a ≤ Real.pi * ρ ^ 2 * b := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top htop) h1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  have hpi := Real.pi_pos
  calc Real.sqrt (2 * a * b / Real.pi)
      ≤ Real.sqrt (2 * (Real.pi * ρ ^ 2 * b) * b / Real.pi) := by
        apply Real.sqrt_le_sqrt
        gcongr
    _ = Real.sqrt ((Real.sqrt 2 * ρ * b) ^ 2) := by
        congr 1
        rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        field_simp
    _ = Real.sqrt 2 * ρ * b := Real.sqrt_sq (by positivity)

end NonUniqueEuler.Smooth
