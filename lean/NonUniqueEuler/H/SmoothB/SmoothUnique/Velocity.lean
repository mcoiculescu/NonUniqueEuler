import NonUniqueEuler.I.Sec2.BSBasic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Helper for `P/SmoothB/SmoothUnique`: the Biot–Savart velocity of a continuous function with
compact support

* `memLp_of_vanish`: a continuous `g` vanishing outside `B_ρ` lies in every `L^p`;
* `velocity_sub`: `K ∗ f - K ∗ g = K ∗ (f - g)` pointwise (all three integrals converge
  absolutely, `lem:BS-basic`(b));
* `integral_sq_velocity_ball_le`: `∫_{B_ρ} |K ∗ g|² ≤ (2ρ)² ∫ g²` (`lem:BS-basic`(c) with
  `R = ρ`, the form used in `B_global_smooth.tex:504-506`).
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace NonUniqueEuler.Smooth.UniqueAux

/-- A continuous function vanishing outside a ball has compact support. -/
theorem hasCompactSupport_of_vanish {g : ℂ → ℝ} {ρ : ℝ} (h : ∀ x, x ∉ ball (0 : ℂ) ρ → g x = 0) :
    HasCompactSupport g :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) ρ)
    (fun x hx => h x (fun h' => hx (ball_subset_closedBall h')))

/-- A continuous function vanishing outside a ball lies in every `L^p`. -/
theorem memLp_of_vanish {g : ℂ → ℝ} (hg : Continuous g) {ρ : ℝ}
    (h : ∀ x, x ∉ ball (0 : ℂ) ρ → g x = 0) (p : ℝ≥0∞) : MemLp g p volume :=
  hg.memLp_of_hasCompactSupport (hasCompactSupport_of_vanish h)

/-- The Biot–Savart integral converges absolutely at every point for a continuous function
with compact support (`lem:BS-basic`(b)). -/
theorem integrable_biotSavart_of_vanish {g : ℂ → ℝ} (hg : Continuous g) {ρ : ℝ}
    (h : ∀ x, x ∉ ball (0 : ℂ) ρ → g x = 0) (x : ℂ) :
    Integrable (fun y => biotSavartKernel (x - y) * (g y : ℂ)) volume :=
  (BS.integrable_and_norm_velocity_le_sqrt_L1_Linf (memLp_of_vanish hg h 1)
    (memLp_of_vanish hg h ⊤) x).1

/-- Linearity of the Biot–Savart velocity on continuous functions vanishing outside a ball. -/
theorem velocity_sub {f g : ℂ → ℝ} (hf : Continuous f) (hg : Continuous g) {ρ : ℝ}
    (hfv : ∀ x, x ∉ ball (0 : ℂ) ρ → f x = 0) (hgv : ∀ x, x ∉ ball (0 : ℂ) ρ → g x = 0)
    (x : ℂ) : velocity f x - velocity g x = velocity (fun y => f y - g y) x := by
  unfold velocity
  rw [← integral_sub (integrable_biotSavart_of_vanish hf hfv x)
    (integrable_biotSavart_of_vanish hg hgv x)]
  congr 1
  funext y
  push_cast
  ring

/-- `(‖g‖_{L²(μ)})² = ∫ |g|² dμ` in real form. -/
theorem toReal_eLpNorm_two_sq {μ : Measure ℂ} {g : ℂ → ℂ} (hg : MemLp g 2 μ) :
    ((eLpNorm g 2 μ).toReal) ^ 2 = ∫ x, ‖g x‖ ^ 2 ∂μ := by
  rw [hg.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  simp only [h2]
  have hnn : 0 ≤ ∫ x, ‖g x‖ ^ (2 : ℝ) ∂μ := integral_nonneg (fun x => by positivity)
  rw [ENNReal.toReal_ofReal (by positivity)]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hnn]
  norm_num

/-- `(‖g‖_{L²})² = ∫ g²` for a real `g ∈ L²`. -/
theorem toReal_eLpNorm_two_sq_real {g : ℂ → ℝ} (hg : MemLp g 2 volume) :
    ((eLpNorm g 2 volume).toReal) ^ 2 = ∫ x, g x ^ 2 := by
  rw [hg.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  simp only [h2]
  have hnn : 0 ≤ ∫ x, ‖g x‖ ^ (2 : ℝ) := integral_nonneg (fun x => by positivity)
  rw [ENNReal.toReal_ofReal (by positivity)]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hnn]
  norm_num

/-- **`lem:BS-basic`(c) in squared form.** For a continuous `g` vanishing outside `B_ρ`,
`K ∗ g ∈ L²(B_ρ)` and `∫_{B_ρ} |K ∗ g|² ≤ (2ρ)² ∫ g²`. -/
theorem integral_sq_velocity_ball_le {g : ℂ → ℝ} (hg : Continuous g) {ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ x, x ∉ ball (0 : ℂ) ρ → g x = 0) :
    MemLp (velocity g) 2 (volume.restrict (ball (0 : ℂ) ρ)) ∧
      ∫ x in ball (0 : ℂ) ρ, ‖velocity g x‖ ^ 2 ≤ (2 * ρ) ^ 2 * ∫ x, g x ^ 2 := by
  have hg2 := memLp_of_vanish hg h 2
  obtain ⟨-, hmem, hle⟩ := BS.velocity_L2_ball_le hρ hρ hg2 (Filter.Eventually.of_forall h)
  refine ⟨hmem, ?_⟩
  rw [← toReal_eLpNorm_two_sq hmem, ← toReal_eLpNorm_two_sq_real hg2]
  have hfin : eLpNorm g 2 volume ≠ ∞ := hg2.eLpNorm_ne_top
  have h1 : (eLpNorm (velocity g) 2 (volume.restrict (ball (0 : ℂ) ρ))).toReal ≤
      (ρ + ρ) * (eLpNorm g 2 volume).toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hle
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at this
  have h0 : 0 ≤ (eLpNorm (velocity g) 2 (volume.restrict (ball (0 : ℂ) ρ))).toReal :=
    ENNReal.toReal_nonneg
  calc (eLpNorm (velocity g) 2 (volume.restrict (ball (0 : ℂ) ρ))).toReal ^ 2
      ≤ ((ρ + ρ) * (eLpNorm g 2 volume).toReal) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = (2 * ρ) ^ 2 * (eLpNorm g 2 volume).toReal ^ 2 := by ring

end NonUniqueEuler.Smooth.UniqueAux
