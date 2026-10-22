import NonUniqueEuler.I.Infra.Polar.Radial
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Helper for `lem:grad-bound`: the radial cutoff

Helper of `P/SmoothB/GradBound.lean` (`B_global_smooth.tex:128-140`). The manuscript applies the
divergence theorem on the annulus `{δ < |z| < ρ'}`, which produces a boundary term on `|z| = δ`.
Following R6 (no divergence theorem), we multiply the kernel by a smooth radial cutoff
`χ(z) = ψ(|z|)` with `ψ = 0` on `(-∞, a]`, `ψ = 1` on `[b, ∞)`, `ψ' ≥ 0`, and integrate by parts on
the whole plane. The boundary term becomes the volume term `∫ ∂_l χ (K_BS)_i g(x - ·)`, which is
bounded by `‖g‖_∞ ∫ ψ'(|z|) (2π|z|)⁻¹ dz = ‖g‖_∞ ∫₀^∞ ψ' = ‖g‖_∞`
(`integral_cutBoundary`), exactly the manuscript's bound for the boundary term.

* `cutProfile a b r = smoothTransition ((r - a)/(b - a))`, `cut a b z = cutProfile a b ‖z‖`;
* `contDiff_cut`, `cut_eq_zero`, `cut_eq_one`, `abs_fderiv_cut_le`;
* `integrable_cutBoundary`, `integral_cutBoundary`: `∫ ψ'(|z|) / (2π|z|) dz = 1`.
-/

noncomputable section

open MeasureTheory Set Metric Real Filter Topology
open scoped ContDiff

namespace NonUniqueEuler.GradBoundH

/-- The radial profile `ψ(r) = smoothTransition((r - a)/(b - a))`: `0` for `r ≤ a`, `1` for
`r ≥ b`. -/
def cutProfile (a b r : ℝ) : ℝ :=
  Real.smoothTransition ((r - a) / (b - a))

/-- The radial cutoff `χ(z) = ψ(|z|)`. -/
def cut (a b : ℝ) (z : ℂ) : ℝ :=
  cutProfile a b ‖z‖

variable {a b : ℝ}

theorem contDiff_cutProfile (a b : ℝ) : ContDiff ℝ ∞ (cutProfile a b) :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp ((contDiff_id.sub contDiff_const).div_const _)

theorem cutProfile_eq_zero (hab : a < b) {r : ℝ} (hr : r ≤ a) : cutProfile a b r = 0 :=
  Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))

theorem cutProfile_eq_one (hab : a < b) {r : ℝ} (hr : b ≤ r) : cutProfile a b r = 1 :=
  Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by linarith)]; linarith)

theorem cutProfile_nonneg (r : ℝ) : 0 ≤ cutProfile a b r :=
  Real.smoothTransition.nonneg _

theorem cutProfile_le_one (r : ℝ) : cutProfile a b r ≤ 1 :=
  Real.smoothTransition.le_one _

theorem monotone_cutProfile (hab : a < b) : Monotone (cutProfile a b) := fun _ _ hxy =>
  Real.smoothTransition.monotone (div_le_div_of_nonneg_right (by linarith) (by linarith))

theorem deriv_cutProfile_nonneg (hab : a < b) (r : ℝ) : 0 ≤ deriv (cutProfile a b) r :=
  (monotone_cutProfile hab).deriv_nonneg

theorem deriv_cutProfile_eq_zero (hab : a < b) {r : ℝ} (hr : r < a ∨ b < r) :
    deriv (cutProfile a b) r = 0 := by
  rcases hr with hr | hr
  · have : cutProfile a b =ᶠ[𝓝 r] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hr] with s hs using cutProfile_eq_zero hab (le_of_lt hs)
    rw [this.deriv_eq, deriv_const]
  · have : cutProfile a b =ᶠ[𝓝 r] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hr] with s hs using cutProfile_eq_one hab (le_of_lt hs)
    rw [this.deriv_eq, deriv_const]

theorem continuous_deriv_cutProfile (a b : ℝ) : Continuous (deriv (cutProfile a b)) :=
  (contDiff_cutProfile a b).continuous_deriv (by simp)

theorem hasCompactSupport_deriv_cutProfile (hab : a < b) :
    HasCompactSupport (deriv (cutProfile a b)) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := a) (b := b)) fun r hr => ?_
  apply deriv_cutProfile_eq_zero hab
  simp only [mem_Icc, not_and_or, not_le] at hr
  exact hr

theorem integrable_deriv_cutProfile (hab : a < b) : Integrable (deriv (cutProfile a b)) :=
  (continuous_deriv_cutProfile a b).integrable_of_hasCompactSupport
    (hasCompactSupport_deriv_cutProfile hab)

/-- `∫₀^∞ ψ' = ψ(∞) - ψ(0) = 1`. -/
theorem integral_Ioi_deriv_cutProfile (ha : 0 ≤ a) (hab : a < b) :
    ∫ r in Ioi (0 : ℝ), deriv (cutProfile a b) r = 1 := by
  have hd := (contDiff_cutProfile a b).differentiable (by simp)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (f := cutProfile a b)
    (f' := deriv (cutProfile a b)) (a := 0) (m := 1)
    (contDiff_cutProfile a b).continuous.continuousWithinAt
    (fun x _ => (hd x).hasDerivAt) (integrable_deriv_cutProfile hab).integrableOn
    (tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop b] with r hr
      exact (cutProfile_eq_one hab hr).symm))
  rw [h, cutProfile_eq_zero hab ha, sub_zero]

/-! ### The cutoff on the plane -/

theorem cut_eq_zero (hab : a < b) {z : ℂ} (hz : ‖z‖ ≤ a) : cut a b z = 0 :=
  cutProfile_eq_zero hab hz

theorem cut_eq_one (hab : a < b) {z : ℂ} (hz : b ≤ ‖z‖) : cut a b z = 1 :=
  cutProfile_eq_one hab hz

theorem cut_nonneg (z : ℂ) : 0 ≤ cut a b z := cutProfile_nonneg _

theorem cut_le_one (z : ℂ) : cut a b z ≤ 1 := cutProfile_le_one _

theorem cut_eventuallyEq_zero (ha : 0 < a) (hab : a < b) :
    cut a b =ᶠ[𝓝 (0 : ℂ)] fun _ => (0 : ℝ) := by
  filter_upwards [ball_mem_nhds (0 : ℂ) ha] with z hz
  rw [mem_ball_zero_iff] at hz
  exact cut_eq_zero hab hz.le

theorem contDiff_cut (ha : 0 < a) (hab : a < b) : ContDiff ℝ ∞ (cut a b) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  rcases eq_or_ne z 0 with rfl | hz
  · exact contDiffAt_const.congr_of_eventuallyEq (cut_eventuallyEq_zero ha hab)
  · exact (contDiff_cutProfile a b).contDiffAt.comp z (contDiffAt_norm ℝ hz)

/-- `|∂_v χ(z)| ≤ ψ'(|z|) |v|` (the norm is `1`-Lipschitz). -/
theorem abs_fderiv_cut_le (ha : 0 < a) (hab : a < b) (z v : ℂ) :
    |fderiv ℝ (cut a b) z v| ≤ deriv (cutProfile a b) ‖z‖ * ‖v‖ := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [(cut_eventuallyEq_zero ha hab).fderiv_eq]
    simp only [fderiv_fun_const, Pi.zero_apply, zero_apply, abs_zero]
    exact mul_nonneg (deriv_cutProfile_nonneg hab _) (norm_nonneg v)
  · have hn : HasFDerivAt (fun x : ℂ => ‖x‖) (fderiv ℝ (fun x : ℂ => ‖x‖) z) z :=
      ((contDiffAt_norm ℝ hz (n := 1)).differentiableAt (by simp)).hasFDerivAt
    have hψ : HasDerivAt (cutProfile a b) (deriv (cutProfile a b) ‖z‖) ‖z‖ :=
      ((contDiff_cutProfile a b).differentiable (by simp) _).hasDerivAt
    have h := hψ.comp_hasFDerivAt z hn
    rw [show cut a b = cutProfile a b ∘ fun x : ℂ => ‖x‖ from rfl, h.fderiv]
    rw [smul_apply, smul_eq_mul, abs_mul]
    have h1 : ‖fderiv ℝ (fun x : ℂ => ‖x‖) z‖ ≤ 1 := by
      have := norm_fderiv_le_of_lipschitz ℝ (x₀ := z) (lipschitzWith_one_norm (E := ℂ))
      simpa using this
    have h2 : |fderiv ℝ (fun x : ℂ => ‖x‖) z v| ≤ ‖v‖ := by
      have := (fderiv ℝ (fun x : ℂ => ‖x‖) z).le_opNorm v
      rw [Real.norm_eq_abs] at this
      exact this.trans (mul_le_of_le_one_left (norm_nonneg v) h1)
    rw [abs_of_nonneg (deriv_cutProfile_nonneg hab _)]
    exact mul_le_mul_of_nonneg_left h2 (deriv_cutProfile_nonneg hab _)

/-! ### The boundary integral -/

theorem integrable_cutBoundary (hab : a < b) :
    Integrable (fun z : ℂ => deriv (cutProfile a b) ‖z‖ / (2 * π * ‖z‖)) := by
  refine (Polar.integrable_comp_norm_iff
    (f := fun r => deriv (cutProfile a b) r / (2 * π * r))).2 ?_
  have hint : Integrable (fun r => deriv (cutProfile a b) r / (2 * π)) :=
    (integrable_deriv_cutProfile hab).div_const _
  refine hint.integrableOn.congr_fun (fun r hr => ?_) measurableSet_Ioi
  have hr0 : r ≠ 0 := ne_of_gt hr
  simp only [smul_eq_mul]
  field_simp

/-- `∫ ψ'(|z|) (2π|z|)⁻¹ dz = ∫₀^∞ ψ' = 1`: the boundary term of the manuscript. -/
theorem integral_cutBoundary (ha : 0 ≤ a) (hab : a < b) :
    ∫ z : ℂ, deriv (cutProfile a b) ‖z‖ / (2 * π * ‖z‖) = 1 := by
  rw [Polar.integral_comp_norm (fun r => deriv (cutProfile a b) r / (2 * π * r))]
  have h : ∫ r in Ioi (0 : ℝ), r • (deriv (cutProfile a b) r / (2 * π * r)) =
      ∫ r in Ioi (0 : ℝ), deriv (cutProfile a b) r / (2 * π) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hr0 : r ≠ 0 := ne_of_gt hr
    simp only [smul_eq_mul]
    field_simp
  rw [h, integral_div, integral_Ioi_deriv_cutProfile ha hab, smul_eq_mul]
  have : (2 * π) ≠ 0 := by positivity
  field_simp

end NonUniqueEuler.GradBoundH
