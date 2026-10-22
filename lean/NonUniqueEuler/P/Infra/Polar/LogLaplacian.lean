import NonUniqueEuler.Defs.Infra.Polar
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import NonUniqueEuler.I.Infra.Polar.Fubini
import NonUniqueEuler.I.Infra.Polar.Power
import NonUniqueEuler.H.Infra.Polar.LogLaplacian.RadialODE
import NonUniqueEuler.H.Infra.Polar.LogLaplacian.WeakDeriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Proof: the logarithmic kernel and the Laplacian, by polar coordinates (I-POLAR, R6)

Proves the declarations of `NonUniqueEuler/I/Infra/Polar/LogLaplacian.lean`.

* `hasDerivAt_mul_deriv_circleAverage`: `H/Infra/Polar/LogLaplacian/RadialODE.lean`
  (differentiation under the integral sign twice, the Laplacian in the rotated frame
  `(e^{iθ}, i e^{iθ})`, and the vanishing of the integral of the angular term by periodicity).
* `integral_log_norm_mul_laplacian`: polar Fubini (`I/Infra/Polar/Fubini.lean`), then
  `∫₀^R log r · (r A')' dr = F(R) - F(0)` with `F(r) = log r · r A'(r) - A(r)`; here
  `F' = log r · (r A')'` on `(0, R)`, `F` is continuous on `[0, R]` (`r log r → 0`, `A'` continuous),
  `F(0) = -A(0) = -h(0)` and `F(R) = 0` (`supp h ⊆ B_R`). This replaces the manuscript's limit
  `ε → 0` of Green's second identity on `{|y| > ε}` (`02_prelim.tex:226-239`).
* `integral_log_norm_mul_fderiv`: `H/Infra/Polar/LogLaplacian/WeakDeriv.lean` (integration by
  parts on horizontal lines after a rotation taking `v` to `‖v‖`).
-/

noncomputable section

open MeasureTheory Set Metric Real Filter Topology
open scoped Laplacian

namespace NonUniqueEuler.Polar

/-- The radial ODE of circle averages: `(r A')' = r ⨍_{C(0,r)} Δh` with `A(r) = ⨍_{C(0,r)} h`. -/
theorem hasDerivAt_mul_deriv_circleAverage {h : ℂ → ℝ} (hh : ContDiff ℝ 2 h) {r : ℝ}
    (hr : 0 < r) :
    HasDerivAt (fun s : ℝ => s * deriv (fun t : ℝ => Real.circleAverage h 0 t) s)
      (r * Real.circleAverage (Δ h) 0 r) r :=
  LogLaplacianH.hasDerivAt_mul_deriv_circleAverage_aux hh hr.ne'

/-- `∫ log‖y‖ Δh(y) dy = 2π h(0)` for `h ∈ C²_c(ℂ; ℝ)`. -/
theorem integral_log_norm_mul_laplacian {h : ℂ → ℝ} (hh : ContDiff ℝ 2 h)
    (hc : HasCompactSupport h) :
    ∫ y, Real.log ‖y‖ * Δ h y = 2 * π * h 0 := by
  have h1 : ContDiff ℝ 1 h := hh.of_le (by norm_num)
  have hΔc : Continuous (Δ h) := LogLaplacianH.continuous_laplacian hh
  have hint : Integrable (fun y => Real.log ‖y‖ * Δ h y) := by
    have := locallyIntegrable_log_norm.integrable_smul_right_of_hasCompactSupport hΔc
      (LogLaplacianH.hasCompactSupport_laplacian hc)
    simpa only [smul_eq_mul] using this
  -- the support radius
  obtain ⟨R₀, hR₀⟩ : ∃ R₀, tsupport h ⊆ closedBall 0 R₀ :=
    hc.isCompact.isBounded.subset_closedBall 0
  set R : ℝ := |R₀| + 1 with hRdef
  have hRpos : 0 < R := by positivity
  have hout : ∀ x : ℂ, |R₀| < ‖x‖ → x ∉ tsupport h := by
    intro x hx hmem
    have := hR₀ hmem
    rw [mem_closedBall, dist_zero_right] at this
    linarith [le_abs_self R₀]
  set A : ℝ → ℝ := fun t => Real.circleAverage h 0 t with hA
  set A' : ℝ → ℝ := deriv A with hA'
  -- vanishing of the circle averages outside the support
  have hA0 : ∀ t : ℝ, |R₀| < t → A t = 0 := by
    intro t ht
    simp only [hA, Real.circleAverage_def]
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun θ _ =>
      image_eq_zero_of_notMem_tsupport (hout _ (by
        rw [norm_circleMap_zero, abs_of_pos (lt_of_le_of_lt (abs_nonneg _) ht)]; exact ht))]
    simp
  have hΔ0 : ∀ t : ℝ, |R₀| < t → Real.circleAverage (Δ h) 0 t = 0 := by
    intro t ht
    simp only [Real.circleAverage_def]
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun θ _ =>
      LogLaplacianH.laplacian_eq_zero_of_notMem_tsupport (hout _ (by
        rw [norm_circleMap_zero, abs_of_pos (lt_of_le_of_lt (abs_nonneg _) ht)]; exact ht))]
    simp
  have hA'R : A' R = 0 := by
    have hev : A =ᶠ[𝓝 R] fun _ => (0 : ℝ) := by
      filter_upwards [lt_mem_nhds (show |R₀| < R by linarith)] with t ht using hA0 t ht
    rw [hA', hev.deriv_eq, deriv_const]
  have hAR : A R = 0 := hA0 R (by linarith)
  -- regularity of `A` and `A'`
  have hAcont : Continuous A := hh.continuous.circleAverage
  have hA'cont : Continuous A' := LogLaplacianH.continuous_deriv_circleAverage h1
  have hAderiv : ∀ t, HasDerivAt A (A' t) t := fun t =>
    (LogLaplacianH.hasDerivAt_circleAverage h1 t).differentiableAt.hasDerivAt
  have hΔavc : Continuous fun r : ℝ => Real.circleAverage (Δ h) 0 r := hΔc.circleAverage
  -- the circle average of the integrand
  have havg : ∀ r : ℝ, 0 < r →
      Real.circleAverage (fun y => Real.log ‖y‖ * Δ h y) 0 r
        = Real.log r * Real.circleAverage (Δ h) 0 r := by
    intro r hr
    have : Real.circleAverage (fun y => Real.log ‖y‖ * Δ h y) 0 r
        = Real.circleAverage (fun y => Real.log r • Δ h y) 0 r := by
      refine Real.circleAverage_congr_sphere fun y hy => ?_
      rw [mem_sphere_zero_iff_norm, abs_of_pos hr] at hy
      simp only [hy, smul_eq_mul]
    rw [this, Real.circleAverage_fun_smul, smul_eq_mul]
  -- the antiderivative
  set F : ℝ → ℝ := fun r => Real.log r * (r * A' r) - A r with hF
  set F' : ℝ → ℝ := fun r => Real.log r * (r * Real.circleAverage (Δ h) 0 r) with hF'
  have hFcont : Continuous F := by
    have : F = fun r => (r * Real.log r) * A' r - A r := by
      funext r; simp only [hF]; ring
    rw [this]
    exact (Real.continuous_mul_log.mul hA'cont).sub hAcont
  have hF'cont : Continuous F' := by
    have : F' = fun r => (r * Real.log r) * Real.circleAverage (Δ h) 0 r := by
      funext r; simp only [hF']; ring
    rw [this]
    exact Real.continuous_mul_log.mul hΔavc
  have hFderiv : ∀ r ∈ Ioo (0 : ℝ) R, HasDerivAt F (F' r) r := by
    intro r hr
    have hr0 : r ≠ 0 := hr.1.ne'
    have hG : HasDerivAt (fun s : ℝ => s * A' s) (r * Real.circleAverage (Δ h) 0 r) r :=
      hasDerivAt_mul_deriv_circleAverage hh hr.1
    have := ((Real.hasDerivAt_log hr0).mul hG).sub (hAderiv r)
    refine this.congr_deriv ?_
    simp only [hF']
    field_simp
    ring
  have hFTC : ∫ r in (0 : ℝ)..R, F' r = F R - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hRpos.le hFcont.continuousOn hFderiv
      (hF'cont.intervalIntegrable _ _)
  have hF0 : F 0 = -h 0 := by
    simp [hF, hA]
  have hFR : F R = 0 := by
    simp only [hF]
    rw [hA'R, hAR]
    ring
  -- assemble
  rw [integral_eq_integral_Ioi_circleAverage hint, smul_eq_mul]
  have hI : ∫ r in Ioi (0 : ℝ), r • Real.circleAverage (fun y => Real.log ‖y‖ * Δ h y) 0 r
      = ∫ r in Ioi (0 : ℝ), F' r := by
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    simp only [hF', smul_eq_mul]
    rw [havg r hr]
    ring
  have hI2 : ∫ r in Ioi (0 : ℝ), F' r = ∫ r in Ioc (0 : ℝ) R, F' r := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
      fun r hr => ?_
    have hrR : R < r := by
      rcases hr with ⟨hr1, hr2⟩
      simp only [mem_Ioc, not_and, not_le] at hr2
      exact hr2 hr1
    simp only [hF']
    rw [hΔ0 r (by linarith), mul_zero, mul_zero]
  rw [hI, hI2, ← intervalIntegral.integral_of_le hRpos.le, hFTC, hFR, hF0]
  ring

/-- The weak derivative of `log‖·‖` is `z/‖z‖²`: for `φ ∈ C¹_c(ℂ; ℝ)` and `v ∈ ℂ`,
`∫ log‖z‖ ∂_vφ(z) dz = -∫ (⟨z, v⟩/‖z‖²) φ(z) dz`. -/
theorem integral_log_norm_mul_fderiv {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) (v : ℂ) :
    ∫ z, Real.log ‖z‖ * fderiv ℝ φ z v = -∫ z, (inner ℝ z v / ‖z‖ ^ 2) * φ z :=
  LogLaplacianH.integral_log_norm_mul_fderiv_aux hφ hc v

end NonUniqueEuler.Polar
