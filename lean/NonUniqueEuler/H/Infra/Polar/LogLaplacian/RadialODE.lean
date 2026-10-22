import NonUniqueEuler.Defs.Infra.Polar
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Helpers for `P/Infra/Polar/LogLaplacian`: the radial ODE of circle averages

For `h : ℂ → ℝ` of class `C²` and `A(r) = ⨍_{C(0,r)} h`:
* `hasDerivAt_integral_circleMap`: `d/dr ∫₀^{2π} g(r e^{iθ}) dθ = ∫₀^{2π} Dg(r e^{iθ}) e^{iθ} dθ`
  for `g ∈ C¹` (differentiation under the integral sign, the `θ`-domain being compact);
* `laplacian_eq_rot`: `Δh(x) = D²h(x)(e,e) + D²h(x)(ie,ie)` for every unit vector `e`;
* `hasDerivAt_angular_term`, `integral_angular_term`: the angular part of the polar Laplacian
  integrates to `0` over a circle (periodicity);
* `hasDerivAt_mul_deriv_circleAverage_aux`: `(r A')' = r ⨍_{C(0,r)} Δh` for `r ≠ 0`.

All proofs are complete.
-/

noncomputable section

open MeasureTheory Set Metric Real Filter Topology InnerProductSpace
open scoped Laplacian

namespace NonUniqueEuler.Polar.LogLaplacianH

theorem circleMap_zero_eq_smul (r θ : ℝ) :
    circleMap 0 r θ = r • Complex.exp (θ * Complex.I) := by
  rw [circleMap_zero, Complex.real_smul]

theorem hasDerivAt_circleMap_radius (r θ : ℝ) :
    HasDerivAt (fun s : ℝ => circleMap 0 s θ) (Complex.exp (θ * Complex.I)) r := by
  have := ((hasDerivAt_id r).ofReal_comp).mul_const (Complex.exp (θ * Complex.I))
  simpa [circleMap_zero] using this

theorem continuous_exp_mul_I : Continuous fun θ : ℝ => Complex.exp (θ * Complex.I) := by
  fun_prop

/-- Differentiation of circle integrals with respect to the radius. -/
theorem hasDerivAt_integral_circleMap {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ θ in (0 : ℝ)..2 * π, g (circleMap 0 s θ))
      (∫ θ in (0 : ℝ)..2 * π,
        fderiv ℝ g (circleMap 0 t θ) (Complex.exp (θ * Complex.I))) t := by
  have hcd : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) (|t| + 1)).exists_bound_of_continuousOn
    hcd.continuousOn
  have hderiv : ∀ θ s : ℝ, HasDerivAt (fun s : ℝ => g (circleMap 0 s θ))
      (fderiv ℝ g (circleMap 0 s θ) (Complex.exp (θ * Complex.I))) s := fun θ s =>
    (hgd _).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_circleMap_radius s θ)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := fun s θ => g (circleMap 0 s θ))
    (F' := fun s θ => fderiv ℝ g (circleMap 0 s θ) (Complex.exp (θ * Complex.I)))
    (bound := fun _ => C) (ball_mem_nhds t one_pos) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Eventually.of_forall fun s =>
      (hg.continuous.comp (continuous_circleMap 0 s)).aestronglyMeasurable
  · exact (hg.continuous.comp (continuous_circleMap 0 t)).intervalIntegrable _ _
  · exact ((hcd.comp (continuous_circleMap 0 t)).clm_apply
      continuous_exp_mul_I).aestronglyMeasurable
  · refine Eventually.of_forall fun θ _ s hs => ?_
    have hmem : circleMap 0 s θ ∈ closedBall (0 : ℂ) (|t| + 1) := by
      rw [mem_closedBall, dist_zero_right, norm_circleMap_zero]
      have h1 := mem_ball.1 hs
      rw [Real.dist_eq] at h1
      have h2 : |s| - |t| ≤ |s - t| := abs_sub_abs_le_abs_sub s t
      linarith
    calc ‖fderiv ℝ g (circleMap 0 s θ) (Complex.exp (θ * Complex.I))‖
        ≤ ‖fderiv ℝ g (circleMap 0 s θ)‖ * ‖Complex.exp (θ * Complex.I)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ g (circleMap 0 s θ)‖ := by rw [Complex.norm_exp_ofReal_mul_I, mul_one]
      _ ≤ C := hC _ hmem
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun θ _ s _ => hderiv θ s

/-! ### The Laplacian in a rotated orthonormal frame -/

theorem bilin_rot_sum (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) :
    B (a • (1 : ℂ) + b • Complex.I) (a • (1 : ℂ) + b • Complex.I)
      + B ((-b) • (1 : ℂ) + a • Complex.I) ((-b) • (1 : ℂ) + a • Complex.I)
      = B 1 1 + B Complex.I Complex.I := by
  simp only [map_add, map_smul, _root_.add_apply, _root_.smul_apply,
    smul_eq_mul]
  linear_combination (B 1 1 + B Complex.I Complex.I) * hab

theorem laplacian_eq_fderiv (h : ℂ → ℝ) (x : ℂ) :
    Δ h x = fderiv ℝ (fderiv ℝ h) x 1 1
      + fderiv ℝ (fderiv ℝ h) x Complex.I Complex.I := by
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- `Δh(x) = D²h(x)(e,e) + D²h(x)(ie,ie)` for every unit vector `e`. -/
theorem laplacian_eq_rot (h : ℂ → ℝ) (x e : ℂ) (he : ‖e‖ = 1) :
    Δ h x = fderiv ℝ (fderiv ℝ h) x e e
      + fderiv ℝ (fderiv ℝ h) x (Complex.I * e) (Complex.I * e) := by
  rw [laplacian_eq_fderiv]
  have hab : e.re ^ 2 + e.im ^ 2 = 1 := by
    have h1 := Complex.sq_norm e
    rw [he, Complex.normSq_apply] at h1
    nlinarith [h1]
  have h1 : e = e.re • (1 : ℂ) + e.im • Complex.I := by
    apply Complex.ext <;> simp
  have h2 : Complex.I * e = (-e.im) • (1 : ℂ) + e.re • Complex.I := by
    apply Complex.ext <;> simp
  rw [h2, ← bilin_rot_sum (fderiv ℝ (fderiv ℝ h) x) hab, ← h1]

theorem contDiff_fderiv_of_two {h : ℂ → ℝ} (hh : ContDiff ℝ 2 h) :
    ContDiff ℝ 1 (fderiv ℝ h) :=
  hh.fderiv_right (by norm_num)

theorem continuous_fderiv_fderiv {h : ℂ → ℝ} (hh : ContDiff ℝ 2 h) :
    Continuous (fderiv ℝ (fderiv ℝ h)) :=
  (contDiff_fderiv_of_two hh).continuous_fderiv one_ne_zero

theorem continuous_laplacian {h : ℂ → ℝ} (hh : ContDiff ℝ 2 h) : Continuous (Δ h) := by
  have hD2 := continuous_fderiv_fderiv hh
  have : Δ h = fun x => fderiv ℝ (fderiv ℝ h) x 1 1
      + fderiv ℝ (fderiv ℝ h) x Complex.I Complex.I := funext (laplacian_eq_fderiv h)
  rw [this]
  exact ((hD2.clm_apply continuous_const).clm_apply continuous_const).add
    ((hD2.clm_apply continuous_const).clm_apply continuous_const)

theorem laplacian_eq_zero_of_notMem_tsupport {h : ℂ → ℝ} {x : ℂ} (hx : x ∉ tsupport h) :
    Δ h x = 0 := by
  have h1 : h =ᶠ[𝓝 x] fun _ => (0 : ℝ) := notMem_tsupport_iff_eventuallyEq.1 hx
  rw [(laplacian_congr_nhds h1).eq_of_nhds, laplacian_const]
  rfl

theorem hasCompactSupport_laplacian {h : ℂ → ℝ} (hc : HasCompactSupport h) :
    HasCompactSupport (Δ h) :=
  hc.mono' fun x hx => by
    by_contra hx'
    exact hx (laplacian_eq_zero_of_notMem_tsupport hx')

/-! ### The angular term -/

/-- `d/dθ [Dh(c) (i c)] = D²h(c)(ic, ic) - Dh(c) c` with `c = r e^{iθ}`. -/
theorem hasDerivAt_angular_term {h : ℂ → ℝ} (hh : ContDiff ℝ 2 h) (r θ : ℝ) :
    HasDerivAt (fun θ : ℝ => fderiv ℝ h (circleMap 0 r θ) (Complex.I * circleMap 0 r θ))
      (fderiv ℝ (fderiv ℝ h) (circleMap 0 r θ) (Complex.I * circleMap 0 r θ)
          (Complex.I * circleMap 0 r θ)
        - fderiv ℝ h (circleMap 0 r θ) (circleMap 0 r θ)) θ := by
  have hfd := contDiff_fderiv_of_two hh
  have hc := hasDerivAt_circleMap 0 r θ
  have h1 : HasDerivAt (fun θ => fderiv ℝ h (circleMap 0 r θ))
      (fderiv ℝ (fderiv ℝ h) (circleMap 0 r θ) (circleMap 0 r θ * Complex.I)) θ :=
    ((hfd.differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt θ hc
  have h2 : HasDerivAt (fun θ => Complex.I * circleMap 0 r θ)
      (Complex.I * (circleMap 0 r θ * Complex.I)) θ := hc.const_mul Complex.I
  refine (h1.clm_apply h2).congr_deriv ?_
  have e2 : Complex.I * (circleMap 0 r θ * Complex.I) = -circleMap 0 r θ := by
    rw [mul_comm (circleMap 0 r θ) Complex.I, ← mul_assoc, Complex.I_mul_I, neg_one_mul]
  have e1 : circleMap 0 r θ * Complex.I = Complex.I * circleMap 0 r θ := mul_comm _ _
  rw [e2, e1, map_neg, sub_eq_add_neg, add_comm]

theorem continuous_angular_term {h : ℂ → ℝ} (hh : ContDiff ℝ 2 h) (r : ℝ) :
    Continuous fun θ : ℝ =>
      fderiv ℝ (fderiv ℝ h) (circleMap 0 r θ) (Complex.I * circleMap 0 r θ)
          (Complex.I * circleMap 0 r θ)
        - fderiv ℝ h (circleMap 0 r θ) (circleMap 0 r θ) := by
  have hD2 := continuous_fderiv_fderiv hh
  have hD1 : Continuous (fderiv ℝ h) := hh.continuous_fderiv (by norm_num)
  have hc := continuous_circleMap 0 r
  have hIc : Continuous fun θ : ℝ => Complex.I * circleMap 0 r θ := continuous_const.mul hc
  exact (((hD2.comp hc).clm_apply hIc).clm_apply hIc).sub ((hD1.comp hc).clm_apply hc)

/-- The angular part of the polar Laplacian integrates to `0` over a circle. -/
theorem integral_angular_term {h : ℂ → ℝ} (hh : ContDiff ℝ 2 h) (r : ℝ) :
    ∫ θ in (0 : ℝ)..2 * π,
      (fderiv ℝ (fderiv ℝ h) (circleMap 0 r θ) (Complex.I * circleMap 0 r θ)
          (Complex.I * circleMap 0 r θ)
        - fderiv ℝ h (circleMap 0 r θ) (circleMap 0 r θ)) = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ _ => hasDerivAt_angular_term hh r θ)
    ((continuous_angular_term hh r).intervalIntegrable _ _)]
  have hp : circleMap 0 r (2 * π) = circleMap 0 r 0 := by
    simpa using periodic_circleMap 0 r 0
  simp only [hp, sub_self]

/-! ### The radial ODE -/

theorem hasFDerivAt_fderiv_apply_self {h : ℂ → ℝ} (hh : ContDiff ℝ 2 h) (x : ℂ) :
    HasFDerivAt (fun x => fderiv ℝ h x x)
      ((fderiv ℝ h x).comp (ContinuousLinearMap.id ℝ ℂ)
        + (fderiv ℝ (fderiv ℝ h) x).flip x) x :=
  (((contDiff_fderiv_of_two hh).differentiable one_ne_zero) x).hasFDerivAt.clm_apply
    (hasFDerivAt_id x)

theorem fderiv_fderiv_apply_self {h : ℂ → ℝ} (hh : ContDiff ℝ 2 h) (x w : ℂ) :
    fderiv ℝ (fun x => fderiv ℝ h x x) x w
      = fderiv ℝ h x w + fderiv ℝ (fderiv ℝ h) x w x := by
  rw [(hasFDerivAt_fderiv_apply_self hh x).fderiv]
  simp

theorem contDiff_fderiv_apply_self {h : ℂ → ℝ} (hh : ContDiff ℝ 2 h) :
    ContDiff ℝ 1 (fun x => fderiv ℝ h x x) :=
  (contDiff_fderiv_of_two hh).clm_apply contDiff_id

/-- The radial derivative of `x ↦ Dh(x) x` integrates to `r ∫ Δh` over the circle of radius
`r ≠ 0`. -/
theorem integral_deriv_radial_term {h : ℂ → ℝ} (hh : ContDiff ℝ 2 h) {r : ℝ} (hr : r ≠ 0) :
    ∫ θ in (0 : ℝ)..2 * π,
      fderiv ℝ (fun x => fderiv ℝ h x x) (circleMap 0 r θ) (Complex.exp (θ * Complex.I))
      = r * ∫ θ in (0 : ℝ)..2 * π, Δ h (circleMap 0 r θ) := by
  set K : ℝ → ℝ := fun θ =>
    fderiv ℝ (fderiv ℝ h) (circleMap 0 r θ) (Complex.I * circleMap 0 r θ)
        (Complex.I * circleMap 0 r θ)
      - fderiv ℝ h (circleMap 0 r θ) (circleMap 0 r θ) with hK
  have hpt : ∀ θ : ℝ,
      fderiv ℝ (fun x => fderiv ℝ h x x) (circleMap 0 r θ) (Complex.exp (θ * Complex.I))
        = r * Δ h (circleMap 0 r θ) - r⁻¹ * K θ := by
    intro θ
    rw [fderiv_fderiv_apply_self hh, laplacian_eq_rot h (circleMap 0 r θ)
      (Complex.exp (θ * Complex.I)) (Complex.norm_exp_ofReal_mul_I θ), hK]
    simp only []
    rw [circleMap_zero_eq_smul]
    simp only [map_smul, _root_.smul_apply, smul_eq_mul, mul_smul_comm]
    field_simp
    ring
  have hΔ : Continuous fun θ : ℝ => Δ h (circleMap 0 r θ) :=
    (continuous_laplacian hh).comp (continuous_circleMap 0 r)
  rw [intervalIntegral.integral_congr (fun θ _ => hpt θ),
    intervalIntegral.integral_sub ((hΔ.const_mul r).intervalIntegrable _ _)
      (((continuous_angular_term hh r).const_mul r⁻¹).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_angular_term hh r, mul_zero, sub_zero]

/-- The derivative of the circle average: `A'(t) = (2π)⁻¹ ∫₀^{2π} Dh(t e^{iθ}) e^{iθ} dθ`. -/
theorem hasDerivAt_circleAverage {h : ℂ → ℝ} (hh : ContDiff ℝ 1 h) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.circleAverage h 0 t)
      ((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π,
        fderiv ℝ h (circleMap 0 t θ) (Complex.exp (θ * Complex.I))) t := by
  simp only [Real.circleAverage_def, smul_eq_mul]
  exact (hasDerivAt_integral_circleMap hh t).const_mul _

theorem deriv_circleAverage {h : ℂ → ℝ} (hh : ContDiff ℝ 1 h) :
    deriv (fun t : ℝ => Real.circleAverage h 0 t) = fun t =>
      (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π,
        fderiv ℝ h (circleMap 0 t θ) (Complex.exp (θ * Complex.I)) :=
  funext fun t => (hasDerivAt_circleAverage hh t).deriv

theorem continuous_deriv_circleAverage {h : ℂ → ℝ} (hh : ContDiff ℝ 1 h) :
    Continuous (deriv (fun t : ℝ => Real.circleAverage h 0 t)) := by
  rw [deriv_circleAverage hh]
  have hcd : Continuous (fderiv ℝ h) := hh.continuous_fderiv one_ne_zero
  refine continuous_const.mul ?_
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun t θ => fderiv ℝ h (circleMap 0 t θ) (Complex.exp (θ * Complex.I))) ?_ _ _
  exact (hcd.comp circleMap.continuous).clm_apply (continuous_exp_mul_I.comp continuous_snd)

/-- The radial ODE of circle averages, `(r A')' = r ⨍_{C(0,r)} Δh`, for `r ≠ 0`. -/
theorem hasDerivAt_mul_deriv_circleAverage_aux {h : ℂ → ℝ} (hh : ContDiff ℝ 2 h) {r : ℝ}
    (hr : r ≠ 0) :
    HasDerivAt (fun s : ℝ => s * deriv (fun t : ℝ => Real.circleAverage h 0 t) s)
      (r * Real.circleAverage (Δ h) 0 r) r := by
  have h1 : ContDiff ℝ 1 h := hh.of_le (by norm_num)
  have heq : (fun s : ℝ => s * deriv (fun t : ℝ => Real.circleAverage h 0 t) s)
      = fun s => (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π,
          (fun x => fderiv ℝ h x x) (circleMap 0 s θ) := by
    funext s
    rw [deriv_circleAverage h1, mul_left_comm, ← intervalIntegral.integral_const_mul]
    congr 1
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only []
    rw [circleMap_zero_eq_smul s θ, map_smul, smul_eq_mul]
  rw [heq]
  have := (hasDerivAt_integral_circleMap (contDiff_fderiv_apply_self hh) r).const_mul
    (2 * π)⁻¹
  refine this.congr_deriv ?_
  rw [integral_deriv_radial_term hh hr, Real.circleAverage_def, smul_eq_mul]
  ring

end NonUniqueEuler.Polar.LogLaplacianH
