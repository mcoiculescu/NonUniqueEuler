import NonUniqueEuler.I.SmoothB.Iterates
import NonUniqueEuler.I.SmoothB.Constants
import NonUniqueEuler.I.Sec2.BSBasic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Helper for `lem:iter-cauchy`: basic facts on the iterates

Consequences of `lem:iterates` (`I/SmoothB/Iterates.lean`) and of the inner radius
(`I/SmoothB/Constants.lean`) used in the energy estimate of `lem:iter-cauchy`
(`B_global_smooth.tex:362-379`):

* smoothness of the slices `ω^{[j]}(t)`, `v^{[j]}(t)`;
* `ω^{[j]}(t, x) = 0` and `∇ω^{[j]}(t, x) = 0` for `|t| ≤ T` and `|x| ≥ R(T)`;
* `ω^{[j]}(t) ∈ L^p` for every `p`;
* linearity of the Biot–Savart integral: `v^{[j]}(t) - v^{[i]}(t) = K ∗ (ω^{[j]}(t) - ω^{[i]}(t))`.

Fully proved (from the interfaces).
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace NonUniqueEuler.Smooth.IterCauchyAux

variable {ω₀ : ℂ → ℝ} {R₀ : ℝ}

theorem one_le_top_withTop : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact_mod_cast le_top

/-- `R₀ > 0` for a nonzero datum. -/
theorem R₀_pos (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) : 0 < R₀ := by
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hne
  have hx' : x ∈ ball (0 : ℂ) R₀ := h.tsupport_subset (subset_tsupport _ hx)
  rw [mem_ball, dist_zero_right] at hx'
  exact (norm_nonneg x).trans_lt hx'

theorem suppRadius_pos (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (T : ℝ) :
    0 < suppRadius ω₀ R₀ T :=
  (R₀_pos h hne).trans_le (le_suppRadius ω₀ R₀ T)

theorem iter_contDiff (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (j : ℕ) :
    ContDiff ℝ 1 (Function.uncurry (iter ω₀ j)) :=
  (iterates_smooth_support h hne j).1.of_le one_le_top_withTop

theorem iter_slice_contDiff (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (j : ℕ) (t : ℝ) :
    ContDiff ℝ 1 (iter ω₀ j t) :=
  (iter_contDiff h hne j).comp (contDiff_const.prodMk contDiff_id)

theorem iterVel_slice_contDiff (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (j : ℕ) (t : ℝ) :
    ContDiff ℝ 1 (iterVel ω₀ j t) := by
  have h1 : ContDiff ℝ 1 (Function.uncurry (iterVel ω₀ j) ∘ fun x : ℂ => (t, x)) :=
    ((iterates_velocity h hne j).1.of_le one_le_top_withTop).comp
      (contDiff_const.prodMk contDiff_id)
  have e : (Function.uncurry (iterVel ω₀ j) ∘ fun x : ℂ => (t, x)) = iterVel ω₀ j t :=
    funext fun x => Function.uncurry_apply_pair (iterVel ω₀ j) t x
  rwa [e] at h1

/-- For `|t| ≤ T` and `|x| ≥ R(T)` we have `|x| > R₀' + U_*|t|`. -/
theorem lt_of_suppRadius_le {R₀' : ℝ} (hR₀' : R₀' < R₀) {T t : ℝ} (ht : |t| ≤ T) {x : ℂ}
    (hx : suppRadius ω₀ R₀ T ≤ ‖x‖) : R₀' + Ustar ω₀ * |t| < ‖x‖ := by
  have h1 : |t| ≤ |T| := ht.trans (le_abs_self T)
  have h2 : Ustar ω₀ * |t| ≤ Ustar ω₀ * |T| := mul_le_mul_of_nonneg_left h1 (Ustar_nonneg ω₀)
  simp only [suppRadius] at hx
  linarith

/-- `ω^{[j]}(t, x) = 0` for `|t| ≤ T`, `|x| ≥ R(T)` (`lem:iterates`(i)). -/
theorem iter_eq_zero (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (j : ℕ) {T t : ℝ}
    (ht : |t| ≤ T) {x : ℂ} (hx : suppRadius ω₀ R₀ T ≤ ‖x‖) : iter ω₀ j t x = 0 := by
  obtain ⟨R₀', hR₀', hz⟩ := exists_inner_radius h
  exact (iterates_smooth_support h hne j).2 R₀' hz t x (lt_of_suppRadius_le hR₀' ht hx)

/-- `∇ω^{[j]}(t, x) = 0` for `|t| ≤ T`, `|x| ≥ R(T)`. -/
theorem fderiv_iter_eq_zero (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (j : ℕ) {T t : ℝ}
    (ht : |t| ≤ T) {x : ℂ} (hx : suppRadius ω₀ R₀ T ≤ ‖x‖) :
    fderiv ℝ (iter ω₀ j t) x = 0 := by
  obtain ⟨R₀', hR₀', hz⟩ := exists_inner_radius h
  have hlt := lt_of_suppRadius_le hR₀' ht hx
  have hev : iter ω₀ j t =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    have hopen : IsOpen {y : ℂ | R₀' + Ustar ω₀ * |t| < ‖y‖} :=
      isOpen_lt continuous_const continuous_norm
    filter_upwards [hopen.mem_nhds hlt] with y hy
    exact (iterates_smooth_support h hne j).2 R₀' hz t y hy
  rw [hev.fderiv_eq]
  exact fderiv_const_apply 0

theorem iter_hasCompactSupport (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (j : ℕ) (t : ℝ) :
    HasCompactSupport (iter ω₀ j t) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (suppRadius ω₀ R₀ |t|)) fun x hx => by
    rw [mem_closedBall, dist_zero_right, not_le] at hx
    exact iter_eq_zero h hne j le_rfl hx.le

theorem iter_memLp (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (j : ℕ) (t : ℝ) (p : ℝ≥0∞) :
    MemLp (iter ω₀ j t) p volume :=
  (iter_slice_contDiff h hne j t).continuous.memLp_of_hasCompactSupport
    (iter_hasCompactSupport h hne j t)

/-- The difference of two iterates at time `t` has compact support. -/
theorem iter_sub_hasCompactSupport (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (i j : ℕ)
    (t : ℝ) : HasCompactSupport (fun x => iter ω₀ i t x - iter ω₀ j t x) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (suppRadius ω₀ R₀ |t|)) fun x hx => by
    rw [mem_closedBall, dist_zero_right, not_le] at hx
    rw [iter_eq_zero h hne i le_rfl hx.le, iter_eq_zero h hne j le_rfl hx.le, sub_zero]

/-- `e_{j+1}(t) = ‖ω^{[j+1]}(t) - ω^{[j]}(t)‖_{L²}`. -/
theorem iterErr_succ (j : ℕ) (t : ℝ) :
    iterErr ω₀ (j + 1) t = (eLpNorm (iter ω₀ (j + 1) t - iter ω₀ j t) 2 volume).toReal := rfl

/-- Linearity of the Biot–Savart integral on the iterates:
`v^{[i]}(t, x) - v^{[j]}(t, x) = (K ∗ (ω^{[i]}(t) - ω^{[j]}(t)))(x)` (the integrals converge
absolutely, `lem:BS-basic`(b)). -/
theorem iterVel_sub (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (i j : ℕ) (t : ℝ) (x : ℂ) :
    iterVel ω₀ i t x - iterVel ω₀ j t x = velocity (iter ω₀ i t - iter ω₀ j t) x := by
  have hi : ∀ n, Integrable (fun y => biotSavartKernel (x - y) * (iter ω₀ n t y : ℂ)) volume :=
    fun n => (BS.integrable_and_norm_velocity_le_sqrt_L1_Linf (iter_memLp h hne n t 1)
      (iter_memLp h hne n t ⊤) x).1
  simp only [iterVel, velocityField, velocity]
  rw [← integral_sub (hi i) (hi j)]
  congr 1
  funext y
  simp [Pi.sub_apply, mul_sub]

end NonUniqueEuler.Smooth.IterCauchyAux
