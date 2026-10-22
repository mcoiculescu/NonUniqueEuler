import NonUniqueEuler.Defs.Infra.Multipole
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Complex.MeanValue

/-!
# Proof: geometric expansions of `(z - w)⁻¹` (I-MULT)

Proof of `NonUniqueEuler/I/Infra/Multipole/Geometric.lean` (same declarations, same statements).

* The two Laurent expansions come from `hasSum_geometric_of_norm_lt_one` for `w/z` (resp. `z/w`).
* The remainders are computed exactly by induction: the exterior remainder is
  `(w/z)^n (z - w)⁻¹`, the interior one `(z/w)^n (z - w)⁻¹`; then `‖z - w‖ ≥ |‖z‖ - ‖w‖|`.
* `∫₀^{2π} (s e^{iϑ})^l dϑ`: for `s ≠ 0` it is `I⁻¹ ∮_{C(0,s)} w^{l-1} dw`, which vanishes for
  `l ≠ 0` (`circleIntegral.integral_sub_zpow_of_ne`).
* The angular mean of the Cauchy kernel: for `s < ‖z‖` it is the mean value property
  (`circleAverage_of_differentiable_on_off_countable`) for the holomorphic `w ↦ (z - w)⁻¹`;
  for `s > ‖z‖`, `z ≠ 0`, partial fractions `w⁻¹ (z - w)⁻¹ = z⁻¹ (w⁻¹ - (w - z)⁻¹)` and
  `circleIntegral.integral_sub_inv_of_mem_ball` twice; for `z = 0` it is the case `l = -1` of the
  previous item.
-/

noncomputable section

open MeasureTheory Set Metric Real

namespace NonUniqueEuler.Multipole

/-! ### Exact remainders -/

/-- Exact exterior remainder: `(z - w)⁻¹ - ∑_{l<n} w^l z^{-(l+1)} = (w/z)^n (z - w)⁻¹`. -/
theorem inv_sub_sub_sum_eq_geom {z w : ℂ} (hz : z ≠ 0) (hzw : z - w ≠ 0) (n : ℕ) :
    (z - w)⁻¹ - ∑ l ∈ Finset.range n, w ^ l * (z ^ (l + 1))⁻¹ = (w / z) ^ n * (z - w)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← sub_sub, ih, div_pow, div_pow, pow_succ, pow_succ]
    field_simp
    ring

/-- Exact interior remainder: `(z - w)⁻¹ + ∑_{l<n} z^l w^{-(l+1)} = (z/w)^n (z - w)⁻¹`. -/
theorem inv_sub_add_sum_eq_geom {z w : ℂ} (hw : w ≠ 0) (hzw : z - w ≠ 0) (n : ℕ) :
    (z - w)⁻¹ + ∑ l ∈ Finset.range n, z ^ l * (w ^ (l + 1))⁻¹ = (z / w) ^ n * (z - w)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ih, div_pow, div_pow, pow_succ, pow_succ]
    field_simp
    ring

/-! ### The two expansions -/

/-- `(z - w)⁻¹ = ∑_{l ≥ 0} w^l / z^{l+1}` for `‖w‖ < ‖z‖`. -/
theorem hasSum_inv_sub_of_norm_lt {z w : ℂ} (h : ‖w‖ < ‖z‖) :
    HasSum (fun l : ℕ => w ^ l * (z ^ (l + 1))⁻¹) (z - w)⁻¹ := by
  have hzpos : 0 < ‖z‖ := (norm_nonneg w).trans_lt h
  have hz : z ≠ 0 := norm_pos_iff.1 hzpos
  have hr : ‖w / z‖ < 1 := by
    rw [norm_div, div_lt_one hzpos]; exact h
  have hzw : z - w ≠ 0 := by
    intro e; rw [sub_eq_zero] at e; rw [e] at h; exact lt_irrefl _ h
  have hg := (hasSum_geometric_of_norm_lt_one hr).mul_left z⁻¹
  have e1 : (fun l : ℕ => w ^ l * (z ^ (l + 1))⁻¹) = fun l : ℕ => z⁻¹ * (w / z) ^ l := by
    funext l
    rw [div_pow, pow_succ]
    field_simp
  have e2 : (z - w)⁻¹ = z⁻¹ * (1 - w / z)⁻¹ := by
    rw [one_sub_div hz, inv_div]
    field_simp
  rw [e1, e2]
  exact hg

/-- `(z - w)⁻¹ = -∑_{l ≥ 0} z^l / w^{l+1}` for `‖z‖ < ‖w‖`. -/
theorem hasSum_inv_sub_of_norm_gt {z w : ℂ} (h : ‖z‖ < ‖w‖) :
    HasSum (fun l : ℕ => -(z ^ l * (w ^ (l + 1))⁻¹)) (z - w)⁻¹ := by
  have hwpos : 0 < ‖w‖ := (norm_nonneg z).trans_lt h
  have hw : w ≠ 0 := norm_pos_iff.1 hwpos
  have hr : ‖z / w‖ < 1 := by
    rw [norm_div, div_lt_one hwpos]; exact h
  have hzw : w - z ≠ 0 := by
    intro e; rw [sub_eq_zero] at e; rw [e] at h; exact lt_irrefl _ h
  have hg := (hasSum_geometric_of_norm_lt_one hr).mul_left (-w⁻¹)
  have e1 : (fun l : ℕ => -(z ^ l * (w ^ (l + 1))⁻¹)) = fun l : ℕ => -w⁻¹ * (z / w) ^ l := by
    funext l
    rw [div_pow, pow_succ]
    field_simp
  have e2 : (z - w)⁻¹ = -w⁻¹ * (1 - z / w)⁻¹ := by
    rw [one_sub_div hw, inv_div, ← neg_sub w z]
    field_simp
  rw [e1, e2]
  exact hg

/-! ### Remainder bounds -/

/-- Remainder of the exterior expansion. -/
theorem norm_inv_sub_sub_sum_le {z w : ℂ} (h : ‖w‖ < ‖z‖) (n : ℕ) :
    ‖(z - w)⁻¹ - ∑ l ∈ Finset.range n, w ^ l * (z ^ (l + 1))⁻¹‖ ≤
      (‖w‖ / ‖z‖) ^ n / (‖z‖ - ‖w‖) := by
  have hzpos : 0 < ‖z‖ := (norm_nonneg w).trans_lt h
  have hz : z ≠ 0 := norm_pos_iff.1 hzpos
  have hzw : z - w ≠ 0 := by
    intro e; rw [sub_eq_zero] at e; rw [e] at h; exact lt_irrefl _ h
  rw [inv_sub_sub_sum_eq_geom hz hzw n, norm_mul, norm_pow, norm_div, norm_inv, div_eq_mul_inv]
  have hpos : 0 < ‖z‖ - ‖w‖ := sub_pos.2 h
  exact mul_le_mul_of_nonneg_left (inv_anti₀ hpos (norm_sub_norm_le z w))
    (pow_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _)) _)

/-- Remainder of the interior expansion. -/
theorem norm_inv_sub_add_sum_le {z w : ℂ} (h : ‖z‖ < ‖w‖) (n : ℕ) :
    ‖(z - w)⁻¹ + ∑ l ∈ Finset.range n, z ^ l * (w ^ (l + 1))⁻¹‖ ≤
      (‖z‖ / ‖w‖) ^ n / (‖w‖ - ‖z‖) := by
  have hwpos : 0 < ‖w‖ := (norm_nonneg z).trans_lt h
  have hw : w ≠ 0 := norm_pos_iff.1 hwpos
  have hzw : z - w ≠ 0 := by
    intro e; rw [sub_eq_zero] at e; rw [e] at h; exact lt_irrefl _ h
  rw [inv_sub_add_sum_eq_geom hw hzw n, norm_mul, norm_pow, norm_div, norm_inv, div_eq_mul_inv]
  have hpos : 0 < ‖w‖ - ‖z‖ := sub_pos.2 h
  have hle : ‖w‖ - ‖z‖ ≤ ‖z - w‖ := by
    rw [norm_sub_rev]; exact norm_sub_norm_le w z
  exact mul_le_mul_of_nonneg_left (inv_anti₀ hpos hle)
    (pow_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _)) _)

/-! ### Angular integrals -/

/-- `∫₀^{2π} (s e^{iϑ})^l dϑ = 2π` if `l = 0` and `0` otherwise (every `s : ℝ`, `l : ℤ`). -/
theorem intervalIntegral_circleMap_zpow (s : ℝ) (l : ℤ) :
    ∫ θ in (0 : ℝ)..2 * π, (circleMap 0 s θ) ^ l = if l = 0 then 2 * (π : ℂ) else 0 := by
  by_cases hl : l = 0
  · subst hl
    simp
  simp only [hl, ↓reduceIte]
  by_cases hs : s = 0
  · subst hs
    simp [circleMap_zero_radius, zero_zpow l hl]
  have key := circleIntegral.integral_sub_zpow_of_ne (n := l - 1) (by omega) 0 0 s
  unfold circleIntegral at key
  have hpt : ∀ θ : ℝ, deriv (circleMap 0 s) θ • (circleMap 0 s θ - 0) ^ (l - 1) =
      Complex.I * (circleMap 0 s θ) ^ l := by
    intro θ
    have hc : circleMap 0 s θ ≠ 0 := circleMap_ne_center hs
    rw [deriv_circleMap, sub_zero, smul_eq_mul, zpow_sub_one₀ hc]
    field_simp
  simp_rw [hpt, intervalIntegral.integral_const_mul] at key
  exact (mul_eq_zero.1 key).resolve_left Complex.I_ne_zero

/-- The interval integral as `2π` times the circle average. -/
theorem intervalIntegral_eq_two_pi_smul_circleAverage (f : ℂ → ℂ) (s : ℝ) :
    ∫ θ in (0 : ℝ)..2 * π, f (circleMap 0 s θ) = (2 * π : ℝ) • circleAverage f 0 s := by
  rw [circleAverage_def, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]

/-- The angular mean of the Cauchy kernel over the circle of radius `s` (`s ≠ ‖z‖`):
`∫₀^{2π} (z - s e^{iϑ})⁻¹ dϑ = 2π/z` if `s < ‖z‖`, and `0` if `s > ‖z‖`. -/
theorem intervalIntegral_inv_sub_circleMap {z : ℂ} {s : ℝ} (hs : 0 ≤ s) (hsz : s ≠ ‖z‖) :
    ∫ θ in (0 : ℝ)..2 * π, (z - circleMap 0 s θ)⁻¹ =
      if s < ‖z‖ then 2 * (π : ℂ) * z⁻¹ else 0 := by
  rw [intervalIntegral_eq_two_pi_smul_circleAverage (fun w => (z - w)⁻¹) s]
  split_ifs with hlt
  · -- mean value property for the holomorphic function `w ↦ (z - w)⁻¹` on `closedBall 0 s`
    have hne : ∀ w ∈ closedBall (0 : ℂ) |s|, z - w ≠ 0 := by
      intro w hw e
      rw [sub_eq_zero] at e
      rw [mem_closedBall_zero_iff, abs_of_nonneg hs, ← e] at hw
      exact absurd hlt (not_lt.2 hw)
    have hmv : circleAverage (fun w => (z - w)⁻¹) 0 s = (z - 0)⁻¹ := by
      refine circleAverage_of_differentiable_on_off_countable (s := (∅ : Set ℂ))
        countable_empty ?_ ?_
      · exact (continuousOn_const.sub continuousOn_id).inv₀ hne
      · intro w hw
        have hw' : w ∈ closedBall (0 : ℂ) |s| := ball_subset_closedBall hw.1
        exact ((differentiableAt_const z).sub differentiableAt_id).inv (hne w hw')
    rw [hmv, sub_zero, Complex.real_smul]
    push_cast
    ring
  · have hgt : ‖z‖ < s := lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hsz)
    have hspos : 0 < s := (norm_nonneg z).trans_lt hgt
    by_cases hz : z = 0
    · subst hz
      rw [← intervalIntegral_eq_two_pi_smul_circleAverage (fun w => ((0 : ℂ) - w)⁻¹) s]
      have h1 := intervalIntegral_circleMap_zpow s (-1)
      simp only [zpow_neg, zpow_one, neg_eq_zero, one_ne_zero, ↓reduceIte] at h1
      simp only [zero_sub, inv_neg]
      rw [intervalIntegral.integral_neg, h1, neg_zero]
    · rw [circleAverage_eq_circleIntegral hspos.ne']
      have hcongr : EqOn (fun w : ℂ => (w - 0)⁻¹ • (z - w)⁻¹)
          (fun w : ℂ => z⁻¹ • ((w - 0)⁻¹ - (w - z)⁻¹)) (sphere (0 : ℂ) s) := by
        intro w hw
        have hw0 : w ≠ 0 := by
          intro e; rw [e, mem_sphere_zero_iff_norm, norm_zero] at hw; exact hspos.ne hw
        have hwz : w - z ≠ 0 := by
          intro e; rw [sub_eq_zero] at e
          rw [e, mem_sphere_zero_iff_norm] at hw; exact hgt.ne hw
        have hzw : z - w ≠ 0 := by
          intro e; exact hwz (by rw [← neg_sub, e, neg_zero])
        simp only [smul_eq_mul, sub_zero]
        field_simp
        ring
      rw [circleIntegral.integral_congr hs hcongr, circleIntegral.integral_smul,
        circleIntegral.integral_sub]
      · rw [circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_self hspos),
          circleIntegral.integral_sub_inv_of_mem_ball (by simpa using hgt)]
        simp
      · rw [circleIntegrable_sub_inv_iff]
        right
        simp [abs_of_nonneg hs, hspos.ne]
      · rw [circleIntegrable_sub_inv_iff]
        right
        simp [abs_of_nonneg hs, hgt.ne]

end NonUniqueEuler.Multipole
