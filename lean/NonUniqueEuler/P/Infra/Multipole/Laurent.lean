import NonUniqueEuler.Defs.Infra.Multipole
import NonUniqueEuler.I.Infra.Multipole.Geometric
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Proof: Laurent expansions of the Cauchy transform (I-MULT)

Proof of `NonUniqueEuler/I/Infra/Multipole/Laurent.lean` (same declarations, statements copied
verbatim).

* Exterior expansion (`lem:ext-multipole`, `02_prelim.tex:487-492`): pointwise on the support of
  `g` (where `‖w‖ ≤ ϱ < ‖z‖`) the geometric expansion `hasSum_inv_sub_of_norm_lt` of
  `(z - w)⁻¹`, multiplied by `g w`; termwise integration by
  `hasSum_integral_of_dominated_convergence` with the summable dominating sequence
  `‖g w‖ · ‖z‖⁻¹ (ϱ₊/‖z‖)^l`, `ϱ₊ = max ϱ 0`.
* Interior expansion (`lem:hollow`, `02_prelim.tex:430-440`): likewise with
  `hasSum_inv_sub_of_norm_gt` on the support (`‖z‖ < R ≤ ‖w‖`), dominating sequence
  `‖g w‖ · R⁻¹ (‖z‖/R)^l`.
* `cauchyTransform_eq_laurentTail` is `HasSum.tsum_eq` of the exterior expansion.

No deviation from the manuscript.
-/

noncomputable section

open MeasureTheory Set Metric Real ComplexConjugate

namespace NonUniqueEuler.Multipole

/-- `x ^ (-(l + 1)) = (x ^ (l + 1))⁻¹` for an integer exponent written as in `moment g (-(l+1))`. -/
private lemma zpow_neg_succ_eq {K : Type*} [DivisionRing K] (x : K) (l : ℕ) :
    x ^ (-((l : ℤ) + 1)) = (x ^ (l + 1))⁻¹ := by
  have h : (-((l : ℤ) + 1)) = -((l + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, zpow_neg, zpow_natCast]

/-- Exterior Laurent expansion of the Cauchy transform (`lem:ext-multipole`). -/
theorem hasSum_cauchyTransform_exterior {g : ℂ → ℂ} (hg : Integrable g) {ϱ : ℝ}
    (hsupp : ∀ᵐ w, ϱ < ‖w‖ → g w = 0) {z : ℂ} (hz : ϱ < ‖z‖) :
    HasSum (fun l : ℕ => moment g l * (z ^ (l + 1))⁻¹) (cauchyTransform g z) := by
  set ρ : ℝ := max ϱ 0 with hρ
  set r : ℝ := ρ / ‖z‖ with hr
  have hr0 : 0 ≤ r := div_nonneg (le_max_right _ _) (norm_nonneg _)
  have hr1 : r < 1 := by
    rcases (norm_nonneg z).eq_or_lt with h0 | hpos
    · rw [hr, ← h0, div_zero]
      exact one_pos
    · rw [hr, div_lt_one hpos]
      exact max_lt hz hpos
  let F : ℕ → ℂ → ℂ := fun l w => g w * w ^ (l : ℤ) * (z ^ (l + 1))⁻¹
  let bound : ℕ → ℂ → ℝ := fun l w => ‖g w‖ * (‖z‖⁻¹ * r ^ l)
  have hF : ∀ l : ℕ, ∫ w, F l w = moment g l * (z ^ (l + 1))⁻¹ := fun l => by
    simp only [F, moment]
    exact integral_mul_const _ _
  have hmeas : ∀ l, AEStronglyMeasurable (F l) volume := fun l =>
    (hg.aestronglyMeasurable.mul
      (measurable_id.pow_const (l : ℤ)).aestronglyMeasurable).mul_const _
  have hbound : ∀ l, ∀ᵐ w ∂(volume : Measure ℂ), ‖F l w‖ ≤ bound l w := by
    intro l
    filter_upwards [hsupp] with w hw
    by_cases hgw : g w = 0
    · simp [F, bound, hgw]
    · have hwρ : ‖w‖ ≤ ρ := le_trans (not_lt.mp fun h => hgw (hw h)) (le_max_left _ _)
      have hpow : ‖w‖ ^ l * (‖z‖ ^ (l + 1))⁻¹ ≤ ρ ^ l * (‖z‖ ^ (l + 1))⁻¹ := by
        gcongr
      have heq : ρ ^ l * (‖z‖ ^ (l + 1))⁻¹ = ‖z‖⁻¹ * r ^ l := by
        rw [hr, div_pow, pow_succ, mul_inv]
        ring
      simp only [F, bound, norm_mul, norm_inv, norm_pow, zpow_natCast]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hpow.trans_eq heq) (norm_nonneg _)
  have hsumm : ∀ᵐ w ∂(volume : Measure ℂ), Summable fun l => bound l w :=
    ae_of_all _ fun w => ((summable_geometric_of_lt_one hr0 hr1).mul_left ‖z‖⁻¹).mul_left _
  have hint : Integrable (fun w => ∑' l, bound l w) volume := by
    have : (fun w => ∑' l, bound l w) = fun w => ‖g w‖ * ∑' l : ℕ, ‖z‖⁻¹ * r ^ l := by
      funext w
      exact tsum_mul_left
    rw [this]
    exact hg.norm.mul_const _
  have hlim : ∀ᵐ w ∂(volume : Measure ℂ),
      HasSum (fun l => F l w) (g w * (z - w)⁻¹) := by
    filter_upwards [hsupp] with w hw
    by_cases hgw : g w = 0
    · simp only [F, hgw, zero_mul]
      exact hasSum_zero
    · have hwz : ‖w‖ < ‖z‖ := lt_of_le_of_lt (not_lt.mp fun h => hgw (hw h)) hz
      have hfun : (fun l => F l w) = fun l : ℕ => g w * (w ^ l * (z ^ (l + 1))⁻¹) := by
        funext l
        simp only [F, zpow_natCast, mul_assoc]
      rw [hfun]
      exact (hasSum_inv_sub_of_norm_lt hwz).mul_left (g w)
  have key := hasSum_integral_of_dominated_convergence bound hmeas hbound hsumm hint hlim
  simpa only [hF, cauchyTransform] using key

theorem cauchyTransform_eq_laurentTail {g : ℂ → ℂ} (hg : Integrable g) {ϱ : ℝ}
    (hsupp : ∀ᵐ w, ϱ < ‖w‖ → g w = 0) {z : ℂ} (hz : ϱ < ‖z‖) :
    cauchyTransform g z = laurentTail (fun l => moment g l) z := by
  rw [laurentTail]
  exact (hasSum_cauchyTransform_exterior hg hsupp hz).tsum_eq.symm

/-- Interior expansion of the Cauchy transform (`lem:hollow`): `C[g](z) = -∑ c_{l+1} z^l`. -/
theorem hasSum_cauchyTransform_interior {g : ℂ → ℂ} (hg : Integrable g) {R : ℝ}
    (hsupp : ∀ᵐ w, ‖w‖ < R → g w = 0) {z : ℂ} (hz : ‖z‖ < R) :
    HasSum (fun l : ℕ => -(moment g (-((l : ℤ) + 1)) * z ^ l)) (cauchyTransform g z) := by
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg z) hz
  set r : ℝ := ‖z‖ / R with hr
  have hr0 : 0 ≤ r := div_nonneg (norm_nonneg _) hR.le
  have hr1 : r < 1 := (div_lt_one hR).mpr hz
  let F : ℕ → ℂ → ℂ := fun l w => -(g w * w ^ (-((l : ℤ) + 1)) * z ^ l)
  let bound : ℕ → ℂ → ℝ := fun l w => ‖g w‖ * (R⁻¹ * r ^ l)
  have hF : ∀ l : ℕ, ∫ w, F l w = -(moment g (-((l : ℤ) + 1)) * z ^ l) := fun l => by
    simp only [F, moment]
    rw [integral_neg, integral_mul_const]
  have hmeas : ∀ l, AEStronglyMeasurable (F l) volume := fun l =>
    ((hg.aestronglyMeasurable.mul
      (measurable_id.pow_const (-((l : ℤ) + 1))).aestronglyMeasurable).mul_const _).neg
  have hbound : ∀ l, ∀ᵐ w ∂(volume : Measure ℂ), ‖F l w‖ ≤ bound l w := by
    intro l
    filter_upwards [hsupp] with w hw
    by_cases hgw : g w = 0
    · simp [F, bound, hgw]
    · have hRw : R ≤ ‖w‖ := not_lt.mp fun h => hgw (hw h)
      have hinv : (‖w‖ ^ (l + 1))⁻¹ ≤ (R ^ (l + 1))⁻¹ :=
        inv_anti₀ (pow_pos hR _) (pow_le_pow_left₀ hR.le hRw _)
      have hpow : (‖w‖ ^ (l + 1))⁻¹ * ‖z‖ ^ l ≤ (R ^ (l + 1))⁻¹ * ‖z‖ ^ l :=
        mul_le_mul_of_nonneg_right hinv (pow_nonneg (norm_nonneg _) _)
      have heq : (R ^ (l + 1))⁻¹ * ‖z‖ ^ l = R⁻¹ * r ^ l := by
        rw [hr, div_pow, pow_succ, mul_inv]
        ring
      simp only [F, bound, norm_neg, norm_mul, norm_pow, zpow_neg_succ_eq, norm_inv]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hpow.trans_eq heq) (norm_nonneg _)
  have hsumm : ∀ᵐ w ∂(volume : Measure ℂ), Summable fun l => bound l w :=
    ae_of_all _ fun w => ((summable_geometric_of_lt_one hr0 hr1).mul_left R⁻¹).mul_left _
  have hint : Integrable (fun w => ∑' l, bound l w) volume := by
    have : (fun w => ∑' l, bound l w) = fun w => ‖g w‖ * ∑' l : ℕ, R⁻¹ * r ^ l := by
      funext w
      exact tsum_mul_left
    rw [this]
    exact hg.norm.mul_const _
  have hlim : ∀ᵐ w ∂(volume : Measure ℂ),
      HasSum (fun l => F l w) (g w * (z - w)⁻¹) := by
    filter_upwards [hsupp] with w hw
    by_cases hgw : g w = 0
    · simp only [F, hgw, zero_mul, neg_zero]
      exact hasSum_zero
    · have hzw : ‖z‖ < ‖w‖ := lt_of_lt_of_le hz (not_lt.mp fun h => hgw (hw h))
      have hfun : (fun l => F l w) = fun l : ℕ => g w * -(z ^ l * (w ^ (l + 1))⁻¹) := by
        funext l
        simp only [F, zpow_neg_succ_eq]
        ring
      rw [hfun]
      exact (hasSum_inv_sub_of_norm_gt hzw).mul_left (g w)
  have key := hasSum_integral_of_dominated_convergence bound hmeas hbound hsumm hint hlim
  simpa only [hF, cauchyTransform] using key

end NonUniqueEuler.Multipole
