import NonUniqueEuler.Defs.Infra.Multipole
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Proof: bounds and symmetries of multipole moments (I-MULT)

Proof of `NonUniqueEuler/I/Infra/Multipole/Moments.lean` (same declarations, same statements).

* Bounds: `norm_integral_le_of_norm_le` against the integrable majorant `‖g‖ ϱ^l` (resp.
  `‖g‖ R^{-l}`), which dominates `‖g w‖ ‖w‖^{±l}` almost everywhere by the support hypothesis.
* Symmetry: `rot θ` preserves `volume` and is a measurable embedding, so
  `∫ F = ∫ F ∘ rot θ` (`MeasurePreserving.integral_comp`). Since `(rot θ w)^l = e^{ilθ} w^l` and
  `g ∘ rot θ = g` a.e., `moment g l = e^{ilθ} moment g l` (`moment_eq_exp_mul_of_rot`); likewise
  `conjMoment g l = e^{-ilθ} conjMoment g l`. For `θ = 2π/m` and `m ∤ l`, `e^{±ilθ} ≠ 1`; for a
  rotation-invariant `g` and `l ≠ 0` take `θ = π/l`, where `e^{ilθ} = -1`.
* Linearity: `integral_sub`.
-/

noncomputable section

open MeasureTheory Set Metric Real ComplexConjugate

namespace NonUniqueEuler.Multipole

/-! ### Helpers -/

private theorem measurableEmbedding_rot (θ : ℝ) : MeasurableEmbedding (rot θ) := by
  rw [Polar.rot_eq_rotation]
  exact (rotation (Circle.exp θ)).toHomeomorph.measurableEmbedding

/-- Change of variables under a rotation (unconditional). -/
private theorem integral_comp_rot (θ : ℝ) (F : ℂ → ℂ) :
    ∫ w, F (rot θ w) = ∫ w, F w :=
  (Polar.measurePreserving_rot θ).integral_comp (measurableEmbedding_rot θ) F

private theorem rot_zpow (θ : ℝ) (w : ℂ) (l : ℤ) :
    rot θ w ^ l = Complex.exp ((l : ℂ) * ((θ : ℂ) * Complex.I)) * w ^ l := by
  rw [rot, mul_zpow, Complex.exp_int_mul]

private theorem conj_rot_zpow (θ : ℝ) (w : ℂ) (l : ℤ) :
    conj (rot θ w) ^ l = Complex.exp (((-l : ℤ) : ℂ) * ((θ : ℂ) * Complex.I)) * conj w ^ l := by
  rw [rot, map_mul, mul_zpow, ← Complex.exp_conj, ← Complex.exp_int_mul]
  congr 2
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- If `g ∘ rot θ = g` a.e., then `moment g l = e^{ilθ} moment g l`. -/
private theorem moment_eq_exp_mul_of_rot {g : ℂ → ℂ} {θ : ℝ}
    (hg : (fun x => g (rot θ x)) =ᵐ[volume] g) (l : ℤ) :
    moment g l = Complex.exp ((l : ℂ) * ((θ : ℂ) * Complex.I)) * moment g l := by
  have h := integral_comp_rot θ (fun w => g w * w ^ l)
  unfold moment
  conv_lhs => rw [← h]
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hg] with w hw
  rw [hw, rot_zpow]
  ring

/-- If `g ∘ rot θ = g` a.e., then `conjMoment g l = e^{-ilθ} conjMoment g l`. -/
private theorem conjMoment_eq_exp_mul_of_rot {g : ℂ → ℂ} {θ : ℝ}
    (hg : (fun x => g (rot θ x)) =ᵐ[volume] g) (l : ℤ) :
    conjMoment g l =
      Complex.exp (((-l : ℤ) : ℂ) * ((θ : ℂ) * Complex.I)) * conjMoment g l := by
  have h := integral_comp_rot θ (fun w => g w * conj w ^ l)
  unfold conjMoment
  conv_lhs => rw [← h]
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hg] with w hw
  rw [hw, conj_rot_zpow]
  ring

private theorem eq_zero_of_eq_mul_of_ne_one {a c : ℂ} (h : a = c * a) (hc : c ≠ 1) : a = 0 := by
  have h' : (1 - c) * a = 0 := by linear_combination h
  rcases mul_eq_zero.1 h' with h1 | h1
  · exact absurd (sub_eq_zero.1 h1).symm hc
  · exact h1

/-- `e^{2πil/m} ≠ 1` when `m ∤ l`. -/
private theorem exp_two_pi_div_ne_one {m : ℕ} (hm : 0 < m) {l : ℤ} (hl : ¬ (m : ℤ) ∣ l) :
    Complex.exp ((l : ℂ) * (((2 * π / m : ℝ) : ℂ) * Complex.I)) ≠ 1 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
  apply hl
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast at hn
  have key : (l : ℂ) * (2 * π * Complex.I) = ((m : ℂ) * n) * (2 * π * Complex.I) := by
    calc (l : ℂ) * (2 * π * Complex.I)
        = ((l : ℂ) * (2 * π / m * Complex.I)) * m := by field_simp
      _ = (n * (2 * π * Complex.I)) * m := by rw [hn]
      _ = ((m : ℂ) * n) * (2 * π * Complex.I) := by ring
  have hne : (2 * π * Complex.I : ℂ) ≠ 0 := by simp [hpi, Complex.I_ne_zero]
  have hlm : (l : ℂ) = (m : ℂ) * n := mul_right_cancel₀ hne key
  exact ⟨n, by exact_mod_cast hlm⟩

/-! ### The interface statements -/

/-- `|Q_l| ≤ ‖g‖₁ ϱ^l` for `g` supported in `closedBall 0 ϱ`. -/
theorem norm_moment_le {g : ℂ → ℂ} (hg : Integrable g) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (hsupp : ∀ᵐ w, ϱ < ‖w‖ → g w = 0) (l : ℕ) :
    ‖moment g l‖ ≤ (∫ w, ‖g w‖) * ϱ ^ l := by
  unfold moment
  rw [← integral_mul_const]
  refine norm_integral_le_of_norm_le (hg.norm.mul_const _) ?_
  filter_upwards [hsupp] with w hw
  rw [zpow_natCast, norm_mul, norm_pow]
  by_cases h : ϱ < ‖w‖
  · simp [hw h]
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (not_lt.1 h) l)
      (norm_nonneg _)

/-- `|∫ g w̄^l| ≤ ‖g‖₁ ϱ^l` for `g` supported in `closedBall 0 ϱ`. -/
theorem norm_conjMoment_le {g : ℂ → ℂ} (hg : Integrable g) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (hsupp : ∀ᵐ w, ϱ < ‖w‖ → g w = 0) (l : ℕ) :
    ‖conjMoment g l‖ ≤ (∫ w, ‖g w‖) * ϱ ^ l := by
  unfold conjMoment
  rw [← integral_mul_const]
  refine norm_integral_le_of_norm_le (hg.norm.mul_const _) ?_
  filter_upwards [hsupp] with w hw
  rw [zpow_natCast, norm_mul, norm_pow, Complex.norm_conj]
  by_cases h : ϱ < ‖w‖
  · simp [hw h]
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (not_lt.1 h) l)
      (norm_nonneg _)

/-- `|c_l| ≤ ‖g‖₁ R^{-l}` for `g` vanishing on `ball 0 R`. -/
theorem norm_moment_neg_le {g : ℂ → ℂ} (hg : Integrable g) {R : ℝ} (hR : 0 < R)
    (hsupp : ∀ᵐ w, ‖w‖ < R → g w = 0) (l : ℕ) :
    ‖moment g (-(l : ℤ))‖ ≤ (∫ w, ‖g w‖) * (R ^ l)⁻¹ := by
  unfold moment
  rw [← integral_mul_const]
  refine norm_integral_le_of_norm_le (hg.norm.mul_const _) ?_
  filter_upwards [hsupp] with w hw
  by_cases h : ‖w‖ < R
  · simp [hw h]
  · rw [norm_mul, zpow_neg, zpow_natCast, norm_inv, norm_pow]
    exact mul_le_mul_of_nonneg_left
      (inv_anti₀ (pow_pos hR l) (pow_le_pow_left₀ hR.le (not_lt.1 h) l)) (norm_nonneg _)

/-- Only multiples of `m` survive for an `m`-fold symmetric real `g`. -/
theorem moment_eq_zero_of_isMFoldSymmetric {g : ℂ → ℝ} {m : ℕ} (hm : 0 < m)
    (hg : IsMFoldSymmetric m g) {l : ℤ} (hl : ¬ (m : ℤ) ∣ l) :
    moment (fun w => (g w : ℂ)) l = 0 := by
  have hg' : (fun x => ((g (rot (2 * π / m) x) : ℝ) : ℂ)) =ᵐ[volume] fun w => (g w : ℂ) := by
    filter_upwards [hg] with x hx
    rw [hx]
  exact eq_zero_of_eq_mul_of_ne_one (moment_eq_exp_mul_of_rot hg' l)
    (exp_two_pi_div_ne_one hm hl)

theorem conjMoment_eq_zero_of_isMFoldSymmetric {g : ℂ → ℝ} {m : ℕ} (hm : 0 < m)
    (hg : IsMFoldSymmetric m g) {l : ℤ} (hl : ¬ (m : ℤ) ∣ l) :
    conjMoment (fun w => (g w : ℂ)) l = 0 := by
  have hg' : (fun x => ((g (rot (2 * π / m) x) : ℝ) : ℂ)) =ᵐ[volume] fun w => (g w : ℂ) := by
    filter_upwards [hg] with x hx
    rw [hx]
  have hl' : ¬ (m : ℤ) ∣ -l := by rwa [dvd_neg]
  exact eq_zero_of_eq_mul_of_ne_one (conjMoment_eq_exp_mul_of_rot hg' l)
    (exp_two_pi_div_ne_one hm hl')

/-- A rotation-invariant (a.e., for every angle) `g` has no moments of order `l ≠ 0`. -/
theorem moment_eq_zero_of_rot_invariant {g : ℂ → ℂ}
    (hg : ∀ θ : ℝ, (fun x => g (rot θ x)) =ᵐ[volume] g) {l : ℤ} (hl : l ≠ 0) :
    moment g l = 0 := by
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl
  have hc : Complex.exp ((l : ℂ) * (((π / l : ℝ) : ℂ) * Complex.I)) ≠ 1 := by
    have h1 : (l : ℂ) * (((π / l : ℝ) : ℂ) * Complex.I) = π * Complex.I := by
      push_cast
      field_simp
    rw [h1, Complex.exp_pi_mul_I]
    norm_num
  exact eq_zero_of_eq_mul_of_ne_one (moment_eq_exp_mul_of_rot (hg (π / l)) l) hc

/-- The angular average has no moments of order `l ≠ 0` (proof of `lem:hollow`). -/
theorem moment_angAvg_eq_zero (g : ℂ → ℝ) {l : ℤ} (hl : l ≠ 0) :
    moment (fun w => ((Polar.angAvg g w : ℝ) : ℂ)) l = 0 := by
  refine moment_eq_zero_of_rot_invariant (fun θ => Filter.Eventually.of_forall fun x => ?_) hl
  simp only [Polar.angAvg_rot]

/-- Linearity of the moments. -/
theorem moment_sub {g₁ g₂ : ℂ → ℂ} {l : ℤ} (h₁ : Integrable fun w => g₁ w * w ^ l)
    (h₂ : Integrable fun w => g₂ w * w ^ l) :
    moment (fun w => g₁ w - g₂ w) l = moment g₁ l - moment g₂ l := by
  unfold moment
  rw [← integral_sub h₁ h₂]
  simp only [sub_mul]

end NonUniqueEuler.Multipole
