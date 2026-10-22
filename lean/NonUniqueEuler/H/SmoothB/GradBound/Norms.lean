import NonUniqueEuler.Defs.SmoothB.Iteration
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Helper for `lem:grad-bound`: the norms `‖g‖_∞`, `‖∇g‖_∞`, `‖g‖₁` of a `C¹_c` function

Helper of `P/SmoothB/GradBound.lean`. For continuous compactly supported real `g` on the plane:
* `abs_le_Amax`: `|g(y)| ≤ ‖g‖_{L^∞} = Amax g` for every `y` (the essential supremum of a
  continuous function dominates every value, `volume` being positive on open sets);
* `Amax_pos`: `0 < Amax g` when `g ≢ 0`;
* `abs_fderiv_e2_le_gradSup`: `|∂_l g(y)| ≤ sup_x |∇g(x)| = gradSup g` for `g ∈ C¹_c`;
* `integral_abs_comp_sub_eq_l1`: `∫ |g(x - z)| dz = ‖g‖_{L¹} = l1 g`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace NonUniqueEuler.GradBoundH

/-- The essential supremum of a continuous function dominates each of its values. -/
theorem enorm_le_eLpNorm_top {g : ℂ → ℝ} (hg : Continuous g) (y : ℂ) :
    ‖g y‖ₑ ≤ eLpNorm g ⊤ volume := by
  rw [eLpNorm_exponent_top]
  have hae : ∀ᵐ z ∂(volume : Measure ℂ), ‖g z‖ₑ ≤ eLpNormEssSup g volume :=
    ae_le_eLpNormEssSup
  have hd : Dense {z | ‖g z‖ₑ ≤ eLpNormEssSup g volume} := Measure.dense_of_ae hae
  have hcl : IsClosed {z | ‖g z‖ₑ ≤ eLpNormEssSup g volume} :=
    isClosed_le hg.enorm continuous_const
  have huniv : {z | ‖g z‖ₑ ≤ eLpNormEssSup g volume} = univ := by
    rw [← hcl.closure_eq]
    exact hd.closure_eq
  have : y ∈ {z | ‖g z‖ₑ ≤ eLpNormEssSup g volume} := by
    rw [huniv]
    exact mem_univ y
  exact this

/-- `|g(y)| ≤ ‖g‖_{L^∞}` for continuous compactly supported `g`. -/
theorem abs_le_Amax {g : ℂ → ℝ} (hg : Continuous g) (hc : HasCompactSupport g) (y : ℂ) :
    |g y| ≤ Smooth.Amax g := by
  have hfin : eLpNorm g ⊤ volume ≠ ⊤ :=
    (hg.memLp_top_of_hasCompactSupport hc volume).eLpNorm_ne_top
  have h := ENNReal.toReal_mono hfin (enorm_le_eLpNorm_top hg y)
  rw [toReal_enorm, Real.norm_eq_abs] at h
  exact h

/-- `‖g‖_{L^∞} > 0` for continuous compactly supported `g ≢ 0`. -/
theorem Amax_pos {g : ℂ → ℝ} (hg : Continuous g) (hc : HasCompactSupport g) (hne : g ≠ 0) :
    0 < Smooth.Amax g := by
  obtain ⟨y, hy⟩ : ∃ y, g y ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  exact lt_of_lt_of_le (abs_pos.2 hy) (abs_le_Amax hg hc y)

theorem norm_e2 (l : Fin 2) : ‖Prelim.e2 l‖ = 1 := by
  fin_cases l <;> simp [Prelim.e2]

/-- `|∇g(y)| ≤ sup_x |∇g(x)|` for `g ∈ C¹_c`. -/
theorem norm_fderiv_le_gradSup {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (y : ℂ) : ‖fderiv ℝ g y‖ ≤ Smooth.gradSup g :=
  le_ciSup ((hg.continuous_fderiv one_ne_zero).norm.bddAbove_range_of_hasCompactSupport
    (hc.fderiv ℝ).norm) y

theorem gradSup_nonneg {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) :
    0 ≤ Smooth.gradSup g :=
  (norm_nonneg _).trans (norm_fderiv_le_gradSup hg hc 0)

/-- `|∂_l g(y)| ≤ ‖∇g‖_∞`. -/
theorem abs_fderiv_e2_le_gradSup {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (l : Fin 2) (y : ℂ) : |fderiv ℝ g y (Prelim.e2 l)| ≤ Smooth.gradSup g := by
  have := (fderiv ℝ g y).le_opNorm (Prelim.e2 l)
  rw [norm_e2, mul_one, Real.norm_eq_abs] at this
  exact this.trans (norm_fderiv_le_gradSup hg hc y)

/-- `∫ |g(x - z)| dz = ‖g‖_{L¹}`. -/
theorem integral_abs_comp_sub_eq_l1 {g : ℂ → ℝ} (hg : Continuous g) (x : ℂ) :
    ∫ z, |g (x - z)| = Smooth.l1 g := by
  rw [integral_sub_left_eq_self (fun z => |g z|) volume x, Smooth.l1,
    eLpNorm_one_eq_lintegral_enorm, ← integral_norm_eq_lintegral_enorm hg.aestronglyMeasurable]
  simp only [Real.norm_eq_abs]

theorem integrable_abs_comp_sub {g : ℂ → ℝ} (hg : Continuous g) (hc : HasCompactSupport g)
    (x : ℂ) : Integrable (fun z => |g (x - z)|) volume :=
  ((hg.integrable_of_hasCompactSupport hc).comp_sub_left x).abs

end NonUniqueEuler.GradBoundH
