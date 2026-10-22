import NonUniqueEuler.Defs.Sec3.Auxiliary
import NonUniqueEuler.Defs.SmoothB.Iteration
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# Proof: the gradient bound of the cutoff `ς_R` (`03_compactness.tex:24-27`)

Proof of `I/Sec3/CutoffGrad.lean`. `fderiv ℝ ς` is continuous with compact support, hence
bounded; for `R > 0`, `ς_R = ς ∘ (R⁻¹ •)`, so `Dς_R(x) = R⁻¹ • Dς(R⁻¹x)` (`fderiv_comp_smul`)
and `‖Dς_R(x)‖ = R⁻¹ ‖Dς(R⁻¹x)‖ ≤ gradSup ς / R`.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler.Weak

/-- `‖∇ς‖_{L^∞}` is a genuine (finite) supremum: the values `‖Dς(x)‖` are bounded above, and
`Smooth.gradSup sigmaCut ≥ 0`. -/
theorem bddAbove_norm_fderiv_sigmaCut :
    BddAbove (range fun x : ℂ => ‖fderiv ℝ sigmaCut x‖) ∧ 0 ≤ Smooth.gradSup sigmaCut := by
  have hcont : Continuous (fderiv ℝ sigmaCut) :=
    isSpatialCutoff_sigmaCut.contDiff.continuous_fderiv (by simp)
  have hsupp : HasCompactSupport (fderiv ℝ sigmaCut) :=
    isSpatialCutoff_sigmaCut.hasCompactSupport.fderiv ℝ
  have hbdd : BddAbove (range fun x : ℂ => ‖fderiv ℝ sigmaCut x‖) :=
    hcont.norm.bddAbove_range_of_hasCompactSupport hsupp.norm
  refine ⟨hbdd, ?_⟩
  exact (norm_nonneg _).trans (le_ciSup hbdd (0 : ℂ))

/-- `03_compactness.tex:26-27`: `|∇ς_R| ≤ ‖∇ς‖_{L^∞}/R` for `R > 0`. -/
theorem norm_fderiv_sigmaCutR_le {R : ℝ} (hR : 0 < R) (x : ℂ) :
    ‖fderiv ℝ (sigmaCutR R) x‖ ≤ Smooth.gradSup sigmaCut / R := by
  have hfun : sigmaCutR R = fun y : ℂ => sigmaCut (R⁻¹ • y) := by
    funext y
    simp [sigmaCutR, Complex.real_smul, Complex.ofReal_inv]
  rw [hfun, fderiv_comp_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le),
    div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (le_ciSup bddAbove_norm_fderiv_sigmaCut.1 _)
    (inv_nonneg.mpr hR.le)

end NonUniqueEuler.Weak
