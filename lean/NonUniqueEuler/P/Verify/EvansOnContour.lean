import NonUniqueEuler.Defs.Verify.Contour
import NonUniqueEuler.Statement.Evans
import NonUniqueEuler.I.Evans.ODE
import NonUniqueEuler.I.Verify.ContourGeom
import Mathlib.Analysis.Complex.Basic

/-!
# Proof: the Evans function along a rectangle contour in the right half-plane

Proof of the interface `NonUniqueEuler/I/Verify/EvansOnContour.lean` (same declarations, same
statements). Manuscript: proof of Proposition A.7 (`A_verification.tex:640-643`) and
Lemma A.6 (`:538-540`).

* `continuous_evans_bdryPath`: `evans_differentiableOn` (`I/Evans/ODE.lean`) gives continuity
  of `E_ℓ(·; G)` on `{Re z > 0}`; the boundary curve is continuous
  (`QRect.continuous_bdryPath`) and has real part `≥ x₀ > 0` (`QRect.x₀_le_re_bdryPath`,
  `I/Verify/ContourGeom.lean`), so `ContinuousOn.comp_continuous` applies.
* `evans_holo_near_rect`: `isOpen_lt` for openness, `QRect.closedSet_subset_re_pos`
  (`Defs/Verify/Contour.lean`) for the inclusion, `evans_differentiableOn` for holomorphy.
-/

open Set

namespace NonUniqueEuler

open RingData

/-- `t ↦ E_ℓ(R.bdryPath t; G)` is continuous when the rectangle lies in `{Re λ > 0}`. -/
theorem continuous_evans_bdryPath {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (ℓ : ℕ) {R : QRect}
    (hx : 0 < R.x₀) (hR : R.x₀ ≤ R.x₁) (G : ℝ) :
    Continuous fun t => evans χ ℓ (R.bdryPath t) G := by
  have hx' : (0 : ℝ) < R.x₀ := by exact_mod_cast hx
  exact (evans_differentiableOn χ hχ ℓ G).continuousOn.comp_continuous
    (QRect.continuous_bdryPath R)
    (fun t => show 0 < (R.bdryPath t).re from
      lt_of_lt_of_le hx' (QRect.x₀_le_re_bdryPath hR t))

/-- `E_ℓ(·; G)` is holomorphic on the open half-plane `{Re λ > 0}`, an open set containing the
closed rectangle when its left edge is positive. -/
theorem evans_holo_near_rect {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (ℓ : ℕ) {R : QRect}
    (hx : 0 < R.x₀) (G : ℝ) :
    IsOpen {z : ℂ | 0 < z.re} ∧ R.closedSet ⊆ {z : ℂ | 0 < z.re} ∧
      DifferentiableOn ℂ (fun z => evans χ ℓ z G) {z : ℂ | 0 < z.re} :=
  ⟨isOpen_lt continuous_const Complex.continuous_re, QRect.closedSet_subset_re_pos hx,
    evans_differentiableOn χ hχ ℓ G⟩

end NonUniqueEuler
