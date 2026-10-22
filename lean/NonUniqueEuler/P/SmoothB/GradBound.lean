import NonUniqueEuler.Defs.SmoothB.Iteration
import NonUniqueEuler.H.SmoothB.GradBound.Core
import NonUniqueEuler.H.SmoothB.GradBound.Optimize

/-!
# Proof: `lem:grad-bound` (the log-Lipschitz bound on `∇(K_BS ∗ g)`)

Proof of `I/SmoothB/GradBound.lean` (`B_global_smooth.tex:114-147`). Same declaration, same
statement.

Structure (helpers in `H/SmoothB/GradBound/`):
1. `Velocity.lean`: `u = K_BS ∗ g ∈ C¹` and `∂_l u_i(x) = ∫ (K_BS)_i(z) ∂_l g(x - z) dz`
   (differentiation under the integral sign, Mathlib's convolution calculus).
2. `Core.lean`: for a smooth radial cutoff between radii `0 < a < b ≤ 1`, the near part is at most
   `b ‖∇g‖_∞`; whole-plane integration by parts (R6) and the bounds of `lem:BS-basic`(a) give
   `‖g‖_∞ (1 + log(1/a)) + ‖g‖₁/(2π)` for the rest (`Cutoff.lean`: the boundary term is
   `‖g‖_∞ ∫ ψ'(|z|)/(2π|z|) dz = ‖g‖_∞`; `Norms.lean`: `|g| ≤ ‖g‖_∞`, `|∂_l g| ≤ ‖∇g‖_∞`).
3. `Optimize.lean`: `a → b = δ`, then `δ = min(1, ‖g‖_∞/‖∇g‖_∞)`.

Deviation (R6): the manuscript's divergence theorem on
`{δ < |z| < ρ'}` with the sharp boundary `|z| = δ` is replaced by a smooth radial cutoff and
whole-plane integration by parts, followed by the limit of the cutoff to the sharp one; the
bounds are the manuscript's term by term.
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler.Smooth

/-- `lem:grad-bound`: for real `g ∈ C¹_c(ℝ²)`, `g ≢ 0`, and `u = K_BS ∗ g`, `u ∈ C¹` and for all
`x` and `i, l`,
`|∂_l u_i(x)| ≤ ‖g‖_{L^∞} (2 + log₊(‖∇g‖_{L^∞}/‖g‖_{L^∞})) + ‖g‖_{L¹}/(2π)`. -/
theorem grad_bound {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (hne : g ≠ 0) :
    ContDiff ℝ 1 (velocity g) ∧
      ∀ x : ℂ, ∀ i l : Fin 2,
        |Prelim.gradEntry (velocity g) i l x| ≤
          Amax g * (2 + Real.posLog (gradSup g / Amax g)) + l1 g / (2 * Real.pi) := by
  refine ⟨GradBoundH.contDiff_velocity_one hg hc, fun x i l => ?_⟩
  rw [GradBoundH.gradEntry_velocity_eq hg hc i l x]
  apply GradBoundH.le_of_forall_delta (GradBoundH.Amax_pos hg.continuous hc hne)
  intro δ hδ hδ1
  apply GradBoundH.le_of_forall_cutoff hδ
  intro a ha haδ
  exact GradBoundH.abs_integral_kernelComp_le ha haδ hδ1 i l hg hc x

end NonUniqueEuler.Smooth
