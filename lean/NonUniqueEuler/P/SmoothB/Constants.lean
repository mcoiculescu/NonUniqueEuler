import NonUniqueEuler.Defs.SmoothB.Iteration
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-!
# Proof: the constants of §B.3 (monotonicity, `𝓛' = V`, the inner radius `R₀'`)

Proof of `I/SmoothB/Constants.lean` (`B_global_smooth.tex:193-197`).

* Monotonicity: `𝓛(t) = (log₊(N₀/A) + c_*) e^{2A|t|} - c_*` with `log₊(N₀/A) + c_* ≥ 0` and
  `A ≥ 0`; `Ψ = A e^{𝓛}` and `V = 2A(𝓛 + c_*)` are monotone functions of `𝓛`.
* `𝓛' = V` on `(0, ∞)`: near `t > 0`, `|s| = s`, and
  `d/dt[(P + c_*)e^{2At}] = 2A(P + c_*)e^{2At} = 2A(𝓛(t) + c_*)`.
* `R₀'`: `tsupport ω₀` is closed and contained in the open ball `B_{R₀}` of the proper space `ℂ`,
  so it is contained in a smaller ball (`exists_lt_subset_ball`).
-/

noncomputable section

open Set Metric

namespace NonUniqueEuler.Smooth

/-- `𝓛` is nondecreasing in `|t|` (`B_global_smooth.tex:193-194`). -/
theorem calL_mono (ω₀ : ℂ → ℝ) {t t' : ℝ} (h : |t| ≤ |t'|) : calL ω₀ t ≤ calL ω₀ t' := by
  have hA : 0 ≤ 2 * Amax ω₀ := mul_nonneg zero_le_two (Amax_nonneg ω₀)
  have hP : 0 ≤ Real.posLog (N0 ω₀ / Amax ω₀) + cstar ω₀ :=
    add_nonneg Real.posLog_nonneg (le_trans zero_le_two (cstar_ge_two ω₀))
  have he : Real.exp (2 * Amax ω₀ * |t|) ≤ Real.exp (2 * Amax ω₀ * |t'|) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h hA)
  have := mul_le_mul_of_nonneg_left he hP
  simp only [calL]
  linarith

/-- `Ψ` is nondecreasing in `|t|` (`B_global_smooth.tex:193-194`). -/
theorem Psi_mono (ω₀ : ℂ → ℝ) {t t' : ℝ} (h : |t| ≤ |t'|) : Psi ω₀ t ≤ Psi ω₀ t' :=
  mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (calL_mono ω₀ h)) (Amax_nonneg ω₀)

/-- `V` is nondecreasing in `|t|` (`B_global_smooth.tex:193-194`). -/
theorem Vbd_mono (ω₀ : ℂ → ℝ) {t t' : ℝ} (h : |t| ≤ |t'|) : Vbd ω₀ t ≤ Vbd ω₀ t' :=
  mul_le_mul_of_nonneg_left (by linarith [calL_mono ω₀ h])
    (mul_nonneg zero_le_two (Amax_nonneg ω₀))

/-- `𝓛' = V` on `(0, ∞)` (`B_global_smooth.tex:195`). -/
theorem hasDerivAt_calL (ω₀ : ℂ → ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (calL ω₀) (Vbd ω₀ t) t := by
  set P := Real.posLog (N0 ω₀ / Amax ω₀) + cstar ω₀
  set A := Amax ω₀
  -- The model function `s ↦ P e^{2As} - c_*`, equal to `𝓛` near `t > 0`.
  have hlin : HasDerivAt (fun s : ℝ => 2 * A * s) (2 * A) t := by
    simpa using (hasDerivAt_id t).const_mul (2 * A)
  have hmodel : HasDerivAt (fun s : ℝ => P * Real.exp (2 * A * s) - cstar ω₀)
      (P * (Real.exp (2 * A * t) * (2 * A))) t :=
    (hlin.exp.const_mul P).sub_const (cstar ω₀)
  have heq : (fun s : ℝ => P * Real.exp (2 * A * s) - cstar ω₀) =ᶠ[nhds t] calL ω₀ := by
    filter_upwards [lt_mem_nhds ht] with s hs
    simp only [calL, abs_of_pos hs, P, A]
  have hval : P * (Real.exp (2 * A * t) * (2 * A)) = Vbd ω₀ t := by
    simp only [Vbd, calL, abs_of_pos ht, P, A]
    ring
  rw [← hval]
  exact hmodel.congr_of_eventuallyEq heq.symm

/-- The inner radius (`B_global_smooth.tex:195-197`): if `supp ω₀ ⊂ B_{R₀}` with `ω₀ ∈ C_c^∞`,
there is `R₀' < R₀` with `ω₀ = 0` outside `\bar B_{R₀'}`. -/
theorem exists_inner_radius {ω₀ : ℂ → ℝ} {R₀ : ℝ} (h : IsSmoothDatum ω₀ R₀) :
    ∃ R₀' : ℝ, R₀' < R₀ ∧ ∀ x : ℂ, R₀' < ‖x‖ → ω₀ x = 0 := by
  obtain ⟨r, hr, hsub⟩ := exists_lt_subset_ball (isClosed_tsupport ω₀) h.tsupport_subset
  refine ⟨r, hr, fun x hx => image_eq_zero_of_notMem_tsupport fun hmem => ?_⟩
  have := hsub hmem
  rw [mem_ball, dist_zero_right] at this
  linarith

end NonUniqueEuler.Smooth
