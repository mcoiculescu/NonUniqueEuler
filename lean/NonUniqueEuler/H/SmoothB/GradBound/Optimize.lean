import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Topology.Order.OrderClosed

/-!
# Helper for `lem:grad-bound`: the limit `a → δ` and the choice of `δ`

Helper of `P/SmoothB/GradBound.lean` (`B_global_smooth.tex:144-147`). Pure real-number facts:
* `le_of_forall_cutoff`: a bound `X ≤ δN + A + A log(1/a) + L` for every `a ∈ (0, δ)` gives the
  same bound at `a = δ` (the cutoff of `Core.lean` tends to the sharp cut at `δ`);
* `le_of_forall_delta`: the bound `X ≤ δN + A(1 + log(1/δ)) + L` for every `δ ∈ (0, 1]` gives
  `X ≤ A(2 + log₊(N/A)) + L`, with `δ = min(1, A/N)` (the manuscript's choice).
-/

noncomputable section

open Set Filter Topology

namespace NonUniqueEuler.GradBoundH

/-- The limit `a → δ⁻` in the cutoff. -/
theorem le_of_forall_cutoff {X N A L δ : ℝ} (hδ : 0 < δ)
    (h : ∀ a, 0 < a → a < δ → X ≤ δ * N + A + A * Real.log (1 / a) + L) :
    X ≤ δ * N + A + A * Real.log (1 / δ) + L := by
  have hlog : ContinuousAt (fun a : ℝ => Real.log (1 / a)) δ :=
    (Real.continuousAt_log (by positivity)).comp
      (continuousAt_const.div continuousAt_id hδ.ne')
  have hcont : ContinuousAt (fun a : ℝ => δ * N + A + A * Real.log (1 / a) + L) δ :=
    (continuousAt_const.add (continuousAt_const.mul hlog)).add continuousAt_const
  have ht := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio δ))
  refine ge_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsLT hδ] with a ha using h a ha.1 ha.2

/-- The choice `δ = min(1, A/N)` (`B_global_smooth.tex:146-147`). -/
theorem le_of_forall_delta {X N A L : ℝ} (hA : 0 < A)
    (h : ∀ δ, 0 < δ → δ ≤ 1 → X ≤ δ * N + A + A * Real.log (1 / δ) + L) :
    X ≤ A * (2 + Real.posLog (N / A)) + L := by
  have hp : 0 ≤ A * Real.posLog (N / A) := mul_nonneg hA.le Real.posLog_nonneg
  by_cases hNA : N ≤ A
  · have h1 := h 1 one_pos le_rfl
    have e : Real.log (1 / 1) = 0 := by simp
    rw [e] at h1
    nlinarith
  · push Not at hNA
    have hN0 : 0 < N := hA.trans hNA
    have hδ : 0 < A / N := div_pos hA hN0
    have hδ1 : A / N ≤ 1 := (div_le_one hN0).2 hNA.le
    have h1 := h (A / N) hδ hδ1
    have e1 : A / N * N = A := div_mul_cancel₀ A hN0.ne'
    have e2 : 1 / (A / N) = N / A := one_div_div A N
    have e3 : Real.posLog (N / A) = Real.log (N / A) := by
      apply Real.posLog_eq_log
      rw [abs_of_pos (div_pos hN0 hA)]
      exact (one_le_div hA).2 hNA.le
    rw [e1, e2] at h1
    rw [e3]
    linarith

end NonUniqueEuler.GradBoundH
