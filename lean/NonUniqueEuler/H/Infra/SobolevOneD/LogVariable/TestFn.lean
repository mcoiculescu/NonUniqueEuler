import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import NonUniqueEuler.Defs.Infra.SobolevOneD

/-!
# Helpers for `P/Infra/SobolevOneD/LogVariable`: test functions under `r = e^x`

* `isTestFn_logPull`, `hasDerivAt_logPull`: for a test function `φ` on `ℝ`, the cut-off
  pullback `ψ = 1_{(0,∞)} · (φ ∘ log)` is a test function on `(0, ∞)`, with
  `ψ'(r) = r⁻¹ φ'(log r)` for `r > 0`;
* `isTestFn_comp_exp`, `hasDerivAt_comp_exp`: for a test function `ψ` on `(0, ∞)`, `ψ ∘ exp` is
  a test function on `ℝ`, with `(ψ ∘ exp)'(x) = e^x ψ'(e^x)`;
* `testFn_eq_zero`, `testFn_deriv_eq_zero`: vanishing outside the domain;
* `iterDirDeriv_derivList_one`: the first weak-derivative direction list gives `deriv`.

All proofs are complete.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace NonUniqueEuler.Sob.LogVarH

theorem iterDirDeriv_derivList_one (φ : ℝ → ℂ) : iterDirDeriv (derivList 1) φ = deriv φ := by
  rw [iterDirDeriv_derivList, iteratedDeriv_one]

theorem testFn_eq_zero {V : Set ℝ} {ψ : ℝ → ℂ} (hψ : IsTestFn V ψ) {r : ℝ}
    (hr : r ∉ V) : ψ r = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hr (hψ.subset h)

theorem testFn_deriv_eq_zero {V : Set ℝ} {ψ : ℝ → ℂ} (hψ : IsTestFn V ψ) {r : ℝ}
    (hr : r ∉ V) : deriv ψ r = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hr (hψ.subset (tsupport_deriv_subset h))

theorem testFn_hasDerivAt {V : Set ℝ} {ψ : ℝ → ℂ} (hψ : IsTestFn V ψ) (x : ℝ) :
    HasDerivAt ψ (deriv ψ x) x :=
  ((hψ.smooth.differentiable (by simp)).differentiableAt).hasDerivAt

/-- A test function on the line vanishes outside `[-M, M]` for some `M`. -/
theorem testFn_exists_bound {V : Set ℝ} {φ : ℝ → ℂ} (hφ : IsTestFn V φ) :
    ∃ M : ℝ, ∀ x, M < |x| → φ x = 0 := by
  obtain ⟨M, hM⟩ := (HasCompactSupport.isCompact hφ.compact).isBounded.subset_closedBall 0
  refine ⟨M, fun x hx => image_eq_zero_of_notMem_tsupport fun hx' => ?_⟩
  have := hM hx'
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
  linarith

theorem logPull_eq_zero {φ : ℝ → ℂ} {M : ℝ} (hM : ∀ x, M < |x| → φ x = 0) {r : ℝ}
    (hr : r ∉ Icc (Real.exp (-M)) (Real.exp M)) :
    (Ioi (0 : ℝ)).indicator (fun r => φ (Real.log r)) r = 0 := by
  by_cases h0 : 0 < r
  · rw [indicator_of_mem (show r ∈ Ioi (0 : ℝ) from h0)]
    apply hM
    rw [mem_Icc, not_and_or, not_le, not_le] at hr
    rcases hr with hr | hr
    · have : Real.log r < -M := (Real.log_lt_iff_lt_exp h0).2 hr
      exact lt_abs.2 (Or.inr (by linarith))
    · have : M < Real.log r := (Real.lt_log_iff_exp_lt h0).2 hr
      exact lt_abs.2 (Or.inl this)
  · exact indicator_of_notMem (show r ∉ Ioi (0 : ℝ) from h0) _

/-- The cut-off log-pullback of a test function on `ℝ` is a test function on `(0, ∞)`. -/
theorem isTestFn_logPull {φ : ℝ → ℂ} (hφ : IsTestFn univ φ) :
    IsTestFn (Ioi 0) ((Ioi (0 : ℝ)).indicator (fun r => φ (Real.log r))) := by
  obtain ⟨M, hM⟩ := testFn_exists_bound hφ
  set ψ := (Ioi (0 : ℝ)).indicator (fun r => φ (Real.log r)) with hψ_def
  have hzero : ∀ r, r ∉ Icc (Real.exp (-M)) (Real.exp M) → ψ r = 0 := fun r hr =>
    logPull_eq_zero hM hr
  have hsupp : Function.support ψ ⊆ Icc (Real.exp (-M)) (Real.exp M) := fun r hr =>
    by_contra fun h => hr (hzero r h)
  refine ⟨?_, HasCompactSupport.intro isCompact_Icc hzero, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro r
    by_cases h0 : 0 < r
    · have heq : ψ =ᶠ[𝓝 r] fun r => φ (Real.log r) := by
        filter_upwards [isOpen_Ioi.mem_nhds h0] with s hs
        exact indicator_of_mem hs _
      exact (hφ.smooth.contDiffAt.comp r (Real.contDiffAt_log.2 h0.ne')).congr_of_eventuallyEq
        heq
    · have hlt : r < Real.exp (-M) := lt_of_le_of_lt (not_lt.1 h0) (Real.exp_pos _)
      have heq : ψ =ᶠ[𝓝 r] fun _ => 0 := by
        filter_upwards [isOpen_Iio.mem_nhds hlt] with s hs
        exact hzero s fun h => absurd h.1 (not_le.2 hs)
      exact contDiffAt_const.congr_of_eventuallyEq heq
  · exact (closure_minimal hsupp isClosed_Icc).trans fun r hr =>
      lt_of_lt_of_le (Real.exp_pos _) hr.1

theorem hasDerivAt_logPull {φ : ℝ → ℂ} (hφ : IsTestFn univ φ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt ((Ioi (0 : ℝ)).indicator (fun r => φ (Real.log r)))
      (r⁻¹ • deriv φ (Real.log r)) r := by
  have h1 := (testFn_hasDerivAt hφ (Real.log r)).scomp r (Real.hasDerivAt_log hr.ne')
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hr] with s hs
  exact indicator_of_mem hs _

/-- The pushforward `ψ ∘ exp` of a test function on `(0, ∞)` is a test function on `ℝ`. -/
theorem isTestFn_comp_exp {ψ : ℝ → ℂ} (hψ : IsTestFn (Ioi 0) ψ) :
    IsTestFn univ (fun x => ψ (Real.exp x)) := by
  refine ⟨hψ.smooth.comp Real.contDiff_exp, ?_, subset_univ _⟩
  have hK : IsCompact (Real.log '' tsupport ψ) :=
    (HasCompactSupport.isCompact hψ.compact).image_of_continuousOn
      (Real.continuousOn_log.mono fun r hr => (hψ.subset hr).ne')
  refine HasCompactSupport.intro hK fun x hx => ?_
  by_contra h
  exact hx ⟨Real.exp x, subset_tsupport _ h, Real.log_exp x⟩

theorem hasDerivAt_comp_exp {ψ : ℝ → ℂ} (hψ : IsTestFn (Ioi 0) ψ) (x : ℝ) :
    HasDerivAt (fun x => ψ (Real.exp x)) (Real.exp x • deriv ψ (Real.exp x)) x :=
  (testFn_hasDerivAt hψ (Real.exp x)).scomp x (Real.hasDerivAt_exp x)

end NonUniqueEuler.Sob.LogVarH
