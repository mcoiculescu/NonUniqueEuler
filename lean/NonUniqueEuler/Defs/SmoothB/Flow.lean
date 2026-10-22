import NonUniqueEuler.Defs.SmoothB.ODE
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Appendix B: flows of smooth bounded vector fields on the plane (`lem:flow`)

Definitions (library I-FLOW) for Lemma `lem:flow`
(`B_global_smooth.tex:46-63`).

* `IsSmoothBoundedField u`: the hypotheses of `lem:flow`: `u ∈ C^∞(ℝ × ℝ²; ℝ²)` (a real vector
  field encoded in `ℂ`, D1) bounded on `[-T, T] × ℝ²` for every `T`;
* `flowOf u t s y = Φ_u(t, s, y)`: "the solution map of `ẋ = u(t,x)` from `lem:ode`(i)", i.e.
  `maxFlow u univ t s y` (`Defs/SmoothB/ODE.lean`). It is also the flow used for time-independent
  fields `V` (`05_single_ring.tex:1169`): `flowOf (fun _ => V)`.

`lem:flow`(a) says that `maxDomain u univ s y = univ` for all `s, y`, so that `flowOf u` is a
genuine global flow. The flow statements (a)–(d) are interface theorems (`I/SmoothB/…`); their
proofs use the generic flow results vendored in `Vendor/` (library I-FLOW). All
lemmas in this file are fully proved.
-/

noncomputable section

open Set
open scoped ContDiff

namespace NonUniqueEuler.Smooth

/-- The hypotheses of `lem:flow` (`B_global_smooth.tex:49-50`): `u ∈ C^∞(ℝ × ℝ²; ℝ²)` and `u` is
bounded on `[-T, T] × ℝ²` for every `T > 0`. -/
structure IsSmoothBoundedField (u : ℝ → ℂ → ℂ) : Prop where
  contDiff : ContDiff ℝ ∞ (Function.uncurry u)
  bounded : ∀ T : ℝ, 0 < T → ∃ M : ℝ, ∀ t ∈ Icc (-T) T, ∀ x : ℂ, ‖u t x‖ ≤ M

/-- The flow `Φ_u(t, s, y)` of `ẋ = u(t, x)` (`lem:flow`, `B_global_smooth.tex:50-51`): the value
at time `t` of the maximal solution with `x(s) = y` (`lem:ode`(i) with `U = ℝ × ℝ²`). -/
def flowOf (u : ℝ → ℂ → ℂ) (t s : ℝ) (y : ℂ) : ℂ :=
  maxFlow u univ t s y

/-! ### Basic lemmas (fully proved) -/

theorem flowOf_eq_of_isMaxSol {u : ℝ → ℂ → ℂ} {s : ℝ} {y : ℂ} {J : Set ℝ} {γ : ℝ → ℂ}
    (h : IsMaxSol u univ s y J γ) {t : ℝ} (ht : t ∈ J) : flowOf u t s y = γ t :=
  h.maxFlow_eq ht

/-- If the maximal solution with data `(s, y)` is global, `t ↦ flowOf u t s y` is that solution:
it solves `ẋ = u(t,x)` on `ℝ` with value `y` at `s`. -/
theorem flowOf_spec_of_maxDomain_eq_univ {u : ℝ → ℂ → ℂ} {s : ℝ} {y : ℂ}
    (hex : ∃ (J : Set ℝ) (γ : ℝ → ℂ), IsMaxSol u univ s y J γ)
    (hdom : maxDomain u univ s y = univ) :
    flowOf u s s y = y ∧ ∀ t, HasDerivAt (fun r => flowOf u r s y) (u t (flowOf u t s y)) t := by
  have h := isMaxSol_maxFlow hex
  rw [hdom] at h
  exact ⟨h.init, fun t => h.hasDerivAt t (mem_univ t)⟩

/-- Non-vacuity: the zero field satisfies the hypotheses of `lem:flow`. -/
theorem isSmoothBoundedField_zero : IsSmoothBoundedField fun _ _ => 0 :=
  ⟨contDiff_const, fun _ _ => ⟨0, fun _ _ _ => by simp⟩⟩

theorem IsSmoothBoundedField.continuous {u : ℝ → ℂ → ℂ} (h : IsSmoothBoundedField u) :
    Continuous (Function.uncurry u) :=
  h.contDiff.continuous

end NonUniqueEuler.Smooth
