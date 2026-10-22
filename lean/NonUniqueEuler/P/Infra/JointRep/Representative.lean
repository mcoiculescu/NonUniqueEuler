import NonUniqueEuler.Defs.Infra.JointRep
import NonUniqueEuler.I.Infra.JointRep.Measurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Proof of (I-JOINT): jointly measurable representatives valid at every time

Proof of `I/Infra/JointRep/Representative.lean` (library I-JOINT).

Construction (a variant of the standard argument: the dense sequence is replaced by the simple
approximations `hu.approx n` of the strongly measurable path, which avoids enumerating a dense
subset of the range).
* `measurable_uncurry_simpleFunc_Lp`: for a simple function `f : SimpleFunc τ L²`, the function
  `(t, x) ↦ f t x` is jointly measurable (finite sum over the range of `f`).
* `exists_jointMeasurable_approx`: for `ε > 0` there is `ψ : τ → L²` with `(t, x) ↦ ψ t x`
  jointly measurable and `‖ψ t - u t‖ < ε` for **every** `t`: take `ψ t = hu.approx (n t) t`
  with `n t` the least index that is `ε`-close (`Measurable.find`).
* `isJointRep_limsup_of_geometric`: if `‖ψ N t - u t‖ < 2^{-N}` for every `N` and `t`, then
  `U t x = limsup_N ψ N t x` is jointly measurable (`Measurable.limsup`), and for each `t` the
  sequence `ψ N t` converges a.e. (`ae_tendsto_of_cauchy_eLpNorm`, the summable Cauchy bound) to a
  limit which is `u t` a.e. (an a.e. convergent subsequence: `tendstoInMeasure_of_tendsto_Lp`,
  `TendstoInMeasure.exists_seq_tendsto_ae`).
* Weakly continuous paths: `WeakContinuousOn.stronglyMeasurable_indicator`
  (`I/Infra/JointRep/Measurable.lean`) applied to `s.indicator u`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace NonUniqueEuler.JointRep

open NonUniqueEuler.WeakL2

variable {τ α : Type*} [MeasurableSpace τ] [MeasurableSpace α] {μ : Measure α}

/-- A simple path into `L²` is jointly measurable. -/
theorem measurable_uncurry_simpleFunc_Lp (f : SimpleFunc τ (Lp ℝ 2 μ)) :
    Measurable fun p : τ × α => (f p.1 : α → ℝ) p.2 := by
  classical
  have key : (fun p : τ × α => (f p.1 : α → ℝ) p.2) =
      fun p => ∑ v ∈ f.range, if f p.1 = v then (v : α → ℝ) p.2 else 0 := by
    funext p
    rw [Finset.sum_ite_eq, ite_eq_left (f.mem_range_self p.1)]
  rw [key]
  refine Finset.measurable_sum _ fun v _ => ?_
  refine Measurable.ite ?_ ((Lp.stronglyMeasurable v).measurable.comp measurable_snd)
    measurable_const
  exact measurable_fst (f.measurableSet_fiber v)

/-- An `ε`-approximation of a strongly measurable path, uniform in time, which is jointly
measurable. -/
theorem exists_jointMeasurable_approx {u : τ → Lp ℝ 2 μ} (hu : StronglyMeasurable u) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ ψ : τ → Lp ℝ 2 μ, Measurable (fun p : τ × α => (ψ p.1 : α → ℝ) p.2) ∧
      ∀ t, dist (ψ t) (u t) < ε := by
  classical
  set f := hu.approx
  have h : ∀ t, ∃ n, dist (f n t) (u t) < ε := fun t =>
    (Metric.tendsto_nhds.1 (hu.tendsto_approx t) ε hε).exists
  refine ⟨fun t => f (Nat.find (h t)) t, ?_, fun t => Nat.find_spec (h t)⟩
  have hp : ∀ n, MeasurableSet {p : τ × α | dist (f n p.1) (u p.1) < ε} := fun n =>
    measurable_fst (measurableSet_lt ((f n).stronglyMeasurable.dist hu).measurable
      measurable_const)
  exact Measurable.find (f := fun n (p : τ × α) => (f n p.1 : α → ℝ) p.2)
    (p := fun n (p : τ × α) => dist (f n p.1) (u p.1) < ε)
    (fun n => measurable_uncurry_simpleFunc_Lp (f n)) hp (fun p => h p.1)

/-- The Cauchy bound for a sequence that is `2^{-N}`-close to a fixed point. -/
theorem dist_lt_two_mul_of_geometric_close {E : Type*} [PseudoMetricSpace E] {ψ : ℕ → E}
    {v : E} (hd : ∀ N, dist (ψ N) v < (1 / 2 : ℝ) ^ N) {N n m : ℕ} (hn : N ≤ n) (hm : N ≤ m) :
    dist (ψ n) (ψ m) < 2 * (1 / 2 : ℝ) ^ N := by
  have h1 : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ N :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have h2 : (1 / 2 : ℝ) ^ m ≤ (1 / 2 : ℝ) ^ N :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
  calc dist (ψ n) (ψ m) ≤ dist (ψ n) v + dist (ψ m) v := dist_triangle_right _ _ _
    _ < (1 / 2 : ℝ) ^ n + (1 / 2 : ℝ) ^ m := add_lt_add (hd n) (hd m)
    _ ≤ 2 * (1 / 2 : ℝ) ^ N := by linarith

/-- The limit construction: a path that is approximated at rate `2^{-N}`, at every time, by
jointly measurable paths has a jointly measurable representative. -/
theorem isJointRep_limsup_of_geometric {ψ : ℕ → τ → Lp ℝ 2 μ} {u : τ → Lp ℝ 2 μ}
    (hψ : ∀ N, Measurable (fun p : τ × α => (ψ N p.1 : α → ℝ) p.2))
    (hd : ∀ N t, dist (ψ N t) (u t) < (1 / 2 : ℝ) ^ N) :
    IsJointRep (fun t x => limsup (fun N => (ψ N t : α → ℝ) x) atTop) u univ := by
  refine ⟨Measurable.limsup hψ, fun t _ => ?_⟩
  -- the full sequence converges a.e.
  have hB : ∑' N : ℕ, ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ N) ≠ ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun N => by positivity)
      (summable_geometric_two.mul_left 2)]
    exact ENNReal.ofReal_ne_top
  have h1 : ∀ᵐ x ∂μ, ∃ l : ℝ, Tendsto (fun N => (ψ N t : α → ℝ) x) atTop (𝓝 l) := by
    refine Lp.ae_tendsto_of_cauchy_eLpNorm (p := 2) (fun n => Lp.aestronglyMeasurable _)
      one_le_two hB fun N n m hn hm => ?_
    rw [← Lp.edist_def, edist_lt_ofReal]
    exact dist_lt_two_mul_of_geometric_close (fun N => hd N t) hn hm
  -- a subsequence converges a.e. to `u t`
  have hlim : Tendsto (fun N => ψ N t) atTop (𝓝 (u t)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ => dist_nonneg) (fun N => (hd N t).le)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  obtain ⟨ns, hns, h2⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  filter_upwards [h1, h2] with x ⟨l, hl⟩ hx
  rw [hl.limsup_eq]
  exact tendsto_nhds_unique (hl.comp hns.tendsto_atTop) hx

/-- A strongly measurable `L²`-valued path has a jointly measurable representative that is
correct at **every** time. -/
theorem exists_isJointRep_of_stronglyMeasurable {u : τ → Lp ℝ 2 μ}
    (hu : StronglyMeasurable u) : ∃ U : τ → α → ℝ, IsJointRep U u univ := by
  choose ψ hψm hψd using fun N : ℕ =>
    exists_jointMeasurable_approx (μ := μ) hu (ε := (1 / 2 : ℝ) ^ N) (by positivity)
  exact ⟨_, isJointRep_limsup_of_geometric hψm hψd⟩

/-- The chosen representative `jointRep u univ` of a strongly measurable path. -/
theorem isJointRep_jointRep_of_stronglyMeasurable {u : τ → Lp ℝ 2 μ}
    (hu : StronglyMeasurable u) : IsJointRep (jointRep u univ) u univ :=
  jointRep_spec (exists_isJointRep_of_stronglyMeasurable hu)

/-- A path that is weakly continuous on a measurable set `s` of times has a jointly measurable
representative that is correct at every time of `s`. -/
theorem exists_isJointRep_of_weakContinuousOn {u : ℝ → Lp ℝ 2 μ} {s : Set ℝ}
    (hs : MeasurableSet s) (hu : WeakContinuousOn u s) :
    ∃ U : ℝ → α → ℝ, IsJointRep U u s := by
  obtain ⟨U, hU⟩ := exists_isJointRep_of_stronglyMeasurable
    (hu.stronglyMeasurable_indicator hs)
  refine ⟨U, hU.measurable, fun t ht => ?_⟩
  have := hU.ae_eq t (mem_univ t)
  rwa [indicator_of_mem ht] at this

/-- The chosen representative `jointRep u s` of a path weakly continuous on `s`. -/
theorem isJointRep_jointRep_of_weakContinuousOn {u : ℝ → Lp ℝ 2 μ} {s : Set ℝ}
    (hs : MeasurableSet s) (hu : WeakContinuousOn u s) : IsJointRep (jointRep u s) u s :=
  jointRep_spec (exists_isJointRep_of_weakContinuousOn hs hu)

end NonUniqueEuler.JointRep
