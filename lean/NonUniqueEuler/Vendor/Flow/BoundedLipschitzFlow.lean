import NonUniqueEuler.Vendor.ODE.GlobalPicard
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.Homeomorph.Defs

/-!
# Vendored: the global flow of a bounded, uniformly Lipschitz time-dependent vector field

**Attribution.** Copied from the OpenAI baseline repository `NavierStokesAndEuler` (Apache-2.0),
files `Euler/BoundedLipschitzFlow.lean` (lines 1-125) and `Euler/BoundedFlowContinuity.lean`
(lines 1-98), concatenated. Only the namespace (`EulerBoundedLipschitzFlow` →
`NonUniqueEuler.Vendor.BoundedLipschitzFlow`), the imports, and the reference to the global
Picard theorem (`EulerPacketExistence.exists_global_solution` →
`NonUniqueEuler.Vendor.GlobalPicard.exists_global_solution`, already vendored in
`Vendor/ODE/GlobalPicard.lean`) were changed.

Content (generic real Banach space `E`): for `V : Data E` (a jointly continuous field
`velocity : ℝ → E → E`, uniformly Lipschitz in space with constant `lipschitzConstant` and
bounded by `speedBound`), the two-time flow `V.flow s t x` (the solution with value `x` at time
`s`, evaluated at time `t`), its uniqueness, cocycle and inverse identities, the Lipschitz bound
in time, the Grönwall bound in space, joint continuity, and the homeomorphisms `flowHomeomorph`.

Part of library I-FLOW. Bridge to the definitions of `Defs/SmoothB/Flow.lean`:
`NonUniqueEuler.Smooth.flowOf u t s y` (manuscript order `Φ_u(t, s, y)`) corresponds to
`V.flow s t y` here.
-/

noncomputable section

open Set Function Metric
open scoped Topology NNReal

namespace NonUniqueEuler.Vendor.BoundedLipschitzFlow

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

structure Data where
  velocity : ℝ → E → E
  continuous : Continuous (Function.uncurry velocity)
  lipschitzConstant : ℝ≥0
  lipschitz : ∀ t, LipschitzWith lipschitzConstant (velocity t)
  speedBound : ℝ≥0
  speed : ∀ t x, ‖velocity t x‖ ≤ speedBound

namespace Data

variable {E} [CompleteSpace E] (V : Data E)

theorem curve_exists (s : ℝ) (x : E) :
    ∃ α : ℝ → E, α s = x ∧ ∀ t, HasDerivAt α (V.velocity t (α t)) t := by
  have hc : Continuous (Function.uncurry (fun (t : ℝ) (y : E) => V.velocity (t+s) y)) :=
    V.continuous.comp ((continuous_fst.add continuous_const).prodMk continuous_snd)
  obtain ⟨α, hα0, hα⟩ := NonUniqueEuler.Vendor.GlobalPicard.exists_global_solution hc
    (fun t => V.lipschitz (t+s)) x
  refine ⟨fun t => α (t-s), by simpa using hα0, ?_⟩
  intro t
  have h := (hα (t-s)).scomp t ((hasDerivAt_id t).sub_const s)
  simpa only [Function.comp_def, id_eq, sub_add_cancel, one_smul] using h

def flow (s t : ℝ) (x : E) : E := (V.curve_exists s x).choose t

@[simp] theorem flow_initial (s : ℝ) (x : E) : V.flow s s x = x :=
  (V.curve_exists s x).choose_spec.1

theorem flow_hasDerivAt (s t : ℝ) (x : E) :
    HasDerivAt (fun r => V.flow s r x) (V.velocity t (V.flow s t x)) t :=
  (V.curve_exists s x).choose_spec.2 t

theorem flow_continuous_time (s : ℝ) (x : E) : Continuous (fun t => V.flow s t x) :=
  continuous_iff_continuousAt.mpr (fun t => (V.flow_hasDerivAt s t x).continuousAt)

theorem flow_unique (s : ℝ) (x : E) (α : ℝ → E)
    (hα : ∀ t, HasDerivAt α (V.velocity t (α t)) t) (hαs : α s = x) :
    α = fun t => V.flow s t x := by
  apply ODE_solution_unique_univ (v := V.velocity) (s := fun _ => Set.univ)
    (t₀ := s) (fun t => (V.lipschitz t).lipschitzOnWith)
    (fun t => ⟨hα t, Set.mem_univ _⟩)
    (fun t => ⟨V.flow_hasDerivAt s t x, Set.mem_univ _⟩)
  simpa only [V.flow_initial] using hαs

theorem flow_cocycle (r s t : ℝ) (x : E) :
    V.flow s t (V.flow r s x) = V.flow r t x := by
  have h := V.flow_unique s (V.flow r s x) (fun t => V.flow r t x)
    (fun t => V.flow_hasDerivAt r t x) rfl
  exact (congrFun h t).symm

@[simp] theorem flow_inverse (s t : ℝ) (x : E) :
    V.flow t s (V.flow s t x) = x := by
  rw [V.flow_cocycle, V.flow_initial]

theorem flow_lipschitz_time (s : ℝ) (x : E) :
    LipschitzWith V.speedBound (fun t => V.flow s t x) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun t => (V.flow_hasDerivAt s t x).differentiableAt)
  intro t
  rw [(V.flow_hasDerivAt s t x).deriv]
  exact_mod_cast V.speed t (V.flow s t x)

omit [CompleteSpace E] in
/-- A two-sided Grönwall estimate for actual global trajectories. -/
theorem trajectory_distance (α β : ℝ → E)
    (hα : ∀ t, HasDerivAt α (V.velocity t (α t)) t)
    (hβ : ∀ t, HasDerivAt β (V.velocity t (β t)) t) (a b : ℝ) :
    dist (α b) (β b) ≤ dist (α a) (β a) * Real.exp (V.lipschitzConstant * |b-a|) := by
  have hαc : Continuous α := continuous_iff_continuousAt.mpr (fun t => (hα t).continuousAt)
  have hβc : Continuous β := continuous_iff_continuousAt.mpr (fun t => (hβ t).continuousAt)
  by_cases hab : a ≤ b
  · have h := dist_le_of_trajectories_ODE V.lipschitz hαc.continuousOn
      (fun t _ => (hα t).hasDerivWithinAt) hβc.continuousOn
      (fun t _ => (hβ t).hasDerivWithinAt) (le_refl (dist (α a) (β a))) b ⟨hab, le_rfl⟩
    simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using h
  · have hba : b ≤ a := le_of_not_ge hab
    have hlip (t : ℝ) : LipschitzWith V.lipschitzConstant
        (fun x => -V.velocity (-t) x) := (V.lipschitz (-t)).neg
    have hαr (t : ℝ) :
        HasDerivAt (fun r => α (-r)) (-V.velocity (-t) (α (-t))) t := by
      simpa only [Function.comp_def, neg_smul, one_smul] using
        (hα (-t)).scomp t (hasDerivAt_neg t)
    have hβr (t : ℝ) :
        HasDerivAt (fun r => β (-r)) (-V.velocity (-t) (β (-t))) t := by
      simpa only [Function.comp_def, neg_smul, one_smul] using
        (hβ (-t)).scomp t (hasDerivAt_neg t)
    have h := dist_le_of_trajectories_ODE hlip
      (hαc.comp continuous_neg).continuousOn (fun t _ => (hαr t).hasDerivWithinAt)
      (hβc.comp continuous_neg).continuousOn (fun t _ => (hβr t).hasDerivWithinAt)
      (le_refl (dist (α (-(-a))) (β (-(-a))))) (-b) ⟨by linarith, le_rfl⟩
    have he : -b - (-a) = |b-a| := by
      rw [abs_of_nonpos (sub_nonpos.mpr hba)]
      ring
    simpa only [Function.comp_apply, neg_neg, he] using h

theorem flow_distance_initial (s t : ℝ) (x y : E) :
    dist (V.flow s t x) (V.flow s t y) ≤
      dist x y * Real.exp (V.lipschitzConstant * |t-s|) := by
  simpa only [V.flow_initial] using V.trajectory_distance
    (fun t => V.flow s t x) (fun t => V.flow s t y)
    (fun t => V.flow_hasDerivAt s t x) (fun t => V.flow_hasDerivAt s t y) s t

end Data

end NonUniqueEuler.Vendor.BoundedLipschitzFlow

noncomputable section

open Set Function Metric
open scoped Topology NNReal

namespace NonUniqueEuler.Vendor.BoundedLipschitzFlow.Data

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (V : NonUniqueEuler.Vendor.BoundedLipschitzFlow.Data E)

theorem flow_distance (s t s₀ t₀ : ℝ) (x x₀ : E) :
    dist (V.flow s t x) (V.flow s₀ t₀ x₀) ≤
      (dist x x₀ + V.speedBound*|s-s₀|) *
        Real.exp (V.lipschitzConstant*|t-s|) + V.speedBound*|t-t₀| := by
  have hs : dist x₀ (V.flow s₀ s x₀) ≤ V.speedBound*|s-s₀| := by
    simpa only [V.flow_initial, Real.dist_eq, abs_sub_comm s₀ s] using
      (V.flow_lipschitz_time s₀ x₀).dist_le_mul s₀ s
  have hx : dist x (V.flow s₀ s x₀) ≤ dist x x₀ + V.speedBound*|s-s₀| :=
    (dist_triangle x x₀ (V.flow s₀ s x₀)).trans (add_le_add (le_refl _) hs)
  have hspace := V.flow_distance_initial s t x (V.flow s₀ s x₀)
  rw [V.flow_cocycle] at hspace
  have ht : dist (V.flow s₀ t x₀) (V.flow s₀ t₀ x₀) ≤ V.speedBound*|t-t₀| := by
    simpa only [Real.dist_eq] using (V.flow_lipschitz_time s₀ x₀).dist_le_mul t t₀
  calc
    _ ≤ dist (V.flow s t x) (V.flow s₀ t x₀) + dist (V.flow s₀ t x₀) (V.flow s₀ t₀ x₀) :=
      dist_triangle _ _ _
    _ ≤ dist x (V.flow s₀ s x₀) * Real.exp (V.lipschitzConstant*|t-s|) +
        V.speedBound*|t-t₀| := add_le_add hspace ht
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le) (le_refl _)

theorem flow_joint_continuous :
    Continuous (fun p : ℝ × (ℝ × E) => V.flow p.1 p.2.1 p.2.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p₀
  apply tendsto_iff_dist_tendsto_zero.2
  have hc : Continuous (fun p : ℝ × (ℝ × E) =>
      (dist p.2.2 p₀.2.2 + V.speedBound*|p.1-p₀.1|) *
        Real.exp (V.lipschitzConstant*|p.2.1-p.1|) + V.speedBound*|p.2.1-p₀.2.1|) := by
    fun_prop
  apply squeeze_zero
    (f := fun p : ℝ × (ℝ × E) => dist (V.flow p.1 p.2.1 p.2.2)
      (V.flow p₀.1 p₀.2.1 p₀.2.2))
    (g := fun p : ℝ × (ℝ × E) =>
      (dist p.2.2 p₀.2.2 + V.speedBound*|p.1-p₀.1|) *
        Real.exp (V.lipschitzConstant*|p.2.1-p.1|) + V.speedBound*|p.2.1-p₀.2.1|)
    (fun _ => dist_nonneg)
    (fun p => V.flow_distance p.1 p.2.1 p₀.1 p₀.2.1 p.2.2 p₀.2.2)
  simpa only [dist_self, sub_self, abs_zero, mul_zero, add_zero, zero_mul] using
    hc.tendsto p₀

def flowHomeomorph (s t : ℝ) : E ≃ₜ E where
  toFun := V.flow s t
  invFun := V.flow t s
  left_inv := V.flow_inverse s t
  right_inv := V.flow_inverse t s
  continuous_toFun := V.flow_joint_continuous.comp
    (continuous_const.prodMk (continuous_const.prodMk continuous_id))
  continuous_invFun := V.flow_joint_continuous.comp
    (continuous_const.prodMk (continuous_const.prodMk continuous_id))

def forward (t : ℝ) (x : E) : E := V.flow 0 t x

def backward (t : ℝ) (x : E) : E := V.flow t 0 x

@[simp] theorem backward_forward (t : ℝ) (x : E) :
    V.backward t (V.forward t x) = x := V.flow_inverse 0 t x

@[simp] theorem forward_backward (t : ℝ) (x : E) :
    V.forward t (V.backward t x) = x := V.flow_inverse t 0 x

@[simp] theorem forward_zero (x : E) : V.forward 0 x = x := V.flow_initial 0 x

@[simp] theorem backward_zero (x : E) : V.backward 0 x = x := V.flow_initial 0 x

theorem forward_hasDerivAt (t : ℝ) (x : E) :
    HasDerivAt (fun s => V.forward s x) (V.velocity t (V.forward t x)) t :=
  V.flow_hasDerivAt 0 t x

theorem forward_joint_continuous : Continuous (Function.uncurry V.forward) :=
  V.flow_joint_continuous.comp (continuous_const.prodMk continuous_id)

theorem backward_joint_continuous : Continuous (Function.uncurry V.backward) :=
  V.flow_joint_continuous.comp
    (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))

theorem forward_displacement (t : ℝ) (x : E) :
    dist (V.forward t x) x ≤ V.speedBound*|t| := by
  simpa only [forward, V.flow_initial, Real.dist_eq, sub_zero] using
    (V.flow_lipschitz_time 0 x).dist_le_mul t 0

end NonUniqueEuler.Vendor.BoundedLipschitzFlow.Data
