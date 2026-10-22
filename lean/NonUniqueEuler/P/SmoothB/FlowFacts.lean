import NonUniqueEuler.I.SmoothB.Flow
import NonUniqueEuler.Defs.SmoothB.Flow
import NonUniqueEuler.Defs.Sec2.Conventions
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Proof of `I/SmoothB/FlowFacts.lean` (I-FLOW): standard consequences of `lem:flow`

All facts follow from `lem:flow` (`I/SmoothB/Flow.lean`) and the uniqueness built into
`IsMaxSol`:
* `flowOf_measurePreserving`: change of variables (`lintegral_abs_det_fderiv_eq_addHaar_image`)
  with `det DΦ = 1` (`det_fderiv_flowOf`) and bijectivity (`flowOf_diffeo`);
* `flowOf_rot`, `flowOf_autonomous_shift`, `flowOf_eq_self_of_zero`: a global solution with the
  right initial value equals the flow (`FlowFactsAux.flowOf_eq_of_solution`, from
  `IsMaxSol.maximal` of `flowOf_global`);
* `flowOf_autonomous_add`: cocycle identity plus the shift;
* `hasDerivAt_comp_flowOf`: `F(τ, z) = g(Φ_u(s, τ, z))` is `C¹` and constant along
  `τ ↦ (τ, Φ_u(τ, t, x))` (cocycle), whose velocity at `τ = t` is `(1, u(t, x))`.
-/

noncomputable section

open Set MeasureTheory

namespace NonUniqueEuler.Smooth

variable {u : ℝ → ℂ → ℂ}

namespace FlowFactsAux

/-- A solution of `ẋ = u(τ, x)` on all of `ℝ` with value `y` at `s` is the flow from `(s, y)`
(uniqueness, `IsMaxSol.maximal` of `flowOf_global`). -/
theorem flowOf_eq_of_solution (hu : IsSmoothBoundedField u) {s : ℝ} {y : ℂ} {γ : ℝ → ℂ}
    (h0 : γ s = y) (hγ : ∀ τ, HasDerivAt γ (u τ (γ τ)) τ) (t : ℝ) :
    flowOf u t s y = γ t := by
  have hloc : IsLocalSol u univ s y univ γ :=
    { isOpen := isOpen_univ
      ordConnected := ordConnected_univ
      mem := mem_univ s
      init := h0
      graph := fun _ _ => mem_univ _
      hasDerivAt := fun τ _ => hγ τ }
  exact (((flowOf_global hu s y).2.maximal univ γ hloc).2 (mem_univ t)).symm

/-- `Φ_u(s, s, y) = y`. -/
theorem flowOf_self (hu : IsSmoothBoundedField u) (s : ℝ) (y : ℂ) : flowOf u s s y = y :=
  (flowOf_global hu s y).2.init

/-- `τ ↦ Φ_u(τ, s, y)` solves `ẋ = u(τ, x)`. -/
theorem hasDerivAt_flowOf (hu : IsSmoothBoundedField u) (s : ℝ) (y : ℂ) (τ : ℝ) :
    HasDerivAt (fun r => flowOf u r s y) (u τ (flowOf u τ s y)) τ :=
  (flowOf_global hu s y).2.hasDerivAt τ (mem_univ τ)

/-- `(τ, z) ↦ Φ_u(s, τ, z)` is `C^∞`. -/
theorem contDiff_flowOf_fst (hu : IsSmoothBoundedField u) (s : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℂ => flowOf u s p.1 p.2) := by
  have h := flowOf_contDiff hu
  have hm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℂ => (s, p.1, p.2)) :=
    contDiff_const.prodMk (contDiff_fst.prodMk contDiff_snd)
  exact h.comp hm

end FlowFactsAux

open FlowFactsAux

/-- A divergence-free smooth field bounded on slabs has area-preserving flow maps. -/
theorem flowOf_measurePreserving (hu : IsSmoothBoundedField u)
    (hdiv : ∀ t : ℝ, ∀ x : ℂ, Prelim.divergence (u t) x = 0) (t s : ℝ) :
    MeasurePreserving (flowOf u t s) volume volume := by
  obtain ⟨hleft, hright, hsmooth, -⟩ := flowOf_diffeo hu t s
  have hmeas : Measurable (flowOf u t s) := hsmooth.continuous.measurable
  have hdiff : Differentiable ℝ (flowOf u t s) := hsmooth.differentiable (by simp)
  refine ⟨hmeas, ?_⟩
  ext A hA
  rw [Measure.map_apply hmeas hA]
  have key := lintegral_abs_det_fderiv_eq_addHaar_image (volume : Measure ℂ) (hmeas hA)
    (fun x _ => (hdiff x).hasFDerivAt.hasFDerivWithinAt) hleft.injective.injOn
  simp only [det_fderiv_flowOf hu hdiv, abs_one, ENNReal.ofReal_one, setLIntegral_one] at key
  rw [key, image_preimage_eq A hright.surjective]

/-- Rotation equivariance: if `u(t, O_θ x) = O_θ u(t, x)`, then
`Φ_u(t, s, O_θ y) = O_θ Φ_u(t, s, y)`. -/
theorem flowOf_rot (hu : IsSmoothBoundedField u) {θ : ℝ}
    (hequi : ∀ t : ℝ, ∀ x : ℂ, u t (rot θ x) = rot θ (u t x)) (t s : ℝ) (y : ℂ) :
    flowOf u t s (rot θ y) = rot θ (flowOf u t s y) := by
  refine flowOf_eq_of_solution hu (γ := fun τ => rot θ (flowOf u τ s y))
    (congrArg (rot θ) (flowOf_self hu s y)) (fun τ => ?_) t
  show HasDerivAt (fun τ => rot θ (flowOf u τ s y)) (u τ (rot θ (flowOf u τ s y))) τ
  rw [hequi]
  exact (hasDerivAt_flowOf hu s y τ).const_mul (Complex.exp ((θ : ℂ) * Complex.I))

/-- Time-independent fields: the flow depends only on `t - s`. -/
theorem flowOf_autonomous_shift {V : ℂ → ℂ} (hV : IsSmoothBoundedField fun _ => V)
    (t s : ℝ) (y : ℂ) :
    flowOf (fun _ => V) t s y = flowOf (fun _ => V) (t - s) 0 y := by
  refine flowOf_eq_of_solution hV (γ := fun τ => flowOf (fun _ => V) (τ - s) 0 y) ?_
    (fun τ => ?_) t
  · show flowOf (fun _ => V) (s - s) 0 y = y
    rw [sub_self]
    exact flowOf_self hV 0 y
  · exact (hasDerivAt_flowOf hV 0 y (τ - s)).comp_sub_const τ s

/-- Time-independent fields: `Y_{κ + κ'} = Y_κ ∘ Y_{κ'}` for `Y_κ = Φ_V(κ, 0, ·)`. -/
theorem flowOf_autonomous_add {V : ℂ → ℂ} (hV : IsSmoothBoundedField fun _ => V)
    (κ κ' : ℝ) (y : ℂ) :
    flowOf (fun _ => V) (κ + κ') 0 y = flowOf (fun _ => V) κ 0 (flowOf (fun _ => V) κ' 0 y) := by
  rw [← flowOf_cocycle hV (κ + κ') κ' 0 y, flowOf_autonomous_shift hV (κ + κ') κ',
    add_sub_cancel_right]

/-- A point where the field vanishes at all times is fixed by the flow. -/
theorem flowOf_eq_self_of_zero (hu : IsSmoothBoundedField u) {y : ℂ}
    (hy : ∀ t : ℝ, u t y = 0) (t s : ℝ) :
    flowOf u t s y = y := by
  refine flowOf_eq_of_solution hu (γ := fun _ => y) rfl (fun τ => ?_) t
  show HasDerivAt (fun _ => y) (u τ y) τ
  rw [hy τ]
  exact hasDerivAt_const τ y

/-- Transport by the flow: for `g ∈ C¹(ℝ²)` real, `w(t, x) = g(Φ_u(s, t, x))` (so
`w(t) = w(s) ∘ Φ_u(t, s, ·)⁻¹`) satisfies `∂_t w + u · ∇w = 0` on `ℝ × ℝ²`. -/
theorem hasDerivAt_comp_flowOf (hu : IsSmoothBoundedField u) {g : ℂ → ℝ}
    (hg : ContDiff ℝ 1 g) (s t : ℝ) (x : ℂ) :
    HasDerivAt (fun τ => g (flowOf u s τ x))
      (-(fderiv ℝ (fun z => g (flowOf u s t z)) x (u t x))) t := by
  -- `F(τ, z) = g(Φ_u(s, τ, z))` is `C¹`.
  set F : ℝ × ℂ → ℝ := fun p => g (flowOf u s p.1 p.2) with hFdef
  have hF : ContDiff ℝ 1 F :=
    hg.comp ((contDiff_flowOf_fst hu s).of_le (by exact_mod_cast le_top))
  set L := fderiv ℝ F (t, x) with hLdef
  have hFL : HasFDerivAt F L (t, x) := (hF.differentiable (by simp) (t, x)).hasFDerivAt
  -- `F` is constant along `γ(τ) = Φ_u(τ, t, x)`.
  have hγ := hasDerivAt_flowOf hu t x t
  rw [flowOf_self hu t x] at hγ
  have hpath : HasDerivAt (fun τ => (τ, flowOf u τ t x)) ((1 : ℝ), u t x) t :=
    (hasDerivAt_id t).prodMk hγ
  have h1 : HasDerivAt (F ∘ fun τ => (τ, flowOf u τ t x)) (L ((1 : ℝ), u t x)) t := by
    refine HasFDerivAt.comp_hasDerivAt t ?_ hpath
    simpa only [flowOf_self hu t x] using hFL
  have hconst : (F ∘ fun τ => (τ, flowOf u τ t x)) = fun _ => g (flowOf u s t x) := by
    funext τ
    simp only [Function.comp_apply, hFdef, flowOf_cocycle hu s τ t x]
  rw [hconst] at h1
  have hzero : L ((1 : ℝ), u t x) = 0 := h1.unique (hasDerivAt_const t _)
  -- The spatial derivative.
  have hsp : HasFDerivAt (fun z => g (flowOf u s t z)) (L.comp (ContinuousLinearMap.inr ℝ ℝ ℂ))
      x := hFL.comp x (hasFDerivAt_prodMk_right t x)
  rw [hsp.fderiv]
  -- The time derivative.
  have htime : HasDerivAt (F ∘ fun τ => (τ, x)) (L ((1 : ℝ), (0 : ℂ))) t :=
    hFL.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  have hsplit : ((1 : ℝ), (0 : ℂ)) = ((1 : ℝ), u t x) - ((0 : ℝ), u t x) := by simp
  rw [hsplit, map_sub, hzero, zero_sub] at htime
  have htime' : HasDerivAt (fun τ => g (flowOf u s τ x)) (-L ((0 : ℝ), u t x)) t := htime
  simpa using htime'

end NonUniqueEuler.Smooth
