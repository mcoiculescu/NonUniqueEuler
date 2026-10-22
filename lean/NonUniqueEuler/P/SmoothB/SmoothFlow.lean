import NonUniqueEuler.Defs.SmoothB.Solution
import NonUniqueEuler.I.SmoothB.Smooth
import NonUniqueEuler.I.SmoothB.Flow
import NonUniqueEuler.I.SmoothB.FlowFacts
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Proof: thm:smooth (4) (the flow of the smooth solution)

Proof of `I/SmoothB/SmoothFlow.lean` (`02_prelim.tex:572-579`, proof
`B_global_smooth.tex:522-531`).

* `vel_isSmoothBoundedField`: thm:smooth (2) (`sol_isSmoothSol`, `SolCore.velocity_contDiff`,
  `SolCore.velocity_bounded` with `n = 0`);
* `flow_global`, `flow_diffeo`, `flow_contDiff`, `flow_measurePreserving`: `lem:flow`
  (`flowOf_global`, `flowOf_diffeo`, `flowOf_contDiff`, `det_fderiv_flowOf`) and
  `flowOf_measurePreserving`, with `div v = 0` from thm:smooth (2);
* `sol_eq_comp_flowInv`: `t ↦ ω(t, Φ(t, a))` has derivative
  `(∂_t ω + v · ∇ω)(t, Φ(t, a)) = 0` by (3) (chain rule for the `C^∞` map `(t, x) ↦ ω(t, x)`),
  hence is constant `= ω₀(a)`; then `x = Φ_t(Φ_t⁻¹ x)`;
* `integral_comp_sol`: `F ∘ ω(t)` is continuous with compact support (supports in
  `B_{R(t)}`, `F(0) = 0`), and `∫ F(ω₀ ∘ Φ_t⁻¹) = ∫ F(ω₀)` since `Φ_t⁻¹` preserves `volume`
  (`integral_map`).
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler.Smooth

variable {ω₀ : ℂ → ℝ} {R₀ : ℝ}

/-- thm:smooth (2) in the form needed for `lem:flow`: `v` is smooth and bounded on every slab. -/
theorem vel_isSmoothBoundedField (h : IsSmoothDatum ω₀ R₀) : IsSmoothBoundedField (vel ω₀) := by
  have hs := (sol_isSmoothSol h).toSolCore
  refine ⟨hs.velocity_contDiff, fun T hT => ?_⟩
  obtain ⟨C, hC⟩ := hs.velocity_bounded T hT 0
  refine ⟨C, fun t ht x => ?_⟩
  have := hC t ht x
  rwa [norm_iteratedFDeriv_zero] at this

/-- `div v = 0` (thm:smooth (2)). -/
private theorem vel_divergence_eq_zero (h : IsSmoothDatum ω₀ R₀) (t : ℝ) (x : ℂ) :
    Prelim.divergence (vel ω₀ t) x = 0 :=
  (sol_isSmoothSol h).toSolCore.divergence_eq_zero t x

/-- thm:smooth (4): the flow `∂_t Φ(t, y) = v(t, Φ(t, y))`, `Φ(0, y) = y`, is defined for all
`t ∈ ℝ`. -/
theorem flow_global (h : IsSmoothDatum ω₀ R₀) (y : ℂ) :
    maxDomain (vel ω₀) univ 0 y = univ ∧
      IsMaxSol (vel ω₀) univ 0 y univ (fun t => flow ω₀ t y) :=
  flowOf_global (vel_isSmoothBoundedField h) 0 y

/-- thm:smooth (4): each `Φ_t` is a `C^∞` diffeomorphism of `ℝ²` with inverse `Φ_t⁻¹` and
`det DΦ_t ≡ 1`. -/
theorem flow_diffeo (h : IsSmoothDatum ω₀ R₀) (t : ℝ) :
    Function.LeftInverse (flowInv ω₀ t) (flow ω₀ t) ∧
      Function.RightInverse (flowInv ω₀ t) (flow ω₀ t) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (flow ω₀ t) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (flowInv ω₀ t) ∧
      ∀ y : ℂ, (fderiv ℝ (flow ω₀ t) y).det = 1 := by
  have hu := vel_isSmoothBoundedField h
  obtain ⟨h1, h2, h3, h4⟩ := flowOf_diffeo hu t 0
  exact ⟨h1, h2, h3, h4, fun y => det_fderiv_flowOf hu (vel_divergence_eq_zero h) t 0 y⟩

/-- thm:smooth (4): the maps `(t, y) ↦ Φ_t(y)` and `(t, x) ↦ Φ_t⁻¹(x)` lie in `C^∞(ℝ × ℝ²)`. -/
theorem flow_contDiff (h : IsSmoothDatum ω₀ R₀) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℂ => flow ω₀ p.1 p.2) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℂ => flowInv ω₀ p.1 p.2) := by
  have hΦ := flowOf_contDiff (vel_isSmoothBoundedField h)
  constructor
  · have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℂ => (p.1, ((0 : ℝ), p.2))) :=
      contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd)
    exact hΦ.comp hg
  · have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℂ => ((0 : ℝ), (p.1, p.2))) :=
      contDiff_const.prodMk (contDiff_fst.prodMk contDiff_snd)
    exact hΦ.comp hg

/-- thm:smooth (4): `Φ_t` and `Φ_t⁻¹` preserve area (from `det DΦ_t ≡ 1`). -/
theorem flow_measurePreserving (h : IsSmoothDatum ω₀ R₀) (t : ℝ) :
    MeasurePreserving (flow ω₀ t) volume volume ∧
      MeasurePreserving (flowInv ω₀ t) volume volume := by
  have hu := vel_isSmoothBoundedField h
  exact ⟨flowOf_measurePreserving hu (vel_divergence_eq_zero h) t 0,
    flowOf_measurePreserving hu (vel_divergence_eq_zero h) 0 t⟩

/-! ### The transport identity `ω(t, Φ(t, a)) = ω₀(a)` -/

/-- For a differentiable function `f` of `(t, x)`, the derivative in the direction `(1, w)` is
`∂_t f + D_x f · w`. -/
private theorem fderiv_uncurry_apply_one {ω : ℝ → ℂ → ℝ} {t : ℝ} {x : ℂ}
    (hd : DifferentiableAt ℝ (Function.uncurry ω) (t, x)) (w : ℂ) :
    fderiv ℝ (Function.uncurry ω) (t, x) (1, w) =
      deriv (fun s => ω s x) t + fderiv ℝ (ω t) x w := by
  set L := fderiv ℝ (Function.uncurry ω) (t, x)
  have hL : HasFDerivAt (Function.uncurry ω) L (t, x) := hd.hasFDerivAt
  -- the time derivative
  have ht : HasDerivAt (fun s => ω s x) (L (1, 0)) t := by
    have hp : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : ℂ)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
    exact hL.comp_hasDerivAt t hp
  -- the space derivative
  have hx : HasFDerivAt (ω t) (L.comp (ContinuousLinearMap.inr ℝ ℝ ℂ)) x := by
    have hp : HasFDerivAt (fun y : ℂ => (t, y)) (ContinuousLinearMap.inr ℝ ℝ ℂ) x :=
      (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
    exact hL.comp x hp
  rw [ht.deriv, hx.fderiv]
  have h1 : ((1 : ℝ), w) = ((1 : ℝ), (0 : ℂ)) + ((0 : ℝ), w) := by simp
  rw [h1, map_add]
  simp

/-- thm:smooth (4): `ω(t, Φ_t(a)) = ω₀(a)` (the vorticity is transported by the flow). -/
private theorem sol_flow_eq (h : IsSmoothDatum ω₀ R₀) (t : ℝ) (a : ℂ) :
    sol ω₀ t (flow ω₀ t a) = ω₀ a := by
  have hs := (sol_isSmoothSol h).toSolCore
  have hglob := (flow_global h a).2
  have hdiff : Differentiable ℝ (Function.uncurry (sol ω₀)) :=
    hs.contDiff.differentiable (by simp)
  -- `g(τ) = ω(τ, Φ(τ, a))` has derivative `0`
  have hg : ∀ τ : ℝ, HasDerivAt (fun r => sol ω₀ r (flow ω₀ r a)) 0 τ := by
    intro τ
    have hγ : HasDerivAt (fun r : ℝ => (r, flow ω₀ r a))
        ((1 : ℝ), vel ω₀ τ (flow ω₀ τ a)) τ :=
      (hasDerivAt_id τ).prodMk (hglob.hasDerivAt τ (mem_univ τ))
    have hcomp := (hdiff (τ, flow ω₀ τ a)).hasFDerivAt.comp_hasDerivAt τ hγ
    rw [fderiv_uncurry_apply_one (hdiff _)] at hcomp
    have htr := hs.transport τ (flow ω₀ τ a)
    rw [vel_eq] at hcomp
    have hv : velocityField (sol ω₀) τ (flow ω₀ τ a) = velocity (sol ω₀ τ) (flow ω₀ τ a) := rfl
    rw [hv] at htr
    rw [htr] at hcomp
    exact hcomp
  have hconst := is_const_of_deriv_eq_zero (fun τ => (hg τ).differentiableAt)
    (fun τ => (hg τ).deriv) t 0
  rw [hconst, hglob.init, hs.init]

/-- thm:smooth (4): `ω(t) = ω₀ ∘ Φ_t⁻¹`. -/
theorem sol_eq_comp_flowInv (h : IsSmoothDatum ω₀ R₀) (t : ℝ) (x : ℂ) :
    sol ω₀ t x = ω₀ (flowInv ω₀ t x) := by
  have hr := (flow_diffeo h t).2.1
  conv_lhs => rw [← hr x]
  exact sol_flow_eq h t (flowInv ω₀ t x)

/-- thm:smooth (4), consequence: `∫ F(ω(t)) dx = ∫ F(ω₀) dx` for every continuous `F` with
`F(0) = 0` (and `F(ω(t))` is integrable). -/
theorem integral_comp_sol (h : IsSmoothDatum ω₀ R₀) {F : ℝ → ℝ} (hF : Continuous F)
    (hF0 : F 0 = 0) (t : ℝ) :
    Integrable (fun x => F (sol ω₀ t x)) ∧ ∫ x, F (sol ω₀ t x) = ∫ x, F (ω₀ x) := by
  have hS := sol_isSmoothSol h
  have hcont : Continuous (sol ω₀ t) := by
    have hc : Continuous (Function.uncurry (sol ω₀)) := hS.toSolCore.contDiff.continuous
    exact hc.comp (continuous_const.prodMk continuous_id)
  have hcs : HasCompactSupport (sol ω₀ t) :=
    (isCompact_closedBall (0 : ℂ) (suppRadius ω₀ R₀ t)).of_isClosed_subset
      (isClosed_tsupport _) ((hS.tsupport_subset t).trans Metric.ball_subset_closedBall)
  have hFcs : HasCompactSupport (fun x => F (sol ω₀ t x)) :=
    hcs.comp_left hF0
  refine ⟨(hF.comp hcont).integrable_of_hasCompactSupport hFcs, ?_⟩
  have hmp := (flow_measurePreserving h t).2
  have hF₀ : Continuous fun y => F (ω₀ y) := hF.comp h.contDiff.continuous
  calc ∫ x, F (sol ω₀ t x) = ∫ x, F (ω₀ (flowInv ω₀ t x)) := by
        simp_rw [sol_eq_comp_flowInv h t]
    _ = ∫ y, F (ω₀ y) ∂(Measure.map (flowInv ω₀ t) volume) :=
        (integral_map hmp.measurable.aemeasurable
          (hF₀.aestronglyMeasurable)).symm
    _ = ∫ y, F (ω₀ y) := by rw [hmp.map_eq]

end NonUniqueEuler.Smooth
