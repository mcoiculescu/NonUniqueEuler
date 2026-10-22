import NonUniqueEuler.I.SmoothB.Smooth
import NonUniqueEuler.I.SmoothB.SmoothFlow
import NonUniqueEuler.I.SmoothB.FlowFacts
import NonUniqueEuler.H.SmoothB.SmoothCovariance.Velocity
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Proof: covariance of the smooth solution (time shift, scaling, rotations)

Proof of `I/SmoothB/SmoothCovariance.lean`. Each item follows the manuscript: check that the
transformed function is a `C¹` solution in the sense of thm:smooth(5) (`IsC1SolOn univ`), and
identify it with the solution of the transformed datum by `smooth_unique`
(`06_datum.tex:139-146`, `B_global_smooth.tex:533-545`). The flows are identified by the
uniqueness of maximal solutions (`IsMaxSol.maximal` of `flow_global`), the inverse flows by
`flow_diffeo`, and the rotation equivariance of the flow by `flowOf_rot`.

The Biot–Savart covariance (`K ∗ (A⁻¹ g(r ·)) = (Ar)⁻¹ (K ∗ g)(r ·)` and
`K ∗ (g ∘ O_θ) = O_θ⁻¹ (K ∗ g) ∘ O_θ`) is in `H/SmoothB/SmoothCovariance/Velocity.lean`.
-/

noncomputable section

open Set Metric

namespace NonUniqueEuler.Smooth

variable {ω₀ : ℂ → ℝ} {R₀ : ℝ}

namespace Covariance

/-- The derivative of a differentiable space–time function in the direction `(1, w)` is
`∂_t ω + ∇ω·w` (as in `P/SmoothB/Smooth.lean`; restated here under a private namespace). -/
theorem fderiv_uncurry_apply_one {ω : ℝ → ℂ → ℝ} {t : ℝ} {x : ℂ}
    (hd : DifferentiableAt ℝ (Function.uncurry ω) (t, x)) (w : ℂ) :
    fderiv ℝ (Function.uncurry ω) (t, x) (1, w) =
      deriv (fun s => ω s x) t + fderiv ℝ (ω t) x w := by
  set D := fderiv ℝ (Function.uncurry ω) (t, x) with hD
  have hf : HasFDerivAt (Function.uncurry ω) D (t, x) := hd.hasFDerivAt
  have ht : HasDerivAt (fun s => ω s x) (D (1, 0)) t := by
    have h1 : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : ℂ)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
    exact HasFDerivAt.comp_hasDerivAt (x := t) hf h1
  have hx : HasFDerivAt (ω t) (D.comp (ContinuousLinearMap.inr ℝ ℝ ℂ)) x := by
    exact HasFDerivAt.comp (x := x) hf (hasFDerivAt_prodMk_right (𝕜 := ℝ) t x)
  rw [ht.deriv, hx.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    ← map_add, Prod.mk_add_mk, add_zero, zero_add]

/-- `C¹` regularity of the solution. -/
theorem sol_contDiff_one (h : IsSmoothDatum ω₀ R₀) :
    ContDiff ℝ 1 (Function.uncurry (sol ω₀)) :=
  (sol_isSmoothSol h).contDiff.of_le (by exact_mod_cast le_top)

/-- The transport equation (3) of the solution, in the form of thm:smooth(5): the derivative of
`(t, x) ↦ ω(t, x)` in the direction `(1, v(t, x))` vanishes. -/
theorem fderiv_sol_apply (h : IsSmoothDatum ω₀ R₀) (t : ℝ) (x : ℂ) :
    fderiv ℝ (Function.uncurry (sol ω₀)) (t, x) (1, vel ω₀ t x) = 0 := by
  rw [fderiv_uncurry_apply_one ((sol_contDiff_one h).differentiable one_ne_zero _)]
  exact (sol_isSmoothSol h).transport t x

/-- The solution has supports in one disk on every compact time interval. -/
theorem tsupport_sol_Icc (h : IsSmoothDatum ω₀ R₀) (a b : ℝ) :
    ∃ R : ℝ, ∀ t ∈ Icc a b, tsupport (sol ω₀ t) ⊆ ball 0 R := by
  refine ⟨suppRadius ω₀ R₀ (max |a| |b|), fun t ht => ?_⟩
  refine ((sol_isSmoothSol h).tsupport_subset t).trans
    (ball_subset_ball (suppRadius_mono_abs ω₀ R₀ ?_))
  rw [abs_of_nonneg (le_max_of_le_left (abs_nonneg a))]
  exact abs_le_max_abs_abs ht.1 ht.2

/-- A `C¹` space–time function with the datum, the transport equation and locally bounded
supports is a solution in the class of thm:smooth(5) on `I = ℝ`. -/
theorem isC1SolOn_univ_of {ω₁ : ℂ → ℝ} {ω : ℝ → ℂ → ℝ}
    (hc : ContDiff ℝ 1 (Function.uncurry ω)) (hinit : ω 0 = ω₁)
    (htr : ∀ t x, fderiv ℝ (Function.uncurry ω) (t, x) (1, velocity (ω t) x) = 0)
    (hsupp : ∀ a b : ℝ, ∃ R : ℝ, ∀ t ∈ Icc a b, tsupport (ω t) ⊆ ball 0 R) :
    IsC1SolOn univ ω₁ ω := by
  refine ⟨hc.contDiffOn, hinit, fun t _ x => ?_, fun a b _ => hsupp a b⟩
  rw [univ_prod_univ, fderivWithin_univ]
  exact htr t x

/-- Supports under the scaling `g ↦ A⁻¹ g(r ·)`. -/
theorem tsupport_scale_subset {g : ℂ → ℝ} {R : ℝ} (hg : tsupport g ⊆ ball 0 R) (A : ℝ)
    {r : ℝ} (hr : 0 < r) :
    tsupport (fun y => A⁻¹ * g ((r : ℂ) * y)) ⊆ ball 0 (R / r) := by
  intro y hy
  have h1 : y ∈ tsupport (g ∘ fun y : ℂ => (r : ℂ) * y) :=
    tsupport_mul_subset_right (f := fun _ => A⁻¹) hy
  have h2 := tsupport_comp_subset_preimage g (f := fun y : ℂ => (r : ℂ) * y)
    (continuous_const.mul continuous_id) h1
  have h3 := hg h2
  rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at h3
  rw [mem_ball_zero_iff, lt_div_iff₀ hr]
  linarith

/-- Supports under rotations. -/
theorem tsupport_rot_subset {g : ℂ → ℝ} {R : ℝ} (hg : tsupport g ⊆ ball 0 R) (θ : ℝ) :
    tsupport (fun x => g (rot θ x)) ⊆ ball 0 R := by
  intro x hx
  have h2 := tsupport_comp_subset_preimage g (f := rot θ)
    (continuous_const.mul continuous_id) hx
  have h3 := hg h2
  rw [mem_ball_zero_iff, rot, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul] at h3
  rwa [mem_ball_zero_iff]

/-- `t ↦ Φ_t(y)` solves the flow equation through `y` at time `0`. -/
theorem hasDerivAt_flow (h : IsSmoothDatum ω₀ R₀) (t : ℝ) (y : ℂ) :
    HasDerivAt (fun s => flow ω₀ s y) (vel ω₀ t (flow ω₀ t y)) t :=
  (flow_global h y).2.hasDerivAt t (mem_univ t)

theorem flow_zero (h : IsSmoothDatum ω₀ R₀) (y : ℂ) : flow ω₀ 0 y = y :=
  (flow_global h y).2.init

/-- Identification of the flow by the uniqueness of maximal solutions: a global solution of the
flow equation with value `y` at time `0` is `t ↦ Φ_t(y)`. -/
theorem flow_eq_of_hasDerivAt (h : IsSmoothDatum ω₀ R₀) {y : ℂ} {γ : ℝ → ℂ} (h0 : γ 0 = y)
    (hγ : ∀ t, HasDerivAt γ (vel ω₀ t (γ t)) t) (t : ℝ) : flow ω₀ t y = γ t := by
  have hloc : IsLocalSol (vel ω₀) univ 0 y univ γ :=
    { isOpen := isOpen_univ
      ordConnected := ordConnected_univ
      mem := mem_univ _
      init := h0
      graph := fun _ _ => mem_univ _
      hasDerivAt := fun t _ => hγ t }
  exact ((flow_global h y).2.maximal univ γ hloc).2 (mem_univ t) |>.symm

end Covariance

open Covariance

/-- Time-translation covariance: `ω(t₁)` is an admissible datum (radius `R(t₁)`), the solution
with datum `ω(t₁)` is `u ↦ ω(t₁ + u)`, its velocity is `v(t₁ + ·)`, and its flow is
`Φ_{t₁+u} ∘ Φ_{t₁}⁻¹`. -/
theorem sol_timeShift (h : IsSmoothDatum ω₀ R₀) (t₁ : ℝ) :
    IsSmoothDatum (sol ω₀ t₁) (suppRadius ω₀ R₀ t₁) ∧
      (∀ (τ : ℝ) (x : ℂ), sol (sol ω₀ t₁) τ x = sol ω₀ (t₁ + τ) x) ∧
      (∀ (τ : ℝ) (x : ℂ), vel (sol ω₀ t₁) τ x = vel ω₀ (t₁ + τ) x) ∧
      (∀ (τ : ℝ) (y : ℂ), flow (sol ω₀ t₁) τ y = flow ω₀ (t₁ + τ) (flowInv ω₀ t₁ y)) := by
  have hs := sol_isSmoothSol h
  -- the datum `ω(t₁)`
  have hd : IsSmoothDatum (sol ω₀ t₁) (suppRadius ω₀ R₀ t₁) :=
    ⟨hs.contDiff.comp (contDiff_const.prodMk contDiff_id), hs.tsupport_subset t₁⟩
  -- the shifted function is a `C¹` solution on `ℝ`
  have hC1 : IsC1SolOn univ (sol ω₀ t₁) (fun τ => sol ω₀ (t₁ + τ)) := by
    have hL : ∀ p : ℝ × ℂ, HasFDerivAt (fun p : ℝ × ℂ => (t₁ + p.1, p.2))
        ((ContinuousLinearMap.fst ℝ ℝ ℂ).prod (ContinuousLinearMap.snd ℝ ℝ ℂ)) p :=
      fun p => (hasFDerivAt_fst.const_add t₁).prodMk hasFDerivAt_snd
    refine isC1SolOn_univ_of ?_ (by simp) ?_ ?_
    · exact (sol_contDiff_one h).comp ((ContDiff.add contDiff_const contDiff_fst).prodMk contDiff_snd)
    · intro τ x
      have hD := (((sol_contDiff_one h).differentiable one_ne_zero (t₁ + τ, x)).hasFDerivAt).comp
        (τ, x) (hL (τ, x))
      have hfun : Function.uncurry (fun τ => sol ω₀ (t₁ + τ)) =
          Function.uncurry (sol ω₀) ∘ (fun p : ℝ × ℂ => (t₁ + p.1, p.2)) := rfl
      rw [hfun, hD.fderiv]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
      exact fderiv_sol_apply h (t₁ + τ) x
    · intro a b
      obtain ⟨R, hR⟩ := tsupport_sol_Icc h (t₁ + a) (t₁ + b)
      exact ⟨R, fun t ht => hR (t₁ + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  have hsol : ∀ τ, sol (sol ω₀ t₁) τ = sol ω₀ (t₁ + τ) := fun τ =>
    (smooth_unique hd ordConnected_univ (mem_univ 0) hC1 τ (mem_univ τ)).symm
  have hvel : ∀ (τ : ℝ) (x : ℂ), vel (sol ω₀ t₁) τ x = vel ω₀ (t₁ + τ) x := by
    intro τ x
    rw [vel_eq, vel_eq, hsol]
  refine ⟨hd, fun τ x => by rw [hsol], hvel, fun τ y => ?_⟩
  refine flow_eq_of_hasDerivAt hd (γ := fun τ => flow ω₀ (t₁ + τ) (flowInv ω₀ t₁ y)) ?_
    (fun τ => ?_) τ
  · rw [add_zero]
    exact (flow_diffeo h t₁).2.1 y
  · rw [hvel]
    exact (hasDerivAt_flow h (t₁ + τ) (flowInv ω₀ t₁ y)).comp_const_add t₁ τ

/-- Scaling covariance (ring units, `06_datum.tex:139-146`): for `A, r > 0` the solution with
datum `A⁻¹ ω₀(r ·)` is `(τ, y) ↦ A⁻¹ ω(τ/A, r y)`, with velocity `(Ar)⁻¹ v(τ/A, r y)`, flow
`y ↦ r⁻¹ Φ_{τ/A}(r y)` and inverse flow `x ↦ r⁻¹ Φ_{τ/A}⁻¹(r x)`. -/
theorem sol_scale (h : IsSmoothDatum ω₀ R₀) {A r : ℝ} (hA : 0 < A) (hr : 0 < r) :
    IsSmoothDatum (fun y => A⁻¹ * ω₀ ((r : ℂ) * y)) (R₀ / r) ∧
      (∀ (τ : ℝ) (y : ℂ), sol (fun y => A⁻¹ * ω₀ ((r : ℂ) * y)) τ y =
        A⁻¹ * sol ω₀ (τ / A) ((r : ℂ) * y)) ∧
      (∀ (τ : ℝ) (y : ℂ), vel (fun y => A⁻¹ * ω₀ ((r : ℂ) * y)) τ y =
        (((A * r)⁻¹ : ℝ) : ℂ) * vel ω₀ (τ / A) ((r : ℂ) * y)) ∧
      (∀ (τ : ℝ) (y : ℂ), flow (fun y => A⁻¹ * ω₀ ((r : ℂ) * y)) τ y =
        ((r⁻¹ : ℝ) : ℂ) * flow ω₀ (τ / A) ((r : ℂ) * y)) ∧
      (∀ (τ : ℝ) (x : ℂ), flowInv (fun y => A⁻¹ * ω₀ ((r : ℂ) * y)) τ x =
        ((r⁻¹ : ℝ) : ℂ) * flowInv ω₀ (τ / A) ((r : ℂ) * x)) := by
  have hs := sol_isSmoothSol h
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  have hA' : A ≠ 0 := hA.ne'
  set ω₁ : ℂ → ℝ := fun y => A⁻¹ * ω₀ ((r : ℂ) * y) with hω₁
  -- the scaled datum
  have hd : IsSmoothDatum ω₁ (R₀ / r) :=
    ⟨ContDiff.mul contDiff_const (h.contDiff.comp (ContDiff.mul contDiff_const contDiff_id)),
      tsupport_scale_subset h.tsupport_subset A hr⟩
  -- the scaled function is a `C¹` solution on `ℝ`
  set ω' : ℝ → ℂ → ℝ := fun τ y => A⁻¹ * sol ω₀ (τ / A) ((r : ℂ) * y) with hω'
  have hC1 : IsC1SolOn univ ω₁ ω' := by
    have hL : ∀ p : ℝ × ℂ, HasFDerivAt (fun p : ℝ × ℂ => (p.1 / A, (r : ℂ) * p.2))
        ((A⁻¹ • ContinuousLinearMap.fst ℝ ℝ ℂ).prod
          ((r : ℂ) • ContinuousLinearMap.snd ℝ ℝ ℂ)) p := by
      intro p
      have h1 : HasFDerivAt (fun p : ℝ × ℂ => p.1 / A) (A⁻¹ • ContinuousLinearMap.fst ℝ ℝ ℂ) p := by
        simpa only [div_eq_mul_inv] using (hasFDerivAt_fst (p := p)).mul_const A⁻¹
      exact h1.prodMk (hasFDerivAt_snd.const_mul (r : ℂ))
    have hfun : Function.uncurry ω' =
        fun p => A⁻¹ * (Function.uncurry (sol ω₀) ∘ (fun p : ℝ × ℂ => (p.1 / A, (r : ℂ) * p.2))) p
        := rfl
    refine isC1SolOn_univ_of ?_ ?_ ?_ ?_
    · rw [hfun]
      exact ContDiff.mul contDiff_const ((sol_contDiff_one h).comp
        ((contDiff_fst.div_const A).prodMk (ContDiff.mul contDiff_const contDiff_snd)))
    · funext y
      simp [hω', hω₁, hs.init]
    · intro τ x
      have hD := ((((sol_contDiff_one h).differentiable one_ne_zero _).hasFDerivAt).comp
        (τ, x) (hL (τ, x))).const_mul A⁻¹
      rw [hfun, hD.fderiv]
      have hv : velocity (ω' τ) x = (((A * r)⁻¹ : ℝ) : ℂ) * vel ω₀ (τ / A) ((r : ℂ) * x) :=
        Covariance.velocity_scale A hr (sol ω₀ (τ / A)) x
      rw [hv]
      have hdir : (A⁻¹ * (1 : ℝ), (r : ℂ) * ((((A * r)⁻¹ : ℝ) : ℂ) *
          vel ω₀ (τ / A) ((r : ℂ) * x))) = A⁻¹ • ((1 : ℝ), vel ω₀ (τ / A) ((r : ℂ) * x)) := by
        rw [Prod.smul_mk, smul_eq_mul, Complex.real_smul]
        congr 1
        push_cast
        field_simp
      simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.coe_snd', smul_eq_mul]
      rw [hdir, map_smul, fderiv_sol_apply h (τ / A) ((r : ℂ) * x), smul_zero, mul_zero]
    · intro a b
      obtain ⟨R, hR⟩ := tsupport_sol_Icc h (a / A) (b / A)
      refine ⟨R / r, fun t ht => tsupport_scale_subset (hR (t / A) ⟨?_, ?_⟩) A hr⟩
      · exact div_le_div_of_nonneg_right ht.1 hA.le
      · exact div_le_div_of_nonneg_right ht.2 hA.le
  have hsol : ∀ τ, sol ω₁ τ = ω' τ := fun τ =>
    (smooth_unique hd ordConnected_univ (mem_univ 0) hC1 τ (mem_univ τ)).symm
  have hvel : ∀ (τ : ℝ) (y : ℂ), vel ω₁ τ y =
      (((A * r)⁻¹ : ℝ) : ℂ) * vel ω₀ (τ / A) ((r : ℂ) * y) := by
    intro τ y
    rw [vel_eq, hsol]
    exact Covariance.velocity_scale A hr (sol ω₀ (τ / A)) y
  have hflow : ∀ (τ : ℝ) (y : ℂ), flow ω₁ τ y = ((r⁻¹ : ℝ) : ℂ) * flow ω₀ (τ / A) ((r : ℂ) * y) := by
    intro τ y
    refine flow_eq_of_hasDerivAt hd
      (γ := fun τ => ((r⁻¹ : ℝ) : ℂ) * flow ω₀ (τ / A) ((r : ℂ) * y)) ?_ (fun τ => ?_) τ
    · show ((r⁻¹ : ℝ) : ℂ) * flow ω₀ (0 / A) ((r : ℂ) * y) = y
      rw [zero_div, flow_zero h]
      push_cast
      field_simp
    · rw [hvel]
      have h1 : HasDerivAt (fun τ => ((r⁻¹ : ℝ) : ℂ) * flow ω₀ (τ / A) ((r : ℂ) * y))
          (((r⁻¹ : ℝ) : ℂ) * ((1 / A) • vel ω₀ (τ / A) (flow ω₀ (τ / A) ((r : ℂ) * y)))) τ := by
        have h2 : HasDerivAt (fun s => flow ω₀ s ((r : ℂ) * y))
            (vel ω₀ (τ / A) (flow ω₀ (τ / A) ((r : ℂ) * y))) (τ / A) :=
          hasDerivAt_flow h _ _
        have h3 : HasDerivAt (fun x : ℝ => x / A) (1 / A) τ := (hasDerivAt_id τ).div_const A
        exact (h2.scomp τ h3).const_mul ((r⁻¹ : ℝ) : ℂ)
      refine h1.congr_deriv ?_
      have hrr : (r : ℂ) * (((r⁻¹ : ℝ) : ℂ) * flow ω₀ (τ / A) ((r : ℂ) * y)) =
          flow ω₀ (τ / A) ((r : ℂ) * y) := by
        push_cast
        field_simp
      rw [hrr, Complex.real_smul]
      push_cast
      field_simp
  refine ⟨hd, fun τ y => by rw [hsol], hvel, hflow, fun τ x => ?_⟩
  -- the inverse flow, from the inverse identities of thm:smooth(4)
  have hx : flow ω₁ τ (((r⁻¹ : ℝ) : ℂ) * flowInv ω₀ (τ / A) ((r : ℂ) * x)) = x := by
    rw [hflow]
    have hrr : (r : ℂ) * (((r⁻¹ : ℝ) : ℂ) * flowInv ω₀ (τ / A) ((r : ℂ) * x)) =
        flowInv ω₀ (τ / A) ((r : ℂ) * x) := by
      push_cast
      field_simp
    rw [hrr, (flow_diffeo h (τ / A)).2.1 ((r : ℂ) * x)]
    push_cast
    field_simp
  conv_lhs => rw [← hx]
  exact (flow_diffeo hd τ).1 _

/-- Rotation conjugation (`B_global_smooth.tex:535-541`): the solution with datum `ω₀ ∘ O_θ` is
`(t, x) ↦ ω(t, O_θ x)`, with velocity `O_θ⁻¹ v(t, O_θ x)`. -/
theorem sol_comp_rot (h : IsSmoothDatum ω₀ R₀) (θ : ℝ) :
    IsSmoothDatum (fun x => ω₀ (rot θ x)) R₀ ∧
      (∀ (t : ℝ) (x : ℂ), sol (fun x => ω₀ (rot θ x)) t x = sol ω₀ t (rot θ x)) ∧
      (∀ (t : ℝ) (x : ℂ), vel (fun x => ω₀ (rot θ x)) t x = rot (-θ) (vel ω₀ t (rot θ x))) := by
  have hs := sol_isSmoothSol h
  set c : ℂ := Complex.exp ((θ : ℂ) * Complex.I) with hc
  have hrot : rot θ = fun x => c * x := rfl
  have hd : IsSmoothDatum (fun x => ω₀ (rot θ x)) R₀ :=
    ⟨h.contDiff.comp (by rw [hrot]; exact ContDiff.mul contDiff_const contDiff_id),
      tsupport_rot_subset h.tsupport_subset θ⟩
  set ω' : ℝ → ℂ → ℝ := fun t x => sol ω₀ t (rot θ x) with hω'
  have hC1 : IsC1SolOn univ (fun x => ω₀ (rot θ x)) ω' := by
    have hL : ∀ p : ℝ × ℂ, HasFDerivAt (fun p : ℝ × ℂ => (p.1, c * p.2))
        ((ContinuousLinearMap.fst ℝ ℝ ℂ).prod (c • ContinuousLinearMap.snd ℝ ℝ ℂ)) p :=
      fun p => hasFDerivAt_fst.prodMk (hasFDerivAt_snd.const_mul c)
    have hfun : Function.uncurry ω' =
        Function.uncurry (sol ω₀) ∘ (fun p : ℝ × ℂ => (p.1, c * p.2)) := rfl
    refine isC1SolOn_univ_of ?_ ?_ ?_ ?_
    · rw [hfun]
      exact (sol_contDiff_one h).comp (contDiff_fst.prodMk (ContDiff.mul contDiff_const contDiff_snd))
    · funext x
      simp [hω', hs.init]
    · intro t x
      have hD := (((sol_contDiff_one h).differentiable one_ne_zero _).hasFDerivAt).comp
        (t, x) (hL (t, x))
      rw [hfun, hD.fderiv]
      have hv : velocity (ω' t) x = rot (-θ) (vel ω₀ t (rot θ x)) :=
        Covariance.velocity_comp_rot (sol ω₀ t) θ x
      rw [hv]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', _root_.smul_apply,
        smul_eq_mul]
      have hcc : c * rot (-θ) (vel ω₀ t (rot θ x)) = vel ω₀ t (rot θ x) :=
        Covariance.rot_rot_neg θ _
      rw [hcc]
      exact fderiv_sol_apply h t (rot θ x)
    · intro a b
      obtain ⟨R, hR⟩ := tsupport_sol_Icc h a b
      exact ⟨R, fun t ht => tsupport_rot_subset (hR t ht) θ⟩
  have hsol : ∀ t, sol (fun x => ω₀ (rot θ x)) t = ω' t := fun t =>
    (smooth_unique hd ordConnected_univ (mem_univ 0) hC1 t (mem_univ t)).symm
  refine ⟨hd, fun t x => by rw [hsol], fun t x => ?_⟩
  rw [vel_eq, hsol]
  exact Covariance.velocity_comp_rot (sol ω₀ t) θ x

/-- Equivariance for a symmetric datum (`05_single_ring.tex:141-145`, `06_datum.tex:255-262`):
if `ω₀ ∘ O_θ = ω₀`, then `v(t, O_θ x) = O_θ v(t, x)`, `Φ_t(O_θ y) = O_θ Φ_t(y)` and
`Φ_t⁻¹(O_θ x) = O_θ Φ_t⁻¹(x)`. -/
theorem vel_flow_rot_of_symm (h : IsSmoothDatum ω₀ R₀) {θ : ℝ}
    (hθ : ∀ x : ℂ, ω₀ (rot θ x) = ω₀ x) (t : ℝ) :
    (∀ x : ℂ, vel ω₀ t (rot θ x) = rot θ (vel ω₀ t x)) ∧
      (∀ y : ℂ, flow ω₀ t (rot θ y) = rot θ (flow ω₀ t y)) ∧
      (∀ x : ℂ, flowInv ω₀ t (rot θ x) = rot θ (flowInv ω₀ t x)) := by
  have hfun : (fun x => ω₀ (rot θ x)) = ω₀ := funext hθ
  have hequi : ∀ (s : ℝ) (x : ℂ), vel ω₀ s (rot θ x) = rot θ (vel ω₀ s x) := by
    intro s x
    have h1 := (sol_comp_rot h θ).2.2 s x
    rw [hfun] at h1
    rw [h1, Covariance.rot_rot_neg]
  have hu := vel_isSmoothBoundedField h
  exact ⟨hequi t, fun y => flowOf_rot hu hequi t 0 y, fun x => flowOf_rot hu hequi 0 t x⟩

end NonUniqueEuler.Smooth
