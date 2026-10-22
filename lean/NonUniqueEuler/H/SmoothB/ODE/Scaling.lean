import NonUniqueEuler.H.SmoothB.ODE.Core
import NonUniqueEuler.Vendor.Flow.BoundedLipschitzFlow
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Helper for `lem:ode`(ii): smoothness of the flow of a time-dependent bounded Lipschitz field

For a vendored bounded Lipschitz flow `V` (`Vendor/Flow/BoundedLipschitzFlow.lean`) whose field
`V.velocity` is `C^k` jointly in `(t, x)` (`k ≥ 1`), with `Φ(t, s, y) = V.flow s t y`:
* `flow_contDiff_of_velocity`: `(t, s, y) ↦ Φ(t, s, y)` is `C^k` on `ℝ × ℝ × E`;
* `flow_fderiv_hasDerivAt`: `D_yΦ` solves the variational equation
  `∂_t D_yΦ(t,s,y) = D_xF(t, Φ(t,s,y)) ∘ D_yΦ(t,s,y)`.

Both reduce the time-dependent problem to the autonomous `C^k` core `Core.lean`:
* smoothness by the *scaling* trick: on `ℝ × ℝ × E` the autonomous field
  `H(τ, σ, x) = (0, τ, τ F(σ, x))` has the flow `(τ, σ + rτ, Φ(σ + rτ, σ, x))`, so
  `Φ(t, s, y)` is the last component of its time-`1` map at `(t - s, s, y)`;
* the variational equation by the autonomization `G(σ, x) = (1, F(σ, x))` on `ℝ × E`, whose flow
  is `(σ + r, Φ(σ + r, σ, x))`.
-/

noncomputable section

open Set Function

namespace NonUniqueEuler.Smooth.ODEH

open NonUniqueEuler.Vendor.BoundedLipschitzFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Joint `C^k` regularity of `(t, s, y) ↦ Φ(t, s, y) = V.flow s t y` (scaling trick). -/
theorem flow_contDiff_of_velocity (V : Data E) {k : ℕ} (hk : 1 ≤ k)
    (hF : ContDiff ℝ k (uncurry V.velocity)) :
    ContDiff ℝ k (fun q : ℝ × ℝ × E => V.flow q.2.1 q.1 q.2.2) := by
  let H : ℝ × (ℝ × E) → ℝ × (ℝ × E) := fun w => (0, (w.1, w.1 • V.velocity w.2.1 w.2.2))
  let Ψ : ℝ → ℝ × (ℝ × E) → ℝ × (ℝ × E) :=
    fun r w => (w.1, (w.2.1 + r * w.1, V.flow w.2.1 (w.2.1 + r * w.1) w.2.2))
  have hH : ContDiff ℝ k H := by
    refine contDiff_const.prodMk (contDiff_fst.prodMk (contDiff_fst.smul ?_))
    exact hF.comp contDiff_snd
  have hΨc : Continuous (uncurry Ψ) := by
    have hc := V.flow_joint_continuous
    refine (continuous_fst.comp continuous_snd).prodMk ?_
    have h1 : Continuous (fun q : ℝ × (ℝ × (ℝ × E)) => q.2.2.1 + q.1 * q.2.1) := by fun_prop
    refine h1.prodMk ?_
    exact hc.comp ((continuous_fst.comp (continuous_snd.comp continuous_snd)).prodMk
      (h1.prodMk (continuous_snd.comp (continuous_snd.comp continuous_snd))))
  have hΨ0 : ∀ w, Ψ 0 w = w := by
    intro w
    simp only [Ψ, zero_mul, add_zero, V.flow_initial]
  have hΨ : ∀ r w, HasDerivAt (fun r => Ψ r w) (H (Ψ r w)) r := by
    intro r w
    have hlin : HasDerivAt (fun r : ℝ => w.2.1 + r * w.1) w.1 r := by
      simpa using ((hasDerivAt_id r).mul_const w.1).const_add w.2.1
    have hfl := (V.flow_hasDerivAt w.2.1 (w.2.1 + r * w.1) w.2.2).scomp r hlin
    exact (hasDerivAt_const r w.1).prodMk (hlin.prodMk hfl)
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = n + 1 := ⟨k - 1, by omega⟩
  have hH' : ContDiff ℝ (n + 1) H := by exact_mod_cast hH
  have h1 := flow_contDiff n hH' hΨc hΨ0 hΨ 1
  have heq : (fun q : ℝ × ℝ × E => V.flow q.2.1 q.1 q.2.2) =
      fun q => (Ψ 1 (q.1 - q.2.1, q.2)).2.2 := by
    funext q
    simp only [Ψ, one_mul, add_sub_cancel]
  rw [heq]
  have ha : ContDiff ℝ (n + 1) (fun q : ℝ × ℝ × E => (q.1 - q.2.1, q.2)) :=
    (contDiff_fst.sub (contDiff_fst.comp contDiff_snd)).prodMk contDiff_snd
  exact_mod_cast (contDiff_snd.comp contDiff_snd).comp (h1.comp ha)

/-- The variational equation for `D_yΦ(t, s, y)`, `Φ(t, s, y) = V.flow s t y`
(autonomization). -/
theorem flow_fderiv_hasDerivAt (V : Data E) (hF : ContDiff ℝ 1 (uncurry V.velocity))
    (s t : ℝ) (y : E) :
    HasDerivAt (fun τ => fderiv ℝ (V.flow s τ) y)
      ((fderiv ℝ (V.velocity t) (V.flow s t y)).comp (fderiv ℝ (V.flow s t) y)) t := by
  let G : ℝ × E → ℝ × E := fun w => (1, V.velocity w.1 w.2)
  let Ψ : ℝ → ℝ × E → ℝ × E := fun r w => (w.1 + r, V.flow w.1 (w.1 + r) w.2)
  have hG : ContDiff ℝ 1 G := contDiff_const.prodMk hF
  have hΨc : Continuous (uncurry Ψ) := by
    have hc := V.flow_joint_continuous
    have h1 : Continuous (fun q : ℝ × (ℝ × E) => q.2.1 + q.1) := by fun_prop
    exact h1.prodMk (hc.comp ((continuous_fst.comp continuous_snd).prodMk
      (h1.prodMk (continuous_snd.comp continuous_snd))))
  have hΨ0 : ∀ w, Ψ 0 w = w := by
    intro w; simp only [Ψ, add_zero, V.flow_initial]
  have hΨ : ∀ r w, HasDerivAt (fun r => Ψ r w) (G (Ψ r w)) r := by
    intro r w
    have hlin : HasDerivAt (fun r : ℝ => w.1 + r) 1 r := by
      simpa using (hasDerivAt_id r).const_add w.1
    have hfl := (V.flow_hasDerivAt w.1 (w.1 + r) w.2).scomp r hlin
    simp only [one_smul] at hfl
    exact hlin.prodMk hfl
  obtain ⟨h1, -, h3⟩ := flow_C1 hG hΨc hΨ0 hΨ
  -- `D r = D_wΨ(r, (s, y))`
  set D : ℝ → (ℝ × E →L[ℝ] ℝ × E) := fun r => fderiv ℝ (Ψ r) (s, y) with hDdef
  have hflow_eq : ∀ τ, V.flow s τ = fun x => (Ψ (τ - s) (s, x)).2 := by
    intro τ; funext x; simp only [Ψ, add_sub_cancel]
  have hfd : ∀ τ, fderiv ℝ (V.flow s τ) y =
      (ContinuousLinearMap.snd ℝ ℝ E).comp ((D (τ - s)).comp (ContinuousLinearMap.inr ℝ ℝ E)) := by
    intro τ
    rw [hflow_eq τ]
    have hc : HasFDerivAt (fun x => Ψ (τ - s) (s, x))
        ((D (τ - s)).comp (ContinuousLinearMap.inr ℝ ℝ E)) y :=
      (h1 (τ - s) (s, y)).comp y (hasFDerivAt_prodMk_right s y)
    exact (hasFDerivAt_snd.comp y hc).fderiv
  have hfun : (fun τ => fderiv ℝ (V.flow s τ) y) = fun τ =>
      (ContinuousLinearMap.snd ℝ ℝ E).comp ((D (τ - s)).comp (ContinuousLinearMap.inr ℝ ℝ E)) := by
    funext τ; exact hfd τ
  rw [hfun, hfd t]
  have hDt : HasDerivAt (fun τ => D (τ - s)) ((fderiv ℝ G (Ψ (t - s) (s, y))).comp (D (t - s))) t := by
    have h := (h3 (t - s) (s, y)).scomp t ((hasDerivAt_id t).sub_const s)
    rw [one_smul] at h
    exact h
  have hder := (hasDerivAt_const t (ContinuousLinearMap.snd ℝ ℝ E)).clm_comp
    (hDt.clm_comp (hasDerivAt_const t (ContinuousLinearMap.inr ℝ ℝ E)))
  convert hder using 1
  simp only [ContinuousLinearMap.comp_zero, add_zero, ContinuousLinearMap.zero_comp, zero_add]
  -- identify the coefficient
  have hΨt : Ψ (t - s) (s, y) = (t, V.flow s t y) := by
    simp only [Ψ, add_sub_cancel]
  have hdiffF : DifferentiableAt ℝ (uncurry V.velocity) (t, V.flow s t y) :=
    hF.differentiable one_ne_zero _
  have hGd : HasFDerivAt G ((0 : ℝ × E →L[ℝ] ℝ).prod
      (fderiv ℝ (uncurry V.velocity) (t, V.flow s t y))) (t, V.flow s t y) :=
    (hasFDerivAt_const (1 : ℝ) _).prodMk hdiffF.hasFDerivAt
  have hFt : HasFDerivAt (V.velocity t)
      ((fderiv ℝ (uncurry V.velocity) (t, V.flow s t y)).comp (ContinuousLinearMap.inr ℝ ℝ E))
      (V.flow s t y) :=
    hdiffF.hasFDerivAt.comp (V.flow s t y) (hasFDerivAt_prodMk_right t (V.flow s t y))
  -- the first component of `D` vanishes on the `E` directions
  have hfst : ∀ v : E, (D (t - s) (0, v)).1 = 0 := by
    intro v
    have hc : HasFDerivAt (fun x => (Ψ (t - s) (s, x)).1)
        ((ContinuousLinearMap.fst ℝ ℝ E).comp ((D (t - s)).comp (ContinuousLinearMap.inr ℝ ℝ E)))
        y :=
      hasFDerivAt_fst.comp y ((h1 (t - s) (s, y)).comp y (hasFDerivAt_prodMk_right s y))
    have hconst : HasFDerivAt (fun x => (Ψ (t - s) (s, x)).1) (0 : E →L[ℝ] ℝ) y := by
      simp only [Ψ]
      exact hasFDerivAt_const _ _
    have := congrArg (fun L : E →L[ℝ] ℝ => L v) (hc.unique hconst)
    simpa using this
  rw [hΨt, hGd.fderiv, hFt.fderiv]
  ext v
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.inr_apply, ContinuousLinearMap.prod_apply]
  congr 1
  ext
  · simp [hfst v]
  · simp
