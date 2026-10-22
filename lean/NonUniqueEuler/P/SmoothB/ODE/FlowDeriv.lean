import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Proof of `I/SmoothB/ODE/FlowDeriv.lean`: differentiability of a flow in its initial point

Sub-step of `lem:ode`(ii), `B_global_smooth.tex:30-35` (Teschl, Theorem 2.10; Hartman,
Theorem V.3.1).

**Proof.** For `r ≥ 0` (`FlowDeriv.hasFDerivAt_flow_nonneg`): let `L`, `M`, `R` bound
`‖DG(Ψ(t, z))‖`, `‖A(t)‖`, `‖Ψ(t, z)‖` on `t ∈ [0, r]`. Given `ε ∈ (0, 1]`, uniform continuity
of `DG` on the compact ball `closedBall 0 (R + 1)` and the mean value inequality give `η > 0`
with `‖G a - G b - DG(b)(a - b)‖ ≤ ε ‖a - b‖` for `‖b‖ ≤ R`, `‖a - b‖ < η`
(`FlowDeriv.exists_linearization`). Joint continuity of `Ψ` and compactness of `[0, r]` give a
neighbourhood of `z` on which `‖Ψ(t, w) - Ψ(t, z)‖ < η` for all `t ∈ [0, r]`
(`FlowDeriv.eventually_flow_close`). There the remainder
`ρ(t) = Ψ(t, w) - Ψ(t, z) - A(t)(w - z)` satisfies `ρ(0) = 0` and
`‖ρ̇(t)‖ ≤ (L + 1) ‖ρ(t)‖ + ε M ‖w - z‖` (write `ρ̇ = [G(a) - G(b) - DG(b)(a - b)] + DG(b) ρ`
with `a = Ψ(t, w)`, `b = Ψ(t, z)`, and `‖a - b‖ ≤ ‖ρ‖ + M ‖w - z‖`), so Grönwall gives
`‖ρ(r)‖ ≤ ε C ‖w - z‖` with `C = M (e^{(L+1) r} - 1) / (L + 1)` independent of `ε`. This is the
little-o estimate. (Compared with the sketch of the interface file, the bound `‖a - b‖ ≤ ‖ρ‖ +
M ‖w - z‖` replaces the separate Grönwall estimate for `Ψ(t, w) - Ψ(t, z)`.)

For `r < 0` apply the case `r ≥ 0` to the reversed flow `(t, w) ↦ Ψ(-t, w)` of `-G`, whose
variational solution is `t ↦ A(-t)`.
-/

noncomputable section

open Set Filter Topology

namespace NonUniqueEuler.Smooth

namespace FlowDeriv

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Uniform linearization of a `C¹` map on a ball: for `ε > 0` there is `η > 0` with
`‖G a - G b - DG(b)(a - b)‖ ≤ ε ‖a - b‖` whenever `‖b‖ ≤ R` and `‖a - b‖ < η`. -/
lemma exists_linearization [FiniteDimensional ℝ W] {G : W → W} (hG : ContDiff ℝ 1 G) (R : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ b : W, ‖b‖ ≤ R → ∀ a : W, ‖a - b‖ < η →
      ‖G a - G b - fderiv ℝ G b (a - b)‖ ≤ ε * ‖a - b‖ := by
  have hDG : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
  have hUC : UniformContinuousOn (fderiv ℝ G) (Metric.closedBall (0 : W) (R + 1)) :=
    (isCompact_closedBall (0 : W) (R + 1)).uniformContinuousOn_of_continuous hDG.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hUC
  obtain ⟨η, hη, hηUC⟩ := hUC ε hε
  have hη1 : 0 < min η 1 := lt_min hη one_pos
  refine ⟨min η 1, hη1, fun b hb a ha => ?_⟩
  have hball : ∀ x ∈ Metric.ball b (min η 1), ‖fderiv ℝ G x - fderiv ℝ G b‖ ≤ ε := by
    intro x hx
    rw [Metric.mem_ball] at hx
    have hx1 : dist x b < η := lt_of_lt_of_le hx (min_le_left _ _)
    have hx2 : ‖x - b‖ < 1 := by
      rw [← dist_eq_norm]; exact lt_of_lt_of_le hx (min_le_right _ _)
    have hxB : x ∈ Metric.closedBall (0 : W) (R + 1) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      calc ‖x‖ = ‖(x - b) + b‖ := by rw [sub_add_cancel]
        _ ≤ ‖x - b‖ + ‖b‖ := norm_add_le _ _
        _ ≤ R + 1 := by linarith
    have hbB : b ∈ Metric.closedBall (0 : W) (R + 1) := by
      rw [Metric.mem_closedBall, dist_zero_right]; linarith
    have h := hηUC x hxB b hbB hx1
    rw [dist_eq_norm] at h
    exact h.le
  have hdiff : ∀ x ∈ Metric.ball b (min η 1), DifferentiableAt ℝ G x :=
    fun x _ => (hG.differentiable one_ne_zero) x
  have ha' : a ∈ Metric.ball b (min η 1) := by rwa [Metric.mem_ball, dist_eq_norm]
  exact (convex_ball b (min η 1)).norm_image_sub_le_of_norm_fderiv_le' hdiff hball
    (Metric.mem_ball_self hη1) ha'

omit [NormedSpace ℝ W] in
/-- Tube lemma: for `w` near `z`, `Ψ(t, w)` stays `η`-close to `Ψ(t, z)` for all `t ∈ [0, r]`. -/
lemma eventually_flow_close {Ψ : ℝ → W → W} (hΨc : Continuous (Function.uncurry Ψ)) (z : W)
    (r : ℝ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ w in 𝓝 z, ∀ t ∈ Icc 0 r, ‖Ψ t w - Ψ t z‖ < η := by
  apply isCompact_Icc.eventually_forall_of_forall_eventually
  intro t _
  have h1 : Continuous (fun p : W × ℝ => Ψ p.2 p.1) :=
    hΨc.comp (continuous_snd.prodMk continuous_fst)
  have h2 : Continuous (fun p : W × ℝ => Ψ p.2 z) :=
    hΨc.comp (continuous_snd.prodMk continuous_const)
  have h0 : Tendsto (fun p : W × ℝ => ‖Ψ p.2 p.1 - Ψ p.2 z‖) (𝓝 (z, t)) (𝓝 0) := by
    simpa using ((h1.sub h2).norm.tendsto (z, t))
  exact h0.eventually (eventually_lt_nhds hη)

/-- The case `r ≥ 0` of `hasFDerivAt_flow_of_variational`. -/
lemma hasFDerivAt_flow_nonneg [FiniteDimensional ℝ W] {G : W → W} (hG : ContDiff ℝ 1 G)
    {Ψ : ℝ → W → W} (hΨc : Continuous (Function.uncurry Ψ)) (hΨ0 : ∀ z, Ψ 0 z = z)
    (hΨ : ∀ r z, HasDerivAt (fun r => Ψ r z) (G (Ψ r z)) r) {z : W}
    {A : ℝ → (W →L[ℝ] W)} (hA0 : A 0 = ContinuousLinearMap.id ℝ W)
    (hA : ∀ r, HasDerivAt A ((fderiv ℝ G (Ψ r z)).comp (A r)) r) {r : ℝ} (hr : 0 ≤ r) :
    HasFDerivAt (Ψ r) (A r) z := by
  have hDG : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
  have hγ : Continuous (fun t => Ψ t z) := hΨc.comp (continuous_id.prodMk continuous_const)
  have hAc : Continuous A := continuous_iff_continuousAt.2 fun t => (hA t).continuousAt
  obtain ⟨L, hL⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := r)).exists_bound_of_continuousOn
    (hDG.comp hγ).continuousOn
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := r)).exists_bound_of_continuousOn
    hAc.continuousOn
  obtain ⟨R, hR⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := r)).exists_bound_of_continuousOn
    hγ.continuousOn
  set L' := max L 0 with hL'def
  set M' := max M 0 with hM'def
  have hL'0 : 0 ≤ L' := le_max_right _ _
  have hM'0 : 0 ≤ M' := le_max_right _ _
  set C := M' / (L' + 1) * (Real.exp ((L' + 1) * r) - 1) with hCdef
  have hC0 : 0 ≤ C := by
    apply mul_nonneg (div_nonneg hM'0 (by linarith))
    have : 1 ≤ Real.exp ((L' + 1) * r) := Real.one_le_exp (by positivity)
    linarith
  -- the key estimate: `‖ρ(r)‖ ≤ ε C ‖w - z‖` near `z`
  have key : ∀ ε, 0 < ε → ε ≤ 1 → ∀ᶠ w in 𝓝 z,
      ‖Ψ r w - Ψ r z - A r (w - z)‖ ≤ ε * C * ‖w - z‖ := by
    intro ε hε hε1
    obtain ⟨η, hη, hlin⟩ := exists_linearization hG R hε
    filter_upwards [eventually_flow_close hΨc z r hη] with w hw
    set ρ : ℝ → W := fun t => Ψ t w - Ψ t z - A t (w - z) with hρdef
    set ρ' : ℝ → W := fun t =>
      G (Ψ t w) - G (Ψ t z) - ((fderiv ℝ G (Ψ t z)).comp (A t)) (w - z) with hρ'def
    have hAw : ∀ t, HasDerivAt (fun s => A s (w - z))
        (((fderiv ℝ G (Ψ t z)).comp (A t)) (w - z)) t := by
      intro t
      simpa using (hA t).clm_apply (hasDerivAt_const t (w - z))
    have hρ : ∀ t, HasDerivAt ρ (ρ' t) t := fun t => ((hΨ t w).sub (hΨ t z)).sub (hAw t)
    have hρc : ContinuousOn ρ (Icc 0 r) :=
      (continuous_iff_continuousAt.2 fun t => (hρ t).continuousAt).continuousOn
    have h0 : ‖ρ 0‖ ≤ 0 := by simp [ρ, hΨ0, hA0]
    have hbound : ∀ t ∈ Ico 0 r, ‖ρ' t‖ ≤ (L' + 1) * ‖ρ t‖ + ε * M' * ‖w - z‖ := by
      intro t ht
      have htI : t ∈ Icc 0 r := Ico_subset_Icc_self ht
      have hρt : ρ t = (Ψ t w - Ψ t z) - A t (w - z) := rfl
      have hρ't : ρ' t = (G (Ψ t w) - G (Ψ t z) - fderiv ℝ G (Ψ t z) (Ψ t w - Ψ t z)) +
          fderiv ℝ G (Ψ t z) (ρ t) := by
        simp only [ρ', hρt, map_sub, ContinuousLinearMap.comp_apply]
        abel
      have h1 : ‖G (Ψ t w) - G (Ψ t z) - fderiv ℝ G (Ψ t z) (Ψ t w - Ψ t z)‖ ≤
          ε * ‖Ψ t w - Ψ t z‖ := hlin _ (hR t htI) _ (hw t htI)
      have h2 : ‖fderiv ℝ G (Ψ t z) (ρ t)‖ ≤ L' * ‖ρ t‖ :=
        ((fderiv ℝ G (Ψ t z)).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right ((hL t htI).trans (le_max_left _ _)) (norm_nonneg _))
      have h3 : ‖A t (w - z)‖ ≤ M' * ‖w - z‖ :=
        ((A t).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right ((hM t htI).trans (le_max_left _ _)) (norm_nonneg _))
      have h4 : ‖Ψ t w - Ψ t z‖ ≤ ‖ρ t‖ + M' * ‖w - z‖ := by
        calc ‖Ψ t w - Ψ t z‖ = ‖ρ t + A t (w - z)‖ := by rw [hρt, sub_add_cancel]
          _ ≤ ‖ρ t‖ + ‖A t (w - z)‖ := norm_add_le _ _
          _ ≤ ‖ρ t‖ + M' * ‖w - z‖ := by linarith
      have h5 : ε * ‖ρ t‖ ≤ ‖ρ t‖ := mul_le_of_le_one_left (norm_nonneg _) hε1
      have h6 : ε * ‖Ψ t w - Ψ t z‖ ≤ ε * (‖ρ t‖ + M' * ‖w - z‖) :=
        mul_le_mul_of_nonneg_left h4 hε.le
      calc ‖ρ' t‖ ≤ ‖G (Ψ t w) - G (Ψ t z) - fderiv ℝ G (Ψ t z) (Ψ t w - Ψ t z)‖ +
            ‖fderiv ℝ G (Ψ t z) (ρ t)‖ := by rw [hρ't]; exact norm_add_le _ _
        _ ≤ (L' + 1) * ‖ρ t‖ + ε * M' * ‖w - z‖ := by nlinarith
    have hgr := norm_le_gronwallBound_of_norm_deriv_right_le hρc
      (fun t _ => (hρ t).hasDerivWithinAt) h0 hbound r ⟨hr, le_rfl⟩
    rw [gronwallBound_of_K_ne_0 (by linarith : L' + 1 ≠ 0)] at hgr
    simp only [zero_mul, zero_add, sub_zero] at hgr
    calc ‖Ψ r w - Ψ r z - A r (w - z)‖ = ‖ρ r‖ := rfl
      _ ≤ ε * M' * ‖w - z‖ / (L' + 1) * (Real.exp ((L' + 1) * r) - 1) := hgr
      _ = ε * C * ‖w - z‖ := by rw [hCdef]; ring
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have hC1 : 0 < C + 1 := by linarith
  set ε := min 1 (c / (C + 1)) with hεdef
  have hε : 0 < ε := lt_min one_pos (div_pos hc hC1)
  filter_upwards [key ε hε (min_le_left _ _)] with w hw
  have hεC : ε * C ≤ c := by
    calc ε * C ≤ c / (C + 1) * C := mul_le_mul_of_nonneg_right (min_le_right _ _) hC0
      _ ≤ c := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hC1]
        nlinarith
  calc ‖Ψ r w - Ψ r z - A r (w - z)‖ ≤ ε * C * ‖w - z‖ := hw
    _ ≤ c * ‖w - z‖ := mul_le_mul_of_nonneg_right hεC (norm_nonneg _)

end FlowDeriv

/-- The time-`r` map of the flow of a `C¹` autonomous field is differentiable at `z`, with
derivative the solution of the variational equation along the trajectory of `z`
(sub-step of `lem:ode`(ii)). -/
theorem hasFDerivAt_flow_of_variational {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] {G : W → W} (hG : ContDiff ℝ 1 G) {Ψ : ℝ → W → W}
    (hΨc : Continuous (Function.uncurry Ψ)) (hΨ0 : ∀ z, Ψ 0 z = z)
    (hΨ : ∀ r z, HasDerivAt (fun r => Ψ r z) (G (Ψ r z)) r) {z : W}
    {A : ℝ → (W →L[ℝ] W)} (hA0 : A 0 = ContinuousLinearMap.id ℝ W)
    (hA : ∀ r, HasDerivAt A ((fderiv ℝ G (Ψ r z)).comp (A r)) r) (r : ℝ) :
    HasFDerivAt (Ψ r) (A r) z := by
  rcases le_total 0 r with hr | hr
  · exact FlowDeriv.hasFDerivAt_flow_nonneg hG hΨc hΨ0 hΨ hA0 hA hr
  · -- reverse time: `(t, w) ↦ Ψ(-t, w)` is the flow of `-G`, with variational solution `A(-·)`
    have hG' : ContDiff ℝ 1 (fun x => -G x) := hG.neg
    have hΨc' : Continuous (Function.uncurry fun (t : ℝ) (w : W) => Ψ (-t) w) :=
      hΨc.comp (continuous_fst.neg.prodMk continuous_snd)
    have hΨ0' : ∀ w, (fun (t : ℝ) (w : W) => Ψ (-t) w) 0 w = w := fun w => by simp [hΨ0]
    have hΨ' : ∀ t w, HasDerivAt (fun t => (fun (t : ℝ) (w : W) => Ψ (-t) w) t w)
        ((fun x => -G x) ((fun (t : ℝ) (w : W) => Ψ (-t) w) t w)) t := by
      intro t w
      have h := (hΨ (-t) w).scomp t (hasDerivAt_neg (x := t))
      simpa [Function.comp_def] using h
    have hA0' : (fun t => A (-t)) 0 = ContinuousLinearMap.id ℝ W := by simp [hA0]
    have hA' : ∀ t, HasDerivAt (fun t => A (-t))
        ((fderiv ℝ (fun x => -G x) ((fun (t : ℝ) (w : W) => Ψ (-t) w) t z)).comp
          ((fun t => A (-t)) t)) t := by
      intro t
      have h := (hA (-t)).scomp t (hasDerivAt_neg (x := t))
      simpa [Function.comp_def, fderiv_fun_neg] using h
    have h := FlowDeriv.hasFDerivAt_flow_nonneg hG' hΨc' hΨ0' hΨ' hA0' hA' (neg_nonneg.2 hr)
    simpa using h

end NonUniqueEuler.Smooth
