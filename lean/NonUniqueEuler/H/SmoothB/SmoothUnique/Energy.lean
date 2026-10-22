import NonUniqueEuler.Defs.SmoothB.Solution
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Helper for `P/SmoothB/SmoothUnique`: the energy `t ↦ ∫ u(t)²` and a Grönwall argument

Generic calculus used in the proof of thm:smooth(5) (`B_global_smooth.tex:494-513`):

* `eq_zero_of_abs_deriv_le_mul`: a nonnegative function `E`, continuous on `[a, b]`,
  differentiable on `(a, b)` with `|E'| ≤ C E`, vanishing at one point `c ∈ [a, b]`, vanishes on
  `[a, b]` (Grönwall, via the monotonicity of `E e^{∓C t}`);
* `continuousOn_integral_sq`: `t ↦ ∫ u(t, x)² dx` is continuous for `u` continuous with
  supports in one ball;
* `hasDerivAt_integral_sq`: for `u ∈ C¹((a, b) × ℝ²)` with supports in one ball,
  `d/dt ∫ u(t)² = ∫ 2 u(t) ∂_t u(t)` (differentiation under the integral sign);
* `hasDerivAt_uncurry_left`, `fderiv_uncurry_apply_one`: the chain rule for the partial
  derivatives of `(t, x) ↦ u(t, x)`.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler.Smooth.UniqueAux

/-! ### Grönwall -/

/-- **Grönwall's inequality, zero case.** -/
theorem eq_zero_of_abs_deriv_le_mul {E E' : ℝ → ℝ} {a b c C : ℝ} (hc : c ∈ Icc a b)
    (hcont : ContinuousOn E (Icc a b)) (hnn : ∀ s ∈ Icc a b, 0 ≤ E s)
    (hder : ∀ s ∈ Ioo a b, HasDerivAt E (E' s) s) (hbd : ∀ s ∈ Ioo a b, |E' s| ≤ C * E s)
    (h0 : E c = 0) : ∀ s ∈ Icc a b, E s = 0 := by
  intro s hs
  refine le_antisymm ?_ (hnn s hs)
  rcases le_total c s with hcs | hsc
  · -- `E e^{-C r}` is antitone on `[c, s]`
    set g : ℝ → ℝ := fun r => E r * Real.exp (-(C * r)) with hg
    have hsub : Icc c s ⊆ Icc a b := Icc_subset_Icc hc.1 hs.2
    have hgd : ∀ r ∈ Ioo c s, HasDerivAt g
        (E' r * Real.exp (-(C * r)) + E r * (Real.exp (-(C * r)) * (-(C * 1)))) r := by
      intro r hr
      have hr' : r ∈ Ioo a b := ⟨lt_of_le_of_lt hc.1 hr.1, lt_of_lt_of_le hr.2 hs.2⟩
      exact (hder r hr').mul ((((hasDerivAt_id r).const_mul C).neg).exp)
    have hanti : AntitoneOn g (Icc c s) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc c s)
      · exact (hcont.mono hsub).mul (by fun_prop : Continuous fun r => Real.exp (-(C * r))).continuousOn
      · rw [interior_Icc]
        intro r hr
        exact (hgd r hr).differentiableAt.differentiableWithinAt
      · rw [interior_Icc]
        intro r hr
        rw [(hgd r hr).deriv]
        have hr' : r ∈ Ioo a b := ⟨lt_of_le_of_lt hc.1 hr.1, lt_of_lt_of_le hr.2 hs.2⟩
        have h1 : E' r ≤ C * E r := (le_abs_self _).trans (hbd r hr')
        have he := Real.exp_pos (-(C * r))
        have : E' r * Real.exp (-(C * r)) + E r * (Real.exp (-(C * r)) * (-(C * 1))) =
            (E' r - C * E r) * Real.exp (-(C * r)) := by ring
        rw [this]
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) he.le
    have := hanti ⟨le_rfl, hcs⟩ ⟨hcs, le_rfl⟩ hcs
    simp only [hg, h0, zero_mul] at this
    by_contra hpos
    have := mul_pos (not_le.1 hpos) (Real.exp_pos (-(C * s)))
    linarith
  · -- `E e^{C r}` is monotone on `[s, c]`
    set g : ℝ → ℝ := fun r => E r * Real.exp (C * r) with hg
    have hsub : Icc s c ⊆ Icc a b := Icc_subset_Icc hs.1 hc.2
    have hgd : ∀ r ∈ Ioo s c, HasDerivAt g
        (E' r * Real.exp (C * r) + E r * (Real.exp (C * r) * (C * 1))) r := by
      intro r hr
      have hr' : r ∈ Ioo a b := ⟨lt_of_le_of_lt hs.1 hr.1, lt_of_lt_of_le hr.2 hc.2⟩
      exact (hder r hr').mul (((hasDerivAt_id r).const_mul C).exp)
    have hmono : MonotoneOn g (Icc s c) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc s c)
      · exact (hcont.mono hsub).mul (by fun_prop : Continuous fun r => Real.exp (C * r)).continuousOn
      · rw [interior_Icc]
        intro r hr
        exact (hgd r hr).differentiableAt.differentiableWithinAt
      · rw [interior_Icc]
        intro r hr
        rw [(hgd r hr).deriv]
        have hr' : r ∈ Ioo a b := ⟨lt_of_le_of_lt hs.1 hr.1, lt_of_lt_of_le hr.2 hc.2⟩
        have h1 : -(C * E r) ≤ E' r := (neg_le_of_abs_le (hbd r hr'))
        have he := Real.exp_pos (C * r)
        have : E' r * Real.exp (C * r) + E r * (Real.exp (C * r) * (C * 1)) =
            (E' r + C * E r) * Real.exp (C * r) := by ring
        rw [this]
        exact mul_nonneg (by linarith) he.le
    have := hmono ⟨le_rfl, hsc⟩ ⟨hsc, le_rfl⟩ hsc
    simp only [hg, h0, zero_mul] at this
    by_contra hpos
    have := mul_pos (not_le.1 hpos) (Real.exp_pos (C * s))
    linarith

/-! ### Continuity of the energy -/

/-- `t ↦ ∫ u(t, x)² dx` is continuous on `s` if `u` is continuous on `s × ℝ²` and `u(t)`
vanishes outside `B_ρ` for `t ∈ s`. -/
theorem continuousOn_integral_sq {u : ℝ → ℂ → ℝ} {s : Set ℝ} {ρ : ℝ}
    (hu : ContinuousOn (Function.uncurry u) (s ×ˢ univ))
    (hsupp : ∀ r ∈ s, ∀ x, x ∉ ball (0 : ℂ) ρ → u r x = 0) :
    ContinuousOn (fun r => ∫ x, u r x ^ 2) s := by
  have h2 : ContinuousOn (Function.uncurry fun r x => u r x ^ 2) (s ×ˢ univ) := hu.pow 2
  refine continuousOn_integral_of_compact_support (isCompact_closedBall (0 : ℂ) ρ) h2 ?_
  intro p x hp hx
  rw [hsupp p hp x (fun h => hx (ball_subset_closedBall h))]
  ring

/-! ### Partial derivatives of `(t, x) ↦ u(t, x)` -/

/-- The time derivative of `t ↦ u(t, x)` is `Du(t, x)(1, 0)`. -/
theorem hasDerivAt_uncurry_left {u : ℝ → ℂ → ℝ} {s : ℝ} {x : ℂ}
    (hd : DifferentiableAt ℝ (Function.uncurry u) (s, x)) :
    HasDerivAt (fun r => u r x) (fderiv ℝ (Function.uncurry u) (s, x) (1, 0)) s := by
  have h1 : HasDerivAt (fun r : ℝ => (r, x)) ((1 : ℝ), (0 : ℂ)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
  exact hd.hasFDerivAt.comp_hasDerivAt s h1

/-- The space derivative of `u(t)` is `Du(t, x)(0, ·)`. -/
theorem fderiv_uncurry_right {u : ℝ → ℂ → ℝ} {s : ℝ} {x : ℂ}
    (hd : DifferentiableAt ℝ (Function.uncurry u) (s, x)) (w : ℂ) :
    fderiv ℝ (u s) x w = fderiv ℝ (Function.uncurry u) (s, x) (0, w) := by
  have h1 : HasFDerivAt (fun y : ℂ => (s, y)) (ContinuousLinearMap.inr ℝ ℝ ℂ) x :=
    hasFDerivAt_prodMk_right s x
  have h2 : HasFDerivAt (u s) ((fderiv ℝ (Function.uncurry u) (s, x)).comp
      (ContinuousLinearMap.inr ℝ ℝ ℂ)) x :=
    hd.hasFDerivAt.comp x h1
  rw [h2.fderiv]
  rfl

/-- The derivative of `(t, x) ↦ u(t, x)` in the direction `(1, w)` is `∂_t u + Du(t)(w)`. -/
theorem fderiv_uncurry_apply_one {u : ℝ → ℂ → ℝ} {s : ℝ} {x : ℂ}
    (hd : DifferentiableAt ℝ (Function.uncurry u) (s, x)) (w : ℂ) :
    fderiv ℝ (Function.uncurry u) (s, x) (1, w) =
      deriv (fun r => u r x) s + fderiv ℝ (u s) x w := by
  rw [(hasDerivAt_uncurry_left hd).deriv, fderiv_uncurry_right hd, ← map_add]
  simp

/-! ### Differentiation of the energy -/

/-- **Differentiation of the energy.** For `u ∈ C¹((a, b) × ℝ²)` with `u(t)` vanishing outside
`B_ρ` for `t ∈ (a, b)`, `d/dt ∫ u(t)² = ∫ 2 u(t) ∂_t u(t)` at every `s ∈ (a, b)`, and the
integrand `2 u(s) ∂_t u(s)` is integrable. -/
theorem hasDerivAt_integral_sq {u : ℝ → ℂ → ℝ} {a b ρ : ℝ}
    (hu : ContDiffOn ℝ 1 (Function.uncurry u) (Ioo a b ×ˢ univ))
    (hsupp : ∀ r ∈ Ioo a b, ∀ x, x ∉ ball (0 : ℂ) ρ → u r x = 0) {s : ℝ} (hs : s ∈ Ioo a b) :
    Integrable (fun x => 2 * u s x * deriv (fun r => u r x) s) ∧
      HasDerivAt (fun r => ∫ x, u r x ^ 2) (∫ x, 2 * u s x * deriv (fun r => u r x) s) s := by
  set U : Set (ℝ × ℂ) := Ioo a b ×ˢ univ with hUdef
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_univ
  have hdiff : ∀ p ∈ U, DifferentiableAt ℝ (Function.uncurry u) p := fun p hp =>
    (hu.contDiffAt (hU.mem_nhds hp)).differentiableAt one_ne_zero
  set D : ℝ → ℂ → ℝ := fun r x => fderiv ℝ (Function.uncurry u) (r, x) (1, 0) with hD
  have hpd : ∀ r ∈ Ioo a b, ∀ x, HasDerivAt (fun r' => u r' x) (D r x) r := fun r hr x =>
    hasDerivAt_uncurry_left (hdiff (r, x) ⟨hr, trivial⟩)
  -- continuity of `u` and `G = 2 u Du(1,0)` on `U`
  have hcu : ContinuousOn (Function.uncurry u) U := hu.continuousOn
  have hcD : ContinuousOn (fun p : ℝ × ℂ => fderiv ℝ (Function.uncurry u) p (1, 0)) U :=
    (hu.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  set G : ℝ × ℂ → ℝ := fun p => 2 * Function.uncurry u p * fderiv ℝ (Function.uncurry u) p (1, 0)
    with hG
  have hcG : ContinuousOn G U := (continuousOn_const.mul hcu).mul hcD
  -- slices are continuous
  have hslice : ∀ r ∈ Ioo a b, Continuous (u r) := fun r hr =>
    hcu.comp_continuous (Continuous.prodMk_right r) (fun x => ⟨hr, trivial⟩)
  have hsliceG : ∀ r ∈ Ioo a b, Continuous (fun x => G (r, x)) := fun r hr =>
    hcG.comp_continuous (Continuous.prodMk_right r) (fun x => ⟨hr, trivial⟩)
  -- a compact neighbourhood
  obtain ⟨ε, hε, hεsub⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (Ioo_mem_nhds hs.1 hs.2)
  have hK : IsCompact (closedBall s ε ×ˢ closedBall (0 : ℂ) ρ) :=
    (isCompact_closedBall s ε).prod (isCompact_closedBall 0 ρ)
  have hKU : closedBall s ε ×ˢ closedBall (0 : ℂ) ρ ⊆ U := prod_mono hεsub (subset_univ _)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hcG.mono hKU)
  set bound : ℂ → ℝ := (closedBall (0 : ℂ) ρ).indicator (fun _ => M) with hbound
  have hvan : ∀ r ∈ Ioo a b, ∀ x, x ∉ closedBall (0 : ℂ) ρ → u r x = 0 := fun r hr x hx =>
    hsupp r hr x (fun h => hx (ball_subset_closedBall h))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun r x => u r x ^ 2) (F' := fun r x => 2 * u r x * D r x) (bound := bound)
    (x₀ := s) (ball_mem_nhds s hε) ?_ ?_ ?_ ?_ ?_ ?_
  · have heq : (fun x => 2 * u s x * D s x) = fun x => 2 * u s x * deriv (fun r => u r x) s := by
      funext x
      rw [(hpd s hs x).deriv]
    rw [heq] at key
    exact key
  · filter_upwards [Ioo_mem_nhds hs.1 hs.2] with r hr
    exact ((hslice r hr).pow 2).aestronglyMeasurable
  · refine Continuous.integrable_of_hasCompactSupport ((hslice s hs).pow 2) ?_
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) ρ) (fun x hx => ?_)
    simp [hvan s hs x hx]
  · exact (hsliceG s hs).aestronglyMeasurable
  · refine Eventually.of_forall (fun x r hr => ?_)
    have hr' : r ∈ Ioo a b := hεsub (ball_subset_closedBall hr)
    by_cases hx : x ∈ closedBall (0 : ℂ) ρ
    · rw [hbound, indicator_of_mem hx]
      exact hM (r, x) ⟨ball_subset_closedBall hr, hx⟩
    · rw [hbound, indicator_of_notMem hx, hvan r hr' x hx]
      simp
  · exact (integrableOn_const (isCompact_closedBall (0 : ℂ) ρ).measure_lt_top.ne).integrable_indicator
      measurableSet_closedBall
  · refine Eventually.of_forall (fun x r hr => ?_)
    have hr' : r ∈ Ioo a b := hεsub (ball_subset_closedBall hr)
    exact ((hpd r hr' x).fun_pow 2).congr_deriv (by norm_num)

end NonUniqueEuler.Smooth.UniqueAux
