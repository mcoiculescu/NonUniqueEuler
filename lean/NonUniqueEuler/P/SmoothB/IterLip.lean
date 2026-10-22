import NonUniqueEuler.Defs.SmoothB.Iteration
import NonUniqueEuler.I.SmoothB.Flow
import NonUniqueEuler.I.SmoothB.GradBound
import NonUniqueEuler.I.SmoothB.Iterates
import NonUniqueEuler.I.SmoothB.Constants
import NonUniqueEuler.I.SmoothB.OpNormEntry
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Proof of `lem:iter-lip` (uniform Lipschitz bounds on the iterates and their velocities)

Proof of `I/SmoothB/IterLip.lean`, following `B_global_smooth.tex:272-300`.

* `IterLipAux.amax_pos`: `A = ‖ω₀‖_{L^∞} > 0` for `ω₀ ≠ 0`;
* `IterLipAux.norm_fderiv_datum_le`, `IterLipAux.N0_le`: `|∇ω₀| ≤ N₀ ≤ A e^{𝓛(0)}`
  (`N₀ e^{-𝓛(0)} = min(N₀, A) ≤ A`);
* `IterLipAux.entry_bound`, `IterLipAux.opNorm_bound`: the first bound at time `τ` implies the
  second (via `grad_bound`) and the third (via `norm_fderiv_le_two_mul_of_gradEntry_le`);
* `IterLipAux.norm_le_exp_of_norm_deriv_le`: a Grönwall inequality with a variable
  coefficient on `[0, T]` (fencing with `B(s) = e^{G(s) + εs}`, then `ε → 0`);
* `IterLipAux.norm_le_of_variational`: `‖Y(0)‖ ≤ e^{𝓛(t) - 𝓛(0)}` for a solution of
  `‖Y'‖ ≤ V ‖Y‖` with `‖Y(t)‖ ≤ 1` (uses `𝓛' = V` on `(0, ∞)` and evenness);
* `IterLipAux.grad_succ_bound`: the chain rule step `j → j + 1`.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace NonUniqueEuler.Smooth

variable {ω₀ : ℂ → ℝ} {R₀ : ℝ}

namespace IterLipAux

/-! ### Facts about the datum -/

/-- `ω₀` vanishes outside `B_{R₀}`. -/
theorem datum_eq_zero (h : IsSmoothDatum ω₀ R₀) : ∀ x : ℂ, R₀ < ‖x‖ → ω₀ x = 0 := by
  intro x hx
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have := h.tsupport_subset hmem
  rw [Metric.mem_ball, dist_zero_right] at this
  linarith

/-- `A = ‖ω₀‖_{L^∞} > 0` when `ω₀ ≠ 0`. -/
theorem amax_pos (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) : 0 < Amax ω₀ := by
  have hc : Continuous ω₀ := h.contDiff.continuous
  have hmem : MemLp ω₀ ⊤ volume := hc.memLp_of_hasCompactSupport h.hasCompactSupport
  have h0 : eLpNorm ω₀ ⊤ volume ≠ 0 := by
    intro h0
    rw [eLpNorm_eq_zero_iff hmem.1 (by simp)] at h0
    exact hne ((hc.ae_eq_iff_eq volume continuous_zero).1 h0)
  exact ENNReal.toReal_pos h0 hmem.eLpNorm_ne_top

theorem bddAbove_norm_fderiv (h : IsSmoothDatum ω₀ R₀) :
    BddAbove (range fun x => ‖fderiv ℝ ω₀ x‖) := by
  have hc : Continuous (fderiv ℝ ω₀) := h.contDiff.continuous_fderiv (by simp)
  exact hc.norm.bddAbove_range_of_hasCompactSupport
    (h.hasCompactSupport.fderiv (𝕜 := ℝ)).norm

/-- `|∇ω₀(y)| ≤ N₀`. -/
theorem norm_fderiv_datum_le (h : IsSmoothDatum ω₀ R₀) (y : ℂ) :
    ‖fderiv ℝ ω₀ y‖ ≤ N0 ω₀ :=
  le_ciSup (bddAbove_norm_fderiv h) y

theorem N0_nonneg (ω₀ : ℂ → ℝ) : 0 ≤ N0 ω₀ :=
  Real.iSup_nonneg fun _ => norm_nonneg _

/-- `y ≤ e^{log₊ y}`. -/
theorem le_exp_posLog (y : ℝ) : y ≤ Real.exp (Real.posLog y) := by
  rcases le_or_gt y 0 with hy | hy
  · exact hy.trans (Real.exp_pos _).le
  · calc y = Real.exp (Real.log y) := (Real.exp_log hy).symm
      _ ≤ Real.exp (Real.posLog y) := by
        rw [Real.exp_le_exp, Real.posLog_apply]
        exact le_max_right _ _

/-- `N₀ ≤ A e^{𝓛(0)} = max(A, N₀)`. -/
theorem N0_le (hA : 0 < Amax ω₀) : N0 ω₀ ≤ Amax ω₀ * Real.exp (calL ω₀ 0) := by
  rw [calL_zero]
  calc N0 ω₀ = Amax ω₀ * (N0 ω₀ / Amax ω₀) := by field_simp
    _ ≤ Amax ω₀ * Real.exp (Real.posLog (N0 ω₀ / Amax ω₀)) :=
      mul_le_mul_of_nonneg_left (le_exp_posLog _) hA.le

theorem continuous_calL (ω₀ : ℂ → ℝ) : Continuous (calL ω₀) := by
  unfold calL
  fun_prop

/-! ### The case `j = 0` -/

theorem grad_zero_bound (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (t : ℝ) (x : ℂ) :
    ‖fderiv ℝ (iter ω₀ 0 t) x‖ ≤ Psi ω₀ t := by
  have h0 : iter ω₀ 0 t = ω₀ := rfl
  rw [h0]
  have hA := amax_pos h hne
  have hL : calL ω₀ 0 ≤ calL ω₀ t := by
    rw [calL_zero]; exact posLog_le_calL ω₀ t
  calc ‖fderiv ℝ ω₀ x‖ ≤ N0 ω₀ := norm_fderiv_datum_le h x
    _ ≤ Amax ω₀ * Real.exp (calL ω₀ 0) := N0_le hA
    _ ≤ Amax ω₀ * Real.exp (calL ω₀ t) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hL) hA.le
    _ = Psi ω₀ t := rfl

/-! ### The first bound implies the second and the third -/

/-- `log₊(Ψ(τ)/A) = 𝓛(τ)`. -/
theorem posLog_Psi_div (hA : 0 < Amax ω₀) (τ : ℝ) :
    Real.posLog (Psi ω₀ τ / Amax ω₀) = calL ω₀ τ := by
  have : Psi ω₀ τ / Amax ω₀ = Real.exp (calL ω₀ τ) := by
    simp only [Psi]; field_simp
  rw [this, Real.posLog_apply, Real.log_exp]
  exact max_eq_right (calL_nonneg ω₀ τ)

/-- The first bound at time `τ` implies the second (`grad_bound`). -/
theorem entry_bound (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (j : ℕ) (τ : ℝ)
    (hj : ∀ x, ‖fderiv ℝ (iter ω₀ j τ) x‖ ≤ Psi ω₀ τ) (x : ℂ) (i l : Fin 2) :
    |Prelim.gradEntry (iterVel ω₀ j τ) i l x| ≤ Amax ω₀ * (calL ω₀ τ + cstar ω₀) := by
  have hA := amax_pos h hne
  have hsm := iterates_smooth_support h hne j
  have hg1 : ContDiff ℝ 1 (iter ω₀ j τ) := by
    have : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (iter ω₀ j τ) :=
      hsm.1.comp (contDiff_const.prodMk contDiff_id)
    exact this.of_le (by simp)
  have hgc : HasCompactSupport (iter ω₀ j τ) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (R₀ + Ustar ω₀ * |τ|)) ?_
    intro y hy
    apply hsm.2 R₀ (datum_eq_zero h) τ y
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hy
    exact hy
  have hAg : Amax (iter ω₀ j τ) = Amax ω₀ := by
    unfold Amax; rw [iterates_eLpNorm h hne j τ le_top]
  have hlg : l1 (iter ω₀ j τ) = l1 ω₀ := by
    unfold l1; rw [iterates_eLpNorm h hne j τ le_rfl]
  have hgne : iter ω₀ j τ ≠ 0 := by
    intro hg0
    rw [hg0] at hAg
    have hz : Amax (0 : ℂ → ℝ) = 0 := by simp [Amax]
    linarith
  have hgb := (grad_bound hg1 hgc hgne).2 x i l
  rw [hAg, hlg] at hgb
  have hsup : gradSup (iter ω₀ j τ) ≤ Psi ω₀ τ := ciSup_le hj
  have hsup0 : 0 ≤ gradSup (iter ω₀ j τ) := Real.iSup_nonneg fun _ => norm_nonneg _
  have hlog : Real.posLog (gradSup (iter ω₀ j τ) / Amax ω₀) ≤ calL ω₀ τ := by
    rw [← posLog_Psi_div hA τ]
    apply Real.posLog_le_posLog
    · have : 0 ≤ gradSup (iter ω₀ j τ) / Amax ω₀ := div_nonneg hsup0 hA.le
      linarith
    · exact div_le_div_of_nonneg_right hsup hA.le
  have hvel : iterVel ω₀ j τ = velocity (iter ω₀ j τ) := rfl
  rw [hvel]
  calc |Prelim.gradEntry (velocity (iter ω₀ j τ)) i l x|
      ≤ Amax ω₀ * (2 + Real.posLog (gradSup (iter ω₀ j τ) / Amax ω₀)) +
          l1 ω₀ / (2 * Real.pi) := hgb
    _ ≤ Amax ω₀ * (2 + calL ω₀ τ) + l1 ω₀ / (2 * Real.pi) := by
      gcongr
    _ = Amax ω₀ * (calL ω₀ τ + cstar ω₀) := by
      simp only [cstar]
      field_simp
      ring

/-- The first bound at time `τ` implies the third. -/
theorem opNorm_bound (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (j : ℕ) (τ : ℝ)
    (hj : ∀ x, ‖fderiv ℝ (iter ω₀ j τ) x‖ ≤ Psi ω₀ τ) (x : ℂ) :
    ‖fderiv ℝ (iterVel ω₀ j τ) x‖ ≤ Vbd ω₀ τ := by
  have := norm_fderiv_le_two_mul_of_gradEntry_le (u := iterVel ω₀ j τ) (x := x)
    (fun i l => entry_bound h hne j τ hj x i l)
  calc ‖fderiv ℝ (iterVel ω₀ j τ) x‖ ≤ 2 * (Amax ω₀ * (calL ω₀ τ + cstar ω₀)) := this
    _ = Vbd ω₀ τ := by simp only [Vbd]; ring

/-! ### Grönwall with a variable coefficient -/

/-- **Grönwall** on `[0, T]` with a variable coefficient: if `‖f'‖ ≤ W ‖f‖`, `G' = W` (right
derivatives) and `‖f(0)‖ ≤ e^{G(0)}`, then `‖f(T)‖ ≤ e^{G(T)}`. -/
theorem norm_le_exp_of_norm_deriv_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f' : ℝ → E} {G W : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn f (Icc 0 T)) (hf' : ∀ s ∈ Ico 0 T, HasDerivWithinAt f (f' s) (Ici s) s)
    (hG : ContinuousOn G (Icc 0 T)) (hG' : ∀ s ∈ Ico 0 T, HasDerivWithinAt G (W s) (Ici s) s)
    (hb : ∀ s ∈ Ico 0 T, ‖f' s‖ ≤ W s * ‖f s‖) (h0 : ‖f 0‖ ≤ Real.exp (G 0)) :
    ‖f T‖ ≤ Real.exp (G T) := by
  have key : ∀ ε : ℝ, 0 < ε → ‖f T‖ ≤ Real.exp (G T + ε * T) := by
    intro ε hε
    refine image_norm_le_of_norm_deriv_right_lt_deriv_boundary' (a := 0) (b := T) hf hf'
      (B := fun s => Real.exp (G s + ε * s))
      (B' := fun s => Real.exp (G s + ε * s) * (W s + ε)) (by simpa using h0) ?_ ?_ ?_
      (right_mem_Icc.2 hT)
    · exact (hG.add (continuousOn_const.mul continuousOn_id)).rexp
    · intro s hs
      have := ((hG' s hs).add ((hasDerivWithinAt_id s (Ici s)).const_mul ε)).exp
      simpa using this
    · intro s hs heq
      have hpos := Real.exp_pos (G s + ε * s)
      calc ‖f' s‖ ≤ W s * ‖f s‖ := hb s hs
        _ = W s * Real.exp (G s + ε * s) := by rw [heq]
        _ < Real.exp (G s + ε * s) * (W s + ε) := by nlinarith
  have hcont : Continuous fun ε : ℝ => Real.exp (G T + ε * T) := by fun_prop
  have hlim : Tendsto (fun ε : ℝ => Real.exp (G T + ε * T)) (𝓝[>] 0)
      (𝓝 (Real.exp (G T))) := by
    have := hcont.tendsto 0
    simp only [zero_mul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)

/-- The Grönwall step for `t ≥ 0`: `‖Y(0)‖ ≤ e^{𝓛(t) - 𝓛(0)}`. -/
theorem norm_le_of_variational_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ω₀ : ℂ → ℝ) {Y Y' : ℝ → E} {t : ℝ} (ht : 0 ≤ t) (hY : ∀ τ, HasDerivAt Y (Y' τ) τ)
    (hb : ∀ τ, ‖Y' τ‖ ≤ Vbd ω₀ τ * ‖Y τ‖) (h1 : ‖Y t‖ ≤ 1) :
    ‖Y 0‖ ≤ Real.exp (calL ω₀ t - calL ω₀ 0) := by
  have hYc : Continuous Y := continuous_iff_continuousAt.2 fun τ => (hY τ).continuousAt
  have hLc := continuous_calL ω₀
  have := norm_le_exp_of_norm_deriv_le (f := fun s => Y (t - s)) (f' := fun s => -Y' (t - s))
    (G := fun s => calL ω₀ t - calL ω₀ (t - s)) (W := fun s => Vbd ω₀ (t - s)) ht
    (hYc.comp (continuous_const.sub continuous_id)).continuousOn
    (fun s _ => ((hY (t - s)).comp_const_sub t s).hasDerivWithinAt)
    (continuous_const.sub (hLc.comp (continuous_const.sub continuous_id))).continuousOn
    (fun s hs => by
      have hpos : 0 < t - s := by linarith [hs.2]
      have := ((hasDerivAt_calL ω₀ hpos).comp_const_sub t s)
      have h2 := (hasDerivAt_const s (calL ω₀ t)).sub this
      simp only [sub_neg_eq_add, zero_add] at h2
      exact h2.hasDerivWithinAt)
    (fun s _ => by rw [norm_neg]; exact hb (t - s))
    (by simpa using h1)
  simpa using this

/-- `‖Y(0)‖ ≤ e^{𝓛(t) - 𝓛(0)}` for every `t`, if `‖Y'‖ ≤ V ‖Y‖` and `‖Y(t)‖ ≤ 1`. -/
theorem norm_le_of_variational {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ω₀ : ℂ → ℝ) {Y Y' : ℝ → E} (t : ℝ) (hY : ∀ τ, HasDerivAt Y (Y' τ) τ)
    (hb : ∀ τ, ‖Y' τ‖ ≤ Vbd ω₀ τ * ‖Y τ‖) (h1 : ‖Y t‖ ≤ 1) :
    ‖Y 0‖ ≤ Real.exp (calL ω₀ t - calL ω₀ 0) := by
  rcases le_or_gt 0 t with ht | ht
  · exact norm_le_of_variational_nonneg ω₀ ht hY hb h1
  · have hZ : ∀ τ, HasDerivAt (fun σ => Y (-σ)) (-Y' (-τ)) τ := by
      intro τ
      have := (hY (-τ)).scomp τ (hasDerivAt_neg τ)
      simpa [Function.comp_def] using this
    have := norm_le_of_variational_nonneg ω₀ (Y := fun σ => Y (-σ)) (t := -t)
      (by linarith) hZ (fun τ => by
        rw [norm_neg]
        have := hb (-τ)
        rwa [Vbd_neg] at this) (by simpa using h1)
    simpa using this

/-! ### The step `j → j + 1` -/

/-- If `‖∇v^{[j]}‖_op ≤ V`, then `|∇ω^{[j+1]}(t, x)| ≤ Ψ(t)`. -/
theorem grad_succ_bound (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (j : ℕ)
    (hV : ∀ τ x, ‖fderiv ℝ (iterVel ω₀ j τ) x‖ ≤ Vbd ω₀ τ) (t : ℝ) (x : ℂ) :
    ‖fderiv ℝ (iter ω₀ (j + 1) t) x‖ ≤ Psi ω₀ t := by
  have hA := amax_pos h hne
  have hu : IsSmoothBoundedField (iterVel ω₀ j) := (iterates_velocity h hne j).2.2.2.2
  have heq : iter ω₀ (j + 1) t = ω₀ ∘ flowOf (iterVel ω₀ j) 0 t :=
    funext fun y => iter_succ ω₀ j t y
  have hdΦ : DifferentiableAt ℝ (flowOf (iterVel ω₀ j) 0 t) x :=
    ((flowOf_diffeo hu 0 t).2.2.1.differentiable (by simp)) x
  have hdω : DifferentiableAt ℝ ω₀ (flowOf (iterVel ω₀ j) 0 t x) :=
    (h.contDiff.differentiable (by simp)) _
  rw [heq, fderiv_comp x hdω hdΦ]
  obtain ⟨hvar, hinit⟩ := flowOf_variational hu t x
  have hY : ‖fderiv ℝ (flowOf (iterVel ω₀ j) 0 t) x‖ ≤
      Real.exp (calL ω₀ t - calL ω₀ 0) := by
    refine norm_le_of_variational ω₀ (Y := fun τ => fderiv ℝ (flowOf (iterVel ω₀ j) τ t) x)
      t hvar (fun τ => ?_) ?_
    · refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      exact mul_le_mul_of_nonneg_right (hV τ _) (norm_nonneg _)
    · simp only [hinit]
      exact ContinuousLinearMap.norm_id_le
  calc ‖(fderiv ℝ ω₀ (flowOf (iterVel ω₀ j) 0 t x)).comp
        (fderiv ℝ (flowOf (iterVel ω₀ j) 0 t) x)‖
      ≤ ‖fderiv ℝ ω₀ (flowOf (iterVel ω₀ j) 0 t x)‖ *
          ‖fderiv ℝ (flowOf (iterVel ω₀ j) 0 t) x‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ N0 ω₀ * Real.exp (calL ω₀ t - calL ω₀ 0) :=
      mul_le_mul (norm_fderiv_datum_le h _) hY (norm_nonneg _) (N0_nonneg ω₀)
    _ ≤ Amax ω₀ * Real.exp (calL ω₀ 0) * Real.exp (calL ω₀ t - calL ω₀ 0) :=
      mul_le_mul_of_nonneg_right (N0_le hA) (Real.exp_pos _).le
    _ = Psi ω₀ t := by
      rw [mul_assoc, ← Real.exp_add, add_sub_cancel]
      rfl

end IterLipAux

open IterLipAux in
/-- `lem:iter-lip`: for every `j ≥ 0`, `t ∈ ℝ`, `x ∈ ℝ²`,
`|∇ω^{[j]}(t, x)| ≤ Ψ(t)`, `max_{i,l} |∂_l v^{[j]}_i(t, x)| ≤ A(𝓛(t) + c_*)` and
`‖∇v^{[j]}(t, x)‖_op ≤ V(t)`. -/
theorem iter_lip (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (j : ℕ) (t : ℝ) (x : ℂ) :
    ‖fderiv ℝ (iter ω₀ j t) x‖ ≤ Psi ω₀ t ∧
      (∀ i l : Fin 2,
        |Prelim.gradEntry (iterVel ω₀ j t) i l x| ≤ Amax ω₀ * (calL ω₀ t + cstar ω₀)) ∧
      ‖fderiv ℝ (iterVel ω₀ j t) x‖ ≤ Vbd ω₀ t := by
  have hfirst : ∀ k : ℕ, ∀ τ : ℝ, ∀ y : ℂ, ‖fderiv ℝ (iter ω₀ k τ) y‖ ≤ Psi ω₀ τ := by
    intro k
    induction k with
    | zero => exact grad_zero_bound h hne
    | succ k ih =>
      exact grad_succ_bound h hne k (fun τ y => opNorm_bound h hne k τ (ih τ) y)
  exact ⟨hfirst j t x, fun i l => entry_bound h hne j t (hfirst j t) x i l,
    opNorm_bound h hne j t (hfirst j t) x⟩

end NonUniqueEuler.Smooth
