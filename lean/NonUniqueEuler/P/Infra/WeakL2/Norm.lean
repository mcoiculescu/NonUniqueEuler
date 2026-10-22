import NonUniqueEuler.Defs.Infra.WeakL2
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Order.LiminfLimsup

/-!
# Proof of `I/Infra/WeakL2/Norm.lean` (I-WEAKL2): norms and weak limits; Radon–Riesz at `p = 2`

Same declarations as `NonUniqueEuler/I/Infra/WeakL2/Norm.lean` (same names, statements copied
verbatim), proved; see that file for the documentation. Used by `lem:RR`
(`03_compactness.tex:692-715`, formalized for `p = 2`, restructuring R8).

Private helpers: `WeakTendsto.eventually_lt_norm` (real form of the weak lower semicontinuity)
and `WeakTendsto.tendsto_of_limsup_norm_le_aux` (Radon–Riesz with an asymptotic upper bound,
proved first so that `tendsto_of_tendsto_norm` can use it).
-/

noncomputable section

open Filter Topology Set
open scoped InnerProductSpace ENNReal

namespace NonUniqueEuler.WeakL2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} {l : Filter ι} {u : ι → E} {x : E}

/-- A weak limit of vectors of norm `≤ M` has norm `≤ M`. -/
theorem WeakTendsto.norm_le [l.NeBot] (h : WeakTendsto u l x) {M : ℝ}
    (hM : ∀ᶠ i in l, ‖u i‖ ≤ M) : ‖x‖ ≤ M := by
  -- `0 ≤ M`, since some `u i` has norm `≤ M`
  have hM0 : 0 ≤ M := by
    obtain ⟨i, hi⟩ := hM.exists
    exact (norm_nonneg _).trans hi
  -- `‖x‖² = lim ⟪u i, x⟫ ≤ M ‖x‖`
  have hle : ‖x‖ * ‖x‖ ≤ M * ‖x‖ := by
    have hlim := h x
    rw [real_inner_self_eq_norm_mul_norm] at hlim
    refine le_of_tendsto hlim ?_
    filter_upwards [hM] with i hi
    exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hi (norm_nonneg _))
  rcases (norm_nonneg x).eq_or_lt with h0 | hpos
  · rw [← h0]; exact hM0
  · exact le_of_mul_le_mul_right hle hpos

/-- Real-valued form of the weak lower semicontinuity: if `r < ‖x‖` then eventually
`r < ‖u i‖`. -/
private theorem WeakTendsto.eventually_lt_norm (h : WeakTendsto u l x) {r : ℝ}
    (hr : r < ‖x‖) : ∀ᶠ i in l, r < ‖u i‖ := by
  rcases lt_or_ge r 0 with hr0 | hr0
  · exact Eventually.of_forall fun i => hr0.trans_le (norm_nonneg _)
  have hx : 0 < ‖x‖ := hr0.trans_lt hr
  have hlt : r * ‖x‖ < ‖x‖ * ‖x‖ := mul_lt_mul_of_pos_right hr hx
  have hlim := h x
  rw [real_inner_self_eq_norm_mul_norm] at hlim
  filter_upwards [hlim.eventually (lt_mem_nhds hlt)] with i hi
  exact lt_of_mul_lt_mul_right (hi.trans_le (real_inner_le_norm _ _)) (norm_nonneg _)

/-- **Weak lower semicontinuity of the norm** (in `ℝ≥0∞`, so that no boundedness hypothesis is
needed). -/
theorem WeakTendsto.enorm_le_liminf (h : WeakTendsto u l x) :
    ‖x‖ₑ ≤ liminf (fun i => ‖u i‖ₑ) l := by
  refine le_of_forall_lt_imp_le_of_dense fun a ha => ?_
  have ha_top : a ≠ ∞ := ne_top_of_lt ha
  have hr : a.toReal < ‖x‖ := by
    rw [← ofReal_norm] at ha
    exact (ENNReal.lt_ofReal_iff_toReal_lt ha_top).mp ha
  refine le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [h.eventually_lt_norm hr] with i hi
  rw [← ofReal_norm, ← ENNReal.ofReal_toReal ha_top]
  exact ENNReal.ofReal_le_ofReal hi.le

/-- Weakly convergent sequences in a Hilbert space are bounded (uniform boundedness). -/
theorem WeakTendsto.exists_norm_le [CompleteSpace E] {u : ℕ → E}
    (h : WeakTendsto u atTop x) : ∃ M : ℝ, ∀ n, ‖u n‖ ≤ M := by
  have hb : ∀ y : E, ∃ C, ∀ n, ‖innerSL ℝ (u n) y‖ ≤ C := by
    intro y
    have hy : Tendsto (fun n => ⟪u n, y⟫_ℝ) atTop (𝓝 ⟪x, y⟫_ℝ) := h y
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
      (Metric.isBounded_range_of_tendsto _ hy)
    exact ⟨C, fun n => by rw [innerSL_apply_apply]; exact hC _ (mem_range_self n)⟩
  obtain ⟨C, hC⟩ := banach_steinhaus hb
  exact ⟨C, fun n => by rw [← innerSL_apply_norm (𝕜 := ℝ)]; exact hC n⟩

/-- Radon–Riesz with an asymptotic upper bound on the norms; proved before
`tendsto_of_tendsto_norm`, which is a special case. -/
private theorem WeakTendsto.tendsto_of_limsup_norm_le_aux (h : WeakTendsto u l x)
    (hn : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ‖u i‖ ≤ ‖x‖ + ε) : Tendsto u l (𝓝 x) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  set A : ℝ := ‖x‖ with hA
  have hA0 : 0 ≤ A := norm_nonneg x
  -- target: `‖u i - x‖² < δ²`
  set η : ℝ := δ ^ 2 with hη
  have hη0 : 0 < η := by positivity
  -- choose `ε` with `2 ε A + ε² ≤ η / 2`
  set ε : ℝ := min 1 (η / (4 * (A + 1))) with hε
  have hε0 : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hε2 : ε ≤ η / (4 * (A + 1)) := min_le_right _ _
  have hεη : 2 * ε * A + ε ^ 2 ≤ η / 2 := by
    have h1 : ε ^ 2 ≤ ε := by nlinarith
    have h2 : ε * (4 * (A + 1)) ≤ η := by
      rwa [le_div_iff₀ (by positivity)] at hε2
    nlinarith
  -- eventually `⟪u i, x⟫ > A² - η / 4`
  have hlim := h x
  rw [real_inner_self_eq_norm_mul_norm] at hlim
  have hev : ∀ᶠ i in l, A * A - η / 4 < ⟪u i, x⟫_ℝ :=
    hlim.eventually (lt_mem_nhds (by linarith))
  filter_upwards [hev, hn ε hε0] with i hi hni
  rw [dist_eq_norm]
  have hsq : ‖u i - x‖ ^ 2 < δ ^ 2 := by
    rw [norm_sub_sq_real]
    have hu2 : ‖u i‖ ^ 2 ≤ (A + ε) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hni 2
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 hδ.le hsq

/-- **Radon–Riesz at `p = 2`** (`lem:RR`): weak convergence plus convergence of the norms gives
strong convergence. -/
theorem WeakTendsto.tendsto_of_tendsto_norm (h : WeakTendsto u l x)
    (hn : Tendsto (fun i => ‖u i‖) l (𝓝 ‖x‖)) : Tendsto u l (𝓝 x) :=
  h.tendsto_of_limsup_norm_le_aux fun _ hε =>
    hn.eventually (eventually_le_nhds (lt_add_of_pos_right _ hε))

/-- Radon–Riesz with an asymptotic upper bound on the norms (`limsup ‖u i‖ ≤ ‖x‖`). -/
theorem WeakTendsto.tendsto_of_limsup_norm_le (h : WeakTendsto u l x)
    (hn : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ‖u i‖ ≤ ‖x‖ + ε) : Tendsto u l (𝓝 x) :=
  h.tendsto_of_limsup_norm_le_aux hn

/-- Weak times strong convergence: `⟪u i, v i⟫ → ⟪x, y⟫` if `u i ⇀ x` (bounded) and
`v i → y`. -/
theorem WeakTendsto.inner_tendsto {v : ι → E} {y : E} (h : WeakTendsto u l x)
    (hv : Tendsto v l (𝓝 y)) {M : ℝ} (hM : ∀ᶠ i in l, ‖u i‖ ≤ M) :
    Tendsto (fun i => ⟪u i, v i⟫_ℝ) l (𝓝 ⟪x, y⟫_ℝ) := by
  -- `⟪u i, v i⟫ = ⟪u i, v i - y⟫ + ⟪u i, y⟫`
  have hsplit : (fun i => ⟪u i, v i⟫_ℝ) =
      fun i => ⟪u i, v i - y⟫_ℝ + ⟪u i, y⟫_ℝ := by
    funext i
    rw [inner_sub_right, sub_add_cancel]
  -- the first term tends to `0`: `|⟪u i, v i - y⟫| ≤ M ‖v i - y‖`
  have hdist : Tendsto (fun i => ‖v i - y‖) l (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero).mp hv
  have h1 : Tendsto (fun i => ⟪u i, v i - y⟫_ℝ) l (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using hdist.const_mul M)
    filter_upwards [hM] with i hi
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hi (norm_nonneg _))
  rw [hsplit]
  simpa using h1.add (h y)

/-- Weak convergence is convergence against every continuous linear functional
(Riesz representation). -/
theorem weakTendsto_iff_forall_dual [CompleteSpace E] :
    WeakTendsto u l x ↔ ∀ f : E →L[ℝ] ℝ, Tendsto (fun i => f (u i)) l (𝓝 (f x)) := by
  constructor
  · intro h f
    set y : E := (InnerProductSpace.toDual ℝ E).symm f
    have hf : ∀ z, f z = ⟪z, y⟫_ℝ := fun z => by
      rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
    simp only [hf]
    exact h y
  · intro h y
    have := h (innerSL ℝ y)
    simp only [innerSL_apply_apply] at this
    simpa only [real_inner_comm y] using this

/-- Bounded linear operators preserve weak convergence. -/
theorem WeakTendsto.map [CompleteSpace E] {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (T : E →L[ℝ] F) (h : WeakTendsto u l x) :
    WeakTendsto (fun i => T (u i)) l (T x) := by
  intro y
  have := (weakTendsto_iff_forall_dual.mp h) ((innerSL ℝ y).comp T)
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply] at this
  simpa only [real_inner_comm y] using this

end NonUniqueEuler.WeakL2
