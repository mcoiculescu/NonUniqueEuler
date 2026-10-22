import NonUniqueEuler.Defs.Infra.JointRep
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Proof of (I-JOINT): measurability of weakly continuous and of sliced paths (Pettis)

Proof of `NonUniqueEuler/I/Infra/JointRep/Measurable.lean` (same declarations, same statements).

* `stronglyMeasurable_of_forall_inner` (Pettis): `‖x‖ = ⨆ⱼ ⟪x, zⱼ⟫ / ‖zⱼ‖` for a dense sequence
  `z` (`MeasurableAux.norm_eq_iSup_inner_div`), so `t ↦ dist (u t) d` is measurable; every open
  set is a countable union of balls centred at the `zₖ` with radii `1/(n+1)`
  (`MeasurableAux.eq_iUnion_ball_of_isOpen`); hence `u` is Borel measurable, and strongly
  measurable since `E` is second countable.
* Weakly continuous paths have separable range on `s` (`MeasurableAux.isSeparable_image`).
  No completeness of `E` is assumed, so we argue in the completion `Ê` of `E`: on the piece
  `s_N = {t ∈ s | ‖u t‖ ≤ N}` the path is bounded, and for a countable dense `D ⊆ s_N` every
  `u t` (`t ∈ s_N`) lies in `(span u(D))ᗮᗮ = closure (span u(D))` inside `Ê` (approximate a
  vector of `(span u(D))ᗮ` by a vector of `E`; the bound `‖u t‖ ≤ N` controls the error). Then
  `u '' s = ⋃_N u '' s_N` is separable. Pettis in the separable subspace `span (u '' s)` gives the
  indicator statement.
* `aestronglyMeasurable_toPath`: replace `ω` by a strongly measurable version `F` of
  `uncurry ω` on the slab; a.e. slice agrees (`Measure.ae_ae_of_ae_prod`), so `toPath` agrees
  a.e.; for `F`, `⟪toPath F t, y⟫ = 1_G(t) ∫ y x F(t,x) dx` with `G = {t | F(t,·) ∈ L²}`
  measurable (`measurableSet_integrable` for `F²`), and the integral is strongly measurable
  (`StronglyMeasurable.integral_prod_right'`); conclude with Pettis in `L²(ℂ)`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped InnerProductSpace ENNReal

namespace NonUniqueEuler.JointRep

open NonUniqueEuler.WeakL2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace MeasurableAux

/-- The norm is the supremum of the normalized inner products against a dense sequence. -/
theorem norm_eq_iSup_inner_div {z : ℕ → E} (hz : DenseRange z) (x : E) :
    ‖x‖ = ⨆ j, ⟪x, z j⟫_ℝ / ‖z j‖ := by
  have hle : ∀ j, ⟪x, z j⟫_ℝ / ‖z j‖ ≤ ‖x‖ := by
    intro j
    rcases eq_or_ne (z j) 0 with h | h
    · simp [h]
    · rw [div_le_iff₀ (norm_pos_iff.2 h)]
      exact real_inner_le_norm _ _
  have hbdd : BddAbove (range fun j => ⟪x, z j⟫_ℝ / ‖z j‖) :=
    ⟨‖x‖, by rintro _ ⟨j, rfl⟩; exact hle j⟩
  refine le_antisymm ?_ (ciSup_le hle)
  rcases eq_or_ne x 0 with hx | hx
  · subst hx
    simp
  have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set δ := min (ε / 2) (‖x‖ / 2) with hδ
  have hδpos : 0 < δ := lt_min (half_pos hε) (half_pos hx0)
  obtain ⟨j, hj⟩ := hz.exists_dist_lt x hδpos
  rw [dist_eq_norm] at hj
  have hδ1 : δ ≤ ε / 2 := min_le_left _ _
  have hδ2 : δ ≤ ‖x‖ / 2 := min_le_right _ _
  have htri : ‖x‖ ≤ ‖z j‖ + ‖x - z j‖ := by
    have := norm_add_le (z j) (x - z j)
    rwa [add_sub_cancel] at this
  have hw : 0 < ‖z j‖ := by linarith
  have hinner : ‖z j‖ ^ 2 - ‖x - z j‖ * ‖z j‖ ≤ ⟪x, z j⟫_ℝ := by
    have h1 : ⟪x, z j⟫_ℝ = ⟪z j, z j⟫_ℝ + ⟪x - z j, z j⟫_ℝ := by
      rw [← inner_add_left, add_sub_cancel]
    have h2 : -(‖x - z j‖ * ‖z j‖) ≤ ⟪x - z j, z j⟫_ℝ := by
      have := abs_real_inner_le_norm (x - z j) (z j)
      exact (abs_le.1 this).1
    rw [h1, real_inner_self_eq_norm_sq]
    linarith
  have hterm : ‖x‖ - ε ≤ ⟪x, z j⟫_ℝ / ‖z j‖ := by
    rw [le_div_iff₀ hw]
    nlinarith
  have := le_ciSup hbdd j
  linarith

/-- In a separable pseudo-metric space with a dense sequence `z`, every open set is the union of
the balls `B(z k, 1/(n+1))` it contains. -/
theorem eq_iUnion_ball_of_isOpen {X : Type*} [PseudoMetricSpace X] {z : ℕ → X}
    (hz : DenseRange z) {U : Set X} (hU : IsOpen U) :
    U = ⋃ k : ℕ, ⋃ n : ℕ, ⋃ (_ : Metric.ball (z k) (1 / ((n : ℝ) + 1)) ⊆ U),
      Metric.ball (z k) (1 / ((n : ℝ) + 1)) := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hε)
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨k, hk⟩ := hz.exists_dist_lt x hpos
    simp only [mem_iUnion]
    refine ⟨k, n, ?_, ?_⟩
    · intro y hy
      apply hball
      rw [Metric.mem_ball] at hy ⊢
      calc dist y x ≤ dist y (z k) + dist (z k) x := dist_triangle _ _ _
        _ < 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) := add_lt_add hy (by rwa [dist_comm])
        _ < ε := by linarith
    · rw [Metric.mem_ball]
      exact hk
  · simp only [iUnion_subset_iff]
    exact fun _ _ h => h

end MeasurableAux

open MeasurableAux in
/-- **Pettis' theorem** (separable real Hilbert space): a path whose inner products with every
vector are measurable is strongly measurable. -/
theorem stronglyMeasurable_of_forall_inner [TopologicalSpace.SeparableSpace E] {τ : Type*}
    [MeasurableSpace τ] {u : τ → E} (h : ∀ y : E, Measurable fun t => ⟪u t, y⟫_ℝ) :
    StronglyMeasurable u := by
  borelize E
  obtain ⟨z, hz⟩ := TopologicalSpace.exists_dense_seq E
  have hdist : ∀ d : E, Measurable fun t => dist (u t) d := by
    intro d
    have : (fun t => dist (u t) d) = fun t => ⨆ j, (⟪u t, z j⟫_ℝ - ⟪d, z j⟫_ℝ) / ‖z j‖ := by
      funext t
      rw [dist_eq_norm, norm_eq_iSup_inner_div hz]
      simp_rw [inner_sub_left]
    rw [this]
    exact Measurable.iSup fun j => ((h (z j)).sub_const _).div_const _
  have hmeas : Measurable u := by
    refine measurable_of_isOpen fun U hU => ?_
    rw [eq_iUnion_ball_of_isOpen hz hU]
    simp only [preimage_iUnion]
    refine MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun n =>
      MeasurableSet.iUnion fun _ => ?_
    exact measurableSet_lt (hdist _) measurable_const
  exact hmeas.stronglyMeasurable

namespace MeasurableAux

/-- On a set of times where it is bounded, a weakly continuous path has separable range. The
argument takes place in the completion of `E` (no completeness of `E` is assumed). -/
theorem isSeparable_image_of_norm_le {u : ℝ → E} {s : Set ℝ} (hu : WeakContinuousOn u s)
    {N : ℝ} (hN : ∀ t ∈ s, ‖u t‖ ≤ N) : TopologicalSpace.IsSeparable (u '' s) := by
  obtain ⟨D, hDs, hDc, hsD⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace s).exists_countable_dense_subset
  let ι : E → UniformSpace.Completion E := (↑)
  let K₀ : Submodule ℝ (UniformSpace.Completion E) := Submodule.span ℝ (ι '' (u '' D))
  have key : ∀ t ∈ s, ι (u t) ∈ K₀ᗮᗮ := by
    intro t ht
    rw [Submodule.mem_orthogonal']
    intro w hw
    have hD : ∀ t' ∈ D, ⟪ι (u t'), w⟫_ℝ = 0 := fun t' ht' =>
      (Submodule.mem_orthogonal K₀ w).1 hw _
        (Submodule.subset_span ⟨u t', ⟨t', ht', rfl⟩, rfl⟩)
    have hbound : ∀ ε > 0, |⟪ι (u t), w⟫_ℝ| ≤ 2 * N * ε := by
      intro ε hε
      obtain ⟨y, hy⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt w hε
      have hwy : ‖ι y - w‖ ≤ ε := by
        rw [← dist_eq_norm, dist_comm]
        exact hy.le
      have hD' : ∀ t' ∈ D, |⟪u t', y⟫_ℝ| ≤ N * ε := by
        intro t' ht'
        have h1 : ⟪u t', y⟫_ℝ = ⟪ι (u t'), ι y - w⟫_ℝ := by
          rw [inner_sub_right, hD t' ht', sub_zero, UniformSpace.Completion.inner_coe]
        rw [h1]
        refine (abs_real_inner_le_norm _ _).trans ?_
        rw [UniformSpace.Completion.norm_coe]
        exact mul_le_mul (hN t' (hDs ht')) hwy (norm_nonneg _)
          ((norm_nonneg _).trans (hN t' (hDs ht')))
      have ht1 : |⟪u t, y⟫_ℝ| ≤ N * ε := by
        have hc : ContinuousWithinAt (fun t => |⟪u t, y⟫_ℝ|) D t :=
          (continuous_abs.continuousAt.comp_continuousWithinAt (hu y t ht)).mono hDs
        exact ContinuousWithinAt.closure_le (hsD ht) hc continuousWithinAt_const hD'
      have h2 : ⟪ι (u t), w⟫_ℝ = ⟪u t, y⟫_ℝ - ⟪ι (u t), ι y - w⟫_ℝ := by
        rw [inner_sub_right, UniformSpace.Completion.inner_coe]
        ring
      have h3 : |⟪ι (u t), ι y - w⟫_ℝ| ≤ N * ε := by
        refine (abs_real_inner_le_norm _ _).trans ?_
        rw [UniformSpace.Completion.norm_coe]
        exact mul_le_mul (hN t ht) hwy (norm_nonneg _) ((norm_nonneg _).trans (hN t ht))
      rw [h2]
      calc |⟪u t, y⟫_ℝ - ⟪ι (u t), ι y - w⟫_ℝ|
          ≤ |⟪u t, y⟫_ℝ| + |⟪ι (u t), ι y - w⟫_ℝ| := abs_sub _ _
        _ ≤ N * ε + N * ε := add_le_add ht1 h3
        _ = 2 * N * ε := by ring
    have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN t ht)
    have habs : |⟪ι (u t), w⟫_ℝ| ≤ 0 := by
      refine le_of_forall_pos_le_add fun δ hδ => ?_
      have hpos : 0 < δ / (2 * N + 1) := by positivity
      refine (hbound _ hpos).trans ?_
      rw [zero_add, ← mul_div_assoc, div_le_iff₀ (by positivity)]
      nlinarith
    exact abs_nonpos_iff.1 habs
  have hsep : TopologicalSpace.IsSeparable
      ((K₀ᗮᗮ : Submodule ℝ (UniformSpace.Completion E)) : Set (UniformSpace.Completion E)) := by
    rw [Submodule.orthogonal_orthogonal_eq_closure, Submodule.topologicalClosure_coe]
    exact (((hDc.image u).image ι).isSeparable.span).closure
  have hsub : u '' s ⊆ ι ⁻¹' ((K₀ᗮᗮ : Submodule ℝ (UniformSpace.Completion E)) :
      Set (UniformSpace.Completion E)) := by
    rintro _ ⟨t, ht, rfl⟩
    exact key t ht
  exact ((UniformSpace.Completion.coe_isometry.isEmbedding).isSeparable_preimage hsep).mono hsub

/-- A weakly continuous path has separable range on its set of times. -/
theorem isSeparable_image {u : ℝ → E} {s : Set ℝ} (hu : WeakContinuousOn u s) :
    TopologicalSpace.IsSeparable (u '' s) := by
  have hs : s = ⋃ N : ℕ, {t | t ∈ s ∧ ‖u t‖ ≤ N} := by
    ext t
    simp only [mem_iUnion]
    constructor
    · intro ht
      obtain ⟨N, hN⟩ := exists_nat_ge ‖u t‖
      exact ⟨N, ht, hN⟩
    · rintro ⟨N, ht, -⟩
      exact ht
  rw [hs, image_iUnion]
  exact TopologicalSpace.IsSeparable.iUnion fun N =>
    isSeparable_image_of_norm_le (hu.mono fun t ht => ht.1) fun t ht => ht.2

end MeasurableAux

open MeasurableAux in
/-- A weakly continuous path on a measurable set of times, extended by zero, is strongly
measurable. -/
theorem _root_.NonUniqueEuler.WeakL2.WeakContinuousOn.stronglyMeasurable_indicator
    {u : ℝ → E} {s : Set ℝ} (hs : MeasurableSet s) (hu : WeakContinuousOn u s) :
    StronglyMeasurable (s.indicator u) := by
  classical
  let Z : Submodule ℝ E := Submodule.span ℝ (u '' s)
  have hZsep : TopologicalSpace.IsSeparable (Z : Set E) := (isSeparable_image hu).span
  have : TopologicalSpace.SeparableSpace Z := hZsep.separableSpace
  let v : ℝ → Z := fun t => if h : t ∈ s then ⟨u t, Submodule.subset_span ⟨t, h, rfl⟩⟩ else 0
  have hv : StronglyMeasurable v := by
    refine stronglyMeasurable_of_forall_inner fun y => ?_
    have : (fun t => ⟪v t, y⟫_ℝ) = s.piecewise (fun t => ⟪u t, (y : E)⟫_ℝ) (fun _ => 0) := by
      funext t
      by_cases ht : t ∈ s <;> simp [v, ht, Submodule.coe_inner]
    rw [this]
    exact (hu (y : E)).measurable_piecewise continuousOn_const hs
  have : s.indicator u = (fun z : Z => (z : E)) ∘ v := by
    funext t
    by_cases ht : t ∈ s <;> simp [v, ht]
  rw [this]
  exact continuous_subtype_val.comp_stronglyMeasurable hv

/-- A weakly continuous path on a measurable set of times is a.e. strongly measurable for the
restricted Lebesgue measure. -/
theorem _root_.NonUniqueEuler.WeakL2.WeakContinuousOn.aestronglyMeasurable
    {u : ℝ → E} {s : Set ℝ} (hs : MeasurableSet s) (hu : WeakContinuousOn u s) :
    AEStronglyMeasurable u (volume.restrict s) :=
  (hu.stronglyMeasurable_indicator hs).aestronglyMeasurable.congr (indicator_ae_eq_restrict hs)

namespace MeasurableAux

/-- `toPath` only depends on the a.e. class of the slice. -/
theorem toPath_congr_ae {ω ω' : ℝ → ℂ → ℝ} {t : ℝ} (h : ω t =ᵐ[volume] ω' t) :
    (toPath ω t : Lp ℝ 2 (volume : Measure ℂ)) = toPath ω' t := by
  by_cases hm : MemLp (ω t) 2 (volume : Measure ℂ)
  · have hm' : MemLp (ω' t) 2 (volume : Measure ℂ) := hm.ae_eq h
    rw [toPath_of_memLp hm, toPath_of_memLp hm']
    exact (MemLp.toLp_eq_toLp_iff _ _).2 h
  · have hm' : ¬ MemLp (ω' t) 2 (volume : Measure ℂ) := fun h' => hm (h'.ae_eq h.symm)
    rw [toPath, toPath, dite_eq_right hm, dite_eq_right hm']

/-- The path of slices of a strongly measurable function on `ℝ × ℂ` is strongly measurable into
`L²(ℂ)`. -/
theorem stronglyMeasurable_toPath {F : ℝ × ℂ → ℝ} (hF : StronglyMeasurable F) :
    StronglyMeasurable
      (fun t => (toPath (fun t x => F (t, x)) t : Lp ℝ 2 (volume : Measure ℂ))) := by
  have := separableSpace_L2_plane
  refine stronglyMeasurable_of_forall_inner fun y => ?_
  let G : Set ℝ := {t | MemLp (fun x => F (t, x)) 2 (volume : Measure ℂ)}
  have hslice : ∀ t, StronglyMeasurable fun x => F (t, x) := fun t =>
    hF.comp_measurable measurable_prodMk_left
  have hG : MeasurableSet G := by
    have hG' : G = {t | Integrable (fun x => F (t, x) ^ 2) (volume : Measure ℂ)} := by
      ext t
      exact memLp_two_iff_integrable_sq (hslice t).aestronglyMeasurable
    rw [hG']
    exact measurableSet_integrable (f := fun t x => F (t, x) ^ 2) (hF.pow 2)
  have hint : StronglyMeasurable fun t => ∫ x, y x * F (t, x) := by
    have hprod : StronglyMeasurable fun p : ℝ × ℂ => y p.2 * F p :=
      ((Lp.stronglyMeasurable y).comp_measurable measurable_snd).mul hF
    exact hprod.integral_prod_right'
  have heq : (fun t => ⟪(toPath (fun t x => F (t, x)) t : Lp ℝ 2 (volume : Measure ℂ)), y⟫_ℝ) =
      G.indicator fun t => ∫ x, y x * F (t, x) := by
    funext t
    by_cases ht : t ∈ G
    · rw [indicator_of_mem ht, toPath_of_memLp (ω := fun t x => F (t, x)) ht, real_inner_comm,
        inner_toLp_eq_integral _ ht]
    · have ht' : ¬ MemLp (fun x => F (t, x)) 2 (volume : Measure ℂ) := ht
      rw [indicator_of_notMem ht, toPath, dite_eq_right ht', inner_zero_left]
  rw [heq]
  exact hint.measurable.indicator hG

end MeasurableAux

open MeasurableAux in
/-- The path of time slices of a function that is a.e. strongly measurable on the slab
`(0, T) × ℂ` is a.e. strongly measurable into `L²(ℂ)`. -/
theorem aestronglyMeasurable_toPath {ω : ℝ → ℂ → ℝ} {T : ℝ}
    (hω : AEStronglyMeasurable (Function.uncurry ω) (volume.restrict (slab T))) :
    AEStronglyMeasurable (fun t => (toPath ω t : Lp ℝ 2 (volume : Measure ℂ)))
      (volume.restrict (Ioo (0 : ℝ) T)) := by
  rw [volume_restrict_slab] at hω
  have hae : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)),
      ω t =ᵐ[(volume : Measure ℂ)] fun x => hω.mk _ (t, x) :=
    Measure.ae_ae_of_ae_prod hω.ae_eq_mk
  refine ⟨fun t => toPath (fun t x => hω.mk _ (t, x)) t,
    stronglyMeasurable_toPath hω.stronglyMeasurable_mk, ?_⟩
  filter_upwards [hae] with t ht
  exact toPath_congr_ae ht

end NonUniqueEuler.JointRep
