import NonUniqueEuler.Defs.Infra.WeakL2
import NonUniqueEuler.I.Infra.WeakL2.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Proof of the interface (I-WEAKL2): a countable test family in `C_c^∞(ℂ)`

Proof of `NonUniqueEuler/I/Infra/WeakL2/TestFamily.lean` (the family `𝓕` of the proof of
`lem:weak-cont`, `03_compactness.tex:146-153`).

* `exists_isTestFamily`: for each rational `q`, the set `suppSet q` of `C_c^∞` functions with
  `tsupport ⊆ B_q` is mapped by the `C¹` jet `ψ ↦ (x ↦ (ψ x, Dψ x))` into the separable metric
  space `C(closedBall 0 q, ℝ × (ℂ →L[ℝ] ℝ))` (Mathlib's `ContinuousMap.instSeparableSpace`).
  A countable subset of the image that is dense in the image (`IsSeparable.
  exists_countable_dense_subset`) is pulled back by choice; outside the closed ball both the
  values and the derivatives vanish, so closeness of the jets on the ball is closeness
  everywhere. The union over `q ∈ ℚ` is enumerated by `Set.Countable.exists_eq_range`. For a
  real `R`, a compact `tsupport ψ ⊆ B_R` lies in `B_q` for a rational `q < R`
  (`exists_lt_subset_ball`, `exists_rat_btwn`).
* The other statements follow as in the docstring of the interface file.
-/

noncomputable section

open Filter Topology Set MeasureTheory
open scoped InnerProductSpace ENNReal ContDiff

namespace NonUniqueEuler.WeakL2

namespace TestFamilyAux

/-- The `C_c^∞` functions on the plane with topological support in `B_r`. -/
def suppSet (r : ℝ) : Set (ℂ → ℝ) :=
  {ψ | ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ Metric.ball 0 r}

/-- The `C¹` jet `x ↦ (ψ x, Dψ x)` of a member of `suppSet r`, on the closed ball. -/
def jet (r : ℝ) (ψ : suppSet r) : C(Metric.closedBall (0 : ℂ) r, ℝ × (ℂ →L[ℝ] ℝ)) :=
  ⟨fun x => (ψ.1 x, fderiv ℝ ψ.1 x),
    ((ψ.2.1.continuous.prodMk (ψ.2.1.continuous_fderiv (by simp))).comp
      continuous_subtype_val)⟩

/-- Outside the closed ball, members of `suppSet r` and their derivatives vanish. -/
theorem eq_zero_of_not_mem {r : ℝ} {ψ : ℂ → ℝ} (hψ : ψ ∈ suppSet r) {x : ℂ}
    (hx : x ∉ Metric.closedBall (0 : ℂ) r) : ψ x = 0 ∧ fderiv ℝ ψ x = 0 := by
  have hx' : x ∉ tsupport ψ := fun h => hx (Metric.ball_subset_closedBall (hψ.2.2 h))
  exact ⟨image_eq_zero_of_notMem_tsupport hx', fderiv_of_notMem_tsupport ℝ hx'⟩

/-- **Separability step.** Each `suppSet r` has a countable subset which is dense for the `C¹`
norm. -/
theorem exists_countable_dense (r : ℝ) :
    ∃ D : Set (ℂ → ℝ), D.Countable ∧ D ⊆ suppSet r ∧
      ∀ ψ ∈ suppSet r, ∀ ε : ℝ, 0 < ε → ∃ f ∈ D,
        (∀ x, |f x - ψ x| ≤ ε) ∧ ∀ x, ‖fderiv ℝ f x - fderiv ℝ ψ x‖ ≤ ε := by
  obtain ⟨t, hts, htc, hst⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace (range (jet r))).exists_countable_dense_subset
  have hpre : ∀ y ∈ t, ∃ ψ : suppSet r, jet r ψ = y := fun y hy => hts hy
  choose g hg using hpre
  have := htc.to_subtype
  refine ⟨range (fun y : t => (g y.1 y.2).1), countable_range _, ?_, ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact (g y.1 y.2).2
  · intro ψ hψ ε hε
    have hmem : jet r ⟨ψ, hψ⟩ ∈ closure t := hst (mem_range_self _)
    obtain ⟨y, hyt, hdist⟩ := (Metric.mem_closure_iff (α := C(Metric.closedBall (0 : ℂ) r, ℝ × (ℂ →L[ℝ] ℝ)))
      (s := t) (a := jet r ⟨ψ, hψ⟩)).mp hmem ε hε
    set f := g y hyt with hf_def
    have hjet : jet r f = y := hg y hyt
    refine ⟨f.1, ⟨⟨y, hyt⟩, rfl⟩, ?_⟩
    have key : ∀ x, |f.1 x - ψ x| ≤ ε ∧ ‖fderiv ℝ f.1 x - fderiv ℝ ψ x‖ ≤ ε := by
      intro x
      by_cases hx : x ∈ Metric.closedBall (0 : ℂ) r
      · have h1 := ContinuousMap.dist_apply_le_dist (f := jet r ⟨ψ, hψ⟩) (g := y) ⟨x, hx⟩
        rw [← hjet, Prod.dist_eq] at h1
        rw [← hjet] at hdist
        have h1' := h1.trans hdist.le
        simp only [jet, ContinuousMap.coe_mk] at h1'
        constructor
        · have := (le_max_left _ _).trans h1'
          rwa [Real.dist_eq, abs_sub_comm] at this
        · have := (le_max_right _ _).trans h1'
          rwa [dist_eq_norm, norm_sub_rev] at this
      · obtain ⟨h1, h2⟩ := eq_zero_of_not_mem f.2 hx
        obtain ⟨h3, h4⟩ := eq_zero_of_not_mem hψ hx
        rw [h1, h2, h3, h4]
        simp [hε.le]
    exact ⟨fun x => (key x).1, fun x => (key x).2⟩

/-- Every compact support inside an open ball `B_R` lies in a ball `B_q`, `q ∈ ℚ`, `q < R`. -/
theorem exists_rat_ball {R : ℝ} {ψ : ℂ → ℝ} (hψR : tsupport ψ ⊆ Metric.ball 0 R) :
    ∃ q : ℚ, (q : ℝ) < R ∧ tsupport ψ ⊆ Metric.ball 0 q := by
  obtain ⟨r', hr', hsub⟩ := exists_lt_subset_ball (isClosed_tsupport ψ) hψR
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hr'
  exact ⟨q, hq2, hsub.trans (Metric.ball_subset_ball hq1.le)⟩

end TestFamilyAux

open TestFamilyAux in
/-- A test family exists. -/
theorem exists_isTestFamily : ∃ F : ℕ → ℂ → ℝ, IsTestFamily F := by
  choose D hDc hDs hDd using fun q : ℚ => exists_countable_dense (q : ℝ)
  set G : Set (ℂ → ℝ) := ⋃ q : ℚ, D q with hG
  have hGc : G.Countable := countable_iUnion hDc
  have hGs : ∀ f ∈ G, ∃ q : ℚ, f ∈ suppSet q := by
    intro f hf
    obtain ⟨q, hq⟩ := mem_iUnion.mp hf
    exact ⟨q, hDs q hq⟩
  have h0 : (0 : ℂ → ℝ) ∈ suppSet (0 : ℚ) :=
    ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
  have hGne : G.Nonempty := by
    obtain ⟨f, hf, -⟩ := hDd 0 0 h0 1 one_pos
    exact ⟨f, mem_iUnion.mpr ⟨0, hf⟩⟩
  obtain ⟨F, hFG⟩ := hGc.exists_eq_range hGne
  have hFs : ∀ i, ∃ q : ℚ, F i ∈ suppSet q := fun i => hGs _ (hFG ▸ mem_range_self i)
  refine ⟨F, fun i => ?_, fun i => ?_, ?_⟩
  · obtain ⟨q, hq⟩ := hFs i
    exact hq.1
  · obtain ⟨q, hq⟩ := hFs i
    exact hq.2.1
  · intro R ψ hψ hψs hψR ε hε
    obtain ⟨q, hqR, hψq⟩ := exists_rat_ball hψR
    obtain ⟨f, hfD, hf1, hf2⟩ := hDd q ψ ⟨hψ, hψs, hψq⟩ ε hε
    have hfG : f ∈ range F := hFG ▸ mem_iUnion.mpr ⟨q, hfD⟩
    obtain ⟨i, rfl⟩ := hfG
    exact ⟨i, (hDs q hfD).2.2.trans (Metric.ball_subset_ball hqR.le), hf1, hf2⟩

namespace IsTestFamily

variable {F : ℕ → ℂ → ℝ}

/-- `C¹` approximation by a sequence from the family, with supports in the same ball. -/
theorem exists_seq_tendsto_C1 (hF : IsTestFamily F) {R : ℝ} {ψ : ℂ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψs : HasCompactSupport ψ) (hψR : tsupport ψ ⊆ Metric.ball 0 R) :
    ∃ i : ℕ → ℕ, (∀ n, tsupport (F (i n)) ⊆ Metric.ball 0 R) ∧
      TendstoUniformly (fun n => F (i n)) ψ atTop ∧
      TendstoUniformly (fun n => fderiv ℝ (F (i n))) (fderiv ℝ ψ) atTop := by
  choose i hi1 hi2 hi3 using fun n : ℕ =>
    hF.dense_C1 R ψ hψ hψs hψR (1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat
  refine ⟨i, hi1, ?_, ?_⟩
  · rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hε)] with n hn x
    rw [Real.dist_eq, abs_sub_comm]
    exact (hi2 n x).trans_lt hn
  · rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hε)] with n hn x
    rw [dist_eq_norm, norm_sub_rev]
    exact (hi3 n x).trans_lt hn

/-- The family is dense in `L²(ℂ)`. -/
theorem dense_L2 (hF : IsTestFamily F) {g : ℂ → ℝ} (hg : MemLp g 2 volume) {ε : ℝ}
    (hε : 0 < ε) : ∃ i, eLpNorm (g - F i) 2 volume < ENNReal.ofReal ε := by
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨ψ, hψc, hψd, hgψ⟩ :=
    hg.exist_eLpNorm_sub_le (p := 2) (by norm_num) (by norm_num) hε4
  obtain ⟨R, hR⟩ := hψc.isCompact.isBounded.subset_ball (0 : ℂ)
  set B : Set ℂ := Metric.ball (0 : ℂ) R with hB
  set C : ℝ≥0∞ := volume B ^ (1 / (2 : ℝ≥0∞).toReal) with hC
  have hCtop : C ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) measure_ball_lt_top.ne
  set δ : ℝ := ε / 4 / (C.toReal + 1) with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨i, hiR, hi, -⟩ := hF.dense_C1 R ψ hψd hψc hR δ hδpos
  refine ⟨i, ?_⟩
  -- the uniform bound gives the `L²` bound on the ball
  have hpt : ∀ x, ‖(ψ - F i) x‖ ≤ ‖B.indicator (fun _ => δ) x‖ := by
    intro x
    by_cases hx : x ∈ B
    · rw [indicator_of_mem hx, Real.norm_of_nonneg hδpos.le, Pi.sub_apply, Real.norm_eq_abs,
        abs_sub_comm]
      exact hi x
    · have h1 : ψ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hR h)
      have h2 : F i x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hiR h)
      simp [h1, h2]
  have hψF : eLpNorm (ψ - F i) 2 volume ≤ ENNReal.ofReal (ε / 4) := by
    refine (eLpNorm_mono hpt).trans ((eLpNorm_indicator_const_le δ 2).trans ?_)
    rw [Real.enorm_eq_ofReal hδpos.le, ← hC, ← ENNReal.ofReal_toReal hCtop,
      ← ENNReal.ofReal_mul hδpos.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have hC0 : 0 ≤ C.toReal := ENNReal.toReal_nonneg
    rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hsplit : g - F i = (g - ψ) + (ψ - F i) := by abel
  rw [hsplit]
  calc eLpNorm ((g - ψ) + (ψ - F i)) 2 volume
      ≤ eLpNorm (g - ψ) 2 volume + eLpNorm (ψ - F i) 2 volume :=
        eLpNorm_add_le (hg.1.sub hψd.continuous.aestronglyMeasurable)
          (hψd.continuous.aestronglyMeasurable.sub
            (hF.contDiff i).continuous.aestronglyMeasurable) (by norm_num)
    _ ≤ ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) := add_le_add hgψ hψF
    _ = ENNReal.ofReal (ε / 2) := by
        rw [← ENNReal.ofReal_add hε4.le hε4.le]
        ring_nf
    _ < ENNReal.ofReal ε := by
        rw [ENNReal.ofReal_lt_ofReal_iff hε]
        linarith

/-- The family, as elements of `L²(ℂ)`, has dense range. -/
theorem denseRange_toL2 (hF : IsTestFamily F) : DenseRange hF.toL2 := by
  rw [Metric.denseRange_iff]
  intro x r hr
  obtain ⟨i, hi⟩ := hF.dense_L2 (Lp.memLp x) hr
  refine ⟨i, ?_⟩
  rw [Lp.dist_def]
  have hae : (⇑x - ⇑(hF.toL2 i)) =ᵐ[volume] (⇑x - F i) :=
    (hF.coeFn_toL2 i).mono fun z hz => by simp [hz]
  rw [eLpNorm_congr_ae hae]
  exact ENNReal.toReal_lt_of_lt_ofReal hi

/-- For a bounded family in `L²(ℂ)`, weak convergence can be tested on the test family. -/
theorem weakTendsto_iff (hF : IsTestFamily F) {ι : Type*} {l : Filter ι}
    {u : ι → Lp ℝ 2 (volume : Measure ℂ)} {x : Lp ℝ 2 (volume : Measure ℂ)} {M : ℝ}
    (hu : ∀ᶠ i in l, ‖u i‖ ≤ M) :
    WeakTendsto u l x ↔
      ∀ k, Tendsto (fun i => ∫ z, u i z * F k z) l (𝓝 (∫ z, x z * F k z)) := by
  constructor
  · intro h k
    exact h.integral_mul_tendsto (hF.memLp k 2)
  · intro h
    refine weakTendsto_of_dense hu hF.denseRange_toL2 ?_
    rintro _ ⟨k, rfl⟩
    simp only [hF.inner_toL2]
    exact h k

/-- A bounded family in `L²(ℂ)` whose integrals against every member of the test family
converge has a weak limit, of norm `≤ M`. -/
theorem exists_weakTendsto (hF : IsTestFamily F) {ι : Type*} {l : Filter ι} [l.NeBot]
    {u : ι → Lp ℝ 2 (volume : Measure ℂ)} {M : ℝ} (hu : ∀ᶠ i in l, ‖u i‖ ≤ M)
    (h : ∀ k, ∃ c : ℝ, Tendsto (fun i => ∫ z, u i z * F k z) l (𝓝 c)) :
    ∃ x : Lp ℝ 2 (volume : Measure ℂ), ‖x‖ ≤ M ∧ WeakTendsto u l x := by
  refine exists_weakTendsto_of_dense hu hF.denseRange_toL2 ?_
  rintro _ ⟨k, rfl⟩
  simp only [hF.inner_toL2]
  exact h k

end IsTestFamily

end NonUniqueEuler.WeakL2
