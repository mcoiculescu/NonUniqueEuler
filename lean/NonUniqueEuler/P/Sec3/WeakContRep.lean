import NonUniqueEuler.Defs.Sec3.Paths
import NonUniqueEuler.Defs.Sec3.Solutions
import NonUniqueEuler.I.Sec3.WeakCont
import NonUniqueEuler.I.Sec3.VelocityField
import NonUniqueEuler.I.Infra.WeakL2.Paths
import NonUniqueEuler.I.Infra.JointRep.Slab
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Topology.Order.IsLUB

/-!
# Proof: weak solutions and their weakly continuous representatives (`03_compactness.tex:236-243`)

Proof of `I/Sec3/WeakContRep.lean`.

* `ae_eq_of_isWeakContL2On`: bridge `isWeakContL2On_iff_toPath` and
  `WeakL2.WeakContinuousOn.eqOn_of_ae_eq` for the paths of `L²` classes.
* `IsWeakSolution.congr_ae`, `IsRenormalizedWeakSolution.congr_ae`: for a.e. `t`,
  `ω'(t) = ω(t)` a.e. (`JointRep.ae_ae_of_ae_eq_slab`), hence `v'(t) = v(t)` everywhere
  (`integral_congr_ae` in the Biot–Savart integral); the integrands of the transport identity
  agree a.e. on the slab (`Measure.quasiMeasurePreserving_fst`) and their inner integrals agree
  for a.e. `t` (`Measure.ae_ae_of_ae_prod`).
* `IsWeakSolution.exists_weakContRep`: `lem:weak-cont` (`weakCont`, `u = ω`, `w = v`,
  `u₀ = ω^in`) followed by `congr_ae`.
* `IsWeakSolution.ae_eq_datum_of_isWeakContL2On`: a path weakly continuous into `L²` on the
  compact `[0,T]` is bounded in `L²` (uniform boundedness, Mathlib `banach_steinhaus`), so
  `ω ∈ L^∞(0,T;L²)`; the representative of `exists_weakContRep` has value `ω^in` at `0` and
  agrees with `ω` at every `t ∈ [0,T]` (`ae_eq_of_isWeakContL2On`). (Deviation from the interface
  sketch, which tests `(te)` with `α(t)ψ(x)`; the argument here is shorter.)
* `eLpNorm_le_of_isWeakContL2On`: `WeakL2.WeakContinuousOn.eLpNorm_le_of_ae` through the bridge.
* `IsWeakSolution.bound_of_isWeakContL2On`: the previous item with `p = 1` and `p = q`.
* `IsWeakSolutionUpTo.exists_weakContRep`: an exhausting sequence `τ j ↑ T₀`, representatives
  `W j` on `[0, τ j]`, consistent on overlaps by uniqueness; the glued function
  `ω'(t) = W (ν t) (t)`, `ν t` the least `j` with `t < τ j` (measurable by `Measurable.find`).
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace NonUniqueEuler.Weak

namespace WeakContRepAux

/-- A property holding for a.e. time holds a.e. on the slab. -/
theorem ae_slab_of_ae_time {T : ℝ} {P : ℝ → Prop}
    (h : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)), P t) :
    ∀ᵐ p ∂(volume.restrict (slab T)), P p.1 := by
  rw [JointRep.volume_restrict_slab]
  exact Measure.quasiMeasurePreserving_fst.ae h

/-- A.e. on the slab gives a.e. in space for a.e. time. -/
theorem ae_time_of_ae_slab {T : ℝ} {P : ℝ × ℂ → Prop}
    (h : ∀ᵐ p ∂(volume.restrict (slab T)), P p) :
    ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)), ∀ᵐ x ∂(volume : Measure ℂ), P (t, x) := by
  rw [JointRep.volume_restrict_slab] at h
  exact Measure.ae_ae_of_ae_prod h

/-- The Biot–Savart field of a slice depends only on the a.e. class of the slice. -/
theorem velocityField_eq_of_ae {ω ω' : ℝ → ℂ → ℝ} {t : ℝ} (h : ω' t =ᵐ[volume] ω t) :
    velocityField ω' t = velocityField ω t := by
  funext x
  simp only [velocityField, velocity]
  refine integral_congr_ae ?_
  filter_upwards [h] with y hy
  rw [hy]

/-- The transport identity is invariant under a.e. modification of `u` on the slab and of the
field `w` on a null set of times. -/
theorem solvesTransport_congr {T : ℝ} {u u' : ℝ → ℂ → ℝ} {w w' : ℝ → ℂ → ℂ} {u₀ : ℂ → ℝ}
    (h : SolvesTransport T u w u₀)
    (hu : Function.uncurry u' =ᵐ[volume.restrict (slab T)] Function.uncurry u)
    (hw : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)), w' t = w t) :
    SolvesTransport T u' w' u₀ := by
  have hF : ∀ φ, transportIntegrand u' w' φ =ᵐ[volume.restrict (slab T)]
      transportIntegrand u w φ := by
    intro φ
    filter_upwards [hu, ae_slab_of_ae_time hw] with p hp hwp
    have hp' : u' p.1 p.2 = u p.1 p.2 := hp
    simp only [transportIntegrand]
    rw [hp', hwp]
  refine ⟨fun φ hφ => Integrable.congr (h.integrableOn φ hφ) (hF φ).symm,
    h.datum_integrable, fun φ hφ => ?_⟩
  have key : ∫ t in Ioo (0 : ℝ) T, ∫ x : ℂ, transportIntegrand u' w' φ (t, x) =
      ∫ t in Ioo (0 : ℝ) T, ∫ x : ℂ, transportIntegrand u w φ (t, x) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_time_of_ae_slab (hF φ)] with t ht
    exact integral_congr_ae ht
  rw [key]
  exact h.identity φ hφ

/-- Uniform boundedness: a path weakly continuous into `L²` on a compact set of times is bounded
in `L²` there (Banach–Steinhaus). -/
theorem exists_bound_of_isWeakContL2On {s : Set ℝ} (hs : IsCompact s) {ω : ℝ → ℂ → ℝ}
    (hc : IsWeakContL2On s ω) :
    ∃ C : ℝ, ∀ t ∈ s, (eLpNorm (ω t) 2 volume).toReal ≤ C := by
  obtain ⟨hm, hw⟩ := isWeakContL2On_iff_toPath.1 hc
  let g : s → (Lp ℝ 2 (volume : Measure ℂ)) →L[ℝ] ℝ :=
    fun t => innerSL ℝ (JointRep.toPath (μ := (volume : Measure ℂ)) ω t)
  have hb : ∀ y, ∃ C, ∀ t : s, ‖g t y‖ ≤ C := by
    intro y
    obtain ⟨C, hC⟩ := hs.exists_bound_of_continuousOn (hw y)
    exact ⟨C, fun t => by simpa [g, innerSL_apply_apply] using hC t t.2⟩
  obtain ⟨C', hC'⟩ := banach_steinhaus hb
  refine ⟨C', fun t ht => ?_⟩
  have h1 := hC' ⟨t, ht⟩
  simp only [g, innerSL_apply_norm] at h1
  rw [JointRep.toPath_of_memLp (hm t ht), Lp.norm_toLp] at h1
  exact h1

/-- An exhausting sequence of times `τ j ∈ (0, T₀)`. -/
theorem exists_seq_exhaust {T₀ : ℝ≥0∞} (hT₀ : 0 < T₀) :
    ∃ τ : ℕ → ℝ, (∀ j, 0 < τ j) ∧ (∀ j, ENNReal.ofReal (τ j) < T₀) ∧
      ∀ t : ℝ, ENNReal.ofReal t < T₀ → ∃ j, t < τ j := by
  obtain ⟨u, -, hu, hlim⟩ := exists_seq_strictMono_tendsto' hT₀
  have hne : ∀ j, u j ≠ ⊤ := fun j => ((hu j).2.trans_le le_top).ne
  have hpos : ∀ j, 0 < (u j).toReal := fun j => ENNReal.toReal_pos (hu j).1.ne' (hne j)
  refine ⟨fun j => (u j).toReal, hpos, fun j => ?_, fun t ht => ?_⟩
  · rw [ENNReal.ofReal_toReal (hne j)]
    exact (hu j).2
  · obtain ⟨j, hj⟩ := (hlim.eventually (lt_mem_nhds ht)).exists
    refine ⟨j, ?_⟩
    rcases le_or_gt t 0 with h0 | h0
    · exact h0.trans_lt (hpos j)
    · exact (ENNReal.ofReal_lt_iff_lt_toReal h0.le (hne j)).1 hj

end WeakContRepAux

open WeakContRepAux

/-- `03_compactness.tex:242-243`: two functions that are weakly continuous into `L²` on `[0,T]`,
`T > 0`, and agree (a.e. in `x`) for almost every `t ∈ (0,T)`, agree for every `t ∈ [0,T]`. -/
theorem ae_eq_of_isWeakContL2On {T : ℝ} (hT : 0 < T) {ω₁ ω₂ : ℝ → ℂ → ℝ}
    (h₁ : IsWeakContL2On (Icc 0 T) ω₁) (h₂ : IsWeakContL2On (Icc 0 T) ω₂)
    (h : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), ω₁ t =ᵐ[volume] ω₂ t) :
    ∀ t ∈ Icc 0 T, ω₁ t =ᵐ[volume] ω₂ t := by
  obtain ⟨hm₁, hc₁⟩ := isWeakContL2On_iff_toPath.1 h₁
  obtain ⟨hm₂, hc₂⟩ := isWeakContL2On_iff_toPath.1 h₂
  have hae : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (JointRep.toPath (μ := (volume : Measure ℂ)) ω₁ t) =
        JointRep.toPath (μ := (volume : Measure ℂ)) ω₂ t := by
    filter_upwards [h, ae_restrict_mem measurableSet_Ioo] with t ht hmem
    have e1 := hm₁ t (Ioo_subset_Icc_self hmem)
    have e2 := hm₂ t (Ioo_subset_Icc_self hmem)
    rw [JointRep.toPath_of_memLp e1, JointRep.toPath_of_memLp e2]
    exact (MemLp.toLp_eq_toLp_iff e1 e2).2 ht
  have heq := WeakL2.WeakContinuousOn.eqOn_of_ae_eq hT hc₁ hc₂ hae
  intro t ht
  have h12 : (JointRep.toPath (μ := (volume : Measure ℂ)) ω₁ t) =
      JointRep.toPath (μ := (volume : Measure ℂ)) ω₂ t := heq ht
  have e1 := JointRep.coeFn_toPath (μ := (volume : Measure ℂ)) (hm₁ t ht)
  have e2 := JointRep.coeFn_toPath (μ := (volume : Measure ℂ)) (hm₂ t ht)
  rw [h12] at e1
  exact e1.symm.trans e2

/-- Weak solutions are invariant under a.e. modification on `(0,T) × ℝ²` (elements of `X_q(T)`
are equivalence classes, `02_prelim.tex:101-120`; used for the identification
`03_compactness.tex:238-240`). -/
theorem _root_.NonUniqueEuler.IsWeakSolution.congr_ae {q T : ℝ} {ωin : ℂ → ℝ}
    {ω ω' : ℝ → ℂ → ℝ} (h : IsWeakSolution q T ωin ω)
    (h' : Function.uncurry ω' =ᵐ[volume.restrict (slab T)] Function.uncurry ω) :
    IsWeakSolution q T ωin ω' := by
  have hslice : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)), ω' t =ᵐ[volume] ω t :=
    JointRep.ae_ae_of_ae_eq_slab h'
  have hv : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)), velocityField ω' t = velocityField ω t :=
    hslice.mono fun t ht => velocityField_eq_of_ae ht
  obtain ⟨hm, M, hM⟩ := h.memX
  refine ⟨h.q_gt, h.T_pos, h.datum_memLp_one, h.datum_memLp_q,
    ⟨hm.congr h'.symm, M, ?_⟩, ?_, solvesTransport_congr h.weak h' hv⟩
  · filter_upwards [hM, hslice] with t ht hts
    rw [eLpNorm_congr_ae hts, eLpNorm_congr_ae hts]
    exact ⟨ht.1.ae_eq hts.symm, ht.2.1.ae_eq hts.symm, ht.2.2⟩
  · filter_upwards [h.velocity_convergent, hslice] with t ht hts
    filter_upwards [ht] with x hx
    refine hx.congr ?_
    filter_upwards [hts] with y hy
    rw [hy]

/-- Renormalized weak solutions are invariant under a.e. modification on `(0,T) × ℝ²`. -/
theorem _root_.NonUniqueEuler.IsRenormalizedWeakSolution.congr_ae {q T : ℝ} {ωin : ℂ → ℝ}
    {ω ω' : ℝ → ℂ → ℝ} (h : IsRenormalizedWeakSolution q T ωin ω)
    (h' : Function.uncurry ω' =ᵐ[volume.restrict (slab T)] Function.uncurry ω) :
    IsRenormalizedWeakSolution q T ωin ω' := by
  have hslice : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)), ω' t =ᵐ[volume] ω t :=
    JointRep.ae_ae_of_ae_eq_slab h'
  have hv : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)), velocityField ω' t = velocityField ω t :=
    hslice.mono fun t ht => velocityField_eq_of_ae ht
  refine ⟨h.toIsWeakSolution.congr_ae h', fun Υ hΥ => ?_⟩
  refine solvesTransport_congr (h.renormalized Υ hΥ) ?_ hv
  filter_upwards [h'] with p hp
  have hp' : ω' p.1 p.2 = ω p.1 p.2 := hp
  show Υ (ω' p.1 p.2) = Υ (ω p.1 p.2)
  rw [hp']

/-- `03_compactness.tex:236-240` (with `b = 2`, D9): a weak solution in `X_q(T)` with
`ω ∈ L^∞(0,T;L²)` has a jointly measurable representative `ω'` (equal to `ω` a.e. on
`(0,T) × ℝ²`) that is a weak solution with the same datum, weakly continuous into `L²` on
`[0,T]`, with `ω'(0) = ω^in`. -/
theorem _root_.NonUniqueEuler.IsWeakSolution.exists_weakContRep {q T : ℝ} {ωin : ℂ → ℝ}
    {ω : ℝ → ℂ → ℝ} (h : IsWeakSolution q T ωin ω)
    (h2 : Prelim.MemLinfLp (Ioo 0 T) univ 2 ω) :
    ∃ ω' : ℝ → ℂ → ℝ, Measurable (Function.uncurry ω') ∧
      Function.uncurry ω' =ᵐ[volume.restrict (slab T)] Function.uncurry ω ∧
      IsWeakSolution q T ωin ω' ∧ IsWeakContL2On (Icc 0 T) ω' ∧
      ω' 0 =ᵐ[volume] ωin := by
  have hT := h.T_pos
  obtain ⟨M, hM⟩ := h2.essBounded
  have hN : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      eLpNorm (ω t) 2 volume ≤ ENNReal.ofReal (max M 0) := by
    filter_upwards [hM] with t ht
    rw [Measure.restrict_univ] at ht
    rw [← ENNReal.ofReal_toReal ht.1.eLpNorm_ne_top]
    exact ENNReal.ofReal_le_ofReal (ht.2.trans (le_max_left _ _))
  obtain ⟨ũ, hm, hc, hae, -, -, h0, -⟩ := weakCont hT (le_max_right M 0)
    (fun R hR => (h.memLinfLp_velocityField hR).1) h2
    (memLp_one_iff_integrable.1 h.datum_memLp_one).locallyIntegrable h.solvesTE hN
  exact ⟨ũ, hm, hae, h.congr_ae hae, hc, h0⟩

/-- `03_compactness.tex:239-240` (`lem:weak-cont`(a), `ũ(0) = u₀`): a weak solution in `X_q(T)`
that is weakly continuous into `L²` on `[0,T]` takes the value `ω^in` at `t = 0`. -/
theorem _root_.NonUniqueEuler.IsWeakSolution.ae_eq_datum_of_isWeakContL2On {q T : ℝ}
    {ωin : ℂ → ℝ} {ω : ℝ → ℂ → ℝ} (h : IsWeakSolution q T ωin ω)
    (hc : IsWeakContL2On (Icc 0 T) ω) :
    ω 0 =ᵐ[volume] ωin := by
  have hT := h.T_pos
  obtain ⟨C, hC⟩ := exists_bound_of_isWeakContL2On isCompact_Icc hc
  have h2 : Prelim.MemLinfLp (Ioo 0 T) univ 2 ω := by
    refine ⟨h.memX.aestronglyMeasurable, C, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [Measure.restrict_univ]
    exact ⟨hc.memLp t (Ioo_subset_Icc_self ht), hC t (Ioo_subset_Icc_self ht)⟩
  obtain ⟨ω', -, hae, -, hc', h0⟩ := h.exists_weakContRep h2
  have h0' := ae_eq_of_isWeakContL2On hT hc' hc (JointRep.ae_ae_of_ae_eq_slab hae) 0
    ⟨le_rfl, hT.le⟩
  exact h0'.symm.trans h0

/-- `03_compactness.tex:240-241` (`lem:weak-cont`(a) bounds): for a function weakly continuous
into `L²` on `[0,T]`, `T > 0`, an essential bound of `‖ω(t)‖_{L^p}` on `(0,T)`, `p ∈ [1,∞]`,
holds at every `t ∈ [0,T]`. -/
theorem eLpNorm_le_of_isWeakContL2On {T : ℝ} (hT : 0 < T) {ω : ℝ → ℂ → ℝ}
    (hc : IsWeakContL2On (Icc 0 T) ω) {p : ℝ≥0∞} (hp : 1 ≤ p) {M : ℝ}
    (hM : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), eLpNorm (ω t) p volume ≤ ENNReal.ofReal M) :
    ∀ t ∈ Icc 0 T, eLpNorm (ω t) p volume ≤ ENNReal.ofReal M := by
  obtain ⟨hm, hw⟩ := isWeakContL2On_iff_toPath.1 hc
  have key := WeakL2.WeakContinuousOn.eLpNorm_le_of_ae hT hw hp (M := ENNReal.ofReal M) (by
    filter_upwards [hM, ae_restrict_mem measurableSet_Ioo] with t ht hmem
    rw [eLpNorm_congr_ae (JointRep.coeFn_toPath (μ := (volume : Measure ℂ))
      (hm t (Ioo_subset_Icc_self hmem)))]
    exact ht)
  intro t ht
  rw [← eLpNorm_congr_ae (JointRep.coeFn_toPath (μ := (volume : Measure ℂ)) (hm t ht))]
  exact key t ht

/-- `03_compactness.tex:239-241`: a weak solution in `X_q(T)` that is weakly continuous into
`L²` on `[0,T]` has `ω(t) ∈ L¹ ∩ L^q` for every `t ∈ [0,T]`, with
`sup_{t ∈ [0,T]} ‖ω(t)‖_{L¹∩L^q} < ∞`. -/
theorem _root_.NonUniqueEuler.IsWeakSolution.bound_of_isWeakContL2On {q T : ℝ}
    {ωin : ℂ → ℝ} {ω : ℝ → ℂ → ℝ} (h : IsWeakSolution q T ωin ω)
    (hc : IsWeakContL2On (Icc 0 T) ω) :
    ∃ M : ℝ, ∀ t ∈ Icc 0 T, MemLp (ω t) 1 volume ∧ MemLp (ω t) (ENNReal.ofReal q) volume ∧
      normL1LpE (ENNReal.ofReal q) (ω t) ≤ ENNReal.ofReal M := by
  have hT := h.T_pos
  obtain ⟨_, M, hM⟩ := h.memX
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith [h.q_gt])
  have hb1 : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      eLpNorm (ω t) 1 volume ≤ ENNReal.ofReal (max M 0) := by
    filter_upwards [hM] with t ht
    rw [← ENNReal.ofReal_toReal ht.1.eLpNorm_ne_top]
    refine ENNReal.ofReal_le_ofReal (le_trans ?_ (le_max_left _ _))
    linarith [ht.2.2, (ENNReal.toReal_nonneg :
      0 ≤ (eLpNorm (ω t) (ENNReal.ofReal q) volume).toReal)]
  have hbq : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      eLpNorm (ω t) (ENNReal.ofReal q) volume ≤ ENNReal.ofReal (max M 0) := by
    filter_upwards [hM] with t ht
    rw [← ENNReal.ofReal_toReal ht.2.1.eLpNorm_ne_top]
    refine ENNReal.ofReal_le_ofReal (le_trans ?_ (le_max_left _ _))
    linarith [ht.2.2, (ENNReal.toReal_nonneg : 0 ≤ (eLpNorm (ω t) 1 volume).toReal)]
  have e1 := eLpNorm_le_of_isWeakContL2On hT hc le_rfl hb1
  have eq := eLpNorm_le_of_isWeakContL2On hT hc hq1 hbq
  refine ⟨2 * max M 0, fun t ht => ⟨?_, ?_, ?_⟩⟩
  · exact ⟨(hc.memLp t ht).aestronglyMeasurable, (e1 t ht).trans_lt ENNReal.ofReal_lt_top⟩
  · exact ⟨(hc.memLp t ht).aestronglyMeasurable, (eq t ht).trans_lt ENNReal.ofReal_lt_top⟩
  · unfold normL1LpE
    calc eLpNorm (ω t) 1 volume + eLpNorm (ω t) (ENNReal.ofReal q) volume
        ≤ ENNReal.ofReal (max M 0) + ENNReal.ofReal (max M 0) := add_le_add (e1 t ht) (eq t ht)
      _ = ENNReal.ofReal (2 * max M 0) := by
        rw [← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _), two_mul]

/-- `03_compactness.tex:241-243`: a weak solution on `[0,T₀)` with `ω ∈ L^∞(0,T;L²)` for every
`T < T₀` has a jointly measurable representative, equal to `ω` a.e. on every `(0,T) × ℝ²`,
`T < T₀`, which is a weak solution on `[0,T₀)` with the same datum, weakly continuous into `L²`
on `[0,T₀)`, with value `ω^in` at `0`. -/
theorem _root_.NonUniqueEuler.Weak.IsWeakSolutionUpTo.exists_weakContRep {q : ℝ}
    {T₀ : ℝ≥0∞} (hT₀ : 0 < T₀) {ωin : ℂ → ℝ} {ω : ℝ → ℂ → ℝ}
    (h : IsWeakSolutionUpTo q T₀ ωin ω)
    (h2 : ∀ T : ℝ, 0 < T → ENNReal.ofReal T < T₀ → Prelim.MemLinfLp (Ioo 0 T) univ 2 ω) :
    ∃ ω' : ℝ → ℂ → ℝ, Measurable (Function.uncurry ω') ∧
      (∀ T : ℝ, 0 < T → ENNReal.ofReal T < T₀ →
        Function.uncurry ω' =ᵐ[volume.restrict (slab T)] Function.uncurry ω) ∧
      IsWeakSolutionUpTo q T₀ ωin ω' ∧ IsWeakContL2On (timeInterval T₀) ω' ∧
      ω' 0 =ᵐ[volume] ωin := by
  classical
  obtain ⟨τ, hτ0, hτT, hτex⟩ := exists_seq_exhaust hT₀
  have hrep : ∀ j, ∃ ω' : ℝ → ℂ → ℝ, Measurable (Function.uncurry ω') ∧
      Function.uncurry ω' =ᵐ[volume.restrict (slab (τ j))] Function.uncurry ω ∧
      IsWeakSolution q (τ j) ωin ω' ∧ IsWeakContL2On (Icc 0 (τ j)) ω' ∧
      ω' 0 =ᵐ[volume] ωin := fun j =>
    (h (τ j) (hτ0 j) (hτT j)).exists_weakContRep (h2 (τ j) (hτ0 j) (hτT j))
  choose W hWm hWae _ hWc hW0 using hrep
  -- the representatives agree on overlaps
  have hcons : ∀ i j, ∀ t ∈ Icc 0 (min (τ i) (τ j)), W i t =ᵐ[volume] W j t := by
    intro i j
    have hm : 0 < min (τ i) (τ j) := lt_min (hτ0 i) (hτ0 j)
    refine ae_eq_of_isWeakContL2On hm
      ((hWc i).mono (Icc_subset_Icc le_rfl (min_le_left _ _)))
      ((hWc j).mono (Icc_subset_Icc le_rfl (min_le_right _ _))) ?_
    have hi : ∀ᵐ t ∂(volume.restrict (Ioo 0 (min (τ i) (τ j)))), W i t =ᵐ[volume] ω t :=
      ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right (min_le_left _ _))
        (JointRep.ae_ae_of_ae_eq_slab (hWae i))
    have hj : ∀ᵐ t ∂(volume.restrict (Ioo 0 (min (τ i) (τ j)))), W j t =ᵐ[volume] ω t :=
      ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right (min_le_right _ _))
        (JointRep.ae_ae_of_ae_eq_slab (hWae j))
    filter_upwards [hi, hj] with t h1 h2
    exact h1.trans h2.symm
  -- the gluing index
  have hP : ∀ t : ℝ, ∃ n, t < τ n ∨ ¬ ∃ j, t < τ j := by
    intro t
    by_cases hex : ∃ j, t < τ j
    · obtain ⟨j, hj⟩ := hex
      exact ⟨j, Or.inl hj⟩
    · exact ⟨0, Or.inr hex⟩
  set ω' : ℝ → ℂ → ℝ := fun t x => W (Nat.find (hP t)) t x with hω'
  have hmeas : Measurable (Function.uncurry ω') := by
    refine Measurable.find (f := fun n => Function.uncurry (W n))
      (p := fun n (z : ℝ × ℂ) => z.1 < τ n ∨ ¬ ∃ j, z.1 < τ j) hWm (fun n => ?_)
      (fun z => hP z.1)
    have hset : MeasurableSet {t : ℝ | t < τ n ∨ ¬ ∃ j, t < τ j} := by
      have : {t : ℝ | t < τ n ∨ ¬ ∃ j, t < τ j} = Iio (τ n) ∪ ⋂ j, Ici (τ j) := by
        ext t
        simp only [mem_ofPred_eq, not_exists, not_lt, mem_union, mem_Iio, mem_iInter, mem_Ici]
      rw [this]
      exact measurableSet_Iio.union (MeasurableSet.iInter fun j => measurableSet_Ici)
    exact measurable_fst hset
  have hν : ∀ t : ℝ, 0 ≤ t → ∀ j, t < τ j → ω' t =ᵐ[volume] W j t := by
    intro t ht j hj
    have hspec := Nat.find_spec (hP t)
    have hlt : t < τ (Nat.find (hP t)) := hspec.resolve_right (not_not.2 ⟨j, hj⟩)
    exact hcons (Nat.find (hP t)) j t ⟨ht, le_min hlt.le hj.le⟩
  -- the slices agree with those of `ω` for a.e. `t ∈ (0, T)`
  have hslab : ∀ T : ℝ, 0 < T → ENNReal.ofReal T < T₀ →
      Function.uncurry ω' =ᵐ[volume.restrict (slab T)] Function.uncurry ω := by
    intro T hT hTT
    obtain ⟨j, hj⟩ := hτex T hTT
    have hW := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right hj.le)
      (JointRep.ae_ae_of_ae_eq_slab (hWae j))
    refine JointRep.ae_eq_slab_of_ae_ae hmeas.aestronglyMeasurable
      (h T hT hTT).memX.aestronglyMeasurable ?_
    filter_upwards [hW, ae_restrict_mem measurableSet_Ioo] with t ht hmem
    exact (hν t hmem.1.le j (hmem.2.trans hj)).trans ht
  refine ⟨ω', hmeas, hslab, fun T hT hTT => (h T hT hTT).congr_ae (hslab T hT hTT), ?_, ?_⟩
  · refine ⟨fun t ht => ?_, fun ψ hψ => ?_⟩
    · obtain ⟨j, hj⟩ := hτex t ht.2
      exact ((hWc j).memLp t ⟨ht.1, hj.le⟩).ae_eq (hν t ht.1 j hj).symm
    · intro t₀ ht₀
      obtain ⟨j, hj⟩ := hτex t₀ ht₀.2
      have hcj : ContinuousWithinAt (fun t => ∫ x, W j t x * ψ x) (Icc 0 (τ j)) t₀ :=
        (hWc j).continuousOn ψ hψ t₀ ⟨ht₀.1, hj.le⟩
      have heq : ∀ t ∈ timeInterval T₀ ∩ Iio (τ j),
          (∫ x, ω' t x * ψ x) = ∫ x, W j t x * ψ x := by
        intro t ht
        refine integral_congr_ae ?_
        filter_upwards [hν t ht.1.1 j ht.2] with x hx
        rw [hx]
      have hcj' : ContinuousWithinAt (fun t => ∫ x, W j t x * ψ x)
          (timeInterval T₀ ∩ Iio (τ j)) t₀ :=
        hcj.mono fun t ht => ⟨ht.1.1, ht.2.le⟩
      have hc2 : ContinuousWithinAt (fun t => ∫ x, ω' t x * ψ x)
          (timeInterval T₀ ∩ Iio (τ j)) t₀ :=
        hcj'.congr heq (heq t₀ ⟨ht₀, hj⟩)
      exact (continuousWithinAt_inter (Iio_mem_nhds hj)).1 hc2
  · exact (hν 0 le_rfl 0 (hτ0 0)).trans (hW0 0)

end NonUniqueEuler.Weak
