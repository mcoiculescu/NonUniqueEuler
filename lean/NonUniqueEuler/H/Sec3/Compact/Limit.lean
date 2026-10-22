import NonUniqueEuler.H.Sec3.Compact.Basic
import NonUniqueEuler.I.Infra.WeakL2.LpNorm
import NonUniqueEuler.I.Infra.JointRep.Representative

/-!
# Helpers for `prop:compact`: the limit `ω`, properties (i), (ii), `ω ∈ X₂(T)`

Helper file of `P/Sec3/Compact.lean`. Manuscript: proof of `prop:compact`
(`03_compactness.tex:281-314`).

Given the sequence (`IsCompactSeq`, already extracted) and a weakly continuous `L²`-valued path
`U` that is the uniform weak limit of the paths `t ↦ [ωₙ(t)]` on `[0,T]` (from
`exists_subseq_weakLimit`), take a jointly measurable representative `ω` of `U` on `[0,T]`
(I-JOINT, `JointRep.exists_isJointRep_of_weakContinuousOn`). Then:

* `ω` is weakly continuous into `L²` on `[0,T]`, and (i) holds (`exists_limit_of_path`);
* (ii) `‖ω(t)‖_{L^q} ≤ liminf ‖ωₙ(t)‖_{L^q}`, `q ∈ [1,2]` (weak lower semicontinuity,
  `WeakL2.eLpNorm_le_liminf_of_weakTendsto`; this covers `q = 1` and `q ∈ (1,2]` at once,
  instead of the manuscript's duality arguments, `03_compactness.tex:291-303`), and
  `‖ω(t)‖_{L¹∩L²} ≤ M` (`WeakL2.eLpNorm_add_eLpNorm_le_of_weakTendsto`);
* `ω ∈ X₂(T)` (`memX_of_bound`): joint measurability replaces the manuscript's Pettis argument
  (`03_compactness.tex:304-314`).
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology InnerProductSpace

namespace NonUniqueEuler.Compact.PropCompact

open Weak

variable {T M : ℝ} {gs : ℕ → ℂ → ℝ} {g : ℂ → ℝ} {ωs : ℕ → ℝ → ℂ → ℝ}

/-- The limit `ω` and properties (i), (ii) of `prop:compact` and the bound
`‖ω(t)‖_{L¹∩L²} ≤ M`. -/
theorem exists_limit_of_path (h : IsCompactSeq T M gs g ωs)
    {U : ℝ → Lp ℝ 2 (volume : Measure ℂ)} (hUc : WeakL2.WeakContinuousOn U (Icc 0 T))
    (hconv : WeakL2.WeakTendstoUniformlyOn
      (fun n t => (JointRep.toPath (μ := (volume : Measure ℂ)) (ωs n) t)) U atTop (Icc 0 T)) :
    ∃ ω : ℝ → ℂ → ℝ, Measurable (Function.uncurry ω) ∧ IsWeakContL2On (Icc 0 T) ω ∧
      WeakTendstoUnifL2On ωs ω (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, ∀ q : ℝ, 1 ≤ q → q ≤ 2 →
        eLpNorm (ω t) (ENNReal.ofReal q) volume ≤
          liminf (fun n => eLpNorm (ωs n t) (ENNReal.ofReal q) volume) atTop) ∧
      (∀ t ∈ Icc 0 T, normL1LpE 2 (ω t) ≤ ENNReal.ofReal M) := by
  obtain ⟨ω, hω⟩ := JointRep.exists_isJointRep_of_weakContinuousOn (μ := (volume : Measure ℂ))
    measurableSet_Icc hUc
  have hpath : ∀ t ∈ Icc 0 T,
      (JointRep.toPath (μ := (volume : Measure ℂ)) ω t) = U t := by
    intro t ht
    rw [JointRep.toPath_of_memLp (hω.memLp ht)]
    exact hω.toLp_eq ht
  have hseq : ∀ n, ∀ t ∈ Icc 0 T, ∀ p : ℝ≥0∞,
      eLpNorm ((JointRep.toPath (μ := (volume : Measure ℂ)) (ωs n) t : ℂ → ℝ)) p volume =
        eLpNorm (ωs n t) p volume :=
    fun n t ht p => eLpNorm_congr_ae (JointRep.coeFn_toPath (seq_memLp_two h n ht))
  have hlim : ∀ t ∈ Icc 0 T, ∀ p : ℝ≥0∞,
      eLpNorm (ω t) p volume = eLpNorm ((U t : ℂ → ℝ)) p volume :=
    fun t ht p => eLpNorm_congr_ae (hω.ae_eq t ht)
  refine ⟨ω, hω.measurable, ?_, ?_, ?_, ?_⟩
  · refine isWeakContL2On_iff_toPath.2 ⟨fun t ht => hω.memLp ht, fun y => ?_⟩
    refine (hUc y).congr fun t ht => ?_
    show ⟪(JointRep.toPath (μ := (volume : Measure ℂ)) ω t), y⟫_ℝ = ⟪U t, y⟫_ℝ
    rw [hpath t ht]
  · intro ψ hψ
    refine ((hconv (hψ.toLp ψ)).congr ?_).congr_right ?_
    · exact Eventually.of_forall fun n t ht => inner_toPath_toLp (seq_memLp_two h n ht) hψ
    · intro t ht
      show ⟪U t, hψ.toLp ψ⟫_ℝ = ∫ x, ω t x * ψ x
      rw [← hpath t ht]
      exact inner_toPath_toLp (hω.memLp ht) hψ
  · intro t ht q hq1 _
    have hw := hconv.weakTendsto ht
    have := WeakL2.eLpNorm_le_liminf_of_weakTendsto (μ := (volume : Measure ℂ))
      (q := ENNReal.ofReal q) (ENNReal.one_le_ofReal.2 hq1) hw
    rw [hlim t ht]
    simpa only [hseq _ t ht] using this
  · intro t ht
    have hw := hconv.weakTendsto ht
    have := WeakL2.eLpNorm_add_eLpNorm_le_of_weakTendsto (μ := (volume : Measure ℂ))
      (p := 1) (q := 2) le_rfl one_le_two hw (M := ENNReal.ofReal M)
      (Eventually.of_forall fun n => by
        rw [hseq n t ht, hseq n t ht]
        exact h.bound n t ht)
    rw [normL1LpE, hlim t ht, hlim t ht]
    exact this

/-- `ω ∈ X₂(T)` from joint measurability and the bound `‖ω(t)‖_{L¹∩L²} ≤ M` on `[0,T]`. -/
theorem memX_of_bound {ω : ℝ → ℂ → ℝ} (hM : 0 ≤ M) (hm : Measurable (Function.uncurry ω))
    (h2 : ∀ t ∈ Icc 0 T, MemLp (ω t) 2 volume)
    (hb : ∀ t ∈ Icc 0 T, normL1LpE 2 (ω t) ≤ ENNReal.ofReal M) :
    MemX 2 T ω := by
  refine ⟨hm.aestronglyMeasurable, M, ae_restrict_of_forall_mem measurableSet_Ioo
    fun t ht => ?_⟩
  have ht' := Ioo_subset_Icc_self ht
  have h1 : MemLp (ω t) 1 volume :=
    ⟨(h2 t ht').aestronglyMeasurable,
      ((eLpNorm_one_le_normL1LpE 2 _).trans (hb t ht')).trans_lt ENNReal.ofReal_lt_top⟩
  rw [ENNReal.ofReal_ofNat]
  refine ⟨h1, h2 t ht', ?_⟩
  rw [← ENNReal.toReal_add h1.eLpNorm_ne_top (h2 t ht').eLpNorm_ne_top]
  exact ENNReal.toReal_le_of_le_ofReal hM (hb t ht')

end NonUniqueEuler.Compact.PropCompact
