import NonUniqueEuler.Defs.Sec2.Spaces
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Helper for `P/SmoothB/SmoothWeak`: `L^p` bounds and `L^p` continuity of continuous families

For a jointly continuous `F : ℝ → ℂ → ℝ` whose slices `F(t)` vanish outside one compact set
`K` for `t` in a time interval (`B_global_smooth.tex:558-562`: "`ω` is continuous and `ω(t)`
vanishes outside `B_{R(T)}` for `|t| ≤ T`, so `ω` is uniformly continuous on `[0,T] × ℝ²`"):

* `eLpNorm_le_of_bound`: `‖f‖_{L^p} ≤ |K|^{1/p} sup |f|` for `f` vanishing outside `K`;
* `tendsto_eLpNorm_sub`: `t ↦ F(t)` is continuous into `L^p` at `t₀` (every `p`, including
  `p = ∞`), by uniform continuity on `[t₀-1, t₀+1] × K` (`IsCompact.mem_uniformity_of_prod`);
* `memLinfLp_of_continuous`: `F ∈ L^∞(0,T; L^p(ℝ²))`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace NonUniqueEuler.Smooth.SmoothWeakH

/-- A real function on the plane vanishing outside `K` and bounded by `C` has
`‖f‖_{L^p} ≤ |K|^{1/p} C`. -/
theorem eLpNorm_le_of_bound {f : ℂ → ℝ} {K : Set ℂ} (hK : ∀ x ∉ K, f x = 0) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) (p : ℝ≥0∞) :
    eLpNorm f p volume ≤ volume K ^ p.toReal⁻¹ * ENNReal.ofReal C := by
  have hsupp : Function.support f ⊆ K := fun x hx => by
    by_contra h
    exact hx (hK x h)
  rw [← eLpNorm_restrict_eq_of_support_subset hsupp]
  have := eLpNorm_le_of_ae_bound (μ := volume.restrict K) (p := p) (f := f) (C := C)
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x)
  simpa [Measure.restrict_apply_univ] using this

/-- Continuity into `L^p` (any `p`) of a jointly continuous family whose slices vanish outside a
fixed compact set for `t` near `t₀`. -/
theorem tendsto_eLpNorm_sub {F : ℝ → ℂ → ℝ} (hF : Continuous (Function.uncurry F)) {K : Set ℂ}
    (hK : IsCompact K) {t₀ : ℝ} (hsupp : ∀ t ∈ Icc (t₀ - 1) (t₀ + 1), ∀ x ∉ K, F t x = 0)
    (p : ℝ≥0∞) :
    Tendsto (fun t => eLpNorm (F t - F t₀) p volume) (𝓝 t₀) (𝓝 0) := by
  set c : ℝ≥0∞ := volume K ^ p.toReal⁻¹ with hc_def
  have hc : c ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) hK.measure_lt_top.ne
  have hlim : Tendsto (fun η : ℝ => c * ENNReal.ofReal η) (𝓝 0) (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul
      (ENNReal.tendsto_ofReal (tendsto_id (x := 𝓝 (0 : ℝ)))) (Or.inr hc)
    simpa using this
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨η, hηε, hη⟩ : ∃ η : ℝ, c * ENNReal.ofReal η < ε ∧ 0 < η :=
    (((hlim.eventually (gt_mem_nhds hε)).filter_mono
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))).and self_mem_nhdsWithin).exists
  obtain ⟨v, hv, hvK⟩ := hK.mem_uniformity_of_prod (f := F) (s := univ) (q := t₀)
    hF.continuousOn (mem_univ _) (Metric.dist_mem_uniformity hη)
  rw [nhdsWithin_univ] at hv
  have hI : Icc (t₀ - 1) (t₀ + 1) ∈ 𝓝 t₀ := Icc_mem_nhds (by linarith) (by linarith)
  have ht₀ : t₀ ∈ Icc (t₀ - 1) (t₀ + 1) := ⟨by linarith, by linarith⟩
  filter_upwards [hv, hI] with t ht htI
  refine le_trans ?_ hηε.le
  refine eLpNorm_le_of_bound (K := K) (fun x hx => ?_) (fun x => ?_) p
  · simp [hsupp t htI x hx, hsupp t₀ ht₀ x hx]
  · by_cases hx : x ∈ K
    · have h1 : dist (F t x) (F t₀ x) < η := hvK t ht x hx
      rw [Real.dist_eq] at h1
      simpa using h1.le
    · simp [hsupp t htI x hx, hsupp t₀ ht₀ x hx, hη.le]

/-- A jointly continuous family whose slices vanish outside a fixed compact set for
`t ∈ [0, T]` lies in `L^∞(0, T; L^p(ℝ²))` for every `p`. -/
theorem memLinfLp_of_continuous {F : ℝ → ℂ → ℝ} (hF : Continuous (Function.uncurry F))
    {K : Set ℂ} (hK : IsCompact K) {T : ℝ} (hsupp : ∀ t ∈ Icc 0 T, ∀ x ∉ K, F t x = 0)
    (p : ℝ≥0∞) : Prelim.MemLinfLp (Ioo 0 T) univ p F := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hF.continuousOn
  refine ⟨hF.aestronglyMeasurable,
    (volume K ^ p.toReal⁻¹ * ENNReal.ofReal (max C 0)).toReal, ?_⟩
  refine ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => ?_
  have htI : t ∈ Icc 0 T := Ioo_subset_Icc_self ht
  rw [Measure.restrict_univ]
  have hcs : HasCompactSupport (F t) := HasCompactSupport.intro hK (hsupp t htI)
  have hFt : Continuous (F t) :=
    hF.comp (continuous_const.prodMk continuous_id : Continuous fun x : ℂ => (t, x))
  refine ⟨hFt.memLp_of_hasCompactSupport hcs, ENNReal.toReal_mono ?_
    (eLpNorm_le_of_bound (hsupp t htI) (fun x => ?_) p)⟩
  · exact ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
        hK.measure_lt_top.ne) ENNReal.ofReal_ne_top
  · by_cases hx : x ∈ K
    · have := hC (t, x) ⟨htI, hx⟩
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_left _ _)
    · rw [hsupp t htI x hx, abs_zero]
      exact le_max_right _ _

end NonUniqueEuler.Smooth.SmoothWeakH
