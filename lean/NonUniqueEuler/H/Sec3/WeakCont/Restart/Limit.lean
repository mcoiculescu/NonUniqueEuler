import NonUniqueEuler.H.Sec3.WeakCont.Restart.Kappa
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Helpers for `P/Sec3/WeakCont/Restart.lean`: the two limits `h → 0⁺`

Manuscript: proof of `lem:weak-cont`(c), `03_compactness.tex:216-225`. With
`ϰ_h(t) = ϰ((t - t₀)/h)` and `0 < t₀ < T`:
* `tendsto_integral_kappaShift_mul`: `∫_0^T ϰ_h I → ∫_{t₀}^T I` for `I ∈ L¹(0,T)`, by dominated
  convergence (`ϰ_h → 1_{(t₀,∞)}` pointwise, `|ϰ_h I| ≤ |I|`);
* `tendsto_integral_deriv_kappaShift_mul`: `∫_0^T ϰ_h' g → g(t₀)` for `g` continuous on `[0,T]`
  (`ϰ_h' ≥ 0`, `ϰ_h' = 0` off `[t₀, t₀+h]`, `∫_0^T ϰ_h' = 1`, so
  `|∫ ϰ_h' g - g(t₀)| ≤ sup_{[t₀,t₀+h]} |g - g(t₀)|`).

All lemmas are fully proved.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace NonUniqueEuler.Weak.WeakCont.Restart

/-- `∫_0^T ϰ_h I → ∫_{t₀}^T I` as `h → 0⁺`, for `0 < t₀` and `I ∈ L¹(0,T)`. -/
theorem tendsto_integral_kappaShift_mul {T t₀ : ℝ} (ht₀ : 0 < t₀) {I : ℝ → ℝ}
    (hI : IntegrableOn I (Ioo 0 T)) :
    Tendsto (fun h => ∫ t in Ioo 0 T, kappa ((t - t₀) / h) * I t) (𝓝[>] 0)
      (𝓝 (∫ t in Ioo t₀ T, I t)) := by
  have hlim : Tendsto (fun h => ∫ t in Ioo 0 T, kappa ((t - t₀) / h) * I t) (𝓝[>] 0)
      (𝓝 (∫ t in Ioo 0 T, (Ioi t₀).indicator I t)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun t => ‖I t‖) ?_ ?_ hI.norm ?_
    · exact Eventually.of_forall fun h =>
        (continuous_kappaShift t₀ h).aestronglyMeasurable.mul hI.aestronglyMeasurable
    · refine Eventually.of_forall fun h => Eventually.of_forall fun t => ?_
      rw [norm_mul, Real.norm_eq_abs (kappa _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (abs_kappaShift_le_one t₀ h t)
    · refine Eventually.of_forall fun t => ?_
      by_cases ht : t₀ < t
      · rw [indicator_of_mem (mem_Ioi.2 ht)]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 ht)] with h hh
        rw [kappaShift_eq_one hh.1 (by linarith [hh.2]), one_mul]
      · rw [indicator_of_notMem (fun h => ht (mem_Ioi.1 h))]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with h hh
        rw [kappaShift_eq_zero (mem_Ioi.1 hh) (not_lt.1 ht), zero_mul]
  have hset : Ioi t₀ ∩ Ioo 0 T = Ioo t₀ T := by
    ext t
    simp only [mem_inter_iff, mem_Ioi, mem_Ioo]
    constructor
    · rintro ⟨h1, _, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨h1, by linarith, h3⟩
  have heq : ∫ t in Ioo 0 T, (Ioi t₀).indicator I t = ∫ t in Ioo t₀ T, I t := by
    rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, hset]
  rwa [heq] at hlim

/-- The averaging estimate: if `d ≥ 0` is continuous, vanishes off `[t₀, t₀ + h]` and has integral
`1` over `(0,T)`, and `|g - g(t₀)| ≤ ε` on `[t₀, t₀ + h] ∩ [0,T]`, then
`|∫_0^T d g - g(t₀)| ≤ ε`. -/
theorem abs_integral_mul_sub_le {T t₀ h ε : ℝ} {d g : ℝ → ℝ} (hd : Continuous d)
    (hd0 : ∀ t, 0 ≤ d t) (hdz : ∀ t, t < t₀ ∨ t₀ + h < t → d t = 0)
    (hd1 : ∫ t in Ioo 0 T, d t = 1) (hg : ContinuousOn g (Icc 0 T))
    (hgε : ∀ t ∈ Icc 0 T, t₀ ≤ t → t ≤ t₀ + h → |g t - g t₀| ≤ ε) :
    |(∫ t in Ioo 0 T, d t * g t) - g t₀| ≤ ε := by
  have hint1 : IntegrableOn d (Ioo 0 T) :=
    hd.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hint : IntegrableOn (fun t => d t * g t) (Ioo 0 T) :=
    (hd.continuousOn.mul hg).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hrw : (∫ t in Ioo 0 T, d t * g t) - g t₀ = ∫ t in Ioo 0 T, d t * (g t - g t₀) := by
    have e1 : (fun t => d t * (g t - g t₀)) = fun t => d t * g t - d t * g t₀ := by
      funext t
      ring
    rw [e1, integral_sub hint (hint1.mul_const (g t₀)), integral_mul_const, hd1, one_mul]
  have hbound : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)), ‖d t * (g t - g t₀)‖ ≤ d t * ε := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [norm_mul, Real.norm_of_nonneg (hd0 t)]
    by_cases hin : t₀ ≤ t ∧ t ≤ t₀ + h
    · refine mul_le_mul_of_nonneg_left ?_ (hd0 t)
      rw [Real.norm_eq_abs]
      exact hgε t (Ioo_subset_Icc_self ht) hin.1 hin.2
    · have hz : d t = 0 := by
        refine hdz t ?_
        rcases not_and_or.1 hin with h1 | h1
        · exact Or.inl (not_le.1 h1)
        · exact Or.inr (not_le.1 h1)
      rw [hz, zero_mul, zero_mul]
  have hle := norm_integral_le_of_norm_le (hint1.mul_const ε) hbound
  rw [integral_mul_const, hd1, one_mul, Real.norm_eq_abs] at hle
  rw [hrw]
  exact hle

/-- `∫_0^T ϰ_h' g → g(t₀)` as `h → 0⁺`, for `t₀ ∈ (0,T)` and `g` continuous on `[0,T]`. -/
theorem tendsto_integral_deriv_kappaShift_mul {T t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 T) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc 0 T)) :
    Tendsto (fun h => ∫ t in Ioo 0 T, deriv (fun t : ℝ => kappa ((t - t₀) / h)) t * g t)
      (𝓝[>] 0) (𝓝 (g t₀)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hgδ⟩ :=
    Metric.continuousWithinAt_iff.1 (hg t₀ (Ioo_subset_Icc_self ht₀)) (ε / 2) (half_pos hε)
  refine ⟨min δ (T - t₀), lt_min hδ (sub_pos.2 ht₀.2), fun h hh hdist => ?_⟩
  have hh0 : 0 < h := hh
  rw [Real.dist_eq, sub_zero, abs_of_pos hh0, lt_min_iff] at hdist
  have hle : |(∫ t in Ioo 0 T, deriv (fun t : ℝ => kappa ((t - t₀) / h)) t * g t) - g t₀| ≤
      ε / 2 := by
    refine abs_integral_mul_sub_le (h := h) (continuous_deriv_kappaShift t₀ h)
      (deriv_kappaShift_nonneg hh0) ?_ (integral_deriv_kappaShift hh0 ht₀.1.le (by linarith))
      hg ?_
    · rintro t (ht | ht)
      · exact deriv_kappaShift_eq_zero_of_lt hh0 ht
      · exact deriv_kappaShift_eq_zero_of_gt hh0 ht
    · intro t ht h1 h2
      have hd : dist t t₀ < δ := by
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith
      have := hgδ ht hd
      rw [Real.dist_eq] at this
      exact this.le
  rw [Real.dist_eq]
  linarith

end NonUniqueEuler.Weak.WeakCont.Restart
