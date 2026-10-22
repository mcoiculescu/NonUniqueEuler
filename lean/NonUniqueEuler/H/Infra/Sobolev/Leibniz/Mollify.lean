import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import NonUniqueEuler.Defs.Infra.Sobolev

/-!
# Helper for `P/Infra/Sobolev/Leibniz`: weak derivatives tested against `C¹` functions

A weak derivative `g = ∂_v u` (tested against smooth compactly supported functions) can be
tested against `C¹` compactly supported functions:
`∫ u ∂_v ψ = - ∫ g ψ` (`integral_mul_dirDeriv_of_contDiff_one`).

Proof: mollify `ψ` with normed bump functions `ρ_n` (`rOut = 1/(n+1)`); `ρ_n ⋆ ψ` is a test
function, `∂_v (ρ_n ⋆ ψ) = ρ_n ⋆ ∂_v ψ`, the mollified functions are uniformly bounded,
supported in the fixed compact set `cthickening 1 (tsupport ψ)` and converge pointwise; dominated
convergence passes to the limit on both sides.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal ContDiff Topology Convolution

namespace NonUniqueEuler.Sob.LeibnizAux

/-- The mollifiers `ρ_n`, with `rOut = 1/(n+1)`. -/
def moll (n : ℕ) : ContDiffBump (0 : ℂ) where
  rIn := 1 / (2 * ((n : ℝ) + 1))
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [div_lt_div_iff_of_pos_left one_pos (by positivity) h]
    linarith

theorem moll_rOut_tendsto : Tendsto (fun n => (moll n).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem moll_rOut_le_one (n : ℕ) : (moll n).rOut ≤ 1 := by
  show 1 / ((n : ℝ) + 1) ≤ 1
  rw [div_le_one (by positivity)]
  linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

/-- Mollification `ρ_n ⋆ h`. -/
def mollify (n : ℕ) (h : ℂ → ℂ) : ℂ → ℂ :=
  (moll n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h

theorem contDiff_mollify (n : ℕ) {h : ℂ → ℂ} (hh : Continuous h) :
    ContDiff ℝ ∞ (mollify n h) :=
  (moll n).hasCompactSupport_normed.contDiff_convolution_left _
    (moll n).contDiff_normed hh.locallyIntegrable

theorem continuous_mollify (n : ℕ) {h : ℂ → ℂ} (hh : Continuous h) :
    Continuous (mollify n h) :=
  (contDiff_mollify n hh).continuous

theorem hasCompactSupport_mollify (n : ℕ) {h : ℂ → ℂ} (hc : HasCompactSupport h) :
    HasCompactSupport (mollify n h) :=
  (moll n).hasCompactSupport_normed.convolution _ hc

theorem mollify_eq_zero (n : ℕ) (h : ℂ → ℂ) {x : ℂ} (hx : x ∉ cthickening 1 (tsupport h)) :
    mollify n h x = 0 := by
  by_contra hne
  have hmem : x ∈ Function.support (mollify n h) := hne
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) hmem
  rw [(moll n).support_normed_eq] at ha
  apply hx
  refine mem_cthickening_of_dist_le _ b 1 _ (subset_tsupport _ hb) ?_
  have : dist (a + b) b = ‖a‖ := by simp [dist_eq_norm]
  rw [this]
  have := mem_ball_zero_iff.1 ha
  exact this.le.trans (moll_rOut_le_one n)

theorem norm_mollify_le (n : ℕ) {h : ℂ → ℂ} (hh : Continuous h) {M : ℝ}
    (hM : ∀ y, ‖h y‖ ≤ M) (x : ℂ) : ‖mollify n h x‖ ≤ 3 * M := by
  have h1 : dist (mollify n h x) (h x) ≤ 2 * M := by
    refine (moll n).dist_normed_convolution_le hh.aestronglyMeasurable fun y _ => ?_
    calc dist (h y) (h x) ≤ ‖h y‖ + ‖h x‖ := dist_le_norm_add_norm _ _
      _ ≤ 2 * M := by linarith [hM y, hM x]
  calc ‖mollify n h x‖ ≤ ‖h x‖ + dist (mollify n h x) (h x) := by
        rw [dist_eq_norm]
        exact norm_le_insert' _ _
    _ ≤ 3 * M := by linarith [hM x]

theorem tendsto_mollify {h : ℂ → ℂ} (hh : Continuous h) (x : ℂ) :
    Tendsto (fun n => mollify n h x) atTop (𝓝 (h x)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous moll_rOut_tendsto hh x

/-- `∂_v (ρ_n ⋆ h) = ρ_n ⋆ ∂_v h` for `h` of class `C¹` with compact support. -/
theorem dirDeriv_mollify (n : ℕ) {h : ℂ → ℂ} (hh : ContDiff ℝ 1 h) (hc : HasCompactSupport h)
    (v : ℂ) : dirDeriv v (mollify n h) = mollify n (dirDeriv v h) := by
  funext x
  have hd := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    ((moll n).integrable_normed (μ := volume)).locallyIntegrable hh x
  simp only [dirDeriv, mollify]
  rw [hd.fderiv]
  exact convolution_precompR_apply _ ((moll n).integrable_normed (μ := volume)).locallyIntegrable
    (hc.fderiv ℝ) (hh.continuous_fderiv one_ne_zero) x v

/-- Dominated convergence for the pairing of a locally integrable function with mollified
continuous compactly supported functions. -/
theorem tendsto_integral_mul_mollify {w h : ℂ → ℂ} (hw : LocallyIntegrable w)
    (hh : Continuous h) (hc : HasCompactSupport h) :
    Tendsto (fun n => ∫ x, w x * mollify n h x) atTop (𝓝 (∫ x, w x * h x)) := by
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuous hh
  set K := cthickening 1 (tsupport h) with hKdef
  have hK : IsCompact K := hc.isCompact.cthickening
  refine tendsto_integral_of_dominated_convergence
    (K.indicator fun x => 3 * M * ‖w x‖) (fun n => ?_) ?_ (fun n => ?_) ?_
  · exact hw.aestronglyMeasurable.mul (continuous_mollify n hh).aestronglyMeasurable
  · rw [integrable_indicator_iff hK.measurableSet]
    exact (hw.integrableOn_isCompact hK).norm.const_mul _
  · refine Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx, norm_mul]
      have h3 := norm_mollify_le n hh hM x
      have h0 : 0 ≤ ‖w x‖ := norm_nonneg _
      nlinarith
    · rw [indicator_of_notMem hx, mollify_eq_zero n h hx]
      simp
  · exact Eventually.of_forall fun x => (tendsto_mollify hh x).const_mul (w x)

/-- A locally integrable function times a continuous compactly supported one is integrable. -/
theorem integrable_mul_of_hasCompactSupport {w a : ℂ → ℂ} (hw : LocallyIntegrable w)
    (ha : Continuous a) (hc : HasCompactSupport a) : Integrable (fun x => w x * a x) := by
  have := hw.integrable_smul_right_of_hasCompactSupport ha hc
  simpa [smul_eq_mul] using this

/-- **Weak derivatives tested against `C¹` compactly supported functions.** -/
theorem integral_mul_dirDeriv_of_contDiff_one {u g : ℂ → ℂ} {v : ℂ} (hu : LocallyIntegrable u)
    (hg : LocallyIntegrable g) (h : HasWeakDerivOn univ [v] u g) {ψ : ℂ → ℂ}
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, u x * dirDeriv v ψ x = - ∫ x, g x * ψ x := by
  have hdc : Continuous (dirDeriv v ψ) :=
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdcs : HasCompactSupport (dirDeriv v ψ) := by
    have : dirDeriv v ψ = (fun L : ℂ →L[ℝ] ℂ => L v) ∘ fderiv ℝ ψ := rfl
    rw [this]
    exact (hψc.fderiv ℝ).comp_left (by simp)
  have hn : ∀ n, ∫ x, u x * mollify n (dirDeriv v ψ) x = - ∫ x, g x * mollify n ψ x := by
    intro n
    have ht : IsTestFn univ (mollify n ψ) :=
      ⟨contDiff_mollify n hψ.continuous, hasCompactSupport_mollify n hψc, subset_univ _⟩
    have := h _ ht
    simp only [iterDirDeriv_cons, iterDirDeriv_nil, List.length_singleton, pow_one,
      neg_one_mul] at this
    rw [dirDeriv_mollify n hψ hψc] at this
    exact this
  have h1 := tendsto_integral_mul_mollify hu hdc hdcs
  have h2 := (tendsto_integral_mul_mollify hg hψ.continuous hψc).neg
  simp_rw [← hn] at h2
  exact tendsto_nhds_unique h1 h2

end NonUniqueEuler.Sob.LeibnizAux
