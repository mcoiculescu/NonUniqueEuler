import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import NonUniqueEuler.Defs.Sec2.Conventions

/-!
# Proof: weakly divergence-free fields tested against `C¹_c` functions

Proof of `I/Infra/Sobolev/DivFreeC1.lean` (used at `03_compactness.tex:505-508`).

Mollify `g` with normed bump functions `ρ_n` (`rOut = 1/(n+1)`): `φ_n = ρ_n ⋆ g` is a test
function, `Dφ_n = ρ_n ⋆ Dg` (`DivFreeC1Aux.fderiv_mollify`), the `Dφ_n` are bounded by
`3 ‖Dg‖_∞`, vanish outside `cthickening 1 (tsupport g)` and converge pointwise to `Dg`. Dominated
convergence with majorant `3 ‖Dg‖_∞ |v| 1_{K₁}` gives `∫ Dg(x)(v x) = lim ∫ Dφ_n(x)(v x) = 0`.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal ContDiff Topology Convolution

namespace NonUniqueEuler.Prelim

namespace DivFreeC1Aux

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

/-- Mollification `ρ_n ⋆ h` of a function with values in a real Banach space. -/
def mollify {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) (h : ℂ → E) :
    ℂ → E :=
  (moll n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h

theorem contDiff_mollify (n : ℕ) {h : ℂ → ℝ} (hh : Continuous h) :
    ContDiff ℝ ∞ (mollify n h) :=
  (moll n).hasCompactSupport_normed.contDiff_convolution_left _
    (moll n).contDiff_normed hh.locallyIntegrable

theorem hasCompactSupport_mollify (n : ℕ) {h : ℂ → ℝ} (hc : HasCompactSupport h) :
    HasCompactSupport (mollify n h) :=
  (moll n).hasCompactSupport_normed.convolution _ hc

/-- `ρ_n ⋆ h` vanishes outside `cthickening 1 S` when `h` vanishes outside `S`. -/
theorem mollify_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ)
    (h : ℂ → E) {S : Set ℂ} (hS : Function.support h ⊆ S) {x : ℂ}
    (hx : x ∉ cthickening 1 S) : mollify n h x = 0 := by
  by_contra hne
  have hmem : x ∈ Function.support (mollify n h) := hne
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) hmem
  rw [(moll n).support_normed_eq] at ha
  apply hx
  refine mem_cthickening_of_dist_le _ b 1 _ (hS hb) ?_
  have : dist (a + b) b = ‖a‖ := by simp [dist_eq_norm]
  rw [this]
  have := mem_ball_zero_iff.1 ha
  exact this.le.trans (moll_rOut_le_one n)

theorem norm_mollify_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (n : ℕ) {h : ℂ → E} (hh : Continuous h) {M : ℝ}
    (hM : ∀ y, ‖h y‖ ≤ M) (x : ℂ) : ‖mollify n h x‖ ≤ 3 * M := by
  have h1 : dist (mollify n h x) (h x) ≤ 2 * M := by
    refine (moll n).dist_normed_convolution_le hh.aestronglyMeasurable fun y _ => ?_
    calc dist (h y) (h x) ≤ ‖h y‖ + ‖h x‖ := dist_le_norm_add_norm _ _
      _ ≤ 2 * M := by linarith [hM y, hM x]
  calc ‖mollify n h x‖ ≤ ‖h x‖ + dist (mollify n h x) (h x) := by
        rw [dist_eq_norm]
        exact norm_le_insert' _ _
    _ ≤ 3 * M := by linarith [hM x]

theorem tendsto_mollify {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {h : ℂ → E} (hh : Continuous h) (x : ℂ) :
    Tendsto (fun n => mollify n h x) atTop (𝓝 (h x)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous moll_rOut_tendsto hh x

/-- `D(ρ_n ⋆ g) = ρ_n ⋆ Dg` for `g` of class `C¹` with compact support. -/
theorem fderiv_mollify (n : ℕ) {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (x : ℂ) : fderiv ℝ (mollify n g) x = mollify n (fderiv ℝ g) x := by
  have hd := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    ((moll n).integrable_normed (μ := volume)).locallyIntegrable hg x
  simp only [mollify]
  rw [hd.fderiv]
  simp only [convolution_def]
  congr 1

end DivFreeC1Aux

open DivFreeC1Aux in
/-- A weakly divergence-free `v ∈ L¹_loc` satisfies `∫ v·∇g = 0` for every real `g ∈ C¹_c(ℝ²)`
(used at `03_compactness.tex:505-508`). -/
theorem IsWeaklyDivFree.integral_fderiv_eq_zero_of_contDiff_one {v : ℂ → ℂ}
    (hdiv : IsWeaklyDivFree v) (hv : LocallyIntegrable v volume) {g : ℂ → ℝ}
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) :
    Integrable (fun x => fderiv ℝ g x (v x)) ∧ ∫ x, fderiv ℝ g x (v x) = 0 := by
  have hDc : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  obtain ⟨M, hM⟩ := (hgc.fderiv ℝ).exists_bound_of_continuous hDc
  set K := cthickening 1 (tsupport g) with hKdef
  have hK : IsCompact K := hgc.isCompact.cthickening
  -- the mollified test functions
  have htest : ∀ n, Integrable (fun x => fderiv ℝ (mollify n g) x (v x)) ∧
      ∫ x, fderiv ℝ (mollify n g) x (v x) = 0 := fun n =>
    hdiv _ (contDiff_mollify n hg.continuous) (hasCompactSupport_mollify n hgc)
  have hF : ∀ n, (fun x => fderiv ℝ (mollify n g) x (v x)) =
      fun x => mollify n (fderiv ℝ g) x (v x) := fun n => by
    funext x
    rw [fderiv_mollify n hg hgc x]
  -- the majorant
  set bound : ℂ → ℝ := K.indicator fun x => 3 * M * ‖v x‖ with hbound
  have hbi : Integrable bound := by
    rw [hbound, integrable_indicator_iff hK.measurableSet]
    exact (hv.integrableOn_isCompact hK).norm.const_mul _
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hbF : ∀ n x, ‖mollify n (fderiv ℝ g) x (v x)‖ ≤ bound x := by
    intro n x
    by_cases hx : x ∈ K
    · rw [hbound, indicator_of_mem hx]
      have h3 := norm_mollify_le n hDc hM x
      calc ‖mollify n (fderiv ℝ g) x (v x)‖ ≤ ‖mollify n (fderiv ℝ g) x‖ * ‖v x‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ 3 * M * ‖v x‖ := by gcongr
    · rw [hbound, indicator_of_notMem hx,
        mollify_eq_zero n (fderiv ℝ g) (support_fderiv_subset ℝ) hx]
      simp
  have hlim : ∀ x, Tendsto (fun n => mollify n (fderiv ℝ g) x (v x)) atTop
      (𝓝 (fderiv ℝ g x (v x))) := fun x =>
    ((ContinuousLinearMap.apply ℝ ℝ (v x)).continuous.tendsto _).comp (tendsto_mollify hDc x)
  have hmeas : ∀ n, AEStronglyMeasurable (fun x => mollify n (fderiv ℝ g) x (v x)) := by
    intro n
    rw [← hF n]
    exact (htest n).1.aestronglyMeasurable
  have hint : Integrable (fun x => fderiv ℝ g x (v x)) := by
    refine hbi.mono' (aestronglyMeasurable_of_tendsto_ae atTop hmeas
      (Eventually.of_forall hlim)) (Eventually.of_forall fun x => ?_)
    exact le_of_tendsto' ((continuous_norm.tendsto _).comp (hlim x)) fun n => hbF n x
  refine ⟨hint, ?_⟩
  have hT := tendsto_integral_of_dominated_convergence bound hmeas hbi
    (fun n => Eventually.of_forall (hbF n)) (Eventually.of_forall hlim)
  have h0 : ∀ n, ∫ x, mollify n (fderiv ℝ g) x (v x) = 0 := fun n => by
    rw [← hF n]
    exact (htest n).2
  simp_rw [h0] at hT
  exact tendsto_nhds_unique hT tendsto_const_nhds

end NonUniqueEuler.Prelim
