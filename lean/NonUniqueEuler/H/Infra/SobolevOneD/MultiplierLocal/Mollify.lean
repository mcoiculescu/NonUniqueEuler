import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import NonUniqueEuler.Defs.Infra.Sobolev

/-!
# Helper for `P/Infra/SobolevOneD/MultiplierLocal`: weak derivatives on the line tested against `C¹`
functions

For an open set `V ⊆ ℝ`, a weak derivative `g = u'` on `V` (tested against smooth compactly
supported functions with support in `V`) can be tested against `C¹` compactly supported
functions `ψ` with `tsupport ψ ⊆ V`: `∫ u ψ' = - ∫ g ψ`
(`integral_mul_deriv_of_contDiff_one`).

Proof (adapted from `H/Infra/Sobolev/Leibniz/Mollify.lean`, the plane case): choose `δ > 0` with
`cthickening δ (tsupport ψ) ⊆ V`; mollify `ψ` with normed bump functions `ρ_n`
(`rOut = δ/(n+1)`); `ρ_n ⋆ ψ` is a test function supported in `V`,
`(ρ_n ⋆ ψ)' = ρ_n ⋆ ψ'`, the mollified functions are uniformly bounded, vanish outside
`cthickening δ (tsupport ψ)` and converge pointwise; dominated convergence passes to the limit
(after replacing `u`, `g` by their indicators on that compact set, which are integrable).

Copied verbatim from `H/Infra/SobolevOneD/Multiplier/Mollify.lean` (helper of the proof of
`secNormSq_mul_le`), with the namespace renamed to `NonUniqueEuler.Sob.MultLocAux` so that
both proofs can coexist in the full library (the import rules forbid importing another proof's
helpers).
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal ContDiff Topology Convolution

namespace NonUniqueEuler.Sob.MultLocAux

/-- The mollifiers `ρ_n` on the line, with `rOut = δ/(n+1)`. -/
def moll {δ : ℝ} (hδ : 0 < δ) (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := δ / (2 * ((n : ℝ) + 1))
  rOut := δ / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [div_lt_div_iff_of_pos_left hδ (by positivity) h]
    linarith

theorem moll_rOut_tendsto {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => (moll hδ n).rOut) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul δ
  rw [mul_zero] at h
  refine h.congr fun n => ?_
  show δ * (1 / ((n : ℝ) + 1)) = δ / ((n : ℝ) + 1)
  ring

theorem moll_rOut_le {δ : ℝ} (hδ : 0 < δ) (n : ℕ) : (moll hδ n).rOut ≤ δ := by
  show δ / ((n : ℝ) + 1) ≤ δ
  rw [div_le_iff₀ (by positivity)]
  nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

/-- Mollification `ρ_n ⋆ h`. -/
def mollify {δ : ℝ} (hδ : 0 < δ) (n : ℕ) (h : ℝ → ℂ) : ℝ → ℂ :=
  (moll hδ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h

theorem contDiff_mollify {δ : ℝ} (hδ : 0 < δ) (n : ℕ) {h : ℝ → ℂ} (hh : Continuous h) :
    ContDiff ℝ ∞ (mollify hδ n h) :=
  (moll hδ n).hasCompactSupport_normed.contDiff_convolution_left _
    (moll hδ n).contDiff_normed hh.locallyIntegrable

theorem continuous_mollify {δ : ℝ} (hδ : 0 < δ) (n : ℕ) {h : ℝ → ℂ} (hh : Continuous h) :
    Continuous (mollify hδ n h) :=
  (contDiff_mollify hδ n hh).continuous

theorem hasCompactSupport_mollify {δ : ℝ} (hδ : 0 < δ) (n : ℕ) {h : ℝ → ℂ}
    (hc : HasCompactSupport h) : HasCompactSupport (mollify hδ n h) :=
  (moll hδ n).hasCompactSupport_normed.convolution _ hc

theorem mollify_eq_zero {δ : ℝ} (hδ : 0 < δ) (n : ℕ) (h : ℝ → ℂ) {x : ℝ}
    (hx : x ∉ cthickening δ (tsupport h)) : mollify hδ n h x = 0 := by
  by_contra hne
  have hmem : x ∈ Function.support (mollify hδ n h) := hne
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) hmem
  rw [(moll hδ n).support_normed_eq] at ha
  apply hx
  refine mem_cthickening_of_dist_le _ b δ _ (subset_tsupport _ hb) ?_
  have : dist (a + b) b = ‖a‖ := by simp [dist_eq_norm]
  rw [this]
  have := mem_ball_zero_iff.1 ha
  exact this.le.trans (moll_rOut_le hδ n)

theorem tsupport_mollify_subset {δ : ℝ} (hδ : 0 < δ) (n : ℕ) (h : ℝ → ℂ) :
    tsupport (mollify hδ n h) ⊆ cthickening δ (tsupport h) := by
  refine closure_minimal (fun x hx => ?_) isClosed_cthickening
  by_contra hxK
  exact hx (mollify_eq_zero hδ n h hxK)

theorem norm_mollify_le {δ : ℝ} (hδ : 0 < δ) (n : ℕ) {h : ℝ → ℂ} (hh : Continuous h) {M : ℝ}
    (hM : ∀ y, ‖h y‖ ≤ M) (x : ℝ) : ‖mollify hδ n h x‖ ≤ 3 * M := by
  have h1 : dist (mollify hδ n h x) (h x) ≤ 2 * M := by
    refine (moll hδ n).dist_normed_convolution_le hh.aestronglyMeasurable fun y _ => ?_
    calc dist (h y) (h x) ≤ ‖h y‖ + ‖h x‖ := dist_le_norm_add_norm _ _
      _ ≤ 2 * M := by linarith [hM y, hM x]
  calc ‖mollify hδ n h x‖ ≤ ‖h x‖ + dist (mollify hδ n h x) (h x) := by
        rw [dist_eq_norm]
        exact norm_le_insert' _ _
    _ ≤ 3 * M := by linarith [hM x]

theorem tendsto_mollify {δ : ℝ} (hδ : 0 < δ) {h : ℝ → ℂ} (hh : Continuous h) (x : ℝ) :
    Tendsto (fun n => mollify hδ n h x) atTop (𝓝 (h x)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous (moll_rOut_tendsto hδ) hh x

/-- `(ρ_n ⋆ h)' = ρ_n ⋆ h'` for `h` of class `C¹` with compact support. -/
theorem deriv_mollify {δ : ℝ} (hδ : 0 < δ) (n : ℕ) {h : ℝ → ℂ} (hh : ContDiff ℝ 1 h)
    (hc : HasCompactSupport h) : deriv (mollify hδ n h) = mollify hδ n (deriv h) := by
  funext x
  exact (hc.hasDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    ((moll hδ n).integrable_normed (μ := volume)).locallyIntegrable hh x).deriv

/-- Dominated convergence for the pairing of an integrable function with mollified continuous
compactly supported functions. -/
theorem tendsto_integral_mul_mollify {δ : ℝ} (hδ : 0 < δ) {w h : ℝ → ℂ} (hw : Integrable w)
    (hh : Continuous h) (hc : HasCompactSupport h) :
    Tendsto (fun n => ∫ x, w x * mollify hδ n h x) atTop (𝓝 (∫ x, w x * h x)) := by
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuous hh
  refine tendsto_integral_of_dominated_convergence
    (fun x => 3 * M * ‖w x‖) (fun n => ?_) (hw.norm.const_mul _) (fun n => ?_) ?_
  · exact hw.aestronglyMeasurable.mul (continuous_mollify hδ n hh).aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    rw [norm_mul]
    have h3 := norm_mollify_le hδ n hh hM x
    have h0 : 0 ≤ ‖w x‖ := norm_nonneg _
    nlinarith
  · exact Eventually.of_forall fun x => (tendsto_mollify hδ hh x).const_mul (w x)

/-- A function locally integrable on `V`, times a continuous compactly supported function with
support in `V`, is integrable. -/
theorem integrable_mul_of_tsupport {V : Set ℝ} {w a : ℝ → ℂ} (hw : LocallyIntegrableOn w V)
    (ha : Continuous a) (hc : HasCompactSupport a) (haV : tsupport a ⊆ V) :
    Integrable (fun x => w x * a x) := by
  have h1 : IntegrableOn w (tsupport a) := hw.integrableOn_compact_subset haV hc
  have h2 : IntegrableOn (fun x => w x * a x) (tsupport a) :=
    h1.mul_continuousOn ha.continuousOn hc
  refine h2.integrable_of_forall_notMem_eq_zero fun x hx => ?_
  simp [image_eq_zero_of_notMem_tsupport hx]

/-- **Weak derivatives on `V ⊆ ℝ` tested against `C¹` compactly supported functions with support
in `V`.** -/
theorem integral_mul_deriv_of_contDiff_one {V : Set ℝ} (hV : IsOpen V) {u g : ℝ → ℂ}
    (hu : LocallyIntegrableOn u V) (hg : LocallyIntegrableOn g V)
    (h : HasWeakDerivOn V [1] u g) {ψ : ℝ → ℂ} (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) (hψV : tsupport ψ ⊆ V) :
    ∫ x, u x * deriv ψ x = - ∫ x, g x * ψ x := by
  obtain ⟨δ, hδ, hδV⟩ := hψc.exists_cthickening_subset_open hV hψV
  set K := cthickening δ (tsupport ψ) with hKdef
  have hKc : IsCompact K := hψc.cthickening
  have hKm : MeasurableSet K := isClosed_cthickening.measurableSet
  have hu' : Integrable (K.indicator u) :=
    (integrable_indicator_iff hKm).2 (hu.integrableOn_compact_subset hδV hKc)
  have hg' : Integrable (K.indicator g) :=
    (integrable_indicator_iff hKm).2 (hg.integrableOn_compact_subset hδV hKc)
  have hdc : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
  have hdcs : HasCompactSupport (deriv ψ) := hψc.deriv
  have hdK : cthickening δ (tsupport (deriv ψ)) ⊆ K :=
    cthickening_subset_of_subset δ tsupport_deriv_subset
  -- the indicator does not change the pairings with functions vanishing outside `K`
  have hind : ∀ (w f : ℝ → ℂ), (∀ x, x ∉ K → f x = 0) →
      ∫ x, w x * f x = ∫ x, K.indicator w x * f x := by
    intro w f hf
    congr 1
    funext x
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx]
    · rw [hf x hx]
      simp
  have hn : ∀ n, ∫ x, K.indicator u x * mollify hδ n (deriv ψ) x =
      - ∫ x, K.indicator g x * mollify hδ n ψ x := by
    intro n
    have ht : IsTestFn V (mollify hδ n ψ) :=
      ⟨contDiff_mollify hδ n hψ.continuous, hasCompactSupport_mollify hδ n hψc,
        (tsupport_mollify_subset hδ n ψ).trans hδV⟩
    have := h _ ht
    simp only [iterDirDeriv_cons, iterDirDeriv_nil, List.length_singleton, pow_one,
      neg_one_mul] at this
    have e : dirDeriv (1 : ℝ) (mollify hδ n ψ) = mollify hδ n (deriv ψ) := by
      rw [← deriv_mollify hδ n hψ hψc]
      rfl
    rw [e] at this
    rw [← hind u _ (fun x hx => mollify_eq_zero hδ n _ (fun h' => hx (hdK h'))),
      ← hind g _ (fun x hx => mollify_eq_zero hδ n _ hx)]
    exact this
  have h1 := tendsto_integral_mul_mollify hδ hu' hdc hdcs
  have h2 := (tendsto_integral_mul_mollify hδ hg' hψ.continuous hψc).neg
  simp_rw [← hn] at h2
  have e := tendsto_nhds_unique h1 h2
  rw [hind u _ (fun x hx => image_eq_zero_of_notMem_tsupport
      (fun h' => hx (hdK (self_subset_cthickening _ h')))),
    hind g _ (fun x hx => image_eq_zero_of_notMem_tsupport
      (fun h' => hx (self_subset_cthickening _ h')))]
  exact e

end NonUniqueEuler.Sob.MultLocAux
