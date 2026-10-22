import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import NonUniqueEuler.H.Infra.Sobolev.Density.Conv
import NonUniqueEuler.I.Infra.ConvMinkowski.Young

/-!
# Helper for `P/Infra/Sobolev/Density`: `L²` convergence of mollifications

* `tendsto_eLpNorm_two_of_dominated`: dominated convergence in `L²`;
* `eLpNorm_conv_normed_le`: `‖ρ ⋆ g‖₂ ≤ ‖g‖₂` for a normed bump `ρ` (Young's inequality
  `Conv.eLpNorm_convAbs_le`, `I/Infra/ConvMinkowski/Young.lean`);
* `tendsto_eLpNorm_conv_sub`: `ρ_n ⋆ g → g` in `L²` for `g ∈ L²` and normed bumps `ρ_n` whose
  radii tend to `0` (first for continuous compactly supported `g`, by dominated convergence, then
  by density, `MemLp.exists_hasCompactSupport_eLpNorm_sub_le`, and an `ε/3` argument).
-/

noncomputable section

open MeasureTheory Set Filter Metric Function
open scoped ENNReal ContDiff Topology Convolution

namespace NonUniqueEuler.Sob.DensityAux

/-- Dominated convergence in `L²`. -/
theorem tendsto_eLpNorm_two_of_dominated {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℂ} {G : α → ℝ} (hF : ∀ n, AEStronglyMeasurable (F n) μ) (hG : MemLp G 2 μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ G x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F n) 2 μ) atTop (𝓝 0) := by
  have h2 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2' : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h2 h2']
  have hlin : Tendsto (fun n => ∫⁻ x, ‖F n x‖ₑ ^ (2 : ℝ≥0∞).toReal ∂μ) atTop (𝓝 0) := by
    have key := tendsto_lintegral_of_dominated_convergence'
      (F := fun n x => ‖F n x‖ₑ ^ (2 : ℝ≥0∞).toReal)
      (fun x => ‖G x‖ₑ ^ (2 : ℝ≥0∞).toReal) (f := fun _ => 0)
      (fun n => (hF n).enorm.pow_const _) ?_ ?_ ?_
    · simpa using key
    · intro n
      filter_upwards [hbound n] with x hx
      have hle : ‖F n x‖ₑ ≤ ‖G x‖ₑ := by
        rw [enorm_le_iff_norm_le]
        exact hx.trans (le_abs_self _)
      exact ENNReal.rpow_le_rpow hle (by norm_num)
    · exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top h2 h2' hG.eLpNorm_lt_top).ne
    · filter_upwards [hlim] with x hx
      have h1 : Tendsto (fun n => ‖F n x‖ₑ) atTop (𝓝 0) := by
        simpa [Function.comp_def] using (continuous_enorm.tendsto 0).comp hx
      have h3 := ((ENNReal.continuous_rpow_const (y := (2 : ℝ≥0∞).toReal)).tendsto 0).comp h1
      simpa [Function.comp_def] using h3
  have key := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ≥0∞).toReal)).tendsto 0).comp hlin
  simpa [Function.comp_def] using key

theorem enorm_conv_le (ρ : ℂ → ℝ) (g : ℂ → ℂ) (x : ℂ) : ‖conv ρ g x‖ₑ ≤ Conv.convAbs ρ g x := by
  rw [Conv.convAbs_eq_lintegral_sub, conv_eq_integral]
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  simp_rw [enorm_smul]

/-- Young: `‖ρ ⋆ g‖₂ ≤ ‖ρ‖₁ ‖g‖₂`. -/
theorem eLpNorm_conv_le {ρ : ℂ → ℝ} (hρ : AEStronglyMeasurable ρ volume) {g : ℂ → ℂ}
    (hg : AEStronglyMeasurable g volume) :
    eLpNorm (conv ρ g) 2 volume ≤ (∫⁻ z, ‖ρ z‖ₑ) * eLpNorm g 2 volume := by
  refine (eLpNorm_mono_enorm fun x => ?_).trans (Conv.eLpNorm_convAbs_le hρ hg (by norm_num))
  rw [enorm_eq_self]
  exact enorm_conv_le ρ g x

theorem lintegral_enorm_normed (b : ContDiffBump (0 : ℂ)) :
    ∫⁻ z, ‖b.normed volume z‖ₑ = 1 := by
  have h := b.integral_normed (μ := volume)
  rw [← ENNReal.ofReal_one, ← h, ofReal_integral_eq_lintegral_ofReal b.integrable_normed
    (Eventually.of_forall b.nonneg_normed)]
  refine lintegral_congr fun z => ?_
  rw [Real.enorm_of_nonneg (b.nonneg_normed z)]

theorem eLpNorm_conv_normed_le (b : ContDiffBump (0 : ℂ)) {g : ℂ → ℂ}
    (hg : AEStronglyMeasurable g volume) :
    eLpNorm (conv (b.normed volume) g) 2 volume ≤ eLpNorm g 2 volume := by
  simpa [lintegral_enorm_normed] using
    eLpNorm_conv_le (b.continuous_normed (μ := volume)).aestronglyMeasurable hg

theorem memLp_conv_normed (b : ContDiffBump (0 : ℂ)) {g : ℂ → ℂ} (hg : MemLp g 2 volume) :
    MemLp (conv (b.normed volume) g) 2 volume :=
  ⟨(continuous_conv b.continuous_normed b.hasCompactSupport_normed
      (hg.locallyIntegrable (by norm_num))).aestronglyMeasurable,
    (eLpNorm_conv_normed_le b hg.1).trans_lt hg.2⟩

/-- Linearity of the mollification. -/
theorem conv_sub {ρ : ℂ → ℝ} (hρc : Continuous ρ) (hρ : HasCompactSupport ρ) {f g : ℂ → ℂ}
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume) :
    conv ρ (f - g) = conv ρ f - conv ρ g := by
  funext x
  have h1 := hρ.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hρc hf x
  have h2 := hρ.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hρc hg x
  simp only [conv, convolution_def, Pi.sub_apply, map_sub]
  exact integral_sub h1 h2

theorem norm_conv_normed_le (b : ContDiffBump (0 : ℂ)) {h : ℂ → ℂ} {C : ℝ}
    (hC : ∀ x, ‖h x‖ ≤ C) (x : ℂ) : ‖conv (b.normed volume) h x‖ ≤ C := by
  rw [conv_eq_integral]
  have hint : Integrable (fun t => b.normed volume t * C) volume :=
    b.integrable_normed.mul_const C
  calc ‖∫ t, b.normed volume t • h (x - t)‖ ≤ ∫ t, b.normed volume t * C :=
        norm_integral_le_of_norm_le hint (Eventually.of_forall fun t => by
          rw [norm_smul, Real.norm_of_nonneg (b.nonneg_normed t)]
          exact mul_le_mul_of_nonneg_left (hC _) (b.nonneg_normed t))
    _ = C := by rw [integral_mul_const, b.integral_normed, one_mul]

/-- `ρ_n ⋆ h → h` in `L²` for continuous compactly supported `h`. -/
theorem tendsto_eLpNorm_conv_sub_of_continuous {b : ℕ → ContDiffBump (0 : ℂ)}
    (hb : Tendsto (fun n => (b n).rOut) atTop (𝓝 0)) (hb1 : ∀ n, (b n).rOut ≤ 1)
    {h : ℂ → ℂ} (hc : Continuous h) (hh : HasCompactSupport h) :
    Tendsto (fun n => eLpNorm (conv ((b n).normed volume) h - h) 2 volume) atTop (𝓝 0) := by
  set S : Set ℂ := cthickening 1 (tsupport h) with hSdef
  have hS : IsCompact S := IsCompact.cthickening hh
  obtain ⟨C, hC⟩ := hc.norm.bddAbove_range_of_hasCompactSupport hh.norm
  have hC' : ∀ x, ‖h x‖ ≤ C := fun x => hC ⟨x, rfl⟩
  refine tendsto_eLpNorm_two_of_dominated (G := S.indicator (fun _ => C + C)) (fun n => ?_)
    (memLp_indicator_const 2 hS.measurableSet (C + C) (Or.inr hS.measure_lt_top.ne))
    (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
  · exact ((continuous_conv (b n).continuous_normed (b n).hasCompactSupport_normed
      (hc.locallyIntegrable)).sub hc).aestronglyMeasurable
  · by_cases hx : x ∈ S
    · rw [indicator_of_mem hx, Pi.sub_apply]
      exact (norm_sub_le _ _).trans (add_le_add (norm_conv_normed_le (b n) hC' x) (hC' x))
    · rw [indicator_of_notMem hx, Pi.sub_apply]
      have hxh : x ∉ tsupport h := fun hx' => hx (self_subset_cthickening _ hx')
      have hsupp : support ((b n).normed volume) ⊆ ball 0 (b n).rOut :=
        (b n).support_normed_eq.subset
      have hconv : tsupport (conv ((b n).normed volume) h) ⊆ S :=
        (tsupport_conv_subset hsupp (K := tsupport h) (Eventually.of_forall fun y hy =>
          image_eq_zero_of_notMem_tsupport hy)).trans (cthickening_mono (hb1 n) _)
      rw [image_eq_zero_of_notMem_tsupport hxh,
        image_eq_zero_of_notMem_tsupport (fun hx' => hx (hconv hx')), sub_zero, norm_zero]
  · have := ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) hb hc x
    rw [← tendsto_sub_nhds_zero_iff] at this
    simpa [conv] using this

/-- `ρ_n ⋆ g → g` in `L²` for `g ∈ L²`. -/
theorem tendsto_eLpNorm_conv_sub {b : ℕ → ContDiffBump (0 : ℂ)}
    (hb : Tendsto (fun n => (b n).rOut) atTop (𝓝 0)) (hb1 : ∀ n, (b n).rOut ≤ 1)
    {g : ℂ → ℂ} (hg : MemLp g 2 volume) :
    Tendsto (fun n => eLpNorm (conv ((b n).normed volume) g - g) 2 volume) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases hεtop : ε = ⊤
  · exact Eventually.of_forall fun n => hεtop ▸ le_top
  have hε3 : ε / 3 ≠ 0 := (ENNReal.div_pos hε.ne' (by norm_num)).ne'
  obtain ⟨h, hhc, hgh, hcont, hhL⟩ :=
    hg.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num) hε3
  have hconv := (ENNReal.tendsto_nhds_zero.1
    (tendsto_eLpNorm_conv_sub_of_continuous hb hb1 hcont hhc)) (ε / 3) (pos_iff_ne_zero.2 hε3)
  filter_upwards [hconv] with n hn
  set ρ := (b n).normed volume with hρdef
  have hgl : LocallyIntegrable g volume := hg.locallyIntegrable (by norm_num)
  have hhl : LocallyIntegrable h volume := hcont.locallyIntegrable
  have hdec : conv ρ g - g = conv ρ (g - h) + (conv ρ h - h) + (h - g) := by
    rw [conv_sub (b n).continuous_normed (b n).hasCompactSupport_normed hgl hhl]
    abel
  have hm1 : AEStronglyMeasurable (conv ρ (g - h)) volume :=
    (continuous_conv (b n).continuous_normed (b n).hasCompactSupport_normed
      (hgl.sub hhl)).aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (conv ρ h - h) volume :=
    ((continuous_conv (b n).continuous_normed (b n).hasCompactSupport_normed
      hhl).sub hcont).aestronglyMeasurable
  have hm3 : AEStronglyMeasurable (h - g) volume := hcont.aestronglyMeasurable.sub hg.1
  rw [hdec]
  calc eLpNorm (conv ρ (g - h) + (conv ρ h - h) + (h - g)) 2 volume
      ≤ eLpNorm (conv ρ (g - h) + (conv ρ h - h)) 2 volume + eLpNorm (h - g) 2 volume :=
        eLpNorm_add_le (hm1.add hm2) hm3 (by norm_num)
    _ ≤ eLpNorm (conv ρ (g - h)) 2 volume + eLpNorm (conv ρ h - h) 2 volume +
          eLpNorm (h - g) 2 volume := by
        gcongr
        exact eLpNorm_add_le hm1 hm2 (by norm_num)
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by
        gcongr
        · exact (eLpNorm_conv_normed_le (b n) (hg.1.sub hcont.aestronglyMeasurable)).trans hgh
        · rw [eLpNorm_sub_comm]
          exact hgh
    _ = ε := ENNReal.add_thirds ε

end NonUniqueEuler.Sob.DensityAux
