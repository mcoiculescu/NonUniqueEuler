import NonUniqueEuler.Defs.Sec3.Auxiliary
import NonUniqueEuler.I.Infra.ConvMinkowski.Young
import NonUniqueEuler.H.Sec3.Transport.MollifyLp.Kernel
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Proof: spatial mollification in `L^p` (bound and convergence)

Proof of `I/Sec3/Transport/MollifyLp.lean` (the standard facts on mollifiers used in the proof of
`lem:transport`, `03_compactness.tex:503-523`, with the notation of `03_compactness.tex:27-30`).

* `memLp_mollify`: `|g ⋆ ρ_ε| ≤ |ρ_ε| ⋆ |g|` pointwise (`MollifyLpH.enorm_mollify_le`), Young's
  inequality `‖|ρ_ε| ⋆ |g|‖_p ≤ ‖ρ_ε‖₁ ‖g‖_p` (`Conv.eLpNorm_convAbs_le`) and `‖ρ_ε‖₁ = 1`;
  measurability from the continuity of `g ⋆ ρ_ε` for `g ∈ L¹_loc`.
* `tendsto_eLpNorm_mollify_sub`: the `η/3` argument of the interface's proof sketch. For a
  continuous compactly supported `h`, `h ⋆ ρ_ε - h` is supported in the compact
  `cthickening 1 (tsupport h)` for `ε ≤ 1` and is uniformly small (uniform continuity and
  `MollifyLpH.dist_mollify_le`), whence `eventually_eLpNorm_mollify_sub_le_of_continuous`
  (Mathlib's `eLpNorm_sub_le_of_dist_bdd`). A general `g ∈ L^p` is approximated by such an `h`
  (`MemLp.exists_hasCompactSupport_eLpNorm_sub_le`), and `‖(g - h) ⋆ ρ_ε‖_p ≤ ‖g - h‖_p` by
  `memLp_mollify`.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.Weak

/-- Young's inequality for the mollifier (`03_compactness.tex:27-30`): for `1 ≤ p ≤ ∞`,
`g ∈ L^p` implies `g ⋆ ρ_ε ∈ L^p` with `‖g ⋆ ρ_ε‖_p ≤ ‖g‖_p`. -/
theorem memLp_mollify {ρ : ℂ → ℝ} (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) {p : ℝ≥0∞}
    (hp : 1 ≤ p) {g : ℂ → ℝ} (hg : MemLp g p volume) :
    MemLp (mollify ρ ε g) p volume ∧ eLpNorm (mollify ρ ε g) p volume ≤ eLpNorm g p volume := by
  have hbound : eLpNorm (mollify ρ ε g) p volume ≤ eLpNorm g p volume := by
    calc eLpNorm (mollify ρ ε g) p volume
        ≤ eLpNorm (Conv.convAbs (scaled ρ ε) g) p volume :=
          eLpNorm_mono_enorm fun x =>
            (MollifyLpH.enorm_mollify_le ρ ε g x).trans_eq (enorm_eq_self _).symm
      _ ≤ (∫⁻ z, ‖scaled ρ ε z‖ₑ) * eLpNorm g p volume :=
          Conv.eLpNorm_convAbs_le (MollifyLpH.continuous_scaled hρ ε).aestronglyMeasurable
            hg.aestronglyMeasurable hp
      _ = eLpNorm g p volume := by rw [MollifyLpH.lintegral_enorm_scaled hρ hε.ne', one_mul]
  exact ⟨⟨(MollifyLpH.continuous_mollify hρ hε.ne'
    (hg.locallyIntegrable hp)).aestronglyMeasurable, hbound.trans_lt hg.eLpNorm_lt_top⟩, hbound⟩

/-- For a continuous compactly supported `h` and `p < ∞`, `‖h ⋆ ρ_ε - h‖_p ≤ η` for all small
`ε > 0`. -/
theorem MollifyLpH.eventually_eLpNorm_mollify_sub_le_of_continuous {ρ : ℂ → ℝ} (hρ : IsMollifier ρ)
    {p : ℝ≥0∞} (hp' : p ≠ ∞) {h : ℂ → ℝ} (hc : Continuous h) (hs : HasCompactSupport h)
    {η : ℝ≥0∞} (hη : 0 < η) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), eLpNorm (fun x => mollify ρ ε h x - h x) p volume ≤ η := by
  have hS : IsCompact (cthickening 1 (tsupport h)) := hs.isCompact.cthickening
  have hM : volume (cthickening 1 (tsupport h)) ^ (1 / p.toReal) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) hS.measure_lt_top.ne
  obtain ⟨c, hc0, hcM⟩ := ENNReal.exists_nnreal_pos_mul_lt hM hη.ne'
  obtain ⟨δ, hδ, hδh⟩ :=
    Metric.uniformContinuous_iff.1 (hs.uniformContinuous_of_continuous hc) (c : ℝ) hc0
  filter_upwards [Ioo_mem_nhdsGT (lt_min hδ one_pos)] with ε hε
  obtain ⟨hε0, hε1⟩ := hε
  have hmh : AEStronglyMeasurable h volume := hc.aestronglyMeasurable
  refine (eLpNorm_sub_le_of_dist_bdd volume hp' (s := cthickening 1 (tsupport h))
    isClosed_cthickening.measurableSet c.coe_nonneg ?_ ?_
    ((subset_tsupport h).trans (self_subset_cthickening _))).trans ?_
  · intro x
    refine MollifyLpH.dist_mollify_le hρ hε0 hmh c.coe_nonneg fun y hy => (hδh ?_).le
    exact (mem_ball.1 hy).trans (hε1.trans_le (min_le_left _ _))
  · intro x hx
    by_contra hxS
    apply hx
    have hd := MollifyLpH.dist_mollify_le hρ hε0 hmh (x₀ := x) (z₀ := 0) le_rfl
      fun y hy => by
        rw [dist_zero_right, norm_le_zero_iff]
        by_contra hy0
        exact hxS (mem_cthickening_of_dist_le x y 1 _ (subset_tsupport h hy0)
          (by rw [dist_comm]; exact (mem_ball.1 hy).le.trans (hε1.le.trans (min_le_right _ _))))
    exact dist_le_zero.1 hd
  · rw [ENNReal.ofReal_coe_nnreal]
    exact hcM.le

/-- Mollifications converge in `L^p`, `1 ≤ p < ∞` (`03_compactness.tex:503-523`):
`‖g ⋆ ρ_ε - g‖_p → 0` as `ε → 0⁺`. -/
theorem tendsto_eLpNorm_mollify_sub {ρ : ℂ → ℝ} (hρ : IsMollifier ρ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hp' : p ≠ ∞) {g : ℂ → ℝ} (hg : MemLp g p volume) :
    Tendsto (fun ε : ℝ => eLpNorm (fun x => mollify ρ ε g x - g x) p volume) (𝓝[>] 0)
      (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  have hη3 : η / 3 ≠ 0 := ENNReal.div_ne_zero.2 ⟨hη.ne', ENNReal.ofNat_ne_top⟩
  obtain ⟨h, hh_supp, hgh, hh_cont, hh_mem⟩ := hg.exists_hasCompactSupport_eLpNorm_sub_le hp' hη3
  have hgl : LocallyIntegrable g volume := hg.locallyIntegrable hp
  have hhl : LocallyIntegrable h volume := hh_mem.locallyIntegrable hp
  filter_upwards [MollifyLpH.eventually_eLpNorm_mollify_sub_le_of_continuous hρ hp' hh_cont hh_supp
    (pos_iff_ne_zero.2 hη3), self_mem_nhdsWithin] with ε hεh hε0
  have hε : 0 < ε := hε0
  have heq : (fun x => mollify ρ ε g x - g x) = fun x =>
      (mollify ρ ε (fun y => g y - h y) x + (mollify ρ ε h x - h x)) + (h x - g x) := by
    funext x
    rw [MollifyLpH.mollify_sub hρ hε.ne' hgl hhl x]
    ring
  have m1 : AEStronglyMeasurable (mollify ρ ε (fun y => g y - h y)) volume :=
    (MollifyLpH.continuous_mollify hρ hε.ne' (hgl.sub hhl)).aestronglyMeasurable
  have m2 : AEStronglyMeasurable (fun x => mollify ρ ε h x - h x) volume :=
    ((MollifyLpH.continuous_mollify hρ hε.ne' hhl).sub hh_cont).aestronglyMeasurable
  have m3 : AEStronglyMeasurable (fun x => h x - g x) volume :=
    hh_mem.aestronglyMeasurable.sub hg.aestronglyMeasurable
  have h1 : eLpNorm (mollify ρ ε (fun y => g y - h y)) p volume ≤ η / 3 :=
    (memLp_mollify hρ hε hp (hg.sub hh_mem)).2.trans hgh
  have h3 : eLpNorm (fun x => h x - g x) p volume ≤ η / 3 := by
    have : eLpNorm (h - g) p volume ≤ η / 3 := by rw [eLpNorm_sub_comm]; exact hgh
    exact this
  rw [heq]
  calc eLpNorm (fun x => (mollify ρ ε (fun y => g y - h y) x + (mollify ρ ε h x - h x)) +
        (h x - g x)) p volume
      ≤ eLpNorm (fun x => mollify ρ ε (fun y => g y - h y) x + (mollify ρ ε h x - h x)) p volume
          + eLpNorm (fun x => h x - g x) p volume := eLpNorm_add_le (m1.add m2) m3 hp
    _ ≤ (eLpNorm (mollify ρ ε (fun y => g y - h y)) p volume
          + eLpNorm (fun x => mollify ρ ε h x - h x) p volume)
          + eLpNorm (fun x => h x - g x) p volume := by
        gcongr
        exact eLpNorm_add_le m1 m2 hp
    _ ≤ η / 3 + η / 3 + η / 3 := by gcongr
    _ = η := ENNReal.add_thirds η

end NonUniqueEuler.Weak
