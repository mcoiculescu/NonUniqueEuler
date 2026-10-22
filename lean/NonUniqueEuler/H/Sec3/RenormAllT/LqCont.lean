import NonUniqueEuler.H.Sec3.RenormAllT.Basic
import NonUniqueEuler.I.Infra.LpInterp.Tendsto
import NonUniqueEuler.I.Infra.LpInterp.Interp
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Algebra.Order.Field

/-!
# Helpers for `lem:renorm-all-t`: continuity into `L^q`, `q ∈ [1,2)`

Helper file of `P/Sec3/RenormAllT.lean` (fully proved).

`03_compactness.tex:685-689`: the uniform tail bound eq:tail and the (local) strong continuity
give `ω ∈ C([0,T);L¹)` (`tendsto_eLpNorm_one`: split `ℝ² = B_{2R} ∪ {|x| ≥ 2R}`, Hölder on the
ball, eq:tail outside); interpolation with the bound `‖ω(t) - ω(s)‖₂ ≤ 2B` gives
`ω ∈ C([0,T);L^q)` for `q ∈ [1,2)` (`continuousIntoLpOn_of_one_two`, I-LPINT).
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.Weak.RenormAllTH

/-- The tails `∫_{|x|≥R}|g|` of `g ∈ L¹` tend to `0` as `R → ∞`. -/
theorem tendsto_lintegral_tail {g : ℂ → ℝ} (hg : MemLp g 1 volume) :
    Tendsto (fun R : ℝ => ∫⁻ x in {x : ℂ | R ≤ ‖x‖}, ‖g x‖ₑ) atTop (𝓝 0) := by
  set ν : Measure ℂ := (volume : Measure ℂ).withDensity (fun x => ‖g x‖ₑ) with hν
  have hS : ∀ R : ℝ, MeasurableSet {x : ℂ | R ≤ ‖x‖} :=
    fun R => measurableSet_le measurable_const measurable_norm
  have heq : (fun R : ℝ => ∫⁻ x in {x : ℂ | R ≤ ‖x‖}, ‖g x‖ₑ) =
      ν ∘ fun R : ℝ => {x : ℂ | R ≤ ‖x‖} := by
    funext R
    simp only [Function.comp, hν]
    rw [withDensity_apply _ (hS R)]
  rw [heq]
  have hfin : ν univ ≠ ⊤ := by
    rw [hν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← eLpNorm_one_eq_lintegral_enorm]
    exact hg.eLpNorm_ne_top
  have h := tendsto_measure_iInter_atTop (μ := ν) (s := fun R : ℝ => {x : ℂ | R ≤ ‖x‖})
    (fun R => (hS R).nullMeasurableSet) (fun R R' hRR' x hx => le_trans hRR' hx)
    ⟨0, ne_top_of_le_ne_top hfin (measure_mono (subset_univ _))⟩
  have hempty : (⋂ R : ℝ, {x : ℂ | R ≤ ‖x‖}) = ∅ := by
    ext x
    simp only [mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall, not_le]
    exact ⟨‖x‖ + 1, by linarith⟩
  rw [hempty, measure_empty] at h
  exact h

/-- `‖f - g‖₁ ≤ |B_ρ|^{1/2} ‖f - g‖₂ + ∫_{|x|≥ρ}|f| + ∫_{|x|≥ρ}|g|`. -/
theorem eLpNorm_one_sub_le {f g : ℂ → ℝ} (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume) (ρ : ℝ) :
    eLpNorm (f - g) 1 volume ≤ eLpNorm (f - g) 2 volume * volume (ball (0 : ℂ) ρ) ^ (1 / 2 : ℝ) +
      ((∫⁻ x in {x : ℂ | ρ ≤ ‖x‖}, ‖f x‖ₑ) + ∫⁻ x in {x : ℂ | ρ ≤ ‖x‖}, ‖g x‖ₑ) := by
  have hB : MeasurableSet (ball (0 : ℂ) ρ) := measurableSet_ball
  have hcompl : (ball (0 : ℂ) ρ)ᶜ = {x : ℂ | ρ ≤ ‖x‖} := by
    ext x
    simp
  rw [eLpNorm_one_eq_lintegral_enorm, ← lintegral_add_compl _ hB, hcompl]
  refine add_le_add ?_ ?_
  · have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (μ := volume.restrict (ball (0 : ℂ) ρ)) (p := 1) (q := 2) one_le_two (hf.sub hg).restrict
    rw [eLpNorm_one_eq_lintegral_enorm, Measure.restrict_apply_univ] at h1
    refine h1.trans ?_
    have hexp : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) := by norm_num
    rw [hexp]
    gcongr
    exact Measure.restrict_le_self
  · calc ∫⁻ x in {x : ℂ | ρ ≤ ‖x‖}, ‖(f - g) x‖ₑ
        ≤ ∫⁻ x in {x : ℂ | ρ ≤ ‖x‖}, (‖f x‖ₑ + ‖g x‖ₑ) :=
          lintegral_mono fun x => (enorm_sub_le : ‖f x - g x‖ₑ ≤ ‖f x‖ₑ + ‖g x‖ₑ)
      _ = _ := lintegral_add_left' hf.enorm.restrict _

/-- Strong continuity into `L²` and a uniform tail bound give continuity into `L¹`. -/
theorem tendsto_eLpNorm_one {T G : ℝ} {Φ : ℝ≥0∞} {ωin : ℂ → ℝ} {ω : ℝ → ℂ → ℝ}
    (hm2 : ∀ t ∈ Ico 0 T, MemLp (ω t) 2 volume) (hin : MemLp ωin 1 volume) (hΦ : Φ ≠ ⊤)
    (hL2 : ∀ t₀ ∈ Ico 0 T,
      Tendsto (fun t => eLpNorm (ω t - ω t₀) 2 volume) (𝓝[Ico 0 T] t₀) (𝓝 0))
    (htail : ∀ R : ℝ, 0 < R → ∀ t ∈ Ico 0 T,
      ∫⁻ x in {x : ℂ | 2 * R ≤ ‖x‖}, ‖ω t x‖ₑ ≤
        (∫⁻ x in {x : ℂ | R ≤ ‖x‖}, ‖ωin x‖ₑ) + ENNReal.ofReal (G / R) * Φ) :
    ∀ t₀ ∈ Ico 0 T,
      Tendsto (fun t => eLpNorm (ω t - ω t₀) 1 volume) (𝓝[Ico 0 T] t₀) (𝓝 0) := by
  intro t₀ ht₀
  set τ : ℝ → ℝ≥0∞ := fun R => (∫⁻ x in {x : ℂ | R ≤ ‖x‖}, ‖ωin x‖ₑ) +
    ENNReal.ofReal (G / R) * Φ with hτ_def
  have hτ : Tendsto τ atTop (𝓝 0) := by
    have h1 := tendsto_lintegral_tail hin
    have h2 : Tendsto (fun R : ℝ => ENNReal.ofReal (G / R) * Φ) atTop (𝓝 0) := by
      have h3 : Tendsto (fun R : ℝ => G / R) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      have h4 := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h3) (Or.inr hΦ)
      simpa using h4
    simpa using h1.add h2
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hδ : 0 < ε / 2 / 2 := ENNReal.half_pos (ENNReal.half_pos hε.ne').ne'
  obtain ⟨R, hRτ, hRpos⟩ :=
    ((ENNReal.tendsto_nhds_zero.1 hτ (ε / 2 / 2) hδ).and (eventually_gt_atTop 0)).exists
  have hC : volume (ball (0 : ℂ) (2 * R)) ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) measure_ball_lt_top.ne
  have hL2C : Tendsto (fun t => eLpNorm (ω t - ω t₀) 2 volume *
      volume (ball (0 : ℂ) (2 * R)) ^ (1 / 2 : ℝ)) (𝓝[Ico 0 T] t₀) (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const (hL2 t₀ ht₀) (Or.inr hC)
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hL2C (ε / 2) (ENNReal.half_pos hε.ne'),
    self_mem_nhdsWithin] with t ht1 ht
  have h2R : 0 < R := hRpos
  calc eLpNorm (ω t - ω t₀) 1 volume
      ≤ eLpNorm (ω t - ω t₀) 2 volume * volume (ball (0 : ℂ) (2 * R)) ^ (1 / 2 : ℝ) +
        ((∫⁻ x in {x : ℂ | 2 * R ≤ ‖x‖}, ‖ω t x‖ₑ) +
          ∫⁻ x in {x : ℂ | 2 * R ≤ ‖x‖}, ‖ω t₀ x‖ₑ) :=
        eLpNorm_one_sub_le (hm2 t ht).1 (hm2 t₀ ht₀).1 (2 * R)
    _ ≤ ε / 2 + (ε / 2 / 2 + ε / 2 / 2) := by
        gcongr
        · exact (htail R h2R t ht).trans hRτ
        · exact (htail R h2R t₀ ht₀).trans hRτ
    _ = ε := by rw [ENNReal.add_halves, ENNReal.add_halves]

/-- Continuity into `L¹` and a uniform `L²` bound give continuity into `L^q`, `q ∈ [1,2)`. -/
theorem continuousIntoLpOn_of_one_two {T : ℝ} {ω : ℝ → ℂ → ℝ} {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (hm1 : ∀ t ∈ Ico 0 T, MemLp (ω t) 1 volume) (hm2 : ∀ t ∈ Ico 0 T, MemLp (ω t) 2 volume)
    (hb : ∀ t ∈ Ico 0 T, eLpNorm (ω t) 2 volume ≤ B)
    (hL1 : ∀ t₀ ∈ Ico 0 T,
      Tendsto (fun t => eLpNorm (ω t - ω t₀) 1 volume) (𝓝[Ico 0 T] t₀) (𝓝 0)) :
    ∀ q : ℝ, 1 ≤ q → q < 2 → ContinuousIntoLpOn (ENNReal.ofReal q) (Ico 0 T) ω := by
  intro q hq1 hq2
  have hq1' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    simpa using ENNReal.ofReal_le_ofReal hq1
  have hq2' : ENNReal.ofReal q < 2 := by
    rw [← ofReal_two]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 hq2
  refine ⟨fun t ht => LpInterp.memLp_of_memLp_of_memLp one_pos hq1' hq2'.le (hm1 t ht)
    (hm2 t ht), fun t₀ ht₀ => ?_⟩
  set F : ℝ → ℂ → ℝ := fun t => if t ∈ Ico 0 T then ω t - ω t₀ else 0 with hF_def
  have hF : ∀ t, AEStronglyMeasurable (F t) volume := by
    intro t
    by_cases ht : t ∈ Ico 0 T
    · simp only [F, ht, ite_true]
      exact (hm1 t ht).1.sub (hm1 t₀ ht₀).1
    · simp only [F, ht, ite_false]
      exact (MemLp.zero : MemLp (0 : ℂ → ℝ) 1 volume).1
  have hev : ∀ᶠ t in 𝓝[Ico 0 T] t₀, F t = ω t - ω t₀ := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [F, ht, ite_true]
  have hbound : ∀ᶠ t in 𝓝[Ico 0 T] t₀, eLpNorm (F t) 2 volume ≤ B + B := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [F, ht, ite_true]
    exact (eLpNorm_sub_le (hm2 t ht).1 (hm2 t₀ ht₀).1 one_le_two).trans
      (add_le_add (hb t ht) (hb t₀ ht₀))
  have hlim : Tendsto (fun t => eLpNorm (F t) 1 volume) (𝓝[Ico 0 T] t₀) (𝓝 0) :=
    (hL1 t₀ ht₀).congr' (hev.mono fun t ht => by simp only [ht])
  have := LpInterp.tendsto_eLpNorm_of_interp hF one_pos hq1' hq2'
    (ENNReal.add_ne_top.2 ⟨hB, hB⟩) hbound hlim
  exact this.congr' (hev.mono fun t ht => by simp only [ht])

end NonUniqueEuler.Weak.RenormAllTH
