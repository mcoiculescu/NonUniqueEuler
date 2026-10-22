import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Proof: density of `C_c^∞` in `L¹ ∩ L²(ℝ²)` (library I-HK)

Proof of `NonUniqueEuler/I/Infra/Sobolev/DensityL1L2.lean`.

Manuscript: `lem:velocity`(c), `02_prelim.tex:376-377` ("Choose `ω_j ∈ C_c^∞(ℝ²)` with
`ω_j → ω` in `L¹` and in `L²`"), a standard fact the manuscript uses without proof.

Argument (the interface sketch, with one simplification: the `L²` approximation is applied to
`f` itself instead of to the truncation `1_{B_R} f`).
1. Tails: `‖1_{ℂ ∖ B_n} f‖_q → 0` for `q = 1, 2` (dominated convergence).
2. Fix `ε > 0` and `R ≥ 1` with both tails `< ε/2`. Let `g` be smooth with compact support and
   `‖f - g‖₂ ≤ η` (Mathlib `MemLp.exist_eLpNorm_sub_le`), let `χ` be a smooth bump equal to `1`
   on `B̄_R`, with support `B_{R+1}` and values in `[0, 1]`, and set `h = χ g`.
3. `f - h = (1 - χ) f + χ (f - g)`. The first term is pointwise bounded by `|1_{ℂ ∖ B_R} f|`.
   The second is bounded by `|f - g|` and supported in `B_{R+1}`, so its `L¹` norm is at most
   `|B_{R+1}|^{1/2} η` (Hölder). With `η = (ε/2)/(1 + |B_{R+1}|^{1/2})` both norms are `≤ ε`.
4. Diagonal choice `ε = 1/(n+1)`.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology ContDiff

namespace NonUniqueEuler.Sob

namespace DensityL1L2

/-- Tails of an `L^p` function on `ℂ` outside large balls tend to zero, `0 < p < ∞`. -/
theorem tendsto_eLpNorm_indicator_compl_ball {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ⊤)
    {f : ℂ → ℝ} (hf : MemLp f p volume) :
    Tendsto (fun n : ℕ => eLpNorm ((Metric.ball (0 : ℂ) n)ᶜ.indicator f) p volume)
      atTop (𝓝 0) := by
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp]
  have hlim : Tendsto
      (fun n : ℕ => ∫⁻ x, ‖(Metric.ball (0 : ℂ) n)ᶜ.indicator f x‖ₑ ^ p.toReal)
      atTop (𝓝 0) := by
    have h := tendsto_lintegral_of_dominated_convergence' (μ := volume)
      (F := fun n : ℕ => fun x => ‖(Metric.ball (0 : ℂ) n)ᶜ.indicator f x‖ₑ ^ p.toReal)
      (f := fun _ => 0) (fun x => ‖f x‖ₑ ^ p.toReal) ?_ ?_ ?_ ?_
    · simpa using h
    · intro n
      exact ((hf.aestronglyMeasurable.indicator
        Metric.isOpen_ball.measurableSet.compl).enorm).pow_const _
    · intro n
      refine Eventually.of_forall (fun x => ?_)
      exact ENNReal.rpow_le_rpow (enorm_indicator_le_enorm_self _ _) hr.le
    · exact ((eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hp).1 hf.2).ne
    · refine Eventually.of_forall (fun x => ?_)
      obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop N] with n hn
      have hxn : x ∈ Metric.ball (0 : ℂ) n := by
        rw [Metric.mem_ball, dist_zero_right]
        exact lt_of_lt_of_le hN (Nat.cast_le.2 hn)
      simp [hxn, ENNReal.zero_rpow_of_pos hr]
  have hc := (ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto 0
  rw [ENNReal.zero_rpow_of_pos (by positivity)] at hc
  exact hc.comp hlim

/-- One-step simultaneous approximation: for every `ε > 0` a smooth compactly supported `g`
with `‖f - g‖₁ ≤ ε` and `‖f - g‖₂ ≤ ε`. -/
theorem exists_smooth_approx_L1_L2 {f : ℂ → ℝ} (h1 : MemLp f 1 volume)
    (h2 : MemLp f 2 volume) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      eLpNorm (f - g) 1 volume ≤ ENNReal.ofReal ε ∧
      eLpNorm (f - g) 2 volume ≤ ENNReal.ofReal ε := by
  have hε2 : 0 < ε / 2 := by positivity
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 2) := ENNReal.ofReal_pos.2 hε2
  have t1 := tendsto_eLpNorm_indicator_compl_ball one_ne_zero ENNReal.one_ne_top h1
  have t2 := tendsto_eLpNorm_indicator_compl_ball two_ne_zero ENNReal.ofNat_ne_top h2
  obtain ⟨R, ⟨hR1, hR2⟩, hR⟩ := (((t1.eventually (gt_mem_nhds hpos)).and
    (t2.eventually (gt_mem_nhds hpos))).and (eventually_ge_atTop 1)).exists
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  set s : Set ℂ := Metric.ball (0 : ℂ) ((R : ℝ) + 1) with hs_def
  set K : ℝ := (volume s).toReal with hK_def
  have hK : volume s = ENNReal.ofReal K :=
    (ENNReal.ofReal_toReal measure_ball_lt_top.ne).symm
  have hK0 : 0 ≤ K := ENNReal.toReal_nonneg
  set η : ℝ := ε / 2 / (1 + K ^ (1 / 2 : ℝ)) with hη_def
  have hden : 0 < 1 + K ^ (1 / 2 : ℝ) := by positivity
  have hη : 0 < η := by positivity
  have hηle : η ≤ ε / 2 := div_le_self hε2.le (le_add_of_nonneg_right (by positivity))
  have hηK : η * K ^ (1 / 2 : ℝ) ≤ ε / 2 := by
    rw [hη_def, div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith [Real.rpow_nonneg hK0 (1 / 2 : ℝ)]
  obtain ⟨g, hgs, hgc, hg⟩ :=
    h2.exist_eLpNorm_sub_le ENNReal.ofNat_ne_top one_le_two hη
  let χ : ContDiffBump (0 : ℂ) := ⟨R, R + 1, hRpos, by linarith⟩
  have hχ0 : ∀ x, 0 ≤ χ x := fun x => χ.nonneg
  have hχ1 : ∀ x, χ x ≤ 1 := fun x => χ.le_one
  have hχs : Function.support χ = s := χ.support_eq
  -- the decomposition `f - χ g = (1 - χ) f + χ (f - g)`
  set A : ℂ → ℝ := fun x => (1 - χ x) * f x with hA_def
  set B : ℂ → ℝ := fun x => χ x * (f x - g x) with hB_def
  have hsplit : (f - fun x => χ x * g x) = A + B := by
    funext x; simp only [Pi.sub_apply, Pi.add_apply, hA_def, hB_def]; ring
  have hAm : AEStronglyMeasurable A volume :=
    (continuous_const.sub χ.continuous).aestronglyMeasurable.mul h1.aestronglyMeasurable
  have hBm : AEStronglyMeasurable B volume :=
    χ.continuous.aestronglyMeasurable.mul
      (h2.aestronglyMeasurable.sub hgc.continuous.aestronglyMeasurable)
  -- the tail term
  have hA_le : ∀ q : ℝ≥0∞, eLpNorm A q volume ≤
      eLpNorm ((Metric.ball (0 : ℂ) R)ᶜ.indicator f) q volume := by
    intro q
    refine eLpNorm_mono (fun x => ?_)
    by_cases hx : x ∈ Metric.ball (0 : ℂ) R
    · have h1x : χ x = 1 := χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
      simp [hA_def, h1x]
    · rw [Set.indicator_of_mem (Set.mem_compl hx), hA_def]
      simp only [norm_mul]
      have : ‖1 - χ x‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith [hχ0 x, hχ1 x]
      exact mul_le_of_le_one_left (norm_nonneg _) this
  -- the cut-off approximation term
  have hB2 : eLpNorm B 2 volume ≤ ENNReal.ofReal η := by
    refine le_trans (eLpNorm_mono (fun x => ?_)) hg
    simp only [hB_def, Pi.sub_apply, norm_mul]
    have : ‖χ x‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (hχ0 x)]; exact hχ1 x
    exact mul_le_of_le_one_left (norm_nonneg _) this
  have hBsupp : Function.support B ⊆ s := by
    rw [← hχs]; exact Function.support_mul_subset_left _ _
  have hB1 : eLpNorm B 1 volume ≤ ENNReal.ofReal (ε / 2) := by
    have hexp : 1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal = (1 / 2 : ℝ) := by norm_num
    have hH := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict s)
      (p := 1) (q := 2) one_le_two hBm.restrict
    rw [eLpNorm_restrict_eq_of_support_subset hBsupp,
      eLpNorm_restrict_eq_of_support_subset hBsupp, Measure.restrict_apply_univ, hexp, hK,
      ENNReal.ofReal_rpow_of_nonneg hK0 (by norm_num)] at hH
    refine hH.trans ?_
    calc eLpNorm B 2 volume * ENNReal.ofReal (K ^ (1 / 2 : ℝ))
        ≤ ENNReal.ofReal η * ENNReal.ofReal (K ^ (1 / 2 : ℝ)) := by gcongr
      _ = ENNReal.ofReal (η * K ^ (1 / 2 : ℝ)) := (ENNReal.ofReal_mul hη.le).symm
      _ ≤ ENNReal.ofReal (ε / 2) := ENNReal.ofReal_le_ofReal hηK
  have hhalf : ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) = ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_add hε2.le hε2.le, add_halves]
  refine ⟨fun x => χ x * g x, χ.contDiff.mul hgc, ?_, ?_, ?_⟩
  · exact HasCompactSupport.mul_right (f := χ) (f' := g) χ.hasCompactSupport
  · rw [hsplit]
    calc eLpNorm (A + B) 1 volume ≤ eLpNorm A 1 volume + eLpNorm B 1 volume :=
          eLpNorm_add_le hAm hBm le_rfl
      _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
          gcongr
          exact (hA_le 1).trans hR1.le
      _ = ENNReal.ofReal ε := hhalf
  · rw [hsplit]
    calc eLpNorm (A + B) 2 volume ≤ eLpNorm A 2 volume + eLpNorm B 2 volume :=
          eLpNorm_add_le hAm hBm one_le_two
      _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
          gcongr
          · exact (hA_le 2).trans hR2.le
          · exact hB2.trans (ENNReal.ofReal_le_ofReal hηle)
      _ = ENNReal.ofReal ε := hhalf

end DensityL1L2

open DensityL1L2 in
/-- Density of real `C_c^∞(ℝ²)` in `L¹ ∩ L²(ℝ²)`: a sequence of smooth compactly supported real
functions converging to `f` in `L¹` and in `L²`. -/
theorem exists_seq_smooth_tendsto_L1_L2 {f : ℂ → ℝ} (h1 : MemLp f 1 volume)
    (h2 : MemLp f 2 volume) :
    ∃ g : ℕ → ℂ → ℝ, (∀ n, ContDiff ℝ ∞ (g n)) ∧ (∀ n, HasCompactSupport (g n)) ∧
      Tendsto (fun n => eLpNorm (f - g n) 1 volume) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (f - g n) 2 volume) atTop (𝓝 0) := by
  choose g hgc hgs hg1 hg2 using fun n : ℕ =>
    exists_smooth_approx_L1_L2 h1 h2 (Nat.one_div_pos_of_nat (α := ℝ) (n := n))
  refine ⟨g, hgc, hgs, ?_, ?_⟩
  · have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le) hg1
  · have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le) hg2

end NonUniqueEuler.Sob
