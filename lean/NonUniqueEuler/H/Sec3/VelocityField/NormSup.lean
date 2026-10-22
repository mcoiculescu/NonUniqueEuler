import NonUniqueEuler.Defs.Infra.Sobolev
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Helpers for `I/Sec3/VelocityField`: norming sequences in `L²(B_R)`

Helper file of `P/Sec3/VelocityField.lean`.

* `enorm_eq_iSup_re_inner`: in a (real or complex) inner product space, the norm is the
  supremum of the normalized pairings `re ⟪d_m, x⟫ / ‖d_m‖` over any dense sequence `d_m`.
* `exists_denseRange_testFn_ball`: there is a sequence of elements of `L²(B_R; ℂ)` with dense
  range, each represented by a test function supported in `B_R` (`Sob.IsTestFn`).

These are used to write `‖∂^γ v(t)‖_{L²(B_R)}` as a countable supremum of
`|∫ v(t) ∂^γ φ_m|`-type expressions, which are measurable in `t` (Fubini); this is the
measurability of `t ↦ ‖v(t)‖_{H¹(B_R)}` required by `Weak.IsBddH1DivFreeField` (the remark
`03_compactness.tex:243-247`).
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal ContDiff ComplexConjugate Topology

namespace NonUniqueEuler.H.VelocityField

/-- In an inner product space, the norm is the supremum of the normalized pairings with any
dense sequence (with the convention `0 / 0 = 0`). -/
theorem enorm_eq_iSup_re_inner {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {D : ℕ → E} (hD : DenseRange D) (x : E) :
    ‖x‖ₑ = ⨆ m, ENNReal.ofReal (RCLike.re (inner 𝕜 (D m) x) / ‖D m‖) := by
  apply le_antisymm
  · rcases eq_or_ne x 0 with rfl | hx
    · simp
    refine le_of_forall_lt fun c hc => ?_
    have hc' : c ≠ ⊤ := ne_top_of_lt hc
    have hcx : c.toReal < ‖x‖ := by
      rw [← ofReal_norm] at hc
      exact ENNReal.toReal_lt_of_lt_ofReal hc
    set U : Set E := {y | c.toReal * ‖y‖ < RCLike.re (inner 𝕜 y x)} with hU_def
    have hU : IsOpen U :=
      isOpen_lt (continuous_const.mul continuous_norm)
        (RCLike.continuous_re.comp (continuous_id.inner continuous_const))
    have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hxU : x ∈ U := by
      show c.toReal * ‖x‖ < RCLike.re (inner 𝕜 x x)
      rw [inner_self_eq_norm_sq_to_K]
      have : RCLike.re ((‖x‖ : 𝕜) ^ 2) = ‖x‖ ^ 2 := by
        rw [← RCLike.ofReal_pow, RCLike.ofReal_re]
      rw [this]
      nlinarith
    obtain ⟨m, hm⟩ := hD.exists_mem_open hU ⟨x, hxU⟩
    have hm' : c.toReal * ‖D m‖ < RCLike.re (inner 𝕜 (D m) x) := hm
    have hDm : 0 < ‖D m‖ := by
      rcases (norm_nonneg (D m)).eq_or_lt with h | h
      · have h0 : D m = 0 := norm_eq_zero.1 h.symm
        rw [h0] at hm'
        simp at hm'
      · exact h
    have hlt : c.toReal < RCLike.re (inner 𝕜 (D m) x) / ‖D m‖ := by
      rw [lt_div_iff₀ hDm]
      exact hm'
    calc c = ENNReal.ofReal c.toReal := (ENNReal.ofReal_toReal hc').symm
      _ < ENNReal.ofReal (RCLike.re (inner 𝕜 (D m) x) / ‖D m‖) :=
          (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt ENNReal.toReal_nonneg hlt)).2 hlt
      _ ≤ ⨆ m, ENNReal.ofReal (RCLike.re (inner 𝕜 (D m) x) / ‖D m‖) :=
          le_iSup (fun m => ENNReal.ofReal (RCLike.re (inner 𝕜 (D m) x) / ‖D m‖)) m
  · refine iSup_le fun m => ?_
    rw [← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    rcases (norm_nonneg (D m)).eq_or_lt with h | h
    · rw [← h, div_zero]
      exact norm_nonneg x
    · rw [div_le_iff₀ h]
      calc RCLike.re (inner 𝕜 (D m) x) ≤ ‖inner 𝕜 (D m) x‖ := RCLike.re_le_norm _
        _ ≤ ‖D m‖ * ‖x‖ := norm_inner_le_norm _ _
        _ = ‖x‖ * ‖D m‖ := mul_comm _ _

/-- The cutoff estimate: for `g` bounded by `C` and a bump `χ` equal to `1` on `closedBall 0 r`,
`‖(1 - χ) g‖_{L²(B_R)} ≤ |B_R ∖ closedBall 0 r|^{1/2} C`. -/
theorem eLpNorm_sub_bump_mul_le {R : ℝ} (χ : ContDiffBump (0 : ℂ)) {g : ℂ → ℂ} {C : ℝ}
    (hg : ∀ x, ‖g x‖ ≤ C) :
    eLpNorm (fun x => g x - ((χ x : ℝ) : ℂ) * g x) 2 (volume.restrict (ball (0 : ℂ) R)) ≤
      (volume (ball (0 : ℂ) R ∩ (closedBall (0 : ℂ) χ.rIn)ᶜ)) ^ (2 : ℝ≥0∞).toReal⁻¹ *
        ENNReal.ofReal C := by
  set f : ℂ → ℂ := fun x => g x - ((χ x : ℝ) : ℂ) * g x with hf_def
  have hsupp : Function.support f ⊆ (closedBall (0 : ℂ) χ.rIn)ᶜ := by
    intro x hx
    simp only [Function.mem_support] at hx
    intro hxc
    apply hx
    simp [hf_def, χ.one_of_mem_closedBall hxc]
  rw [← eLpNorm_restrict_eq_of_support_subset hsupp]
  refine (eLpNorm_le_of_ae_bound (C := C) (Eventually.of_forall fun x => ?_)).trans
    (le_of_eq ?_)
  · have h1 : ‖(1 : ℂ) - ((χ x : ℝ) : ℂ)‖ ≤ 1 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_le]
      constructor <;> linarith [χ.nonneg (x := x), χ.le_one (x := x)]
    calc ‖f x‖ = ‖((1 : ℂ) - ((χ x : ℝ) : ℂ)) * g x‖ := by simp only [hf_def]; ring_nf
      _ = ‖(1 : ℂ) - ((χ x : ℝ) : ℂ)‖ * ‖g x‖ := norm_mul _ _
      _ ≤ 1 * C := mul_le_mul h1 (hg x) (norm_nonneg _) zero_le_one
      _ = C := one_mul C
  · rw [Measure.restrict_restrict (measurableSet_closedBall.compl), Measure.restrict_apply_univ,
      inter_comm]

/-- The family of test functions supported in `B_R` is dense in `L²(B_R; ℂ)`. -/
theorem dense_testFn_ball {R : ℝ} (hR : 0 < R) :
    Dense {f : Lp ℂ 2 (volume.restrict (ball (0 : ℂ) R)) |
      ∃ φ : ℂ → ℂ, Sob.IsTestFn (ball (0 : ℂ) R) φ ∧
        (f : ℂ → ℂ) =ᵐ[volume.restrict (ball (0 : ℂ) R)] φ} := by
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨one_le_two⟩
  set μ : Measure ℂ := volume.restrict (ball (0 : ℂ) R) with hμ
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  rw [Metric.dense_iff]
  intro f ε hε
  -- smooth compactly supported approximation in `L²(B_R)`
  obtain ⟨g, hgc, hgs, hgf⟩ := MemLp.exist_eLpNorm_sub_le (μ := μ) (p := 2) ENNReal.ofNat_ne_top
    one_le_two (Lp.memLp f) (by positivity : (0:ℝ) < ε / 4)
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖g x‖ ≤ C := by
    obtain ⟨C, hC⟩ := hgs.continuous.norm.bddAbove_range_of_hasCompactSupport hgc.norm
    exact ⟨C, fun x => hC ⟨x, rfl⟩⟩
  -- the measure of the annuli `B_R ∖ closedBall 0 r_n` tends to `0`
  set r : ℕ → ℝ := fun n => R * (1 - 1 / ((n : ℝ) + 2)) with hr_def
  have hr_pos : ∀ n, 0 < r n := fun n => by
    have : 1 / ((n : ℝ) + 2) < 1 := by
      rw [div_lt_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
    exact mul_pos hR (by linarith)
  have hr_lt : ∀ n, r n < R := fun n => by
    have : 0 < 1 / ((n : ℝ) + 2) := by positivity
    have : R * (1 - 1 / ((n : ℝ) + 2)) < R * 1 := mul_lt_mul_of_pos_left (by linarith) hR
    simpa [hr_def] using this
  have hr_mono : Monotone r := by
    intro m n hmn
    have hmn' : (m : ℝ) ≤ n := Nat.cast_le.2 hmn
    have : 1 / ((n : ℝ) + 2) ≤ 1 / ((m : ℝ) + 2) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    exact mul_le_mul_of_nonneg_left (by linarith) hR.le
  set A : ℕ → Set ℂ := fun n => ball (0 : ℂ) R ∩ (closedBall (0 : ℂ) (r n))ᶜ with hA_def
  have hA_anti : Antitone A := by
    intro m n hmn x hx
    refine ⟨hx.1, fun hxc => hx.2 ?_⟩
    exact closedBall_subset_closedBall (hr_mono hmn) hxc
  have hA_inter : (⋂ n, A n) = ∅ := by
    ext x
    simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall]
    by_cases hx : x ∈ ball (0 : ℂ) R
    · have hxR : ‖x‖ < R := by simpa using hx
      -- choose `n` with `r n ≥ ‖x‖`
      obtain ⟨n, hn⟩ := exists_nat_gt (R / (R - ‖x‖))
      refine ⟨n, fun h => h.2 ?_⟩
      rw [mem_closedBall, dist_zero_right]
      have hpos : 0 < R - ‖x‖ := by linarith
      have h1 : R / (R - ‖x‖) < (n : ℝ) + 2 := by linarith
      have h2 : R / ((n : ℝ) + 2) < R - ‖x‖ := by
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ hpos] at h1
        linarith
      show ‖x‖ ≤ R * (1 - 1 / ((n : ℝ) + 2))
      have : R * (1 - 1 / ((n : ℝ) + 2)) = R - R / ((n : ℝ) + 2) := by ring
      rw [this]
      linarith
    · exact ⟨0, fun h => hx h.1⟩
  have hA_tend : Tendsto (fun n => volume (A n)) atTop (𝓝 0) := by
    have := tendsto_measure_iInter_atTop (μ := volume) (s := A)
      (fun n => (measurableSet_ball.inter measurableSet_closedBall.compl).nullMeasurableSet)
      hA_anti ⟨0, (measure_mono inter_subset_left).trans_lt measure_ball_lt_top |>.ne⟩
    rwa [hA_inter, measure_empty] at this
  have hB_tend : Tendsto (fun n => volume (A n) ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal C)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => volume (A n) ^ (2 : ℝ≥0∞).toReal⁻¹) atTop (𝓝 0) := by
      have := (ENNReal.continuous_rpow_const (y := (2 : ℝ≥0∞).toReal⁻¹)).tendsto 0
      rw [ENNReal.zero_rpow_of_pos (by norm_num)] at this
      exact this.comp hA_tend
    have h2 := ENNReal.Tendsto.mul_const h1 (b := ENNReal.ofReal C) (Or.inr ENNReal.ofReal_ne_top)
    rwa [zero_mul] at h2
  obtain ⟨n, hn⟩ := (hB_tend.eventually
    (Iio_mem_nhds (ENNReal.ofReal_pos.2 (by positivity : (0:ℝ) < ε / 4)))).exists
  -- a bump equal to `1` on `closedBall 0 (r n)`, supported in `B_R`
  let χ : ContDiffBump (0 : ℂ) :=
    { rIn := r n, rOut := (r n + R) / 2, rIn_pos := hr_pos n,
      rIn_lt_rOut := by linarith [hr_lt n] }
  have hχ_out : χ.rOut < R := by show (r n + R) / 2 < R; linarith [hr_lt n]
  set φ : ℂ → ℂ := fun x => ((χ x : ℝ) : ℂ) * g x with hφ_def
  have hφ : Sob.IsTestFn (ball (0 : ℂ) R) φ := by
    refine ⟨?_, ?_, ?_⟩
    · exact (Complex.ofRealCLM.contDiff.comp χ.contDiff).mul hgs
    · have : HasCompactSupport (fun x => ((χ x : ℝ) : ℂ)) :=
        χ.hasCompactSupport.comp_left Complex.ofReal_zero
      exact this.mul_right
    · refine (tsupport_mul_subset_left).trans ?_
      have : tsupport (fun x => ((χ x : ℝ) : ℂ)) ⊆ tsupport χ :=
        tsupport_comp_subset Complex.ofReal_zero _
      refine this.trans ?_
      rw [χ.tsupport_eq]
      exact closedBall_subset_ball hχ_out
  have hφm : MemLp φ 2 μ := hφ.memLp 2 μ
  refine ⟨hφm.toLp φ, ?_, φ, hφ, hφm.coeFn_toLp⟩
  rw [mem_ball, dist_comm, Lp.dist_def]
  have hfm := Lp.memLp f
  have hgm : MemLp g 2 μ := hgs.continuous.memLp_of_hasCompactSupport hgc
  have heq : ((f : ℂ → ℂ) - (hφm.toLp φ : ℂ → ℂ)) =ᵐ[μ]
      (((f : ℂ → ℂ) - g) + fun x => g x - φ x) := by
    filter_upwards [hφm.coeFn_toLp] with x hx
    simp only [Pi.sub_apply, Pi.add_apply, hx]
    ring
  rw [eLpNorm_congr_ae heq]
  have hle : eLpNorm (((f : ℂ → ℂ) - g) + fun x => g x - φ x) 2 μ ≤
      ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) := by
    refine (eLpNorm_add_le (hfm.sub hgm).aestronglyMeasurable
      (hgm.sub hφm).aestronglyMeasurable one_le_two).trans (add_le_add hgf ?_)
    exact (eLpNorm_sub_bump_mul_le χ hC).trans hn.le
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at hle
  have := ENNReal.toReal_le_of_le_ofReal (by positivity) hle
  linarith

/-- A dense sequence in `L²(B_R; ℂ)` whose members are represented by test functions supported
in `B_R`. -/
theorem exists_denseRange_testFn_ball {R : ℝ} (hR : 0 < R) :
    ∃ D : ℕ → Lp ℂ 2 (volume.restrict (ball (0 : ℂ) R)), DenseRange D ∧
      ∀ m, ∃ φ : ℂ → ℂ, Sob.IsTestFn (ball (0 : ℂ) R) φ ∧
        (D m : ℂ → ℂ) =ᵐ[volume.restrict (ball (0 : ℂ) R)] φ := by
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨one_le_two⟩
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  obtain ⟨t, hts, htc, htd⟩ := (dense_testFn_ball hR).exists_countable_dense_subset
  obtain ⟨D, rfl⟩ := htc.exists_eq_range htd.nonempty
  exact ⟨D, htd, fun m => hts (mem_range_self m)⟩

end NonUniqueEuler.H.VelocityField
