import NonUniqueEuler.Defs.Sec3.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Helpers for `prop:compact`: generic analytic lemmas

Helper file of `P/Sec3/Compact.lean` (`prop:compact`, `03_compactness.tex:251-340`).

* `abs_integral_mul_le`: Cauchy–Schwarz `|∫ f g| ≤ ‖f‖₂ ‖g‖₂` (real functions on `ℂ`).
* `tendsto_integral_mul_of_weak_strong`: weak–strong pairing, `fₙ ⇀ f` bounded in `L²`,
  `hₙ → h` in `L²` ⇒ `∫ fₙ hₙ → ∫ f h`.
* `tendsto_eLpNorm_zero_of_dominated`: dominated convergence for `L^p` norms (`p < ∞`) of
  `ℝ≥0∞`-valued functions on a finite measure space, **without** measurability (through a
  measurable minorant with the same integral, `exists_measurable_le_lintegral_eq`).
* Bounds and supports of test functions `φ ∈ 𝒟_T` (`exists_testFn_bounds`).
* Slice bounds of a sequence satisfying `IsCompactSeq` (`IsCompactSeq.slice_*`).
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology InnerProductSpace

namespace NonUniqueEuler.Compact.PropCompact

open Weak

/-! ### Cauchy–Schwarz and weak–strong pairing -/

theorem abs_integral_mul_le {f g : ℂ → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    |∫ x, f x * g x| ≤ (eLpNorm f 2 volume).toReal * (eLpNorm g 2 volume).toReal := by
  rw [← WeakL2.inner_toLp_toLp hf hg, ← Lp.norm_toLp f hf, ← Lp.norm_toLp g hg]
  exact abs_real_inner_le_norm _ _

theorem integrable_mul_of_L2 {f g : ℂ → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Integrable (fun x => f x * g x) volume :=
  hf.integrable_mul hg

/-- Weak–strong pairing in `L²`. -/
theorem tendsto_integral_mul_of_weak_strong {fs : ℕ → ℂ → ℝ} {f : ℂ → ℝ} {hs : ℕ → ℂ → ℝ}
    {h : ℂ → ℝ} {M : ℝ} (hfs : ∀ n, MemLp (fs n) 2 volume)
    (hhs : ∀ n, MemLp (hs n) 2 volume) (hh : MemLp h 2 volume)
    (hw : ∀ ψ : ℂ → ℝ, MemLp ψ 2 volume →
      Tendsto (fun n => ∫ x, fs n x * ψ x) atTop (𝓝 (∫ x, f x * ψ x)))
    (hb : ∀ n, (eLpNorm (fs n) 2 volume).toReal ≤ M)
    (hst : Tendsto (fun n => eLpNorm (hs n - h) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, fs n x * hs n x) atTop (𝓝 (∫ x, f x * h x)) := by
  have key : ∀ n, ∫ x, fs n x * hs n x =
      (∫ x, fs n x * (hs n - h) x) + ∫ x, fs n x * h x := by
    intro n
    rw [← integral_add (integrable_mul_of_L2 (hfs n) ((hhs n).sub hh))
      (integrable_mul_of_L2 (hfs n) hh)]
    congr 1
    funext x
    simp only [Pi.sub_apply]
    ring
  simp_rw [key]
  rw [← zero_add (∫ x, f x * h x)]
  refine Tendsto.add ?_ (hw h hh)
  have hst' : Tendsto (fun n => (eLpNorm (hs n - h) 2 volume).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hst
    simpa [Function.comp_def] using this
  have hM : Tendsto (fun n => M * (eLpNorm (hs n - h) 2 volume).toReal) atTop (𝓝 0) := by
    simpa using hst'.const_mul M
  refine squeeze_zero_norm (fun n => ?_) hM
  rw [Real.norm_eq_abs]
  refine (abs_integral_mul_le (hfs n) ((hhs n).sub hh)).trans ?_
  exact mul_le_mul_of_nonneg_right (hb n) ENNReal.toReal_nonneg

/-! ### Dominated convergence for `L^p` norms of `ℝ≥0∞`-valued functions -/

/-- Dominated convergence for `‖fₙ‖_{L^p(μ)}`, `0 < p < ∞`, `μ` finite, `fₙ` bounded by a
constant and tending to `0` a.e.; no measurability of `fₙ` is needed. -/
theorem tendsto_eLpNorm_zero_of_dominated {μ : Measure ℝ} [IsFiniteMeasure μ]
    {f : ℕ → ℝ → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ ∞) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (hb : ∀ n, ∀ᵐ t ∂μ, f n t ≤ c) (hl : ∀ᵐ t ∂μ, Tendsto (fun n => f n t) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n) p μ) atTop (𝓝 0) := by
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp, enorm_eq_self]
  choose g hgm hgle hgeq using
    fun n => exists_measurable_le_lintegral_eq μ (fun t => f n t ^ p.toReal)
  have h1 : Tendsto (fun n => ∫⁻ t, g n t ∂μ) atTop (𝓝 0) := by
    have hfin : ∫⁻ _t, c ^ p.toReal ∂μ ≠ ∞ := by
      rw [lintegral_const]
      exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hr.le hc)
        (measure_ne_top μ univ)
    have := tendsto_lintegral_of_dominated_convergence (f := fun _ => 0)
      (fun _ => c ^ p.toReal) hgm ?_ hfin ?_
    · simpa using this
    · intro n
      filter_upwards [hb n] with t ht
      exact (hgle n t).trans (ENNReal.rpow_le_rpow ht hr.le)
    · filter_upwards [hl] with t ht
      have hpow : Tendsto (fun n => f n t ^ p.toReal) atTop (𝓝 0) := by
        have := (ENNReal.continuous_rpow_const (y := p.toReal)).tendsto 0 |>.comp ht
        simpa [Function.comp_def, ENNReal.zero_rpow_of_pos hr] using this
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hpow
        (fun _ => zero_le) (fun n => hgle n t)
  have h2 : Tendsto (fun n => ∫⁻ t, f n t ^ p.toReal ∂μ) atTop (𝓝 0) := by
    simpa only [hgeq] using h1
  have := (ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto 0 |>.comp h2
  simpa [Function.comp_def, ENNReal.zero_rpow_of_pos (inv_pos.2 hr)] using this

/-! ### Test functions: bounds and supports -/

theorem testFn_differentiable {T : ℝ} {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) :
    Differentiable ℝ φ :=
  hφ.contDiff.differentiable (by simp)

theorem testFn_continuous_fderiv {T : ℝ} {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) :
    Continuous (fderiv ℝ φ) :=
  hφ.contDiff.continuous_fderiv (by simp)

theorem testFn_timeDeriv_eq {T : ℝ} {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) (t : ℝ)
    (x : ℂ) : timeDeriv φ t x = fderiv ℝ φ (t, x) ((1 : ℝ), (0 : ℂ)) := by
  have h1 : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : ℂ)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  exact (((testFn_differentiable hφ) (t, x)).hasFDerivAt.comp_hasDerivAt t h1).deriv

theorem testFn_fderiv_slice_eq {T : ℝ} {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) (t : ℝ)
    (x : ℂ) :
    fderiv ℝ (fun y => φ (t, y)) x = (fderiv ℝ φ (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ ℂ) :=
  (((testFn_differentiable hφ) (t, x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)).fderiv

theorem testFn_continuous_timeDeriv {T : ℝ} {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ)
    (t : ℝ) : Continuous (fun x : ℂ => timeDeriv φ t x) := by
  have : (fun x : ℂ => timeDeriv φ t x) = fun x => fderiv ℝ φ (t, x) ((1 : ℝ), (0 : ℂ)) := by
    funext x
    exact testFn_timeDeriv_eq hφ t x
  rw [this]
  exact ((testFn_continuous_fderiv hφ).comp (Continuous.prodMk_right t)).clm_apply
    continuous_const

theorem testFn_continuous_fderiv_slice {T : ℝ} {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ)
    (t : ℝ) : Continuous (fun x : ℂ => fderiv ℝ (fun y => φ (t, y)) x) := by
  have : (fun x : ℂ => fderiv ℝ (fun y => φ (t, y)) x) =
      fun x => (fderiv ℝ φ (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ ℂ) := by
    funext x
    exact testFn_fderiv_slice_eq hφ t x
  rw [this]
  exact ((testFn_continuous_fderiv hφ).comp (Continuous.prodMk_right t)).clm_comp
    continuous_const

/-- A test function, its time derivative and its spatial derivative are bounded by `D` and vanish
for `‖x‖ ≥ r`, uniformly in `t`. -/
theorem exists_testFn_bounds {T : ℝ} {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) :
    ∃ r : ℝ, 0 < r ∧ ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ, ∀ x : ℂ,
      |φ (t, x)| ≤ D ∧ |timeDeriv φ t x| ≤ D ∧ ‖fderiv ℝ (fun y => φ (t, y)) x‖ ≤ D ∧
      (r ≤ ‖x‖ → φ (t, x) = 0 ∧ timeDeriv φ t x = 0 ∧
        fderiv ℝ (fun y => φ (t, y)) x = 0) := by
  obtain ⟨r₀, hr₀⟩ := hφ.hasCompactSupport.isCompact.isBounded.subset_ball (0 : ℝ × ℂ)
  obtain ⟨D₁, hD₁⟩ := hφ.contDiff.continuous.bounded_above_of_compact_support hφ.hasCompactSupport
  obtain ⟨D₂, hD₂⟩ := (testFn_continuous_fderiv hφ).bounded_above_of_compact_support
    (hφ.hasCompactSupport.fderiv (𝕜 := ℝ))
  refine ⟨max r₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), max D₁ D₂,
    (norm_nonneg _).trans ((hD₁ 0).trans (le_max_left _ _)), fun t x => ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [← Real.norm_eq_abs]
    exact (hD₁ _).trans (le_max_left _ _)
  · rw [testFn_timeDeriv_eq hφ, ← Real.norm_eq_abs]
    refine ((fderiv ℝ φ (t, x)).le_opNorm _).trans ?_
    have h1 : ‖((1 : ℝ), (0 : ℂ))‖ = 1 := by simp [Prod.norm_def]
    rw [h1, mul_one]
    exact (hD₂ _).trans (le_max_right _ _)
  · rw [testFn_fderiv_slice_eq hφ]
    refine ((fderiv ℝ φ (t, x)).opNorm_comp_le _).trans ?_
    refine (mul_le_mul (hD₂ _) (ContinuousLinearMap.norm_inr_le_one ℝ ℝ ℂ) (norm_nonneg _)
      ((norm_nonneg _).trans (hD₂ 0))).trans ?_
    rw [mul_one]
    exact le_max_right _ _
  · intro hx
    have hnot : (t, x) ∉ tsupport φ := by
      intro hmem
      have h1 := hr₀ hmem
      rw [mem_ball, dist_zero_right] at h1
      have h2 : ‖x‖ ≤ ‖(t, x)‖ := norm_snd_le (t, x)
      linarith [le_max_left r₀ 1]
    have hd : fderiv ℝ φ (t, x) = 0 := fderiv_of_notMem_tsupport ℝ hnot
    refine ⟨image_eq_zero_of_notMem_tsupport hnot, ?_, ?_⟩
    · rw [testFn_timeDeriv_eq hφ, hd]
      rfl
    · rw [testFn_fderiv_slice_eq hφ, hd, ContinuousLinearMap.zero_comp]

/-- A continuous function on `ℂ` vanishing for `‖x‖ ≥ r` is in every `L^p`. -/
theorem memLp_of_continuous_of_vanish {E : Type*} [NormedAddCommGroup E] {f : ℂ → E}
    (hf : Continuous f) {r : ℝ} (hr : ∀ x : ℂ, r ≤ ‖x‖ → f x = 0) (p : ℝ≥0∞) :
    MemLp f p volume := by
  have hc : HasCompactSupport f := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) r) fun x hx => hr x ?_
    rw [mem_closedBall, dist_zero_right, not_le] at hx
    exact hx.le
  exact hf.memLp_of_hasCompactSupport hc

/-! ### Slices of a sequence satisfying `IsCompactSeq` -/

variable {T M : ℝ} {gs : ℕ → ℂ → ℝ} {g : ℂ → ℝ} {ωs : ℕ → ℝ → ℂ → ℝ}

theorem seq_memLp_two (h : IsCompactSeq T M gs g ωs) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 T) : MemLp (ωs n t) 2 volume :=
  (h.weakCont n).memLp t ht

theorem seq_eLpNorm_one_le (h : IsCompactSeq T M gs g ωs) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 T) : eLpNorm (ωs n t) 1 volume ≤ ENNReal.ofReal M :=
  (eLpNorm_one_le_normL1LpE 2 _).trans (h.bound n t ht)

theorem seq_eLpNorm_two_le (h : IsCompactSeq T M gs g ωs) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 T) : eLpNorm (ωs n t) 2 volume ≤ ENNReal.ofReal M :=
  (eLpNorm_le_normL1LpE 2 _).trans (h.bound n t ht)

theorem seq_memLp_one (h : IsCompactSeq T M gs g ωs) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 T) : MemLp (ωs n t) 1 volume :=
  ⟨(seq_memLp_two h n ht).aestronglyMeasurable,
    (seq_eLpNorm_one_le h n ht).trans_lt ENNReal.ofReal_lt_top⟩

theorem seq_toReal_eLpNorm_two_le (h : IsCompactSeq T M gs g ωs) (hM : 0 ≤ M)
    (n : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) : (eLpNorm (ωs n t) 2 volume).toReal ≤ M :=
  ENNReal.toReal_le_of_le_ofReal hM (seq_eLpNorm_two_le h n ht)

theorem seq_normL1Lp_le (h : IsCompactSeq T M gs g ωs) (hM : 0 ≤ M) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 T) : Prelim.normL1Lp 2 (ωs n t) ≤ M := by
  rw [normL1Lp_eq_toReal (seq_memLp_one h n ht) (seq_memLp_two h n ht)]
  exact ENNReal.toReal_le_of_le_ofReal hM (h.bound n t ht)

/-- The bound `M` may be replaced by `max M 0`. -/
theorem seq_max_zero (h : IsCompactSeq T M gs g ωs) :
    IsCompactSeq T (max M 0) gs g ωs where
  T_pos := h.T_pos
  memLp_one := h.memLp_one
  memLp_two := h.memLp_two
  memLp_one_seq := h.memLp_one_seq
  memLp_two_seq := h.memLp_two_seq
  weakTendsto := h.weakTendsto
  weakSolution := h.weakSolution
  weakCont := h.weakCont
  bound n t ht := (h.bound n t ht).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))

theorem ofReal_max_zero (M : ℝ) : ENNReal.ofReal (max M 0) = ENNReal.ofReal M := by
  rcases le_total 0 M with hM | hM
  · rw [max_eq_left hM]
  · rw [max_eq_right hM, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos hM]

end NonUniqueEuler.Compact.PropCompact
