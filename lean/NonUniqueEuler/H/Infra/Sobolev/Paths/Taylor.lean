import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import NonUniqueEuler.H.Infra.Sobolev.Paths.Joint

/-!
# Helper for `P/Infra/Sobolev/Paths`: first-order Taylor bound in `L²`, uniformly in space

For `H : ℝ × ℂ → ℂ` jointly smooth with `H(s, x) = 0` for `s ∈ I` (open) and `x ∉ K` (compact),
the remainder `H(s, x) - H(t, x) - (s - t) ∂_t H(t, x)` is bounded by `ε |s - t| 1_K(x)` for `s`
near `t ∈ I`: the mean value theorem in time and the uniform continuity of `∂_t H` on the compact
set `[t - r, t + r] × K` (`IsCompact.uniformContinuousOn_of_continuous`).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace NonUniqueEuler.Sob.PathsH

/-- The pointwise first-order Taylor bound, uniformly in `x`. -/
theorem taylor_bound {H : ℝ × ℂ → ℂ} (hH : ContDiff ℝ ∞ H) {K : Set ℂ} (hK : IsCompact K)
    {I : Set ℝ} (hI : IsOpen I) (hsupp : ∀ s ∈ I, ∀ x ∉ K, H (s, x) = 0) {t : ℝ} (ht : t ∈ I)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s in 𝓝 t, ∀ x, ‖H (s, x) - H (t, x) - (s - t) • fderiv ℝ H (t, x) (1, 0)‖ ≤
      K.indicator (fun _ => ε * |s - t|) x := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hI t ht
  set S : Set (ℝ × ℂ) := Metric.closedBall t (r / 2) ×ˢ K with hS
  have hSc : IsCompact S := (isCompact_closedBall t (r / 2)).prod hK
  set Ht : ℝ × ℂ → ℂ := fun p => fderiv ℝ H p (1, 0) with hHt
  have hHtc : Continuous Ht := (contDiff_fderiv_apply hH (1, 0)).continuous
  obtain ⟨δ, hδ, hδS⟩ :=
    Metric.uniformContinuousOn_iff.1 (hSc.uniformContinuousOn_of_continuous hHtc.continuousOn)
      ε hε
  have hU : IsOpen (I ×ˢ Kᶜ) := hI.prod hK.isClosed.isOpen_compl
  have hHU : ∀ p ∈ I ×ˢ Kᶜ, H p = 0 := fun p hp => hsupp p.1 hp.1 p.2 hp.2
  have hdiff : ∀ p, DifferentiableAt ℝ H p := fun p => (hH.differentiable (by simp)) p
  filter_upwards [Metric.ball_mem_nhds t (lt_min hδ (half_pos hr))] with s hs x
  have hs' : |s - t| < min δ (r / 2) := by
    rw [Metric.mem_ball, Real.dist_eq] at hs
    exact hs
  by_cases hx : x ∈ K
  · rw [indicator_of_mem hx]
    -- the mean value theorem for `τ ↦ H(τ, x) - τ • ∂_t H(t, x)` on `[t, s]`
    set φ : ℝ → ℂ := fun τ => H (τ, x) - τ • Ht (t, x) with hφ
    have hderiv : ∀ τ ∈ uIcc t s, HasDerivWithinAt φ (Ht (τ, x) - Ht (t, x)) (uIcc t s) τ := by
      intro τ _
      have h1 := hasDerivAt_time_slice (hdiff (τ, x))
      have h2 := (hasDerivAt_id τ).smul_const (Ht (t, x))
      simp only [one_smul] at h2
      exact (h1.sub h2).hasDerivWithinAt
    have hbound : ∀ τ ∈ uIcc t s, ‖Ht (τ, x) - Ht (t, x)‖ ≤ ε := by
      intro τ hτ
      have hτt : |τ - t| ≤ |s - t| := by
        rw [mem_uIcc] at hτ
        rcases hτ with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
          linarith
        · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
          linarith
      have hτS : (τ, x) ∈ S := by
        refine ⟨?_, hx⟩
        rw [Metric.mem_closedBall, Real.dist_eq]
        exact (hτt.trans hs'.le).trans (min_le_right _ _)
      have htS : (t, x) ∈ S := ⟨Metric.mem_closedBall_self (by linarith), hx⟩
      have hdist : dist (τ, x) (t, x) < δ := by
        rw [Prod.dist_eq, dist_self, Real.dist_eq]
        exact lt_of_le_of_lt (max_le hτt (abs_nonneg _)) (lt_of_lt_of_le hs' (min_le_left _ _))
      have := hδS (τ, x) hτS (t, x) htS hdist
      rw [dist_eq_norm] at this
      exact this.le
    have hmvt := (convex_uIcc t s).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
      left_mem_uIcc right_mem_uIcc
    have heq : φ s - φ t = H (s, x) - H (t, x) - (s - t) • fderiv ℝ H (t, x) (1, 0) := by
      simp only [hφ, hHt, sub_smul]
      abel
    rw [← heq]
    calc ‖φ s - φ t‖ ≤ ε * ‖s - t‖ := hmvt
      _ = ε * |s - t| := by rw [Real.norm_eq_abs]
  · rw [indicator_of_notMem hx]
    have hsI : s ∈ I := hball (Metric.mem_ball.2 (lt_of_lt_of_le
      (by rw [Real.dist_eq]; exact hs') ((min_le_right _ _).trans (half_le_self hr.le))))
    have h0 : fderiv ℝ H (t, x) = 0 := fderiv_eq_zero_of_eqOn_zero hU hHU ⟨ht, hx⟩
    simp [hsupp s hsI x hx, hsupp t ht x hx, h0]

/-- The `L²` form of the Taylor bound. -/
theorem eLpNorm_taylor_le {H : ℝ × ℂ → ℂ} (hH : ContDiff ℝ ∞ H) {K : Set ℂ} (hK : IsCompact K)
    {I : Set ℝ} (hI : IsOpen I) (hsupp : ∀ s ∈ I, ∀ x ∉ K, H (s, x) = 0) {t : ℝ} (ht : t ∈ I)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s in 𝓝 t,
      (eLpNorm (fun x => H (s, x) - H (t, x) - (s - t) • fderiv ℝ H (t, x) (1, 0)) 2
        (volume : Measure ℂ)).toReal ≤ ε * |s - t| * (volume K ^ (1 / (2 : ℝ))).toReal := by
  filter_upwards [taylor_bound hH hK hI hsupp ht hε] with s hs
  have hle := eLpNorm_mono_real (p := 2) (μ := (volume : Measure ℂ)) hs
  rw [eLpNorm_indicator_const hK.measurableSet two_ne_zero ENNReal.ofNat_ne_top] at hle
  have hfin : ‖ε * |s - t|‖ₑ * volume K ^ (1 / (2 : ℝ≥0∞).toReal) ≠ (⊤ : ℝ≥0∞) := by
    refine ENNReal.mul_ne_top enorm_ne_top ?_
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hK.measure_lt_top.ne
  have h2 : (1 / (2 : ℝ≥0∞).toReal) = 1 / (2 : ℝ) := by norm_num
  refine (ENNReal.toReal_mono hfin hle).trans_eq ?_
  rw [ENNReal.toReal_mul, toReal_enorm, h2, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hε.le (abs_nonneg _))]

end NonUniqueEuler.Sob.PathsH
