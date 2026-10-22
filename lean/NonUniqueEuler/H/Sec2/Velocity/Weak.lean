import NonUniqueEuler.H.Sec2.Velocity.Bounds
import NonUniqueEuler.H.Sec2.Velocity.Exponents
import NonUniqueEuler.I.Infra.ConvMinkowski.YoungGeneral
import NonUniqueEuler.I.Infra.LpDual.WeakBounded
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Helpers for `lem:velocity`(b): weak convergence of the vorticity

Helper file of `P/Sec2/Velocity.lean` (namespace `NonUniqueEuler.BS.VelH`), following
`02_prelim.tex:345-374`. For `0 < ε ≤ L` the kernel splits as
`K = 1_{B_ε} K + 1_{B_L ∖ B_ε} K + 1_{ℝ²∖B_L} K` (`kBall`, `kAnn`, `kOut`):

* the small-ball part is handled by Young's inequality and `‖1_{B_ε} K‖_{L^{s_p}} → 0`
  (`tendsto_eLpNorm_kBall`), uniformly in `n`;
* the annulus kernel `1_{B_L ∖ B_ε} K(x - ·)` is bounded with bounded support, hence in `L^{p'}`:
  weak convergence gives pointwise convergence, and dominated convergence gives convergence in
  `L^{p'}(B_R)` (`tendsto_eLpNorm_cv_kAnn`);
* the outer part is bounded by `2M/(2πL)` (`eLpNorm_cv_kOut_ball`).

Deviation (harmless): the manuscript splits `K_near` at `ε` and splits the `y`-integral of the far
part at `B_L`; we split the kernel itself at `|z| = ε` and `|z| = L`, which gives the same three
estimates.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.BS.VelH

theorem enorm_le_enorm_of_norm_le {a b : ℂ} (h : ‖a‖ ≤ ‖b‖) : ‖a‖ₑ ≤ ‖b‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal h

/-! ### The small ball -/

theorem kBall_eq_indicator_kernelNear {ε : ℝ} (hε1 : ε ≤ 1) (z : ℂ) :
    kBall ε z = (ball (0 : ℂ) ε).indicator kernelNear z := by
  unfold kBall
  by_cases hz : z ∈ ball (0 : ℂ) ε
  · rw [indicator_of_mem hz, indicator_of_mem hz, kernelNear_of_norm_lt]
    have := mem_ball_zero_iff.mp hz
    linarith
  · rw [indicator_of_notMem hz, indicator_of_notMem hz]

theorem lintegral_kBall_rpow {ε s : ℝ} (hε1 : ε ≤ 1) (hs : 0 < s) :
    ∫⁻ z, ‖kBall ε z‖ₑ ^ s = ∫⁻ z in ball (0 : ℂ) ε, ‖kernelNear z‖ₑ ^ s := by
  rw [← lintegral_indicator measurableSet_ball]
  congr 1
  funext z
  rw [kBall_eq_indicator_kernelNear hε1]
  by_cases hz : z ∈ ball (0 : ℂ) ε
  · simp [indicator_of_mem hz]
  · simp [indicator_of_notMem hz, ENNReal.zero_rpow_of_pos hs]

theorem tendsto_volume_ball_seq :
    Tendsto (fun m : ℕ => volume (ball (0 : ℂ) (1 / ((m : ℝ) + 1)))) atTop (𝓝 0) := by
  have h : ∀ m : ℕ, volume (ball (0 : ℂ) (1 / ((m : ℝ) + 1))) =
      ENNReal.ofReal ((1 / ((m : ℝ) + 1)) ^ 2) * volume (ball (0 : ℂ) 1) := by
    intro m
    rw [Measure.addHaar_ball_of_pos volume 0 (by positivity), Complex.finrank_real_complex]
  simp_rw [h]
  have h1 : Tendsto (fun m : ℕ => ENNReal.ofReal ((1 / ((m : ℝ) + 1)) ^ 2)) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
    rw [zero_pow two_ne_zero] at this
    simpa using ENNReal.tendsto_ofReal this
  -- `b` is given explicitly and no `simp` is used: with `Complex.volume_ball` in the simp set
  -- (imported once `Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls` is in scope, e.g.
  -- in the full library) a `simpa` here leaves the measure in `measure_ball_lt_top` undetermined.
  have h2 := ENNReal.Tendsto.mul_const (b := volume (ball (0 : ℂ) 1)) h1
    (Or.inr measure_ball_lt_top.ne)
  rwa [zero_mul] at h2

/-- `‖1_{B_ε} K‖_{L^s} → 0` as `ε = 1/(m+1) → 0`, for `1 ≤ s < 2`. -/
theorem tendsto_eLpNorm_kBall {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s < 2) :
    Tendsto (fun m : ℕ => eLpNorm (kBall (1 / ((m : ℝ) + 1))) (ENNReal.ofReal s) volume) atTop
      (𝓝 0) := by
  have hs0 : 0 < s := by linarith
  have hs0' : ENNReal.ofReal s ≠ 0 := by simpa using hs0
  have hfin : ∫⁻ z, ‖kernelNear z‖ₑ ^ s ≠ ∞ := by
    have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hs0' ENNReal.ofReal_ne_top
      (memLp_kernelNear hs1 hs2).eLpNorm_lt_top
    rw [ENNReal.toReal_ofReal hs0.le] at h
    exact h.ne
  have hint := tendsto_setLIntegral_zero hfin
    (s := fun m : ℕ => ball (0 : ℂ) (1 / ((m : ℝ) + 1))) tendsto_volume_ball_seq
  have heq : ∀ m : ℕ, eLpNorm (kBall (1 / ((m : ℝ) + 1))) (ENNReal.ofReal s) volume =
      (∫⁻ z in ball (0 : ℂ) (1 / ((m : ℝ) + 1)), ‖kernelNear z‖ₑ ^ s) ^ (1 / s) := by
    intro m
    have hm1 : 1 / ((m : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hs0' ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hs0.le, lintegral_kBall_rpow hm1 hs0]
  simp_rw [heq]
  have h2 := (ENNReal.continuous_rpow_const (y := 1 / s)).tendsto 0
  rw [ENNReal.zero_rpow_of_pos (by positivity)] at h2
  exact h2.comp hint

/-! ### Hölder, splitting -/

theorem convAbs_le_holder {k : ℂ → ℂ} (hk : AEStronglyMeasurable k volume) {f : ℂ → ℝ}
    (hf : AEStronglyMeasurable f volume) {p : ℝ} (hp : 1 < p) (x : ℂ) :
    Conv.convAbs k f x ≤
      eLpNorm k (ENNReal.ofReal p.conjExponent) volume * eLpNorm f (ENNReal.ofReal p) volume :=
  Conv.convAbs_le_eLpNorm_mul_eLpNorm hk hf
    (Real.HolderConjugate.conjExponent hp).symm.ennrealOfReal x

theorem convAbs_sub_le {k : ℂ → ℂ} (hk : AEStronglyMeasurable k volume) {f g : ℂ → ℝ}
    (hf : AEStronglyMeasurable f volume) (x : ℂ) :
    Conv.convAbs k (f - g) x ≤ Conv.convAbs k f x + Conv.convAbs k g x := by
  have hmp := Measure.measurePreserving_sub_left (volume : Measure ℂ) x
  have hk' : AEMeasurable (fun y => ‖k (x - y)‖ₑ) volume :=
    (hk.comp_measurePreserving hmp).enorm
  unfold Conv.convAbs
  have hadd := lintegral_add_left' (hk'.mul hf.enorm) (fun y => ‖k (x - y)‖ₑ * ‖g y‖ₑ)
  simp only [Pi.mul_apply] at hadd
  rw [← hadd]
  refine lintegral_mono fun y => ?_
  rw [← mul_add]
  gcongr
  exact enorm_sub_le

theorem kernel_split3 {ε L : ℝ} (hεL : ε ≤ L) (z : ℂ) :
    kBall ε z + kAnn ε L z + kOut L z = biotSavartKernel z := by
  unfold kBall kAnn kOut
  by_cases h1 : z ∈ ball (0 : ℂ) ε
  · have h2 : z ∉ ball (0 : ℂ) L \ ball (0 : ℂ) ε := fun h => h.2 h1
    have h3 : z ∉ (ball (0 : ℂ) L)ᶜ := fun h => h (ball_subset_ball hεL h1)
    rw [indicator_of_mem h1, indicator_of_notMem h2, indicator_of_notMem h3]
    ring
  · by_cases h4 : z ∈ ball (0 : ℂ) L
    · have h5 : z ∈ ball (0 : ℂ) L \ ball (0 : ℂ) ε := ⟨h4, h1⟩
      have h6 : z ∉ (ball (0 : ℂ) L)ᶜ := fun h => h h4
      rw [indicator_of_notMem h1, indicator_of_mem h5, indicator_of_notMem h6]
      ring
    · have h5 : z ∉ ball (0 : ℂ) L \ ball (0 : ℂ) ε := fun h => h4 h.1
      have h6 : z ∈ (ball (0 : ℂ) L)ᶜ := h4
      rw [indicator_of_notMem h1, indicator_of_notMem h5, indicator_of_mem h6]
      ring

theorem cv_split3 {f : ℂ → ℝ} (hf : AEStronglyMeasurable f volume) {x : ℂ}
    (hx : Conv.convAbs biotSavartKernel f x ≠ ∞) {ε L : ℝ} (hεL : ε ≤ L) :
    cv biotSavartKernel f x = cv (kBall ε) f x + cv (kAnn ε L) f x + cv (kOut L) f x := by
  have hB := integrable_of_convAbs (measurable_kBall ε).aestronglyMeasurable hf
    (ne_top_of_le_ne_top hx (Conv.convAbs_mono_kernel f
      (fun z => enorm_le_enorm_of_norm_le (norm_kBall_le ε z)) x))
  have hA := integrable_of_convAbs (measurable_kAnn ε L).aestronglyMeasurable hf
    (ne_top_of_le_ne_top hx (Conv.convAbs_mono_kernel f
      (fun z => enorm_le_enorm_of_norm_le (norm_kAnn_le ε L z)) x))
  have hO := integrable_of_convAbs (measurable_kOut L).aestronglyMeasurable hf
    (ne_top_of_le_ne_top hx (Conv.convAbs_mono_kernel f
      (fun z => enorm_le_enorm_of_norm_le (norm_kOut_le L z)) x))
  have hBA : Integrable (fun y => kBall ε (x - y) * (f y : ℂ) + kAnn ε L (x - y) * (f y : ℂ)) :=
    hB.add hA
  unfold cv
  rw [← integral_add hB hA, ← integral_add hBA hO]
  congr 1
  funext y
  rw [← kernel_split3 hεL (x - y)]
  ring

/-- `K ∗ f - K ∗ g = 1_{B_ε}K ∗ (f - g) + 1_{B_L∖B_ε}K ∗ (f - g) + 1_{ℝ²∖B_L}K ∗ (f - g)` a.e. -/
theorem velocity_sub_ae_eq_split {f g : ℂ → ℝ} (hf : MemLp f 1 volume) (hg : MemLp g 1 volume)
    {ε L : ℝ} (hεL : ε ≤ L) :
    velocity f - velocity g =ᵐ[volume]
      cv (kBall ε) (f - g) + cv (kAnn ε L) (f - g) + cv (kOut L) (f - g) := by
  filter_upwards [ae_convAbs_lt_top hf, ae_convAbs_lt_top hg] with x hxf hxg
  have hfg : AEStronglyMeasurable (f - g) volume := hf.1.sub hg.1
  have hx : Conv.convAbs biotSavartKernel (f - g) x ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.add_lt_top.2 ⟨hxf, hxg⟩).ne
      (convAbs_sub_le measurable_K.aestronglyMeasurable hf.1 x)
  have h1 := integrable_of_convAbs measurable_K.aestronglyMeasurable hf.1 hxf.ne
  have h2 := integrable_of_convAbs measurable_K.aestronglyMeasurable hg.1 hxg.ne
  simp only [Pi.sub_apply, Pi.add_apply]
  rw [velocity_eq_cv, velocity_eq_cv, ← cv_sub_right h1 h2, cv_split3 hfg hx hεL]

/-! ### The three estimates -/

/-- Young and Hölder on `B_R`: `‖k ∗ f‖_{L^q(B_R)} ≤ ‖k‖_s ‖f‖_p |B_R|^{1/q - 1/r}`. -/
theorem eLpNorm_cv_young_ball {k : ℂ → ℂ} (hk : AEStronglyMeasurable k volume) {f : ℂ → ℝ}
    (hf : AEStronglyMeasurable f volume) {s p r q : ℝ} (hs : 1 ≤ s) (hp : 1 ≤ p) (hr : 1 ≤ r)
    (hspr : 1 / s + 1 / p = 1 + 1 / r) (hq : 0 < q) (hqr : q ≤ r) (R : ℝ) :
    eLpNorm (cv k f) (ENNReal.ofReal q) (volume.restrict (ball (0 : ℂ) R)) ≤
      eLpNorm k (ENNReal.ofReal s) volume * eLpNorm f (ENNReal.ofReal p) volume *
        volume (ball (0 : ℂ) R) ^ (1 / q - 1 / r) := by
  set μR := volume.restrict (ball (0 : ℂ) R)
  have mN : AEStronglyMeasurable (Conv.convAbs k f) μR :=
    (Conv.measurable_convAbs hk hf).aestronglyMeasurable
  have h1 : eLpNorm (cv k f) (ENNReal.ofReal q) μR ≤
      eLpNorm (Conv.convAbs k f) (ENNReal.ofReal q) μR :=
    eLpNorm_mono_enorm fun x => by rw [enorm_eq_self]; exact enorm_cv_le k f x
  have h2 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μR)
    (ENNReal.ofReal_le_ofReal hqr) mN
  rw [ENNReal.toReal_ofReal hq.le, ENNReal.toReal_ofReal (by linarith),
    Measure.restrict_apply_univ] at h2
  refine h1.trans (h2.trans ?_)
  gcongr
  exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans
    (Conv.eLpNorm_convAbs_le_young hk hf hs hp hr hspr)

/-- The outer part: `‖1_{ℝ²∖B_L}K ∗ f‖_{L^q(B_R)} ≤ (2πL)⁻¹ ‖f‖₁ |B_R|^{1/q}`. -/
theorem eLpNorm_cv_kOut_ball {f : ℂ → ℝ} (hf : AEStronglyMeasurable f volume) {L : ℝ}
    (hL : 0 < L) (R : ℝ) (q : ℝ≥0∞) :
    eLpNorm (cv (kOut L) f) q (volume.restrict (ball (0 : ℂ) R)) ≤
      ENNReal.ofReal (2 * Real.pi * L)⁻¹ * eLpNorm f 1 volume *
        volume (ball (0 : ℂ) R) ^ q.toReal⁻¹ := by
  have hb : ∀ x, Conv.convAbs (kOut L) f x ≤
      ENNReal.ofReal (2 * Real.pi * L)⁻¹ * eLpNorm f 1 volume := fun x =>
    (Conv.convAbs_le_eLpNorm_top_mul (measurable_kOut L).aestronglyMeasurable hf x).trans
      (by gcongr; exact eLpNorm_kOut_top_le hL)
  refine (eLpNorm_mono_enorm fun x => ?_).trans (eLpNorm_ball_le_of_bound hb R q)
  rw [enorm_eq_self]
  exact enorm_cv_le _ _ _

/-- `k ∗ f = ∫ f Re k(x - ·) + i ∫ f Im k(x - ·)` at a point of absolute convergence. -/
theorem cv_eq_re_im {k : ℂ → ℂ} {f : ℂ → ℝ} {x : ℂ}
    (h : Integrable (fun y => k (x - y) * (f y : ℂ))) :
    cv k f x = ((∫ y, f y * (k (x - y)).re : ℝ) : ℂ) +
      ((∫ y, f y * (k (x - y)).im : ℝ) : ℂ) * Complex.I := by
  have h1 : (cv k f x).re = ∫ y, f y * (k (x - y)).re := by
    rw [cv, ← RCLike.re_to_complex, ← integral_re h]
    congr 1
    funext y
    simp [mul_comm]
  have h2 : (cv k f x).im = ∫ y, f y * (k (x - y)).im := by
    rw [cv, ← RCLike.im_to_complex, ← integral_im h]
    congr 1
    funext y
    simp [mul_comm]
  apply Complex.ext <;> simp [h1, h2]

theorem memLp_kAnn_comp {ε : ℝ} (hε : 0 < ε) (L : ℝ) (q : ℝ≥0∞) (x : ℂ) :
    MemLp (fun y => kAnn ε L (x - y)) q volume :=
  (memLp_kAnn hε L q).comp_measurePreserving (Measure.measurePreserving_sub_left volume x)

theorem integrable_cv_kAnn {ε : ℝ} (hε : 0 < ε) (L : ℝ) {p : ℝ} (hp : 1 < p) {g : ℂ → ℝ}
    (hg : MemLp g (ENNReal.ofReal p) volume) (x : ℂ) :
    Integrable (fun y => kAnn ε L (x - y) * (g y : ℂ)) := by
  refine integrable_of_convAbs (measurable_kAnn ε L).aestronglyMeasurable hg.1 ?_
  exact ((convAbs_le_holder (measurable_kAnn ε L).aestronglyMeasurable hg.1 hp x).trans_lt
    (ENNReal.mul_lt_top (memLp_kAnn hε L _).eLpNorm_lt_top hg.eLpNorm_lt_top)).ne

/-- Weak convergence gives pointwise convergence of `1_{B_L∖B_ε}K ∗ ωₙ`. -/
theorem tendsto_cv_kAnn {p : ℝ} (hp : 1 < p) {ωs : ℕ → ℂ → ℝ} {ω : ℂ → ℝ}
    (hconv : Prelim.WeakTendstoLp p ωs ω) {ε : ℝ} (hε : 0 < ε) (L : ℝ) (x : ℂ) :
    Tendsto (fun n => cv (kAnn ε L) (ωs n) x) atTop (𝓝 (cv (kAnn ε L) ω x)) := by
  have hk := memLp_kAnn_comp hε L (ENNReal.ofReal p.conjExponent) x
  have hre := hconv.2.2 (fun y => (kAnn ε L (x - y)).re) hk.re
  have him := hconv.2.2 (fun y => (kAnn ε L (x - y)).im) hk.im
  rw [cv_eq_re_im (integrable_cv_kAnn hε L hp hconv.2.1 x)]
  have heq : ∀ n, cv (kAnn ε L) (ωs n) x =
      ((∫ y, ωs n y * (kAnn ε L (x - y)).re : ℝ) : ℂ) +
        ((∫ y, ωs n y * (kAnn ε L (x - y)).im : ℝ) : ℂ) * Complex.I := fun n =>
    cv_eq_re_im (integrable_cv_kAnn hε L hp (hconv.1 n) x)
  simp_rw [heq]
  exact ((Complex.continuous_ofReal.tendsto _).comp hre).add
    (((Complex.continuous_ofReal.tendsto _).comp him).mul_const _)

/-- The annulus part tends to `0` in `L^q(B_R)`. -/
theorem tendsto_eLpNorm_cv_kAnn {p : ℝ} (hp : 1 < p) {ωs : ℕ → ℂ → ℝ} {ω : ℂ → ℝ}
    (hconv : Prelim.WeakTendstoLp p ωs ω) {N : ℝ≥0∞} (hN : N ≠ ∞)
    (hNb : ∀ n, eLpNorm (ωs n) (ENNReal.ofReal p) volume ≤ N) {ε : ℝ} (hε : 0 < ε) (L R : ℝ)
    {q : ℝ≥0∞} (hq0 : q ≠ 0) (hq : q ≠ ∞) :
    Tendsto (fun n => eLpNorm (cv (kAnn ε L) (ωs n - ω)) q (volume.restrict (ball (0 : ℂ) R)))
      atTop (𝓝 0) := by
  have : IsFiniteMeasure (volume.restrict (ball (0 : ℂ) R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  set Ck := eLpNorm (kAnn ε L) (ENNReal.ofReal p.conjExponent) volume
  have hCk : Ck ≠ ∞ := (memLp_kAnn hε L _).eLpNorm_ne_top
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp.le
  set B := Ck * (N + eLpNorm ω (ENNReal.ofReal p) volume)
  have hB : B ≠ ∞ := ENNReal.mul_ne_top hCk (ENNReal.add_ne_top.2 ⟨hN, hconv.2.1.eLpNorm_ne_top⟩)
  have hmk := (measurable_kAnn ε L).aestronglyMeasurable (μ := volume)
  refine tendsto_eLpNorm_zero_of_bound
    (fun n => (aestronglyMeasurable_cv hmk ((hconv.1 n).1.sub hconv.2.1.1)).restrict)
    (C := B.toReal) (fun n => Eventually.of_forall fun x => ?_)
    (Eventually.of_forall fun x => ?_) hq0 hq
  · have h : ‖cv (kAnn ε L) (ωs n - ω) x‖ₑ ≤ B := by
      refine (enorm_cv_le _ _ x).trans
        ((convAbs_le_holder hmk ((hconv.1 n).1.sub hconv.2.1.1) hp x).trans ?_)
      refine mul_le_mul_right ?_ _
      exact (eLpNorm_sub_le (hconv.1 n).1 hconv.2.1.1 hp1).trans (add_le_add (hNb n) le_rfl)
    rw [← ofReal_norm] at h
    exact (ENNReal.ofReal_le_iff_le_toReal hB).mp h
  · have heq : ∀ n, cv (kAnn ε L) (ωs n - ω) x = cv (kAnn ε L) (ωs n) x - cv (kAnn ε L) ω x :=
      fun n => cv_sub_right (integrable_cv_kAnn hε L hp (hconv.1 n) x)
        (integrable_cv_kAnn hε L hp hconv.2.1 x)
    simp_rw [heq]
    have := (tendsto_cv_kAnn hp hconv hε L x).sub_const (cv (kAnn ε L) ω x)
    rwa [sub_self] at this

end NonUniqueEuler.BS.VelH
