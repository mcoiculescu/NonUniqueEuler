import NonUniqueEuler.H.Sec2.Velocity.Kernel
import NonUniqueEuler.I.Sec2.KernelSplit
import NonUniqueEuler.Defs.Sec2.Spaces

/-!
# Helpers for `lem:velocity`(a): the near/far estimates

Helper file of `P/Sec2/Velocity.lean` (namespace `NonUniqueEuler.BS.VelH`). With
`K = K_near + K_far` (`kernelNear`, `kernelFar`), for `ω ∈ L¹`:

* `|K| ∗ |ω| ≤ |K_near| ∗ |ω| + |K_far| ∗ |ω|` and `|K_far| ∗ |ω| ≤ ‖ω‖₁/(2π)` everywhere;
* `K ∗ ω ∈ L¹ + L^∞` (`memL1AddLinf_velocity`);
* the local bound: if `‖|K_near| ∗ |ω|‖_{L^r} ≤ A` and `1 ≤ q ≤ r`, then
  `‖K ∗ ω‖_{L^q(B_R)} ≤ A |B_R|^{1/q-1/r} + ‖ω‖₁/(2π) |B_R|^{1/q}` (`eLpNorm_velocity_ball_le`);
* the energy-type bound `∫ |ω| (|K| ∗ |ω|) ≤ ‖ω‖_{r'} A + ‖ω‖₁²/(2π)` (`lintegral_mul_convAbs_le`).

These are the steps of the proof of `lem:velocity`(a) (`02_prelim.tex:323-343`), with the
exponents `r_p`, `s_p` left abstract.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.BS.VelH

/-- `1/(2π)` as an extended real. -/
def cFar : ℝ≥0∞ := ENNReal.ofReal (1 / (2 * Real.pi))

theorem cFar_ne_top : cFar ≠ ∞ := ENNReal.ofReal_ne_top

theorem measurable_kernelNear : Measurable kernelNear :=
  measurable_K.indicator measurableSet_ball

theorem measurable_kernelFar : Measurable kernelFar :=
  measurable_K.indicator measurableSet_ball.compl

theorem norm_K_le_near_far (z : ℂ) :
    ‖biotSavartKernel z‖ ≤ ‖kernelNear z‖ + ‖kernelFar z‖ := by
  rw [← kernelNear_add_kernelFar z]
  exact norm_add_le _ _

theorem lintegral_kernelNear : ∫⁻ z, ‖kernelNear z‖ₑ = 1 := by
  have h := lintegral_kBall (ε := 1) one_pos
  rw [ENNReal.ofReal_one] at h
  exact h

theorem memLp_kernelNear_one : MemLp kernelNear 1 volume := by
  have h := memLp_kernelNear (s := 1) le_rfl one_lt_two
  rwa [ENNReal.ofReal_one] at h

theorem convAbs_le_near_far {ω : ℂ → ℝ} (hω : AEStronglyMeasurable ω volume) (x : ℂ) :
    Conv.convAbs biotSavartKernel ω x ≤
      Conv.convAbs kernelNear ω x + Conv.convAbs kernelFar ω x :=
  convAbs_le_add measurable_kernelNear.aestronglyMeasurable hω norm_K_le_near_far x

theorem convAbs_far_le {ω : ℂ → ℝ} (hω : AEStronglyMeasurable ω volume) (x : ℂ) :
    Conv.convAbs kernelFar ω x ≤ cFar * eLpNorm ω 1 volume :=
  (Conv.convAbs_le_eLpNorm_top_mul measurable_kernelFar.aestronglyMeasurable hω x).trans
    (mul_le_mul_left memLp_kernelFar_top.2 _)

theorem ae_convAbs_lt_top {ω : ℂ → ℝ} (hω : MemLp ω 1 volume) :
    ∀ᵐ x, Conv.convAbs biotSavartKernel ω x < ∞ :=
  Conv.ae_convAbs_lt_top_of_split memLp_kernelNear_one memLp_kernelFar_top.1
    norm_K_le_near_far hω

/-- `lem:velocity`(a): `K ∗ ω ∈ L¹ + L^∞` for `ω ∈ L¹`, with `K_near ∗ ω ∈ L¹` and
`K_far ∗ ω ∈ L^∞`. -/
theorem memL1AddLinf_velocity {ω : ℂ → ℝ} (hω : MemLp ω 1 volume) :
    Prelim.MemL1AddLinf (velocity ω) := by
  have hm := hω.aestronglyMeasurable
  set v₁ := cv kernelNear ω with hv₁
  have hv₁m : AEStronglyMeasurable v₁ volume :=
    aestronglyMeasurable_cv measurable_kernelNear.aestronglyMeasurable hm
  have hv₁L1 : MemLp v₁ 1 volume := by
    refine ⟨hv₁m, ?_⟩
    rw [eLpNorm_one_eq_lintegral_enorm]
    calc ∫⁻ x, ‖v₁ x‖ₑ ≤ ∫⁻ x, Conv.convAbs kernelNear ω x :=
          lintegral_mono fun x => enorm_cv_le _ _ _
      _ = (∫⁻ z, ‖kernelNear z‖ₑ) * ∫⁻ y, ‖ω y‖ₑ :=
          Conv.lintegral_convAbs measurable_kernelNear.aestronglyMeasurable hm
      _ < ∞ := by
          rw [lintegral_kernelNear, one_mul, ← eLpNorm_one_eq_lintegral_enorm]
          exact hω.eLpNorm_lt_top
  have hvm : AEStronglyMeasurable (velocity ω) volume :=
    (Conv.stronglyMeasurable_velocity hm).aestronglyMeasurable
  refine ⟨v₁, velocity ω - v₁, hv₁L1, ?_, Eventually.of_forall fun x => by simp⟩
  refine memLp_top_of_bound (hvm.sub hv₁m) (cFar * eLpNorm ω 1 volume).toReal ?_
  filter_upwards [ae_convAbs_lt_top hω] with x hx
  have hK := integrable_of_convAbs measurable_K.aestronglyMeasurable hm hx.ne
  have hN := integrable_of_convAbs measurable_kernelNear.aestronglyMeasurable hm
    ((Conv.convAbs_mono_kernel ω (fun z => by
      rw [← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (by
        unfold kernelNear; exact norm_indicator_le_norm_self _ _)) x).trans_lt hx).ne
  have heq : velocity ω x - v₁ x = cv kernelFar ω x := by
    rw [velocity_eq_cv, hv₁, ← cv_sub_left hK hN]
    congr 1
    funext z
    rw [← kernelNear_add_kernelFar z]
    ring
  rw [Pi.sub_apply, heq]
  have h1 := (enorm_cv_le kernelFar ω x).trans (convAbs_far_le hm x)
  rw [← ofReal_norm] at h1
  exact (ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_ne_top cFar_ne_top hω.eLpNorm_ne_top)).mp
    h1

/-- The local bound `‖K ∗ ω‖_{L^q(B_R)} ≤ A |B_R|^{1/q-1/r} + ‖ω‖₁/(2π) |B_R|^{1/q}`, `1 ≤ q ≤ r`,
where `A ≥ ‖|K_near| ∗ |ω|‖_{L^r}`. -/
theorem eLpNorm_velocity_ball_le {ω : ℂ → ℝ} (hω : AEStronglyMeasurable ω volume) {q r : ℝ}
    (hq : 1 ≤ q) (hqr : q ≤ r) {A : ℝ≥0∞}
    (hA : eLpNorm (Conv.convAbs kernelNear ω) (ENNReal.ofReal r) volume ≤ A) (R : ℝ) :
    eLpNorm (velocity ω) (ENNReal.ofReal q) (volume.restrict (ball (0 : ℂ) R)) ≤
      A * volume (ball (0 : ℂ) R) ^ (1 / q - 1 / r) +
        cFar * eLpNorm ω 1 volume * volume (ball (0 : ℂ) R) ^ (1 / q) := by
  set μR := volume.restrict (ball (0 : ℂ) R)
  have hq0 : 0 < q := by linarith
  have hr0 : 0 < r := by linarith
  have mN : AEStronglyMeasurable (Conv.convAbs kernelNear ω) μR :=
    (Conv.measurable_convAbs measurable_kernelNear.aestronglyMeasurable hω).aestronglyMeasurable
  have mF : AEStronglyMeasurable (Conv.convAbs kernelFar ω) μR :=
    (Conv.measurable_convAbs measurable_kernelFar.aestronglyMeasurable hω).aestronglyMeasurable
  have h1 : eLpNorm (velocity ω) (ENNReal.ofReal q) μR ≤
      eLpNorm (Conv.convAbs kernelNear ω + Conv.convAbs kernelFar ω) (ENNReal.ofReal q) μR := by
    refine eLpNorm_mono_enorm fun x => ?_
    rw [enorm_eq_self]
    exact (Conv.enorm_velocity_le ω x).trans (convAbs_le_near_far hω x)
  refine h1.trans ((eLpNorm_add_le mN mF (by simpa using hq)).trans (add_le_add ?_ ?_))
  · have h2 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μR)
      (ENNReal.ofReal_le_ofReal hqr) mN
    rw [ENNReal.toReal_ofReal hq0.le, ENNReal.toReal_ofReal hr0.le,
      Measure.restrict_apply_univ] at h2
    refine h2.trans ?_
    gcongr
    exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans hA
  · have h3 := eLpNorm_ball_le_of_bound (convAbs_far_le hω) R (ENNReal.ofReal q)
    rwa [ENNReal.toReal_ofReal hq0.le, ← one_div] at h3

/-- `∫ |ω| (|K| ∗ |ω|) ≤ ‖ω‖_{r'} A + ‖ω‖₁²/(2π)` where `A ≥ ‖|K_near| ∗ |ω|‖_{L^r}`. -/
theorem lintegral_mul_convAbs_le {ω : ℂ → ℝ} (hω : AEStronglyMeasurable ω volume) {r r' : ℝ}
    (hrr' : r'.HolderConjugate r) {A : ℝ≥0∞}
    (hA : eLpNorm (Conv.convAbs kernelNear ω) (ENNReal.ofReal r) volume ≤ A) :
    ∫⁻ x, ‖ω x‖ₑ * Conv.convAbs biotSavartKernel ω x ≤
      eLpNorm ω (ENNReal.ofReal r') volume * A + cFar * eLpNorm ω 1 volume * eLpNorm ω 1 volume := by
  have mN : AEMeasurable (Conv.convAbs kernelNear ω) volume :=
    (Conv.measurable_convAbs measurable_kernelNear.aestronglyMeasurable hω).aemeasurable
  calc ∫⁻ x, ‖ω x‖ₑ * Conv.convAbs biotSavartKernel ω x
      ≤ ∫⁻ x, (‖ω x‖ₑ * Conv.convAbs kernelNear ω x + ‖ω x‖ₑ * (cFar * eLpNorm ω 1 volume)) := by
        refine lintegral_mono fun x => ?_
        rw [← mul_add]
        gcongr
        exact (convAbs_le_near_far hω x).trans (add_le_add le_rfl (convAbs_far_le hω x))
    _ = (∫⁻ x, ‖ω x‖ₑ * Conv.convAbs kernelNear ω x) +
          ∫⁻ x, ‖ω x‖ₑ * (cFar * eLpNorm ω 1 volume) :=
        lintegral_add_left' (f := fun x => ‖ω x‖ₑ * Conv.convAbs kernelNear ω x)
          (hω.enorm.mul mN) (fun x => ‖ω x‖ₑ * (cFar * eLpNorm ω 1 volume))
    _ ≤ eLpNorm ω (ENNReal.ofReal r') volume * A +
          cFar * eLpNorm ω 1 volume * eLpNorm ω 1 volume := by
        refine add_le_add ((lintegral_enorm_mul_le hω mN hrr').trans (mul_le_mul_right hA _)) ?_
        rw [lintegral_mul_const'' _ hω.enorm, ← eLpNorm_one_eq_lintegral_enorm, mul_comm]

/-! ### Finishing: the form of the statement -/

/-- The local bound with an explicit linear right side, plus membership. -/
theorem velocity_ball_final {ω : ℂ → ℝ} (h1 : MemLp ω 1 volume) {p : ℝ≥0∞}
    (hp : MemLp ω p volume) {q r : ℝ} (hq : 1 ≤ q) (hqr : q ≤ r) {A : ℝ≥0∞} (hA0 : A ≠ ∞)
    (hA : eLpNorm (Conv.convAbs kernelNear ω) (ENNReal.ofReal r) volume ≤ A * eLpNorm ω p volume)
    (R : ℝ) :
    MemLp (velocity ω) (ENNReal.ofReal q) (volume.restrict (ball (0 : ℂ) R)) ∧
      eLpNorm (velocity ω) (ENNReal.ofReal q) (volume.restrict (ball (0 : ℂ) R)) ≤
        (A * volume (ball (0 : ℂ) R) ^ (1 / q - 1 / r)) * eLpNorm ω p volume +
          (cFar * volume (ball (0 : ℂ) R) ^ (1 / q)) * eLpNorm ω 1 volume := by
  have hV : volume (ball (0 : ℂ) R) ≠ ∞ := measure_ball_lt_top.ne
  have hq0 : 0 < q := by linarith
  have hexp : 0 ≤ 1 / q - 1 / r := by
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le hq0 hqr
  have h := eLpNorm_velocity_ball_le h1.aestronglyMeasurable hq hqr hA R
  have h' : eLpNorm (velocity ω) (ENNReal.ofReal q) (volume.restrict (ball (0 : ℂ) R)) ≤
      (A * volume (ball (0 : ℂ) R) ^ (1 / q - 1 / r)) * eLpNorm ω p volume +
        (cFar * volume (ball (0 : ℂ) R) ^ (1 / q)) * eLpNorm ω 1 volume := by
    refine h.trans (le_of_eq ?_)
    ring
  refine ⟨⟨(Conv.stronglyMeasurable_velocity h1.aestronglyMeasurable).aestronglyMeasurable,
    h'.trans_lt ?_⟩, h'⟩
  refine ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (ENNReal.mul_lt_top hA0.lt_top
    (ENNReal.rpow_lt_top_of_nonneg hexp hV)) hp.eLpNorm_lt_top,
    ENNReal.mul_lt_top (ENNReal.mul_lt_top cFar_ne_top.lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by positivity) hV)) h1.eLpNorm_lt_top⟩

/-- Linear finishing: `X ≤ A b + B a` gives `X ≤ (A + B)(‖ω‖₁ + ‖ω‖_p)` in real form. -/
theorem le_ofReal_mul_normL1Lp {X : ℝ≥0∞} {ω : ℂ → ℝ} {p : ℝ≥0∞} (h1 : MemLp ω 1 volume)
    (hp : MemLp ω p volume) {A B : ℝ≥0∞} (hA : A ≠ ∞) (hB : B ≠ ∞)
    (h : X ≤ A * eLpNorm ω p volume + B * eLpNorm ω 1 volume) :
    X ≤ ENNReal.ofReal ((A.toReal + B.toReal) * Prelim.normL1Lp p ω) := by
  have ha := h1.eLpNorm_ne_top
  have hb := hp.eLpNorm_ne_top
  unfold Prelim.normL1Lp
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_toReal hA,
    ENNReal.ofReal_toReal hB, ENNReal.ofReal_toReal ha, ENNReal.ofReal_toReal hb]
  refine h.trans ?_
  calc A * eLpNorm ω p volume + B * eLpNorm ω 1 volume
      ≤ A * (eLpNorm ω 1 volume + eLpNorm ω p volume) +
          B * (eLpNorm ω 1 volume + eLpNorm ω p volume) := by
        gcongr
        · exact le_add_self
        · exact le_self_add
    _ = (A + B) * (eLpNorm ω 1 volume + eLpNorm ω p volume) := by ring

/-- Quadratic finishing: `X ≤ (a + b)(A b) + B a a` gives `X ≤ (A + B)(a + b)²`. -/
theorem le_ofReal_mul_normL1Lp_sq {X : ℝ≥0∞} {ω : ℂ → ℝ} {p : ℝ≥0∞} (h1 : MemLp ω 1 volume)
    (hp : MemLp ω p volume) {A B : ℝ≥0∞} (hA : A ≠ ∞) (hB : B ≠ ∞)
    (h : X ≤ (eLpNorm ω 1 volume + eLpNorm ω p volume) * (A * eLpNorm ω p volume) +
      B * eLpNorm ω 1 volume * eLpNorm ω 1 volume) :
    X ≤ ENNReal.ofReal ((A.toReal + B.toReal) * Prelim.normL1Lp p ω ^ 2) := by
  have ha := h1.eLpNorm_ne_top
  have hb := hp.eLpNorm_ne_top
  unfold Prelim.normL1Lp
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_toReal hA,
    ENNReal.ofReal_toReal hB, ENNReal.ofReal_toReal ha, ENNReal.ofReal_toReal hb]
  refine h.trans ?_
  set a := eLpNorm ω 1 volume
  set b := eLpNorm ω p volume
  calc (a + b) * (A * b) + B * a * a ≤ (a + b) * (A * (a + b)) + B * (a + b) * (a + b) := by
        gcongr
        · exact le_add_self
        · exact le_self_add
        · exact le_self_add
    _ = (A + B) * (a + b) ^ 2 := by ring

theorem ofReal_mul_le_of_le {C C' x : ℝ} (hx : 0 ≤ x) (hC : C ≤ C') :
    ENNReal.ofReal (C * x) ≤ ENNReal.ofReal (C' * x) :=
  ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC hx)

end NonUniqueEuler.BS.VelH
