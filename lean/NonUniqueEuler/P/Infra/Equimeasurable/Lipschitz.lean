import NonUniqueEuler.Defs.Infra.Equimeasurable
import NonUniqueEuler.I.Infra.Equimeasurable.Distribution
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# Proof: equimeasurability from `Lip₀` renormalizations; stability (I-EQM)

Proof of `NonUniqueEuler/I/Infra/Equimeasurable/Lipschitz.lean` (same declarations, same
statements).

* `of_integral_lipO_eq` (`lem:renorm-all-t`, `03_compactness.tex:670-677`): the ramps
  `β_n(z) = min 1 ((n+1) (z - s)⁺)` are in `Lip₀` for `s > 0`, are nonnegative, increase in
  `n` and converge pointwise to `1_{(s,∞)}`; monotone convergence
  (`lintegral_tendsto_of_tendsto_of_monotone`) identifies `|{g > s}|` as the limit of
  `∫ β_n(g)`. The sets `{g < -s}` use `z ↦ β_n(-z)`.
* `integral_lipO_eq`: `Equimeasurable.integral_comp_eq` (interface `Distribution`).
* `comp_measurePreserving`: `MeasurePreserving.measure_preimage`.
* `of_tendsto`: `|∫ β(gₙ) - ∫ β(g)| ≤ K ‖gₙ - g‖₁` (`tendsto_integral_of_L1`).
* `IsRenormalization.isLipO`: `lipschitzWith_of_nnnorm_deriv_le`.

Helper lemmas live in the namespace `NonUniqueEuler.EquimeasLipschitzAux`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace NonUniqueEuler

namespace EquimeasLipschitzAux

/-- A `Lip₀` function of an `L¹` function is integrable. -/
theorem integrable_lipO_comp {g : ℂ → ℝ} (hg : MemLp g 1) {β : ℝ → ℝ}
    (hβ : Equimeas.IsLipO β) : Integrable (fun x => β (g x)) := by
  obtain ⟨⟨K, hK⟩, h0⟩ := hβ
  exact memLp_one_iff_integrable.1 (hK.comp_memLp h0 hg)

/-- The ramp `z ↦ min 1 ((n+1) (z - s)⁺)`, increasing to `1_{(s,∞)}` as `n → ∞`. -/
def ramp (s : ℝ) (n : ℕ) (z : ℝ) : ℝ := min 1 (((n : ℝ) + 1) * max (z - s) 0)

theorem ramp_lipschitz (s : ℝ) (n : ℕ) : LipschitzWith ((n : NNReal) + 1) (ramp s n) := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  rw [Real.dist_eq, Real.dist_eq]
  unfold ramp
  have hc : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  calc |min 1 (((n : ℝ) + 1) * max (a - s) 0) - min 1 (((n : ℝ) + 1) * max (b - s) 0)|
      ≤ max |(1 : ℝ) - 1|
          |((n : ℝ) + 1) * max (a - s) 0 - ((n : ℝ) + 1) * max (b - s) 0| :=
        abs_min_sub_min_le_max _ _ _ _
    _ = ((n : ℝ) + 1) * |max (a - s) 0 - max (b - s) 0| := by
        rw [sub_self, abs_zero, ← mul_sub, abs_mul, abs_of_pos hc]
        exact max_eq_right (mul_nonneg hc.le (abs_nonneg _))
    _ ≤ ((n : ℝ) + 1) * |(a - s) - (b - s)| := by
        exact mul_le_mul_of_nonneg_left (abs_max_sub_max_le_abs (a - s) (b - s) 0) hc.le
    _ = (((n : NNReal) + 1 : NNReal) : ℝ) * |a - b| := by
        push_cast
        rw [sub_sub_sub_cancel_right]

theorem ramp_zero {s : ℝ} (hs : 0 < s) (n : ℕ) : ramp s n 0 = 0 := by
  unfold ramp
  rw [max_eq_right (by linarith), mul_zero, min_eq_right zero_le_one]

theorem ramp_isLipO {s : ℝ} (hs : 0 < s) (n : ℕ) : Equimeas.IsLipO (ramp s n) :=
  ⟨⟨_, ramp_lipschitz s n⟩, ramp_zero hs n⟩

theorem ramp_nonneg (s : ℝ) (n : ℕ) (z : ℝ) : 0 ≤ ramp s n z :=
  le_min zero_le_one (mul_nonneg (by positivity) (le_max_right _ _))

theorem ramp_mono (s z : ℝ) : Monotone fun n => ramp s n z := by
  intro n m hnm
  simp only [ramp]
  refine min_le_min_left 1 (mul_le_mul_of_nonneg_right ?_ (le_max_right _ _))
  have : (n : ℝ) ≤ m := Nat.cast_le.2 hnm
  linarith

theorem ramp_tendsto (s z : ℝ) :
    Tendsto (fun n => ramp s n z) atTop (𝓝 ((Ioi s).indicator 1 z)) := by
  by_cases hz : s < z
  · rw [indicator_of_mem (show z ∈ Ioi s from hz), Pi.one_apply]
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / (z - s))
    have hzs : 0 < z - s := by linarith
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    unfold ramp
    rw [max_eq_left hzs.le, min_eq_left]
    have h1 : 1 < (N : ℝ) * (z - s) := by
      rwa [div_lt_iff₀ hzs] at hN
    have h2 : (N : ℝ) ≤ n := Nat.cast_le.2 hn
    nlinarith
  · rw [indicator_of_notMem (show z ∉ Ioi s from hz)]
    refine tendsto_const_nhds.congr' (Eventually.of_forall fun n => ?_)
    show (0 : ℝ) = ramp s n z
    unfold ramp
    rw [max_eq_right (by linarith [not_lt.1 hz]), mul_zero, min_eq_right zero_le_one]

theorem isLipO_neg : Equimeas.IsLipO (fun z : ℝ => -z) :=
  ⟨⟨1, LipschitzWith.of_dist_le_mul fun a b => by simp [dist_neg_neg]⟩, neg_zero⟩

/-- Monotone convergence: `ofReal (∫ bₙ(g)) → |g⁻¹(A)|` when `bₙ ∈ Lip₀`, `bₙ ≥ 0`, `bₙ ↑ 1_A`. -/
theorem tendsto_ofReal_integral_of_approx {g : ℂ → ℝ} (hg : MemLp g 1) {A : Set ℝ}
    (hA : MeasurableSet A) {b : ℕ → ℝ → ℝ} (hb : ∀ n, Equimeas.IsLipO (b n))
    (hb0 : ∀ n z, 0 ≤ b n z) (hmono : ∀ z, Monotone fun n => b n z)
    (hlim : ∀ z, Tendsto (fun n => b n z) atTop (𝓝 (A.indicator 1 z))) :
    Tendsto (fun n => ENNReal.ofReal (∫ x, b n (g x))) atTop (𝓝 (volume (g ⁻¹' A))) := by
  have heq : ∀ n, ENNReal.ofReal (∫ x, b n (g x)) = ∫⁻ x, ENNReal.ofReal (b n (g x)) :=
    fun n => ofReal_integral_eq_lintegral_ofReal (integrable_lipO_comp hg (hb n))
      (Eventually.of_forall fun x => hb0 n (g x))
  simp only [heq]
  have hF : (fun x => ENNReal.ofReal (A.indicator 1 (g x))) = (g ⁻¹' A).indicator 1 := by
    funext x
    by_cases hx : g x ∈ A
    · simp [indicator_of_mem hx, indicator_of_mem (show x ∈ g ⁻¹' A from hx)]
    · simp [indicator_of_notMem hx, indicator_of_notMem (show x ∉ g ⁻¹' A from hx)]
  have hlim' := lintegral_tendsto_of_tendsto_of_monotone (μ := volume)
    (f := fun n x => ENNReal.ofReal (b n (g x)))
    (F := fun x => ENNReal.ofReal (A.indicator 1 (g x)))
    (fun n => ENNReal.measurable_ofReal.comp_aemeasurable
      ((hb n).1.choose_spec.continuous.measurable.comp_aemeasurable hg.1.aemeasurable))
    (Eventually.of_forall fun x => fun i j hij => ENNReal.ofReal_le_ofReal (hmono (g x) hij))
    (Eventually.of_forall fun x => ENNReal.tendsto_ofReal (hlim (g x)))
  rw [hF, lintegral_indicator_one₀ (hg.1.aemeasurable.nullMeasurable hA)] at hlim'
  exact hlim'

/-- Equal `∫ bₙ(·)` along an approximation `bₙ ↑ 1_A` gives equal measures of preimages. -/
theorem volume_preimage_eq_of_approx {g h : ℂ → ℝ} (hg : MemLp g 1) (hh : MemLp h 1)
    {A : Set ℝ} (hA : MeasurableSet A) {b : ℕ → ℝ → ℝ} (hb : ∀ n, Equimeas.IsLipO (b n))
    (hb0 : ∀ n z, 0 ≤ b n z) (hmono : ∀ z, Monotone fun n => b n z)
    (hlim : ∀ z, Tendsto (fun n => b n z) atTop (𝓝 (A.indicator 1 z)))
    (H : ∀ n, ∫ x, b n (g x) = ∫ x, b n (h x)) :
    volume (g ⁻¹' A) = volume (h ⁻¹' A) := by
  have h1 := tendsto_ofReal_integral_of_approx hg hA hb hb0 hmono hlim
  have h2 := tendsto_ofReal_integral_of_approx hh hA hb hb0 hmono hlim
  simp only [H] at h1
  exact tendsto_nhds_unique h1 h2

/-- `∫ β(Gₙ) → ∫ β(g)` when `Gₙ → g` in `L¹` and `β ∈ Lip₀`. -/
theorem tendsto_integral_lipO {G : ℕ → ℂ → ℝ} {g : ℂ → ℝ} (hGm : ∀ n, MemLp (G n) 1)
    (hg : MemLp g 1) (hG : Tendsto (fun n => eLpNorm (G n - g) 1 volume) atTop (𝓝 0))
    {β : ℝ → ℝ} (hβ : Equimeas.IsLipO β) :
    Tendsto (fun n => ∫ x, β (G n x)) atTop (𝓝 (∫ x, β (g x))) := by
  obtain ⟨⟨K, hK⟩, h0⟩ := hβ
  refine tendsto_integral_of_L1 _ (integrable_lipO_comp hg ⟨⟨K, hK⟩, h0⟩).aestronglyMeasurable
    (Eventually.of_forall fun n => integrable_lipO_comp (hGm n) ⟨⟨K, hK⟩, h0⟩) ?_
  have hup : ∀ n, ∫⁻ x, ‖β (G n x) - β (g x)‖ₑ ≤ K * eLpNorm (G n - g) 1 volume := by
    intro n
    rw [eLpNorm_one_eq_lintegral_enorm, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    refine lintegral_mono fun x => ?_
    have := hK.edist_le_mul (G n x) (g x)
    simpa [edist_eq_enorm_sub] using this
  have hlim : Tendsto (fun n => (K : ℝ≥0∞) * eLpNorm (G n - g) 1 volume) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hG (Or.inr ENNReal.coe_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le) hup

end EquimeasLipschitzAux

namespace Equimeasurable

open EquimeasLipschitzAux in
/-- If `∫ β(g) = ∫ β(h)` for every `β ∈ Lip₀`, then `g` and `h` are equimeasurable. -/
theorem of_integral_lipO_eq {g h : ℂ → ℝ} (hg : MemLp g 1) (hh : MemLp h 1)
    (H : ∀ β : ℝ → ℝ, Equimeas.IsLipO β → ∫ x, β (g x) = ∫ x, β (h x)) :
    Equimeasurable g h := by
  refine ⟨hg, hh, fun s hs => ⟨?_, ?_⟩⟩
  · exact volume_preimage_eq_of_approx hg hh measurableSet_Ioi (b := ramp s)
      (ramp_isLipO hs) (ramp_nonneg s) (ramp_mono s) (ramp_tendsto s)
      (fun n => H _ (ramp_isLipO hs n))
  · have hind : ∀ z : ℝ, (Iio (-s)).indicator (1 : ℝ → ℝ) z = (Ioi s).indicator 1 (-z) := by
      intro z
      by_cases hz : z < -s
      · rw [indicator_of_mem (show z ∈ Iio (-s) from hz),
          indicator_of_mem (show -z ∈ Ioi s from by simp only [mem_Ioi]; linarith)]
        rfl
      · rw [indicator_of_notMem (show z ∉ Iio (-s) from hz),
          indicator_of_notMem (show -z ∉ Ioi s from by simp only [mem_Ioi]; linarith)]
    exact volume_preimage_eq_of_approx hg hh measurableSet_Iio
      (b := fun n z => ramp s n (-z))
      (fun n => (ramp_isLipO hs n).comp isLipO_neg) (fun n z => ramp_nonneg s n (-z))
      (fun z => ramp_mono s (-z)) (fun z => by rw [hind]; exact ramp_tendsto s (-z))
      (fun n => H _ ((ramp_isLipO hs n).comp isLipO_neg))

/-- Equimeasurable functions have the same `∫ β(·)` for every `β ∈ Lip₀`. -/
theorem integral_lipO_eq {g h : ℂ → ℝ} (H : Equimeasurable g h) {β : ℝ → ℝ}
    (hβ : Equimeas.IsLipO β) : ∫ x, β (g x) = ∫ x, β (h x) :=
  H.integral_comp_eq hβ.1.choose_spec.continuous.measurable hβ.2

/-- Composition with a measure-preserving map. -/
theorem comp_measurePreserving {g : ℂ → ℝ} (hg : MemLp g 1) {T : ℂ → ℂ}
    (hT : MeasurePreserving T volume volume) : Equimeasurable (g ∘ T) g := by
  refine ⟨hg.comp_measurePreserving hT, hg, fun s _ => ⟨?_, ?_⟩⟩
  · exact hT.measure_preimage (hg.1.aemeasurable.nullMeasurable measurableSet_Ioi)
  · exact hT.measure_preimage (hg.1.aemeasurable.nullMeasurable measurableSet_Iio)

open EquimeasLipschitzAux in
/-- `L¹` limits of equimeasurable pairs are equimeasurable. -/
theorem of_tendsto {G H : ℕ → ℂ → ℝ} {g h : ℂ → ℝ} (hGH : ∀ n, Equimeasurable (G n) (H n))
    (hg : MemLp g 1) (hh : MemLp h 1)
    (hG : Tendsto (fun n => eLpNorm (G n - g) 1 volume) atTop (𝓝 0))
    (hH : Tendsto (fun n => eLpNorm (H n - h) 1 volume) atTop (𝓝 0)) :
    Equimeasurable g h := by
  refine of_integral_lipO_eq hg hh fun β hβ => ?_
  have h1 := tendsto_integral_lipO (fun n => (hGH n).1) hg hG hβ
  have h2 := tendsto_integral_lipO (fun n => (hGH n).2.1) hh hH hβ
  have h1' : Tendsto (fun n => ∫ x, β (H n x)) atTop (𝓝 (∫ x, β (g x))) :=
    h1.congr fun n => integral_lipO_eq (hGH n) hβ
  exact tendsto_nhds_unique h1' h2

end Equimeasurable

/-- Every renormalization of `def:weak` (`C¹`, bounded derivative, `Υ(0) = 0`) is in `Lip₀`. -/
theorem IsRenormalization.isLipO {Υ : ℝ → ℝ} (hΥ : IsRenormalization Υ) :
    Equimeas.IsLipO Υ := by
  obtain ⟨C, hC⟩ := hΥ.deriv_bounded
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  refine ⟨⟨C.toNNReal, lipschitzWith_of_nnnorm_deriv_le
    (hΥ.contDiff.differentiable one_ne_zero) fun x => ?_⟩, hΥ.map_zero⟩
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, Real.coe_toNNReal _ hC0]
  exact hC x

end NonUniqueEuler
