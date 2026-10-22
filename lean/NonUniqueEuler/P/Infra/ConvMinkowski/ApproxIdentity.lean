import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Proof: approximate identities in `L¹_loc(ℝ²)` (library I-CONV)

Proof of `I/Infra/ConvMinkowski/ApproxIdentity.lean`. Manuscript: the proof of `lem:commutator`,
`03_compactness.tex:425-431` (convergence `g ⋆ ψ_ε → (∫ψ) g` in `L¹(B_R)`: for continuous `g` by
uniform continuity, in general by density and the bound `‖g ⋆ ψ_ε‖_{1,R} ≤ ‖ψ‖_{L¹} ‖g‖_{1,R+1}`).

**Structure (density on the whole operator, as in the manuscript).**
1. `tendsto_aux_of_measurable`: the claim for a *measurable* `g`. For a continuous `φ`,
   `T_ε g - T_ε φ` is bounded pointwise by
   `K ∫_{B₁} |g - φ|(x - εz) dz + |∫ψ| |g - φ|(x)` (`enorm_pointwise_le`), whose `L¹(B_R)` norm is
   `≤ (K |B₁| + |∫ψ|) ‖g - φ‖_{L¹(B_{R+1})}` for `0 < ε ≤ 1` (Tonelli and translation invariance,
   `setLIntegral_ball_comp_sub_le`); and `|T_ε φ| ≤ θ K |B₁|` on `B_R` once `ε` is below the
   uniform-continuity modulus of `φ` on `\bar B_{R+1}` (`norm_integral_comp_sub_smul_sub_le`).
   The approximating `φ` comes from `Integrable.exists_hasCompactSupport_lintegral_sub_le` applied
   to `1_{B_{R+1}} g`. The combined estimate is `lintegral_le_of_measurable`.
2. The theorem: replace `g` by a measurable representative `g'`; for `ε ≠ 0` the inner integrals
   agree for every `x` (the map `z ↦ x - εz` is quasi-measure-preserving), and `g x = g' x` for a.e.
   `x`.

No deviation from the manuscript: this is its argument (with `T_ε` kept in the substituted form
`∫_{B₁} g(x - εz) ψ(z) dz`). The Bochner integral is `0` where the integrand is not integrable;
`enorm_integral_sub_le_of_integrable` handles this without any a.e. argument in `x`.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.Conv

/-- `‖∫ F - ∫ G‖ₑ ≤ ∫⁻ ‖F - G‖ₑ` for an integrable `G` and an a.e. strongly measurable `F`
(`F` need not be integrable: then the right side is `∞`). -/
private lemma enorm_integral_sub_le_of_integrable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F G : α → ℝ} (hF : AEStronglyMeasurable F μ) (hG : Integrable G μ) :
    ‖(∫ a, F a ∂μ) - ∫ a, G a ∂μ‖ₑ ≤ ∫⁻ a, ‖F a - G a‖ₑ ∂μ := by
  by_cases h : ∫⁻ a, ‖F a - G a‖ₑ ∂μ = ∞
  · rw [h]; exact le_top
  · have hFG : Integrable (fun a => F a - G a) μ :=
      ⟨hF.sub hG.aestronglyMeasurable, lt_top_iff_ne_top.2 h⟩
    have hFi : Integrable F μ :=
      (hFG.add hG).congr (Eventually.of_forall fun a => by simp)
    rw [← integral_sub hFi hG]
    exact enorm_integral_le_lintegral_enorm _

/-- Translation by a vector of norm `< 1` maps `B_R` into `B_{R+1}`, so
`∫_{B_R} h(x - a) dx ≤ ∫_{B_{R+1}} h`. -/
private lemma setLIntegral_ball_comp_sub_le (h : ℂ → ℝ≥0∞) (R : ℝ) {a : ℂ} (ha : ‖a‖ < 1) :
    ∫⁻ x in ball (0 : ℂ) R, h (x - a) ≤ ∫⁻ x in ball (0 : ℂ) (R + 1), h x := by
  calc ∫⁻ x in ball (0 : ℂ) R, h (x - a)
      = ∫⁻ x in ball (0 : ℂ) R, (ball (0 : ℂ) (R + 1)).indicator h (x - a) := by
        refine setLIntegral_congr_fun measurableSet_ball (fun x hx => ?_)
        rw [indicator_of_mem]
        rw [mem_ball_zero_iff] at hx ⊢
        calc ‖x - a‖ ≤ ‖x‖ + ‖a‖ := norm_sub_le _ _
          _ < R + 1 := add_lt_add hx ha
    _ ≤ ∫⁻ x, (ball (0 : ℂ) (R + 1)).indicator h (x - a) := setLIntegral_le_lintegral _ _
    _ = ∫⁻ x, (ball (0 : ℂ) (R + 1)).indicator h x :=
        lintegral_sub_right_eq_self (fun y => (ball (0 : ℂ) (R + 1)).indicator h y) a
    _ = ∫⁻ x in ball (0 : ℂ) (R + 1), h x := lintegral_indicator measurableSet_ball h

/-- A continuous function on `ℂ` is integrable on the unit ball. -/
private lemma integrableOn_ball_one_of_continuous {f : ℂ → ℝ} (hf : Continuous f) :
    IntegrableOn f (ball (0 : ℂ) 1) volume :=
  (hf.continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℂ) 1)).mono_set
    ball_subset_closedBall

/-- The pointwise comparison of `T_ε g` with `T_ε φ`:
`|T_ε g(x)| ≤ K ∫_{B₁} |g - φ|(x - εz) dz + |T_ε φ(x)| + |∫ψ| |g - φ|(x)`. -/
private lemma enorm_pointwise_le {g φ ψ : ℂ → ℝ} (hg : Measurable g) (hφ : Continuous φ)
    (hψ : Continuous ψ) {K : ℝ} (hK : ∀ z ∈ closedBall (0 : ℂ) 1, ‖ψ z‖ ≤ K) (ε : ℝ) (x : ℂ) :
    ‖(∫ z in ball (0 : ℂ) 1, g (x - ε • z) * ψ z) - (∫ z in ball (0 : ℂ) 1, ψ z) * g x‖ₑ ≤
      ENNReal.ofReal K * (∫⁻ z in ball (0 : ℂ) 1, ‖g (x - ε • z) - φ (x - ε • z)‖ₑ)
      + ‖(∫ z in ball (0 : ℂ) 1, φ (x - ε • z) * ψ z) - (∫ z in ball (0 : ℂ) 1, ψ z) * φ x‖ₑ
      + ‖∫ z in ball (0 : ℂ) 1, ψ z‖ₑ * ‖g x - φ x‖ₑ := by
  set a := ∫ z in ball (0 : ℂ) 1, g (x - ε • z) * ψ z
  set b := ∫ z in ball (0 : ℂ) 1, φ (x - ε • z) * ψ z
  set c := ∫ z in ball (0 : ℂ) 1, ψ z
  have hm : Measurable fun z : ℂ => x - ε • z := measurable_const.sub (measurable_id.const_smul ε)
  have hFm : AEStronglyMeasurable (fun z => g (x - ε • z) * ψ z) (volume.restrict (ball 0 1)) :=
    ((hg.comp hm).mul hψ.measurable).aestronglyMeasurable
  have hGi : Integrable (fun z => φ (x - ε • z) * ψ z) (volume.restrict (ball 0 1)) :=
    integrableOn_ball_one_of_continuous
      ((hφ.comp (continuous_const.sub (continuous_id.const_smul ε))).mul hψ)
  have hab : ‖a - b‖ₑ ≤
      ENNReal.ofReal K * (∫⁻ z in ball (0 : ℂ) 1, ‖g (x - ε • z) - φ (x - ε • z)‖ₑ) := by
    refine (enorm_integral_sub_le_of_integrable hFm hGi).trans ?_
    rw [mul_comm, ← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_ball fun z hz => ?_)
    rw [← sub_mul, enorm_mul]
    gcongr
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hK z (ball_subset_closedBall hz))
  have hsplit : a - c * g x = (a - b) + (b - c * φ x) - c * (g x - φ x) := by ring
  rw [hsplit]
  calc ‖(a - b) + (b - c * φ x) - c * (g x - φ x)‖ₑ
      ≤ ‖(a - b) + (b - c * φ x)‖ₑ + ‖c * (g x - φ x)‖ₑ := enorm_sub_le
    _ ≤ (‖a - b‖ₑ + ‖b - c * φ x‖ₑ) + ‖c‖ₑ * ‖g x - φ x‖ₑ := by
        gcongr
        · exact enorm_add_le _ _
        · exact (enorm_mul _ _).le
    _ ≤ _ := add_le_add_left (add_le_add_left hab _) _

/-- The continuous part: `|T_ε φ(x)| ≤ θ K |B₁|` when `|φ(x - εz) - φ(x)| ≤ θ` on `B₁`. -/
private lemma norm_integral_comp_sub_smul_sub_le {φ ψ : ℂ → ℝ} (hφ : Continuous φ)
    (hψ : Continuous ψ) {K θ : ℝ} (hK : ∀ z ∈ closedBall (0 : ℂ) 1, ‖ψ z‖ ≤ K) (hθ0 : 0 ≤ θ) (ε : ℝ) (x : ℂ)
    (hθ : ∀ z ∈ ball (0 : ℂ) 1, ‖φ (x - ε • z) - φ x‖ ≤ θ) :
    ‖(∫ z in ball (0 : ℂ) 1, φ (x - ε • z) * ψ z) - (∫ z in ball (0 : ℂ) 1, ψ z) * φ x‖ ≤
      θ * K * volume.real (ball (0 : ℂ) 1) := by
  have hGi : Integrable (fun z => φ (x - ε • z) * ψ z) (volume.restrict (ball 0 1)) :=
    integrableOn_ball_one_of_continuous
      ((hφ.comp (continuous_const.sub (continuous_id.const_smul ε))).mul hψ)
  have hHi : Integrable (fun z => ψ z * φ x) (volume.restrict (ball 0 1)) :=
    integrableOn_ball_one_of_continuous (hψ.mul continuous_const)
  rw [← integral_mul_const, ← integral_sub hGi hHi]
  refine norm_setIntegral_le_of_norm_le_const measure_ball_lt_top (fun z hz => ?_)
  have h1 : φ (x - ε • z) * ψ z - ψ z * φ x = (φ (x - ε • z) - φ x) * ψ z := by ring
  rw [h1, norm_mul]
  exact mul_le_mul (hθ z hz) (hK z (ball_subset_closedBall hz)) (norm_nonneg _) hθ0

/-- The combined estimate for a measurable `g`, a continuous `φ` and `0 < ε ≤ 1`:
`‖T_ε g‖_{L¹(B_R)} ≤ (K|B₁| + |∫ψ|) ‖g - φ‖_{L¹(B_{R+1})} + θ K |B₁| |B_R|`. -/
private lemma lintegral_le_of_measurable {g φ ψ : ℂ → ℝ} (hg : Measurable g) (hφ : Continuous φ)
    (hψ : Continuous ψ) {K θ : ℝ} (hK : ∀ z ∈ closedBall (0 : ℂ) 1, ‖ψ z‖ ≤ K) (hθ0 : 0 ≤ θ)
    (R : ℝ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hθ : ∀ x ∈ ball (0 : ℂ) R, ∀ z ∈ ball (0 : ℂ) 1, ‖φ (x - ε • z) - φ x‖ ≤ θ) :
    ∫⁻ x in ball (0 : ℂ) R,
        ‖(∫ z in ball (0 : ℂ) 1, g (x - ε • z) * ψ z) - (∫ z in ball (0 : ℂ) 1, ψ z) * g x‖ₑ ≤
      (ENNReal.ofReal K * volume (ball (0 : ℂ) 1) + ‖∫ z in ball (0 : ℂ) 1, ψ z‖ₑ) *
          (∫⁻ x in ball (0 : ℂ) (R + 1), ‖g x - φ x‖ₑ)
        + ENNReal.ofReal (θ * K * volume.real (ball (0 : ℂ) 1)) * volume (ball (0 : ℂ) R) := by
  set c := ∫ z in ball (0 : ℂ) 1, ψ z
  set M := ENNReal.ofReal (θ * K * volume.real (ball (0 : ℂ) 1))
  set J := ∫⁻ x in ball (0 : ℂ) (R + 1), ‖g x - φ x‖ₑ
  set f : ℂ × ℂ → ℝ≥0∞ := fun p => ‖g (p.1 - ε • p.2) - φ (p.1 - ε • p.2)‖ₑ with hf_def
  have hmp : Measurable fun p : ℂ × ℂ => p.1 - ε • p.2 :=
    measurable_fst.sub (measurable_snd.const_smul ε)
  have hfm : Measurable f := ((hg.comp hmp).sub (hφ.measurable.comp hmp)).enorm
  have hAm : Measurable fun x => ENNReal.ofReal K *
      ∫⁻ z in ball (0 : ℂ) 1, ‖g (x - ε • z) - φ (x - ε • z)‖ₑ :=
    (hfm.lintegral_prod_right' (ν := volume.restrict (ball (0 : ℂ) 1))).const_mul _
  have hCm : Measurable fun x => ‖c‖ₑ * ‖g x - φ x‖ₑ :=
    ((hg.sub hφ.measurable).enorm).const_mul _
  -- Step 1: the pointwise bound on `B_R`.
  have hpt : ∀ x ∈ ball (0 : ℂ) R,
      ‖(∫ z in ball (0 : ℂ) 1, g (x - ε • z) * ψ z) - c * g x‖ₑ ≤
        (ENNReal.ofReal K * (∫⁻ z in ball (0 : ℂ) 1, ‖g (x - ε • z) - φ (x - ε • z)‖ₑ)
          + ‖c‖ₑ * ‖g x - φ x‖ₑ) + M := by
    intro x hx
    refine (enorm_pointwise_le hg hφ hψ hK ε x (φ := φ)).trans ?_
    have hB : ‖(∫ z in ball (0 : ℂ) 1, φ (x - ε • z) * ψ z) - c * φ x‖ₑ ≤ M := by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal
        (norm_integral_comp_sub_smul_sub_le hφ hψ hK hθ0 ε x (hθ x hx))
    calc _ ≤ ENNReal.ofReal K * (∫⁻ z in ball (0 : ℂ) 1, ‖g (x - ε • z) - φ (x - ε • z)‖ₑ)
          + M + ‖c‖ₑ * ‖g x - φ x‖ₑ := by gcongr
      _ = _ := by ring
  -- Step 2: Tonelli and translation for the first term.
  have hA : ∫⁻ x in ball (0 : ℂ) R,
      ∫⁻ z in ball (0 : ℂ) 1, ‖g (x - ε • z) - φ (x - ε • z)‖ₑ ≤
        J * volume (ball (0 : ℂ) 1) := by
    rw [lintegral_lintegral_swap (f := fun x z => ‖g (x - ε • z) - φ (x - ε • z)‖ₑ)
      hfm.aemeasurable, ← setLIntegral_const]
    refine lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_ball fun z hz => ?_)
    have hεz : ‖ε • z‖ < 1 := by
      rw [norm_smul, Real.norm_of_nonneg hε0.le]
      rw [mem_ball_zero_iff] at hz
      calc ε * ‖z‖ ≤ 1 * ‖z‖ := by gcongr
        _ < 1 := by rw [one_mul]; exact hz
    exact setLIntegral_ball_comp_sub_le (fun y => ‖g y - φ y‖ₑ) R hεz
  have hC : ∫⁻ x in ball (0 : ℂ) R, ‖g x - φ x‖ₑ ≤ J :=
    lintegral_mono_set (ball_subset_ball (by linarith))
  calc ∫⁻ x in ball (0 : ℂ) R, ‖(∫ z in ball (0 : ℂ) 1, g (x - ε • z) * ψ z) - c * g x‖ₑ
      ≤ ∫⁻ x in ball (0 : ℂ) R,
          ((ENNReal.ofReal K * (∫⁻ z in ball (0 : ℂ) 1, ‖g (x - ε • z) - φ (x - ε • z)‖ₑ)
            + ‖c‖ₑ * ‖g x - φ x‖ₑ) + M) :=
        lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_ball hpt)
    _ = ENNReal.ofReal K * (∫⁻ x in ball (0 : ℂ) R,
            ∫⁻ z in ball (0 : ℂ) 1, ‖g (x - ε • z) - φ (x - ε • z)‖ₑ)
          + ‖c‖ₑ * (∫⁻ x in ball (0 : ℂ) R, ‖g x - φ x‖ₑ) + M * volume (ball (0 : ℂ) R) := by
        rw [lintegral_add_right _ measurable_const, lintegral_add_left hAm,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ enorm_ne_top, setLIntegral_const]
    _ ≤ ENNReal.ofReal K * (J * volume (ball (0 : ℂ) 1)) + ‖c‖ₑ * J
          + M * volume (ball (0 : ℂ) R) := by gcongr
    _ = _ := by ring

/-- An elementary inequality used to split the error budget: `A · d/(2(A+1)) ≤ d/2`. -/
private lemma mul_div_two_mul_add_one_le {A d : ℝ} (hA : 0 ≤ A) (hd : 0 ≤ d) :
    A * (d / (2 * (A + 1))) ≤ d / 2 := by
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- The theorem for a measurable `g`. -/
private lemma tendsto_aux_of_measurable {g : ℂ → ℝ} (hgm : Measurable g)
    (hg : LocallyIntegrable g volume) {ψ : ℂ → ℝ} (hψ : Continuous ψ) (R : ℝ) :
    Tendsto (fun ε : ℝ => ∫⁻ x in ball (0 : ℂ) R,
        ‖(∫ z in ball (0 : ℂ) 1, g (x - ε • z) * ψ z) - (∫ z in ball (0 : ℂ) 1, ψ z) * g x‖ₑ)
      (𝓝[>] 0) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  obtain ⟨d, hd0, hd, hdδ⟩ := ENNReal.lt_iff_exists_real_btwn.1 hδ
  have hd' : 0 < d := ENNReal.ofReal_pos.1 hd
  -- the bound `K` for `ψ` on the closed unit ball
  obtain ⟨K₀, hK₀⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hψ.continuousOn
  set K := max K₀ 0 with hK_def
  have hK0 : 0 ≤ K := le_max_right _ _
  have hK : ∀ z ∈ closedBall (0 : ℂ) 1, ‖ψ z‖ ≤ K := fun z hz => (hK₀ z hz).trans (le_max_left _ _)
  set c := ∫ z in ball (0 : ℂ) 1, ψ z
  set V1 := volume.real (ball (0 : ℂ) 1)
  set VR := volume.real (ball (0 : ℂ) R)
  have hV1 : 0 ≤ V1 := measureReal_nonneg
  have hVR : 0 ≤ VR := measureReal_nonneg
  -- the `L¹(B_{R+1})` approximation of `g` by a continuous `φ`
  set η₁ := d / (2 * (K * V1 + ‖c‖ + 1))
  have hη₁ : 0 < η₁ := by positivity
  have hgi : Integrable ((ball (0 : ℂ) (R + 1)).indicator g) volume :=
    ((hg.integrableOn_isCompact (isCompact_closedBall (0 : ℂ) (R + 1))).mono_set
      ball_subset_closedBall).integrable_indicator measurableSet_ball
  obtain ⟨φ, -, hφJ, hφc, -⟩ :=
    hgi.exists_hasCompactSupport_lintegral_sub_le (ENNReal.ofReal_pos.2 hη₁).ne'
  have hJ : ∫⁻ x in ball (0 : ℂ) (R + 1), ‖g x - φ x‖ₑ ≤ ENNReal.ofReal η₁ := by
    calc ∫⁻ x in ball (0 : ℂ) (R + 1), ‖g x - φ x‖ₑ
        = ∫⁻ x in ball (0 : ℂ) (R + 1), ‖(ball (0 : ℂ) (R + 1)).indicator g x - φ x‖ₑ :=
          setLIntegral_congr_fun measurableSet_ball (fun x hx => by rw [indicator_of_mem hx])
      _ ≤ ∫⁻ x, ‖(ball (0 : ℂ) (R + 1)).indicator g x - φ x‖ₑ := setLIntegral_le_lintegral _ _
      _ ≤ _ := hφJ
  -- uniform continuity of `φ` on `\bar B_{R+1}`
  set θ := d / (2 * (K * V1 * VR + 1))
  have hθ : 0 < θ := by positivity
  obtain ⟨η, hη, hφu⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_closedBall (0 : ℂ) (R + 1)).uniformContinuousOn_of_continuous
      hφc.continuousOn) θ hθ
  filter_upwards [Ioo_mem_nhdsGT (lt_min hη one_pos)] with ε hε
  obtain ⟨hε0, hε1⟩ := hε
  have hεη : ε < η := hε1.trans_le (min_le_left _ _)
  have hε1' : ε ≤ 1 := (hε1.trans_le (min_le_right _ _)).le
  have hθx : ∀ x ∈ ball (0 : ℂ) R, ∀ z ∈ ball (0 : ℂ) 1, ‖φ (x - ε • z) - φ x‖ ≤ θ := by
    intro x hx z hz
    rw [mem_ball_zero_iff] at hx hz
    have hεz : ‖ε • z‖ < η ∧ ‖ε • z‖ < 1 := by
      rw [norm_smul, Real.norm_of_nonneg hε0.le]
      constructor
      · calc ε * ‖z‖ ≤ ε * 1 := by gcongr
          _ < η := by rw [mul_one]; exact hεη
      · calc ε * ‖z‖ ≤ 1 * ‖z‖ := by gcongr
          _ < 1 := by rw [one_mul]; exact hz
    have hx' : x ∈ closedBall (0 : ℂ) (R + 1) := by
      rw [mem_closedBall_zero_iff]; linarith
    have hxz : x - ε • z ∈ closedBall (0 : ℂ) (R + 1) := by
      rw [mem_closedBall_zero_iff]
      calc ‖x - ε • z‖ ≤ ‖x‖ + ‖ε • z‖ := norm_sub_le _ _
        _ ≤ R + 1 := by linarith [hεz.2]
    have h1 := hφu (x - ε • z) hxz x hx' (by
      rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]; exact hεz.1)
    rw [dist_eq_norm] at h1
    exact h1.le
  refine (lintegral_le_of_measurable hgm hφc hψ hK hθ.le R hε0 hε1' hθx).trans ?_
  refine le_trans ?_ hdδ.le
  have hvol1 : volume (ball (0 : ℂ) 1) = ENNReal.ofReal V1 :=
    (ofReal_measureReal measure_ball_lt_top.ne).symm
  have hvolR : volume (ball (0 : ℂ) R) = ENNReal.ofReal VR :=
    (ofReal_measureReal measure_ball_lt_top.ne).symm
  rw [hvol1, hvolR, ← ofReal_norm, ← ENNReal.ofReal_mul hK0, ← ENNReal.ofReal_add
    (by positivity) (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
  calc ENNReal.ofReal (K * V1 + ‖c‖) * (∫⁻ x in ball (0 : ℂ) (R + 1), ‖g x - φ x‖ₑ)
        + ENNReal.ofReal (θ * K * V1 * VR)
      ≤ ENNReal.ofReal (K * V1 + ‖c‖) * ENNReal.ofReal η₁ + ENNReal.ofReal (θ * K * V1 * VR) := by
        gcongr
    _ = ENNReal.ofReal ((K * V1 + ‖c‖) * η₁ + θ * K * V1 * VR) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
    _ ≤ ENNReal.ofReal d := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : (K * V1 + ‖c‖) * η₁ ≤ d / 2 :=
          mul_div_two_mul_add_one_le (by positivity) hd'.le
        have h2 : θ * K * V1 * VR ≤ d / 2 := by
          have := mul_div_two_mul_add_one_le (A := K * V1 * VR) (by positivity) hd'.le
          calc θ * K * V1 * VR = K * V1 * VR * θ := by ring
            _ ≤ d / 2 := this
        linarith

/-- Approximate identity in `L¹_loc(ℝ²)` (`03_compactness.tex:425-431`): for `g ∈ L¹_loc` and a
continuous `ψ`, `∫_{B₁} g(· - εz) ψ(z) dz → (∫_{B₁} ψ) g` in `L¹(B_R)` as `ε → 0⁺`. -/
theorem tendsto_lintegral_ball_integral_comp_sub_smul {g : ℂ → ℝ}
    (hg : LocallyIntegrable g volume) {ψ : ℂ → ℝ} (hψ : Continuous ψ) (R : ℝ) :
    Tendsto (fun ε : ℝ => ∫⁻ x in ball (0 : ℂ) R,
        ‖(∫ z in ball (0 : ℂ) 1, g (x - ε • z) * ψ z) - (∫ z in ball (0 : ℂ) 1, ψ z) * g x‖ₑ)
      (𝓝[>] 0) (𝓝 0) := by
  set g' := hg.aestronglyMeasurable.mk g
  have hg'm : Measurable g' := hg.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hgg' : g =ᵐ[volume] g' := hg.aestronglyMeasurable.ae_eq_mk
  have hg'li : LocallyIntegrable g' volume := hg.congr hgg'
  refine (tendsto_aux_of_measurable hg'm hg'li hψ R).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  refine lintegral_congr_ae ?_
  have hx : ∀ᵐ x ∂(volume.restrict (ball (0 : ℂ) R)), g' x = g x := ae_restrict_of_ae hgg'.symm
  filter_upwards [hx] with x hx
  have hq : Measure.QuasiMeasurePreserving (fun z : ℂ => x - ε • z) volume volume :=
    (quasiMeasurePreserving_sub_left volume x).comp
      (Measure.quasiMeasurePreserving_smul volume hε.ne')
  have hint : ∫ z in ball (0 : ℂ) 1, g' (x - ε • z) * ψ z =
      ∫ z in ball (0 : ℂ) 1, g (x - ε • z) * ψ z := by
    refine integral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hq.ae_eq_comp hgg'.symm] with z hz
    simp only [Function.comp_apply] at hz
    rw [hz]
  rw [hint, hx]

end NonUniqueEuler.Conv
