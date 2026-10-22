import NonUniqueEuler.H.Sec3.Stable.Basic
import NonUniqueEuler.I.Sec3.Stable.WeakLimit
import NonUniqueEuler.I.Sec3.Transport
import NonUniqueEuler.I.Sec3.VelocityField

/-!
# Helpers for `prop:stable`: bounded renormalizations converge strongly

Helper file of `P/Sec3/Stable.lean`. Manuscript: proof of `prop:stable`, third paragraph
(`03_compactness.tex:774-789`): with the weak limits `ū`, `z̄` of `β(ωₙ)`, `β(ωₙ)²`
(`stable_weakLimit`, `I/Sec3/Stable/WeakLimit.lean`),
* `ae_eq_sq_of_weakLimit`: `z̄ = ū²` a.e. on `(0,T) × ℝ²`, by `lem:transport`(i) applied to
  `ū` with `γ(s) = T_B(s)²` (`γ(s) = s²` for `|s| ≤ B`, `γ ∈ Lip₀`) and `lem:transport`(iii)
  applied to `z̄ - γ(ū)` (datum `β(g)² - γ(β(g)) = 0`);
* `tendsto_lintegral_of_weak_sq`: weak convergence of `uₙ` to `ū` and of `uₙ²` to `ū²`
  (bounded functions) gives `uₙ → ū` in `L²(S)`, hence in `L¹(S)`, for every set `S` of finite
  measure: `∫_S (uₙ - ū)² = ∫_S uₙ² - 2∫_S uₙ ū + ∫_S ū² → 0`;
* `stable_bddRenorm`: for bounded `β ∈ Lip₀`, along a subsequence, `β(ωₙ) → ū` in
  `L¹((0,T) × B_R)` for every `R > 0`.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace NonUniqueEuler.Compact.StableAux

open Weak

/-! ### Strong convergence from weak convergence of `uₙ` and `uₙ²` -/

/-- Weak convergence (against `L²`) of bounded `uₙ → ū` and `uₙ² → ū²` gives `uₙ → ū` in `L¹(S)`
for every measurable `S` of finite measure. -/
theorem tendsto_lintegral_of_weak_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {u : ℕ → α → ℝ} {ub : α → ℝ} {B : ℝ}
    (hu : ∀ n, AEStronglyMeasurable (u n) μ) (huB : ∀ n, ∀ᵐ x ∂μ, |u n x| ≤ B)
    (hub : AEStronglyMeasurable ub μ) (hubB : ∀ᵐ x ∂μ, |ub x| ≤ B)
    (hw1 : ∀ Φ : α → ℝ, MemLp Φ 2 μ →
      Tendsto (fun n => ∫ x, u n x * Φ x ∂μ) atTop (𝓝 (∫ x, ub x * Φ x ∂μ)))
    (hw2 : ∀ Φ : α → ℝ, MemLp Φ 2 μ →
      Tendsto (fun n => ∫ x, u n x ^ 2 * Φ x ∂μ) atTop (𝓝 (∫ x, ub x ^ 2 * Φ x ∂μ)))
    {S : Set α} (hS : MeasurableSet S) (hμS : μ S ≠ ∞) :
    Tendsto (fun n => ∫⁻ x in S, ‖u n x - ub x‖ₑ ∂μ) atTop (𝓝 0) := by
  have : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.2 hμS
  -- set integrals as integrals against indicators
  have hind : ∀ (f g : α → ℝ), ∫ x, f x * S.indicator g x ∂μ = ∫ x in S, f x * g x ∂μ := by
    intro f g
    rw [← integral_indicator hS]
    congr 1
    funext x
    rw [Set.indicator_mul_right]
  have hΦ1 : MemLp (S.indicator (fun _ => (1 : ℝ))) 2 μ :=
    memLp_indicator_const 2 hS 1 (Or.inr hμS)
  have hubS : MemLp ub 2 (μ.restrict S) :=
    MemLp.of_bound hub.restrict B (ae_restrict_of_ae (hubB.mono fun x hx => by
      rwa [Real.norm_eq_abs]))
  have hΦ2 : MemLp (S.indicator ub) 2 μ := (memLp_indicator_iff_restrict hS).2 hubS
  have hA : Tendsto (fun n => ∫ x in S, u n x ^ 2 ∂μ) atTop (𝓝 (∫ x in S, ub x ^ 2 ∂μ)) := by
    have h := hw2 _ hΦ1
    simp only [hind, mul_one] at h
    exact h
  have hC : Tendsto (fun n => ∫ x in S, u n x * ub x ∂μ) atTop
      (𝓝 (∫ x in S, ub x * ub x ∂μ)) := by
    have h := hw1 _ hΦ2
    simp only [hind] at h
    exact h
  -- integrability on `S`
  have hbdd : ∀ {f : α → ℝ} {C : ℝ}, AEStronglyMeasurable f μ → (∀ᵐ x ∂μ, |f x| ≤ C) →
      Integrable f (μ.restrict S) := fun hf hC =>
    Integrable.of_bound hf.restrict _ (ae_restrict_of_ae (hC.mono fun x hx => by
      rwa [Real.norm_eq_abs]))
  have hint1 : ∀ n, Integrable (fun x => u n x ^ 2) (μ.restrict S) := fun n =>
    hbdd (C := B ^ 2) ((hu n).pow 2) ((huB n).mono fun x hx => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hx 2)
  have hint2 : ∀ n, Integrable (fun x => u n x * ub x) (μ.restrict S) := fun n =>
    hbdd (C := B * B) ((hu n).mul hub) (((huB n).and hubB).mono fun x hx => by
      rw [abs_mul]; exact mul_le_mul hx.1 hx.2 (abs_nonneg _) ((abs_nonneg _).trans hx.1))
  have hint3 : Integrable (fun x => ub x ^ 2) (μ.restrict S) :=
    hbdd (C := B ^ 2) (hub.pow 2) (hubB.mono fun x hx => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hx 2)
  -- `∫_S (uₙ - ū)² → 0`
  have hI : Tendsto (fun n => ∫ x in S, (u n x - ub x) ^ 2 ∂μ) atTop (𝓝 0) := by
    have heq : ∀ n, ∫ x in S, (u n x - ub x) ^ 2 ∂μ =
        (∫ x in S, u n x ^ 2 ∂μ) - 2 * (∫ x in S, u n x * ub x ∂μ) +
          ∫ x in S, ub x ^ 2 ∂μ := by
      intro n
      have h1 : (fun x => (u n x - ub x) ^ 2) =
          fun x => (u n x ^ 2 - 2 * (u n x * ub x)) + ub x ^ 2 := by
        funext x; ring
      have i2 : Integrable (fun x => 2 * (u n x * ub x)) (μ.restrict S) :=
        (hint2 n).const_mul 2
      have i1 : Integrable (fun x => u n x ^ 2 - 2 * (u n x * ub x)) (μ.restrict S) :=
        (hint1 n).sub i2
      rw [h1, integral_add i1 hint3, integral_sub (hint1 n) i2, integral_const_mul]
    simp_rw [heq]
    have hlim := (hA.sub (hC.const_mul 2)).add (tendsto_const_nhds (x := ∫ x in S, ub x ^ 2 ∂μ))
    have h0 : (∫ x in S, ub x ^ 2 ∂μ) - 2 * (∫ x in S, ub x * ub x ∂μ) +
        ∫ x in S, ub x ^ 2 ∂μ = 0 := by
      simp only [← sq]; ring
    rwa [h0] at hlim
  -- `L²(S)` norms tend to `0`
  have hmem : ∀ n, MemLp (fun x => u n x - ub x) 2 (μ.restrict S) := fun n =>
    MemLp.of_bound ((hu n).sub hub).restrict (B + B) (ae_restrict_of_ae
      (((huB n).and hubB).mono fun x hx => by
        rw [Real.norm_eq_abs]; exact (abs_sub _ _).trans (add_le_add hx.1 hx.2)))
  have hL2 : Tendsto (fun n => eLpNorm (fun x => u n x - ub x) 2 (μ.restrict S)) atTop
      (𝓝 0) := by
    have heq : ∀ n, eLpNorm (fun x => u n x - ub x) 2 (μ.restrict S) =
        ENNReal.ofReal ((∫ x in S, (u n x - ub x) ^ 2 ∂μ) ^ (2 : ℝ)⁻¹) := by
      intro n
      rw [(hmem n).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
      simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
    simp_rw [heq]
    have hc : Tendsto (fun y : ℝ => ENNReal.ofReal (y ^ (2 : ℝ)⁻¹)) (𝓝 0)
        (𝓝 (ENNReal.ofReal ((0 : ℝ) ^ (2 : ℝ)⁻¹))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp
        ((Real.continuousAt_rpow_const _ _ (Or.inr (by norm_num))).tendsto)
    rw [Real.zero_rpow (by norm_num), ENNReal.ofReal_zero] at hc
    exact hc.comp hI
  -- `L¹(S)` from `L²(S)`
  have hfin : (μ.restrict S) univ ^ (1 / 2 : ℝ) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _)
  have hup : Tendsto (fun n => eLpNorm (fun x => u n x - ub x) 2 (μ.restrict S) *
      (μ.restrict S) univ ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const hL2 (Or.inr hfin)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun _ => zero_le) (fun n => ?_)
  have h := eLpNorm_one_le_two_mul (μ := μ.restrict S) ((hu n).sub hub).restrict
  rw [eLpNorm_one_eq_lintegral_enorm] at h
  exact h

/-! ### `z̄ = ū²` -/

/-- **`z̄ = ū²`** (`03_compactness.tex:774-783`): `lem:transport`(i) with `γ(s) = T_B(s)²` and
`lem:transport`(iii) applied to `z̄ - γ(ū)`. -/
theorem ae_eq_sq_of_weakLimit {T : ℝ} (hT : 0 < T) {g : ℂ → ℝ} {ω : ℝ → ℂ → ℝ}
    (hω : IsWeakSolution 2 T g ω) {β : ℝ → ℝ} (hβ : Equimeas.IsLipO β) {B : ℝ}
    (hB : ∀ s, |β s| ≤ B) {ub zb : ℝ → ℂ → ℝ}
    (hubB : ∀ᵐ p ∂(volume.restrict (slab T)), |ub p.1 p.2| ≤ B)
    (hub1 : Prelim.MemLinfLp (Ioo 0 T) univ 1 ub) (hub2 : Prelim.MemLinfLp (Ioo 0 T) univ 2 ub)
    (hzb1 : Prelim.MemLinfLp (Ioo 0 T) univ 1 zb) (hzb2 : Prelim.MemLinfLp (Ioo 0 T) univ 2 zb)
    (hubv : Integrable (fun p : ℝ × ℂ => ub p.1 p.2 • velocityField ω p.1 p.2)
      (volume.restrict (slab T)))
    (hzbv : Integrable (fun p : ℝ × ℂ => zb p.1 p.2 • velocityField ω p.1 p.2)
      (volume.restrict (slab T)))
    (hteu : SolvesTE 0 T ub (velocityField ω) (fun x => β (g x)))
    (htez : SolvesTE 0 T zb (velocityField ω) (fun x => β (g x) ^ 2)) :
    ∀ᵐ p ∂(volume.restrict (slab T)), zb p.1 p.2 = ub p.1 p.2 ^ 2 := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  set γ : ℝ → ℝ := fun s => trunc B s ^ 2 with hγdef
  have hγabs : ∀ s, |γ s| ≤ B * |s| := by
    intro s
    simp only [hγdef, sq]
    rw [abs_mul]
    exact mul_le_mul (abs_trunc_le hB0 s) (abs_trunc_le_abs hB0 s) (abs_nonneg _) hB0
  have hγ : Equimeas.IsLipO γ := by
    refine ⟨⟨Real.toNNReal (2 * B), LipschitzWith.of_dist_le_mul fun a b => ?_⟩, ?_⟩
    · have h1 := (lipschitzWith_trunc B).dist_le_mul a b
      simp only [NNReal.coe_one, one_mul, Real.dist_eq] at h1
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by linarith)]
      simp only [hγdef]
      rw [sq_sub_sq, abs_mul]
      have h2 : |trunc B a + trunc B b| ≤ 2 * B := by
        have := abs_add_le (trunc B a) (trunc B b)
        linarith [abs_trunc_le hB0 a, abs_trunc_le hB0 b]
      exact mul_le_mul h2 h1 (abs_nonneg _) (by linarith)
    · simp only [hγdef, trunc_of_abs_le (by simpa using hB0 : |(0 : ℝ)| ≤ B)]; norm_num
  have h2 : ENNReal.ofReal 2 = 2 := by norm_num
  obtain ⟨hω1, hω2⟩ := Prelim.memX_iff.1 hω.memX
  rw [h2] at hω2
  have hvf : IsBddH1DivFreeField (Ioo 0 T) (velocityField ω) :=
    isBddH1DivFreeField_velocityField hω1 hω2
  have hg1 : MemLp (fun x => β (g x)) 1 volume := memLp_comp_lipO hω.datum_memLp_one hβ
  have hg2 : MemLp (fun x => β (g x)) 2 volume := by
    have := hω.datum_memLp_q; rw [h2] at this; exact memLp_comp_lipO this hβ
  have ht0 : (0 : ℝ) ∈ Ico 0 T := ⟨le_rfl, hT⟩
  have hγu := transport_renorm hT ht0 hvf hub1 hub2 hubv hg1 hg2 hteu γ hγ
  have hdat : (fun x => γ (β (g x))) = fun x => β (g x) ^ 2 := by
    funext x; simp only [hγdef, trunc_of_abs_le (hB (g x))]
  rw [hdat] at hγu
  have hdiff := htez.sub hγu
  have hzero_fun : (fun x => β (g x) ^ 2 - β (g x) ^ 2) = (0 : ℂ → ℝ) := by
    funext x; simp
  rw [hzero_fun] at hdiff
  have hd1 : Prelim.MemLinfLp (Ioo 0 T) univ 1 (fun t x => zb t x - γ (ub t x)) :=
    memLinfLp_sub le_rfl hzb1 (memLinfLp_comp_lipO hub1 hγ)
  have hd2 : Prelim.MemLinfLp (Ioo 0 T) univ 2 (fun t x => zb t x - γ (ub t x)) :=
    memLinfLp_sub (by norm_num) hzb2 (memLinfLp_comp_lipO hub2 hγ)
  have hγv : Integrable (fun p : ℝ × ℂ => γ (ub p.1 p.2) • velocityField ω p.1 p.2)
      (volume.restrict (slab T)) := by
    refine Integrable.mono' (hubv.norm.const_mul B) ?_ (Eventually.of_forall fun p => ?_)
    · exact (hγ.continuous.comp_aestronglyMeasurable hub1.aestronglyMeasurable).smul
        hvf.aestronglyMeasurable
    · simp only [norm_smul, Real.norm_eq_abs]
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hγabs _) (norm_nonneg _)
  have hdv : Integrable (fun p : ℝ × ℂ => (zb p.1 p.2 - γ (ub p.1 p.2)) • velocityField ω p.1 p.2)
      (volume.restrict (slab T)) := by
    simp only [sub_smul]
    exact hzbv.sub hγv
  have hz := transport_eq_zero hT ht0 hvf hd1 hd2 hdv MemLp.zero MemLp.zero hdiff
    (ae_eq_refl _)
  rw [slabFrom_zero] at hz
  filter_upwards [hz, hubB] with p hp hb
  simp only [Pi.zero_apply] at hp
  have : γ (ub p.1 p.2) = ub p.1 p.2 ^ 2 := by simp only [hγdef, trunc_of_abs_le hb]
  have hp' : zb p.1 p.2 - γ (ub p.1 p.2) = 0 := hp
  linarith

/-! ### Strong convergence of bounded renormalizations -/

theorem volume_Ioo_prod_ball_ne_top (T R : ℝ) :
    volume (Ioo (0 : ℝ) T ×ˢ ball (0 : ℂ) R) ≠ ∞ := by
  rw [Measure.volume_eq_prod ℝ ℂ, Measure.prod_prod]
  exact ENNReal.mul_ne_top (by simp) measure_ball_lt_top.ne

theorem Ioo_prod_ball_subset_slab (T R : ℝ) : Ioo (0 : ℝ) T ×ˢ ball (0 : ℂ) R ⊆ slab T :=
  prod_mono subset_rfl (subset_univ _)

/-- **Bounded renormalizations converge strongly** (`03_compactness.tex:739-789`): for bounded
`β ∈ Lip₀`, along a subsequence, `β(ωₙ) → ū` in `L¹((0,T) × B_R)` for every `R > 0`. -/
theorem stable_bddRenorm {T M : ℝ} {gs : ℕ → ℂ → ℝ} {g : ℂ → ℝ} {ωs : ℕ → ℝ → ℂ → ℝ}
    {ω : ℝ → ℂ → ℝ} (hseq : IsCompactSeq T M gs g ωs) (hlim : IsCompactLimit T g ωs ω)
    (hstrong : Tendsto (fun n => normL1LpE 2 (gs n - g)) atTop (𝓝 0))
    (hren : ∀ n, IsRenormalizedWeakSolution 2 T (gs n) (ωs n))
    {β : ℝ → ℝ} (hβ : Equimeas.IsLipO β) {B : ℝ} (hB : ∀ s, |β s| ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ub : ℝ → ℂ → ℝ,
      Prelim.MemLinfLp (Ioo 0 T) univ 1 ub ∧
      ∀ R : ℝ, 0 < R →
        Tendsto (fun n => ∫⁻ p in Ioo 0 T ×ˢ ball (0 : ℂ) R,
          ‖β (ωs (φ n) p.1 p.2) - ub p.1 p.2‖ₑ) atTop (𝓝 0) := by
  obtain ⟨φ, hφ, ub, zb, hw1, hw2, hubB, hub1, hub2, hzb1, hzb2, hubv, hzbv, hteu, htez⟩ :=
    stable_weakLimit hseq hlim hstrong hren hβ hB
  have hzu := ae_eq_sq_of_weakLimit hseq.T_pos hlim.weakSolution hβ hB hubB hub1 hub2 hzb1 hzb2
    hubv hzbv hteu htez
  refine ⟨φ, hφ, ub, hub1, fun R _ => ?_⟩
  have hS : MeasurableSet (Ioo (0 : ℝ) T ×ˢ ball (0 : ℂ) R) :=
    measurableSet_Ioo.prod measurableSet_ball
  have hμS : (volume.restrict (slab T)) (Ioo (0 : ℝ) T ×ˢ ball (0 : ℂ) R) ≠ ∞ := by
    rw [Measure.restrict_apply hS]
    exact ne_top_of_le_ne_top (volume_Ioo_prod_ball_ne_top T R) (measure_mono inter_subset_left)
  have hw2' : ∀ Φ : ℝ × ℂ → ℝ, MemLp Φ 2 (volume.restrict (slab T)) →
      Tendsto (fun n => ∫ p in slab T, β (ωs (φ n) p.1 p.2) ^ 2 * Φ p) atTop
        (𝓝 (∫ p in slab T, ub p.1 p.2 ^ 2 * Φ p)) := by
    intro Φ hΦ
    have h := hw2 Φ hΦ
    have he : ∫ p in slab T, zb p.1 p.2 * Φ p = ∫ p in slab T, ub p.1 p.2 ^ 2 * Φ p :=
      integral_congr_ae (hzu.mono fun p hp => by simp only [hp])
    rwa [he] at h
  have h := tendsto_lintegral_of_weak_sq (μ := volume.restrict (slab T))
    (u := fun n p => β (ωs (φ n) p.1 p.2)) (ub := fun p => ub p.1 p.2) (B := B)
    (fun n => hβ.continuous.comp_aestronglyMeasurable
      (hseq.weakSolution (φ n)).memX.aestronglyMeasurable)
    (fun n => Eventually.of_forall fun p => hB _) hub1.aestronglyMeasurable hubB hw1 hw2' hS hμS
  rwa [Measure.restrict_restrict hS, inter_eq_left.2 (Ioo_prod_ball_subset_slab T R)] at h

end NonUniqueEuler.Compact.StableAux
