import NonUniqueEuler.H.Sec3.Stable.WeakLimit.Bounds
import NonUniqueEuler.I.Sec3.LipRenorm
import NonUniqueEuler.I.Sec3.VelocityField
import NonUniqueEuler.I.Infra.ConvMinkowski.Measurable

/-!
# Helpers for `prop:stable`, step 1a: passage to the limit in `(te)`

Helper file of `P/Sec3/Stable/WeakLimit.lean` (`03_compactness.tex:755-763`).

Let `uₙ = γ(ωₙ)` with `γ ∈ Lip₀` bounded, `uₙ ⇀ G` weakly in `L²((0,T) × ℝ²)`. For `φ ∈ 𝒟_T`
with support in `ℝ × B_R`:
* `memLp_testIntegrand`: `Ψ = ∂_tφ + v·∇φ ∈ L²((0,T) × ℝ²)` (`v ∈ L^∞(0,T; L²(B_R))`), so
  `∫∫ uₙ Ψ → ∫∫ G Ψ`;
* `enorm_integral_transport_sub_le`: `|∫∫ uₙ (vₙ - v)·∇φ| ≤ B ‖∇φ‖_∞ ‖vₙ - v‖_{L¹((0,T) × B_R)}`;
* `tendsto_lintegral_velocity_sub`: `‖vₙ - v‖_{L¹((0,T) × B_R)} → 0` (`prop:compact`(iii) with
  `s = 1` and Hölder on `B_R`);
* `tendsto_datum`: `∫ γ(gₙ) φ(0) → ∫ γ(g) φ(0)` (`|γ(gₙ) - γ(g)| ≤ L |gₙ - g|`);
* `solvesTE_of_weak`: `G` satisfies `(te)` with field `v` and datum `γ(g)`.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace NonUniqueEuler.Compact.WeakLimitAux

open Weak

variable {T M : ℝ} {gs : ℕ → ℂ → ℝ} {g : ℂ → ℝ} {ωs : ℕ → ℝ → ℂ → ℝ} {ω : ℝ → ℂ → ℝ}

theorem prod_ball_inter_slab (T R : ℝ) :
    ((univ : Set ℝ) ×ˢ ball (0 : ℂ) R) ∩ slab T = Ioo 0 T ×ˢ ball (0 : ℂ) R := by
  rw [slab, prod_inter_prod, univ_inter, inter_univ]

theorem measurableSet_univ_prod_ball (R : ℝ) :
    MeasurableSet ((univ : Set ℝ) ×ˢ ball (0 : ℂ) R) :=
  MeasurableSet.univ.prod measurableSet_ball

/-- `v ∈ L²((0,T) × B_R)` for a weak solution in `X₂(T)`. -/
theorem memLp_velocity_ball {ωin : ℂ → ℝ} (hω : IsWeakSolution 2 T ωin ω) {R : ℝ} (hR : 0 < R) :
    MemLp (Function.uncurry (velocityField ω)) 2 (volume.restrict (Ioo 0 T ×ˢ ball (0 : ℂ) R)) := by
  have hv := (hω.memLinfLp_velocityField hR).1
  obtain ⟨Mv, hMv⟩ := hv.essBounded
  refine memLp_two_prodSet_of_ae_slice (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    hv.aestronglyMeasurable ENNReal.ofReal_ne_top (C := ENNReal.ofReal Mv) (hMv.mono fun t ht => ?_)
  change eLpNorm (velocityField ω t) 2 _ ≤ _
  rw [← ENNReal.ofReal_toReal ht.1.eLpNorm_ne_top]
  exact ENNReal.ofReal_le_ofReal ht.2

/-- A function vanishing off `ℝ × B_R`, and in `L²((0,T) × B_R)`, is in `L²` of the slab. -/
theorem memLp_slab_of_ball {f : ℝ × ℂ → ℝ} {R : ℝ} (hf0 : ∀ p : ℝ × ℂ, p.2 ∉ ball (0 : ℂ) R → f p = 0)
    (hf : MemLp f 2 (volume.restrict (Ioo 0 T ×ˢ ball (0 : ℂ) R))) :
    MemLp f 2 (volume.restrict (slab T)) := by
  have hfi : ((univ : Set ℝ) ×ˢ ball (0 : ℂ) R).indicator f = f := by
    funext p
    by_cases hp : p.2 ∈ ball (0 : ℂ) R
    · exact indicator_of_mem (show p ∈ (univ : Set ℝ) ×ˢ ball (0 : ℂ) R from ⟨mem_univ _, hp⟩) f
    · rw [indicator_of_notMem (fun h => hp h.2), hf0 p hp]
  rw [← hfi, memLp_indicator_iff_restrict (measurableSet_univ_prod_ball R),
    Measure.restrict_restrict (measurableSet_univ_prod_ball R), prod_ball_inter_slab]
  exact hf

/-- `Ψ = ∂_tφ + v·∇φ ∈ L²((0,T) × ℝ²)`. -/
theorem memLp_testIntegrand {ωin : ℂ → ℝ} (hω : IsWeakSolution 2 T ωin ω) {φ : ℝ × ℂ → ℝ}
    (hφ : IsTestFunction T φ) :
    MemLp (fun p : ℝ × ℂ => timeDeriv φ p.1 p.2 + spaceDeriv φ p.1 p.2 (velocityField ω p.1 p.2))
      2 (volume.restrict (slab T)) := by
  obtain ⟨R, hR, b, -, hsupp⟩ := exists_ball_of_isTestFunction hφ
  obtain ⟨D, -, hD⟩ := exists_bound_fderiv_of_isTestFunction hφ
  refine (memLp_timeDeriv hφ _ 2).add (memLp_slab_of_ball (R := R) (fun p hp => ?_) ?_)
  · exact spaceDeriv_eq_zero_of_notMem hφ (fun h => hp (hsupp _ h).2) _
  · have hv := memLp_velocity_ball hω hR
    exact hv.of_le_mul (aestronglyMeasurable_spaceDeriv hφ hv.1)
      (Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs]
        exact abs_spaceDeriv_le hφ hD _ _ _)

/-- `|∫∫ u (w₁ - w₂)·∇φ| ≤ B D ‖w₁ - w₂‖_{L¹((0,T) × B_R)}`. -/
theorem enorm_integral_transport_sub_le {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) {R : ℝ}
    (hsupp : ∀ p ∈ tsupport φ, p.2 ∈ ball (0 : ℂ) R) {D : ℝ} (hD : ∀ p, ‖fderiv ℝ φ p‖ ≤ D)
    {u : ℝ → ℂ → ℝ} {B : ℝ} (hB : 0 ≤ B) (huB : ∀ t x, |u t x| ≤ B) {w₁ w₂ : ℝ → ℂ → ℂ}
    (h1 : IntegrableOn (transportIntegrand u w₁ φ) (slab T))
    (h2 : IntegrableOn (transportIntegrand u w₂ φ) (slab T)) :
    ‖(∫ p in slab T, transportIntegrand u w₁ φ p) - ∫ p in slab T, transportIntegrand u w₂ φ p‖ₑ ≤
      ENNReal.ofReal (B * D) * ∫⁻ p in Ioo 0 T ×ˢ ball (0 : ℂ) R, ‖w₁ p.1 p.2 - w₂ p.1 p.2‖ₑ := by
  rw [← integral_sub h1 h2]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  have hpt : ∀ p : ℝ × ℂ, ‖transportIntegrand u w₁ φ p - transportIntegrand u w₂ φ p‖ₑ ≤
      ((univ : Set ℝ) ×ˢ ball (0 : ℂ) R).indicator
        (fun p => ENNReal.ofReal (B * D) * ‖w₁ p.1 p.2 - w₂ p.1 p.2‖ₑ) p := by
    intro p
    have heq : transportIntegrand u w₁ φ p - transportIntegrand u w₂ φ p =
        u p.1 p.2 * spaceDeriv φ p.1 p.2 (w₁ p.1 p.2 - w₂ p.1 p.2) := by
      simp only [transportIntegrand, spaceDeriv_sub]
      ring
    rw [heq]
    by_cases hp : p.2 ∈ ball (0 : ℂ) R
    · rw [indicator_of_mem (show p ∈ (univ : Set ℝ) ×ˢ ball (0 : ℂ) R from ⟨mem_univ _, hp⟩)]
      rw [Real.enorm_eq_ofReal_abs, abs_mul, ← ofReal_norm, ← ENNReal.ofReal_mul
        (mul_nonneg hB ((norm_nonneg _).trans (hD 0)))]
      refine ENNReal.ofReal_le_ofReal ?_
      calc |u p.1 p.2| * |spaceDeriv φ p.1 p.2 (w₁ p.1 p.2 - w₂ p.1 p.2)|
          ≤ B * (D * ‖w₁ p.1 p.2 - w₂ p.1 p.2‖) :=
            mul_le_mul (huB _ _) (abs_spaceDeriv_le hφ hD _ _ _) (abs_nonneg _) hB
        _ = B * D * ‖w₁ p.1 p.2 - w₂ p.1 p.2‖ := by ring
    · rw [spaceDeriv_eq_zero_of_notMem hφ (fun h => hp (hsupp _ h)), mul_zero, enorm_zero]
      exact zero_le
  refine (lintegral_mono hpt).trans (le_of_eq ?_)
  rw [lintegral_indicator (measurableSet_univ_prod_ball R),
    Measure.restrict_restrict (measurableSet_univ_prod_ball R), prod_ball_inter_slab,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- `‖vₙ - v‖_{L¹((0,T) × B_R)} → 0` (`prop:compact`(iii) with `s = 1`, Hölder on `B_R`). -/
theorem tendsto_lintegral_velocity_sub (hseq : IsCompactSeq T M gs g ωs)
    (hlim : IsCompactLimit T g ωs ω) {R : ℝ} (hR : 0 < R) :
    Tendsto (fun n => ∫⁻ p in Ioo 0 T ×ˢ ball (0 : ℂ) R,
      ‖velocityField (ωs n) p.1 p.2 - velocityField ω p.1 p.2‖ₑ) atTop (𝓝 0) := by
  have hconv := hlim.velocity_tendsto 1 le_rfl R hR
  have : IsFiniteMeasure (volume.restrict (ball (0 : ℂ) R)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  set c := (volume.restrict (ball (0 : ℂ) R)) univ ^
    (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) with hc_def
  have hc : c ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _)
  have hle : ∀ n, ∫⁻ p in Ioo 0 T ×ˢ ball (0 : ℂ) R,
      ‖velocityField (ωs n) p.1 p.2 - velocityField ω p.1 p.2‖ₑ ≤
      bochnerNorm (ENNReal.ofReal 1) 2 (Ioo 0 T) (ball (0 : ℂ) R)
        (fun t x => velocityField (ωs n) t x - velocityField ω t x) * c := by
    intro n
    refine (lintegral_prodSet_le _ _ _).trans ?_
    rw [bochnerNorm, ENNReal.ofReal_one, eLpNorm_one_eq_lintegral_enorm,
      ← lintegral_mul_const' _ _ hc]
    have hm : AEStronglyMeasurable
        (fun p : ℝ × ℂ => velocityField (ωs n) p.1 p.2 - velocityField ω p.1 p.2)
        ((volume.restrict (Ioo 0 T)).prod volume) := by
      rw [← restrict_slab_eq_prod]
      exact (Conv.aestronglyMeasurable_velocityField_slab
        (hseq.weakSolution n).memX.aestronglyMeasurable).sub
        (Conv.aestronglyMeasurable_velocityField_slab hlim.weakSolution.memX.aestronglyMeasurable)
    refine lintegral_mono_ae ?_
    filter_upwards [hm.prodMk_left] with t ht
    rw [enorm_eq_self]
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num)
      (ht.restrict (s := ball (0 : ℂ) R))
    rw [eLpNorm_one_eq_lintegral_enorm] at h
    exact h
  have h0 : Tendsto (fun n => bochnerNorm (ENNReal.ofReal 1) 2 (Ioo 0 T) (ball (0 : ℂ) R)
      (fun t x => velocityField (ωs n) t x - velocityField ω t x) * c) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const hconv (Or.inr hc)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun _ => zero_le) hle

/-- The datum term is integrable. -/
theorem integrable_datum {γ : ℝ → ℝ} (hγ : Equimeas.IsLipO γ) {h : ℂ → ℝ} (hh : MemLp h 1 volume)
    {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) :
    Integrable (fun x => γ (h x) * φ (0, x)) := by
  obtain ⟨L, hL0, hLs, -⟩ := isLipO_exists_abs_le hγ
  obtain ⟨A, hA0, hA⟩ := exists_bound_of_isTestFunction hφ
  have hc : Continuous fun x : ℂ => φ (0, x) :=
    hφ.contDiff.continuous.comp (continuous_const.prodMk continuous_id)
  refine Integrable.mono' ((memLp_one_iff_integrable.1 hh).norm.const_mul (L * A))
    (((isLipO_continuous hγ).comp_aestronglyMeasurable hh.1).mul hc.aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
  calc |γ (h x)| * |φ (0, x)| ≤ (L * |h x|) * A :=
        mul_le_mul (hLs _) (hA _) (abs_nonneg _) (by positivity)
    _ = L * A * |h x| := by ring

/-- The data converge: `∫ γ(gₙ) φ(0) → ∫ γ(g) φ(0)`. -/
theorem tendsto_datum (hseq : IsCompactSeq T M gs g ωs)
    (hstrong : Tendsto (fun n => normL1LpE 2 (gs n - g)) atTop (𝓝 0)) {γ : ℝ → ℝ}
    (hγ : Equimeas.IsLipO γ) {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) :
    Tendsto (fun n => ∫ x, γ (gs n x) * φ (0, x)) atTop (𝓝 (∫ x, γ (g x) * φ (0, x))) := by
  obtain ⟨L, hL0, -, hL⟩ := isLipO_exists_abs_le hγ
  obtain ⟨A, hA0, hA⟩ := exists_bound_of_isTestFunction hφ
  refine tendsto_of_enorm_sub_le (e := fun n => ENNReal.ofReal (L * A) * normL1LpE 2 (gs n - g))
    (fun n => ?_) ?_
  · rw [← integral_sub (integrable_datum hγ (hseq.memLp_one_seq n) hφ)
      (integrable_datum hγ hseq.memLp_one hφ)]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    refine le_trans ?_ (mul_le_mul_right (eLpNorm_one_le_normL1LpE 2 _) _)
    rw [eLpNorm_one_eq_lintegral_enorm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun x => ?_
    rw [← sub_mul, Real.enorm_eq_ofReal_abs, Pi.sub_apply, Real.enorm_eq_ofReal_abs,
      ← ENNReal.ofReal_mul (by positivity), abs_mul]
    refine ENNReal.ofReal_le_ofReal ?_
    calc |γ (gs n x) - γ (g x)| * |φ (0, x)| ≤ (L * |gs n x - g x|) * A :=
          mul_le_mul (hL _ _) (hA _) (abs_nonneg _) (by positivity)
      _ = L * A * |gs n x - g x| := by ring
  · simpa using ENNReal.Tendsto.const_mul hstrong (Or.inr ENNReal.ofReal_ne_top)

end NonUniqueEuler.Compact.WeakLimitAux
