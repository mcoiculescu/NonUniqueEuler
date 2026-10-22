import NonUniqueEuler.Defs.Sec3.Compact
import NonUniqueEuler.I.Sec3.VelocityField
import NonUniqueEuler.H.Sec3.Stable.RenormLimit.Basic
import NonUniqueEuler.H.Sec3.Stable.RenormLimit.Terms

/-!
# Proof: `prop:stable`, step 3 — the limit is renormalized

Proof of `I/Sec3/Stable/RenormLimit.lean` (`03_compactness.tex:802-815`).

Let `Υ` be a renormalization (`|Υ(a) - Υ(b)| ≤ L|a - b|`, `|Υ(s)| ≤ L|s|`) and `φ ∈ 𝒟_T` with
`supp φ ⊂ ℝ × B_R`, `‖Dφ‖ ≤ D`, `|φ| ≤ A`.
* Integrability: `Υ(ω)(∂_tφ + v·∇φ)` and `Υ(g)φ(0)` are dominated by `L` times the integrands of
  the weak formulation of `ω` (`RenormLimitAux.integrable_renorm_mul`).
* Identity: eq:renorm holds for every `ωₙ`. The space–time integrands converge in
  `L¹((0,T)×ℝ²)`: by `RenormLimitAux.lintegral_transport_sub_le` the error is at most
  `LD (∫|ωₙ - ω| + ∫|ωₙ||vₙ - v| + ∫|ωₙ - ω||v|)` over `(0,T) × B_R`. The first term tends to `0`
  by hypothesis; the second is `≤ M ∫_0^T ‖vₙ(t) - v(t)‖_{L²(B_R)} dt → 0`
  (`prop:compact`(iii)); the third tends to `0` by the weak `L²` argument of the manuscript
  (`RenormLimitAux.tendsto_lintegral_sub_mul`; `‖ωₙ(t) - ω(t)‖₂ ≤ 2M`, `v ∈ L^∞(0,T;L²(B_R))`).
  The data converge in `L¹`: `|Υ(gₙ) - Υ(g)||φ(0)| ≤ LA|gₙ - g|`.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace NonUniqueEuler.Compact

open Weak RenormLimitAux

/-- For `t ∈ [0, T]`, `‖ω(t)‖_{L²} ≤ M` for the limit (lower semicontinuity, `prop:compact`(ii)). -/
private theorem eLpNorm_limit_le {T M : ℝ} {gs : ℕ → ℂ → ℝ} {g : ℂ → ℝ} {ωs : ℕ → ℝ → ℂ → ℝ}
    {ω : ℝ → ℂ → ℝ} (hseq : IsCompactSeq T M gs g ωs) (hlim : IsCompactLimit T g ωs ω)
    {t : ℝ} (ht : t ∈ Icc 0 T) : eLpNorm (ω t) 2 volume ≤ ENNReal.ofReal M := by
  have h := hlim.eLpNorm_le_liminf t ht 2 one_le_two le_rfl
  rw [ENNReal.ofReal_ofNat] at h
  refine h.trans (liminf_le_of_frequently_le' (Frequently.of_forall fun n => ?_))
  exact (eLpNorm_le_normL1LpE 2 (ωs n t)).trans (hseq.bound n t ht)

/-- `‖ωₙ(t) - ω(t)‖_{L²(B_R)} ≤ 2M` for `t ∈ (0, T)`. -/
private theorem ae_eLpNorm_sub_le {T M R : ℝ} {gs : ℕ → ℂ → ℝ} {g : ℂ → ℝ}
    {ωs : ℕ → ℝ → ℂ → ℝ} {ω : ℝ → ℂ → ℝ} (hseq : IsCompactSeq T M gs g ωs)
    (hlim : IsCompactLimit T g ωs ω) (n : ℕ) :
    ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)),
      eLpNorm (fun x => ωs n t x - ω t x) 2 (volume.restrict (ball (0 : ℂ) R)) ≤
        ENNReal.ofReal M + ENNReal.ofReal M := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have ht' : t ∈ Icc 0 T := Ioo_subset_Icc_self ht
  calc eLpNorm (fun x => ωs n t x - ω t x) 2 (volume.restrict (ball (0 : ℂ) R)) ≤
        eLpNorm (ωs n t - ω t) 2 volume := eLpNorm_mono_measure _ Measure.restrict_le_self
    _ ≤ eLpNorm (ωs n t) 2 volume + eLpNorm (ω t) 2 volume :=
        eLpNorm_sub_le ((hseq.weakCont n).memLp t ht').aestronglyMeasurable
          (hlim.weakCont.memLp t ht').aestronglyMeasurable one_le_two
    _ ≤ ENNReal.ofReal M + ENNReal.ofReal M :=
        add_le_add ((eLpNorm_le_normL1LpE 2 (ωs n t)).trans (hseq.bound n t ht'))
          (eLpNorm_limit_le hseq hlim ht')

/-- The velocity of a weak solution has a uniform `L²(B_R)` bound on a.e. slice. -/
private theorem exists_ae_eLpNorm_velocity_le {T : ℝ} {g : ℂ → ℝ} {ω : ℝ → ℂ → ℝ}
    (hω : IsWeakSolution 2 T g ω) {R : ℝ} (hR : 0 < R) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)),
      eLpNorm (velocityField ω t) 2 (volume.restrict (ball (0 : ℂ) R)) ≤ K := by
  obtain ⟨K, hK⟩ := (hω.memLinfLp_velocityField hR).1.essBounded
  refine ⟨ENNReal.ofReal K, ENNReal.ofReal_ne_top, ?_⟩
  filter_upwards [hK] with t ht
  rw [← ENNReal.ofReal_toReal ht.1.eLpNorm_ne_top]
  exact ENNReal.ofReal_le_ofReal ht.2

/-- The renormalized transport integrands converge in `L¹((0,T)×ℝ²)`. -/
private theorem tendsto_lintegral_transport {T M : ℝ} {gs : ℕ → ℂ → ℝ} {g : ℂ → ℝ}
    {ωs : ℕ → ℝ → ℂ → ℝ} {ω : ℝ → ℂ → ℝ} (hseq : IsCompactSeq T M gs g ωs)
    (hlim : IsCompactLimit T g ωs ω)
    (hL1 : ∀ R : ℝ, 0 < R →
      Tendsto (fun n => ∫⁻ p in Ioo 0 T ×ˢ ball (0 : ℂ) R, ‖ωs n p.1 p.2 - ω p.1 p.2‖ₑ) atTop
        (𝓝 0))
    {Υ : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L) (hlip : ∀ a b, |Υ a - Υ b| ≤ L * |a - b|)
    (hlin : ∀ s, |Υ s| ≤ L * |s|) {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) :
    Tendsto (fun n => ∫⁻ p in slab T,
      ‖transportIntegrand (fun t x => Υ (ωs n t x)) (velocityField (ωs n)) φ p -
        transportIntegrand (fun t x => Υ (ω t x)) (velocityField ω) φ p‖ₑ) atTop (𝓝 0) := by
  obtain ⟨D, hD0, hD⟩ := exists_bound_fderiv_of_isTestFunction hφ
  obtain ⟨R, hR0, hR⟩ := exists_ball_of_isTestFunction hφ
  have hsub : Ioo (0 : ℝ) T ×ˢ ball (0 : ℂ) R ⊆ slab T := fun p hp => ⟨hp.1, mem_univ _⟩
  have hωn : ∀ n, AEStronglyMeasurable (Function.uncurry (ωs n))
      (volume.restrict (Ioo (0 : ℝ) T ×ˢ ball (0 : ℂ) R)) := fun n =>
    (hseq.weakSolution n).memX.aestronglyMeasurable.mono_set hsub
  have hω : AEStronglyMeasurable (Function.uncurry ω)
      (volume.restrict (Ioo (0 : ℝ) T ×ˢ ball (0 : ℂ) R)) :=
    hlim.weakSolution.memX.aestronglyMeasurable.mono_set hsub
  have hv := (hlim.weakSolution.memLinfLp_velocityField hR0).1
  -- second term: `∫|ωₙ||vₙ - v| ≤ M ‖vₙ - v‖_{L¹(0,T;L²(B_R))} → 0`
  have hT2 : Tendsto (fun n => ∫⁻ p in Ioo (0 : ℝ) T ×ˢ ball (0 : ℂ) R,
      ‖ωs n p.1 p.2‖ₑ * ‖velocityField (ωs n) p.1 p.2 - velocityField ω p.1 p.2‖ₑ) atTop
      (𝓝 0) := by
    have hvel : Tendsto (fun n => bochnerNorm 1 2 (Ioo 0 T) (ball (0 : ℂ) R)
        (fun t x => velocityField (ωs n) t x - velocityField ω t x)) atTop (𝓝 0) := by
      simpa only [ENNReal.ofReal_one] using hlim.velocity_tendsto 1 le_rfl R hR0
    have hlim2 := ENNReal.Tendsto.const_mul hvel (Or.inr (ENNReal.ofReal_ne_top (r := M)))
    rw [mul_zero] at hlim2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim2
      (fun _ => zero_le) (fun n => ?_)
    have hvn := ((hseq.weakSolution n).memLinfLp_velocityField hR0).1
    refine lintegral_prodSet_mul_le ENNReal.ofReal_ne_top ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have ht' : t ∈ Icc 0 T := Ioo_subset_Icc_self ht
      exact ⟨((hseq.weakCont n).memLp t ht').aestronglyMeasurable.restrict,
        (eLpNorm_mono_measure _ Measure.restrict_le_self).trans
          ((eLpNorm_le_normL1LpE 2 (ωs n t)).trans (hseq.bound n t ht'))⟩
    · filter_upwards [hvn.essBounded.choose_spec, hv.essBounded.choose_spec] with t h1 h2
      exact h1.1.aestronglyMeasurable.sub h2.1.aestronglyMeasurable
  -- third term: `∫|ωₙ - ω||v| → 0`
  have hT3 : Tendsto (fun n => ∫⁻ p in Ioo (0 : ℝ) T ×ˢ ball (0 : ℂ) R,
      ‖ωs n p.1 p.2 - ω p.1 p.2‖ₑ * ‖velocityField ω p.1 p.2‖ₑ) atTop (𝓝 0) := by
    obtain ⟨Kv, hKv, hKvb⟩ := exists_ae_eLpNorm_velocity_le hlim.weakSolution hR0
    exact tendsto_lintegral_sub_mul measure_Ioo_lt_top.ne
      (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩) hKv hωn hω
      hv.aestronglyMeasurable (hL1 R hR0) (ae_eLpNorm_sub_le hseq hlim) hKvb
  have hsum := ENNReal.Tendsto.const_mul ((hL1 R hR0).add hT2 |>.add hT3)
    (Or.inr (ENNReal.ofReal_ne_top (r := L * D)))
  simp only [add_zero, mul_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) (fun n => ?_)
  exact lintegral_transport_sub_le hL hD0 hlip hlin hφ hD hR (hωn n) hω hv.aestronglyMeasurable

/-- The renormalized data converge in `L¹`. -/
private theorem tendsto_lintegral_datum {T M : ℝ} {gs : ℕ → ℂ → ℝ} {g : ℂ → ℝ}
    {ωs : ℕ → ℝ → ℂ → ℝ} (_hseq : IsCompactSeq T M gs g ωs)
    (hstrong : Tendsto (fun n => normL1LpE 2 (gs n - g)) atTop (𝓝 0))
    {Υ : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L) (hlip : ∀ a b, |Υ a - Υ b| ≤ L * |a - b|)
    {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) :
    Tendsto (fun n => ∫⁻ x, ‖Υ (gs n x) * φ (0, x) - Υ (g x) * φ (0, x)‖ₑ) atTop (𝓝 0) := by
  obtain ⟨A, hA0, hA⟩ := exists_bound_of_isTestFunction hφ
  have hlim2 := ENNReal.Tendsto.const_mul hstrong
    (Or.inr (ENNReal.ofReal_ne_top (r := L * A)))
  rw [mul_zero] at hlim2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim2
    (fun _ => zero_le) (fun n => ?_)
  calc ∫⁻ x, ‖Υ (gs n x) * φ (0, x) - Υ (g x) * φ (0, x)‖ₑ ≤
        ∫⁻ x, ENNReal.ofReal (L * A) * ‖gs n x - g x‖ₑ := by
        refine lintegral_mono fun x => enorm_le_ofReal_mul_enorm (by positivity) ?_
        rw [← sub_mul, abs_mul]
        calc |Υ (gs n x) - Υ (g x)| * |φ (0, x)| ≤ (L * |gs n x - g x|) * A :=
              mul_le_mul (hlip _ _) (hA _) (abs_nonneg _) (by positivity)
          _ = L * A * |gs n x - g x| := by ring
    _ = ENNReal.ofReal (L * A) * eLpNorm (gs n - g) 1 volume := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, eLpNorm_one_eq_lintegral_enorm]
        rfl
    _ ≤ ENNReal.ofReal (L * A) * normL1LpE 2 (gs n - g) := by
        gcongr; exact eLpNorm_one_le_normL1LpE 2 _

/-- **`prop:stable`, step 3** (`03_compactness.tex:802-815`): if, in the setting of
`prop:stable`, `ωₙ → ω` in `L¹((0,T) × B_R)` for every `R > 0`, then `ω` is a renormalized weak
solution in `X₂(T)` with datum `g`. -/
theorem stable_renormalized {T M : ℝ} {gs : ℕ → ℂ → ℝ} {g : ℂ → ℝ} {ωs : ℕ → ℝ → ℂ → ℝ}
    {ω : ℝ → ℂ → ℝ} (hseq : IsCompactSeq T M gs g ωs) (hlim : IsCompactLimit T g ωs ω)
    (hstrong : Tendsto (fun n => normL1LpE 2 (gs n - g)) atTop (𝓝 0))
    (hren : ∀ n, IsRenormalizedWeakSolution 2 T (gs n) (ωs n))
    (hL1 : ∀ R : ℝ, 0 < R →
      Tendsto (fun n => ∫⁻ p in Ioo 0 T ×ˢ ball (0 : ℂ) R, ‖ωs n p.1 p.2 - ω p.1 p.2‖ₑ) atTop
        (𝓝 0)) :
    IsRenormalizedWeakSolution 2 T g ω := by
  refine ⟨hlim.weakSolution, fun Υ hΥ => ?_⟩
  obtain ⟨L, hL, hlip, hlin⟩ := exists_lipschitz_of_isRenormalization hΥ
  have hΥc : Continuous Υ := hΥ.contDiff.continuous
  have hint : ∀ φ, IsTestFunction T φ →
      IntegrableOn (transportIntegrand (fun t x => Υ (ω t x)) (velocityField ω) φ) (slab T) :=
    fun φ hφ => integrable_renorm_mul hΥc hΥ.map_zero hlin
      hlim.weakSolution.memX.aestronglyMeasurable (hlim.weakSolution.weak.integrableOn φ hφ)
  have hdat : ∀ φ, IsTestFunction T φ → Integrable (fun x : ℂ => Υ (g x) * φ (0, x)) :=
    fun φ hφ => integrable_renorm_mul hΥc hΥ.map_zero hlin hseq.memLp_one.aestronglyMeasurable
      (hlim.weakSolution.weak.datum_integrable φ hφ)
  refine ⟨hint, hdat, fun φ hφ => ?_⟩
  have hFint : ∀ n, IntegrableOn
      (transportIntegrand (fun t x => Υ (ωs n t x)) (velocityField (ωs n)) φ) (slab T) :=
    fun n => ((hren n).renormalized Υ hΥ).integrableOn φ hφ
  have hn : ∀ n, (∫ p in slab T,
      transportIntegrand (fun t x => Υ (ωs n t x)) (velocityField (ωs n)) φ p) +
        ∫ x : ℂ, Υ (gs n x) * φ (0, x) = 0 := fun n => by
    have h := ((hren n).renormalized Υ hΥ).identity φ hφ
    rwa [integral_Ioo_integral_eq (t₀ := 0) (hFint n)] at h
  have h1 := tendsto_integral_of_L1 _ (hint φ hφ).aestronglyMeasurable
    (Eventually.of_forall hFint) (tendsto_lintegral_transport hseq hlim hL1 hL hlip hlin hφ)
  have h2 := tendsto_integral_of_L1 _ (hdat φ hφ).aestronglyMeasurable
    (Eventually.of_forall fun n => ((hren n).renormalized Υ hΥ).datum_integrable φ hφ)
    (tendsto_lintegral_datum hseq hstrong hL hlip hφ)
  have h3 := h1.add h2
  simp only [hn] at h3
  rw [integral_Ioo_integral_eq (t₀ := 0) (hint φ hφ)]
  exact tendsto_nhds_unique h3 tendsto_const_nhds

end NonUniqueEuler.Compact
