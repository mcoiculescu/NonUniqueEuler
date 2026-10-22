import NonUniqueEuler.H.Sec3.Stable.WeakLimit.Basic
import NonUniqueEuler.H.Sec3.Stable.WeakLimit.Weak
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-!
# Helpers for `prop:stable`, step 1a: bounds and extraction of the weak limits

Helper file of `P/Sec3/Stable/WeakLimit.lean` (`03_compactness.tex:743-755`).

For a continuous `γ` with `|γ(s)| ≤ C|s|` and `|γ| ≤ B` (the cases `γ = β` and `γ = β²`):
* `lintegral_seq_le`: `∫_E ‖γ(ωₙ(t))‖_{L¹} dt ≤ C M |E ∩ (0,T)|` (Tonelli and the bound
  `‖ωₙ(t)‖_{L¹} ≤ M` of `IsCompactSeq`);
* `memLp_two_seq`, `eLpNorm_two_seq_le`: `γ(ωₙ)` is bounded in `L²((0,T) × ℝ²)` (by
  `(B C M T)^{1/2}`; restructuring R5);
* `exists_weak_limit`: along a subsequence `γ(ωₙ) ⇀ G` weakly in `L²((0,T) × ℝ²)`, with `G`
  measurable, `|G| ≤ B` everywhere, and `‖G(t)‖_{L¹} ≤ C M` for a.e. `t ∈ (0,T)` (testing with
  `1_{E × ℝ²}`, `03_compactness.tex:749-752`);
* `memLinfLp_of_slice`: such a `G` lies in `L^∞(0,T; L¹) ∩ L^∞(0,T; L²)`
  (`‖G(t)‖₂² ≤ B ‖G(t)‖₁`).
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace NonUniqueEuler.Compact.WeakLimitAux

open Weak

variable {T M : ℝ} {gs : ℕ → ℂ → ℝ} {g : ℂ → ℝ} {ωs : ℕ → ℝ → ℂ → ℝ}

theorem seq_eLpNorm_one_le (hseq : IsCompactSeq T M gs g ωs) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 T) : eLpNorm (ωs n t) 1 volume ≤ ENNReal.ofReal M :=
  (eLpNorm_one_le_normL1LpE 2 _).trans (hseq.bound n t ht)

theorem prod_univ_inter_slab (E : Set ℝ) (T : ℝ) :
    (E ×ˢ (univ : Set ℂ)) ∩ slab T = (E ∩ Ioo 0 T) ×ˢ (univ : Set ℂ) := by
  rw [slab, prod_inter_prod, inter_univ]

/-- `∫_{E × ℝ²} |f| ≤ C M |E ∩ (0,T)|` on the slab for `|f| ≤ C |ωₙ|`. -/
theorem lintegral_seq_le (hseq : IsCompactSeq T M gs g ωs) (n : ℕ) {C : ℝ} (hC : 0 ≤ C)
    {f : ℝ × ℂ → ℝ} (hf : ∀ p, |f p| ≤ C * |ωs n p.1 p.2|) {E : Set ℝ} (hE : MeasurableSet E) :
    ∫⁻ p in E ×ˢ univ, ‖f p‖ₑ ∂(volume.restrict (slab T)) ≤
      ENNReal.ofReal (C * M) * volume (E ∩ Ioo 0 T) := by
  rw [Measure.restrict_restrict (hE.prod MeasurableSet.univ), prod_univ_inter_slab]
  refine (lintegral_prodSet_le _ _ _).trans ?_
  have hb : ∀ t ∈ E ∩ Ioo 0 T, ∫⁻ x in univ, ‖f (t, x)‖ₑ ≤ ENNReal.ofReal (C * M) := by
    intro t ht
    rw [Measure.restrict_univ]
    have h1 : ∀ x, ‖f (t, x)‖ₑ ≤ ENNReal.ofReal C * ‖ωs n t x‖ₑ := by
      intro x
      rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul hC]
      exact ENNReal.ofReal_le_ofReal (hf (t, x))
    calc ∫⁻ x, ‖f (t, x)‖ₑ ≤ ∫⁻ x, ENNReal.ofReal C * ‖ωs n t x‖ₑ := lintegral_mono h1
      _ = ENNReal.ofReal C * eLpNorm (ωs n t) 1 volume := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, eLpNorm_one_eq_lintegral_enorm]
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal M := by
          gcongr
          exact seq_eLpNorm_one_le hseq n (Ioo_subset_Icc_self ht.2)
      _ = ENNReal.ofReal (C * M) := (ENNReal.ofReal_mul hC).symm
  refine (setLIntegral_mono' (hE.inter measurableSet_Ioo) hb).trans ?_
  rw [setLIntegral_const, mul_comm]

/-- `∫_{slab} |f| ≤ C M T` for `|f| ≤ C |ωₙ|`. -/
theorem lintegral_seq_le_slab (hseq : IsCompactSeq T M gs g ωs) (n : ℕ) {C : ℝ} (hC : 0 ≤ C)
    {f : ℝ × ℂ → ℝ} (hf : ∀ p, |f p| ≤ C * |ωs n p.1 p.2|) :
    ∫⁻ p, ‖f p‖ₑ ∂(volume.restrict (slab T)) ≤ ENNReal.ofReal (C * M) * ENNReal.ofReal T := by
  have h := lintegral_seq_le hseq n hC hf MeasurableSet.univ
  rw [univ_prod_univ, Measure.restrict_univ, univ_inter, Real.volume_Ioo, sub_zero] at h
  exact h

/-- The `L²` bound of the sequence (restructuring R5). -/
theorem eLpNorm_two_seq_le (hseq : IsCompactSeq T M gs g ωs) (n : ℕ) {C B : ℝ} (hC : 0 ≤ C)
    {f : ℝ × ℂ → ℝ} (hf : ∀ p, |f p| ≤ C * |ωs n p.1 p.2|) (hfB : ∀ p, |f p| ≤ B) :
    eLpNorm f 2 (volume.restrict (slab T)) ≤
      (ENNReal.ofReal B * (ENNReal.ofReal (C * M) * ENNReal.ofReal T)) ^ (1 / 2 : ℝ) := by
  refine (eLpNorm_two_le_of_bound (Eventually.of_forall hfB)).trans ?_
  gcongr
  exact lintegral_seq_le_slab hseq n hC hf

theorem bound_ne_top (B C M T : ℝ) :
    (ENNReal.ofReal B * (ENNReal.ofReal (C * M) * ENNReal.ofReal T)) ^ (1 / 2 : ℝ) ≠ ∞ :=
  ENNReal.rpow_ne_top_of_nonneg (by norm_num)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top))

theorem aestronglyMeasurable_seq (hseq : IsCompactSeq T M gs g ωs) (n : ℕ) {γ : ℝ → ℝ}
    (hγc : Continuous γ) :
    AEStronglyMeasurable (fun p : ℝ × ℂ => γ (ωs n p.1 p.2)) (volume.restrict (slab T)) :=
  hγc.comp_aestronglyMeasurable (hseq.weakSolution n).memX.aestronglyMeasurable

theorem memLp_two_seq (hseq : IsCompactSeq T M gs g ωs) (n : ℕ) {γ : ℝ → ℝ}
    (hγc : Continuous γ) {C B : ℝ} (hC : 0 ≤ C) (hγC : ∀ s, |γ s| ≤ C * |s|)
    (hγB : ∀ s, |γ s| ≤ B) :
    MemLp (fun p : ℝ × ℂ => γ (ωs n p.1 p.2)) 2 (volume.restrict (slab T)) :=
  ⟨aestronglyMeasurable_seq hseq n hγc,
    lt_of_le_of_lt (eLpNorm_two_seq_le hseq n hC (fun _ => hγC _) (fun _ => hγB _))
      (bound_ne_top B C M T).lt_top⟩

/-- Tonelli in the time slices of the slab, for measurable integrands. -/
theorem setLIntegral_slice_eq {G : ℝ × ℂ → ℝ} (hGm : Measurable G) {s : Set ℝ}
    (hs : MeasurableSet s) :
    ∫⁻ t in s, (∫⁻ x : ℂ, ‖G (t, x)‖ₑ) ∂(volume.restrict (Ioo 0 T)) =
      ∫⁻ p in s ×ˢ univ, ‖G p‖ₑ ∂(volume.restrict (slab T)) := by
  rw [Measure.restrict_restrict hs, Measure.restrict_restrict (hs.prod MeasurableSet.univ),
    prod_univ_inter_slab, lintegral_prodSet_eq _ _ hGm.enorm]
  simp only [Measure.restrict_univ]

/-- An integral bound on every set `E × ℝ²` gives an a.e. bound of the slices. -/
theorem ae_slice_le_of_forall {G : ℝ × ℂ → ℝ} (hGm : Measurable G) {A : ℝ≥0∞}
    (hE : ∀ E : Set ℝ, MeasurableSet E →
      ∫⁻ p in E ×ˢ univ, ‖G p‖ₑ ∂(volume.restrict (slab T)) ≤ A * volume (E ∩ Ioo 0 T)) :
    ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), ∫⁻ x, ‖G (t, x)‖ₑ ≤ A := by
  have hF : Measurable fun t => ∫⁻ x, ‖G (t, x)‖ₑ := hGm.enorm.lintegral_prod_right'
  refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (g := fun _ => A) hF fun s hs _ => ?_
  rw [setLIntegral_slice_eq hGm hs, setLIntegral_const, Measure.restrict_apply hs]
  exact hE s hs

/-- **Extraction.** Along a subsequence `γ(ωₙ) ⇀ G` weakly in `L²((0,T) × ℝ²)`; `G` is measurable,
`|G| ≤ B`, and `‖G(t)‖_{L¹} ≤ C M` for a.e. `t ∈ (0,T)`. -/
theorem exists_weak_limit (hseq : IsCompactSeq T M gs g ωs) {γ : ℝ → ℝ} (hγc : Continuous γ)
    {C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B) (hγC : ∀ s, |γ s| ≤ C * |s|) (hγB : ∀ s, |γ s| ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : ℝ × ℂ → ℝ, Measurable G ∧ (∀ p, |G p| ≤ B) ∧
      MemLp G 2 (volume.restrict (slab T)) ∧
      (∀ Φ : ℝ × ℂ → ℝ, MemLp Φ 2 (volume.restrict (slab T)) →
        Tendsto (fun n => ∫ p in slab T, γ (ωs (φ n) p.1 p.2) * Φ p) atTop
          (𝓝 (∫ p in slab T, G p * Φ p))) ∧
      (∀ᵐ t ∂(volume.restrict (Ioo 0 T)), ∫⁻ x, ‖G (t, x)‖ₑ ≤ ENNReal.ofReal (C * M)) := by
  set K := (ENNReal.ofReal B * (ENNReal.ofReal (C * M) * ENNReal.ofReal T)) ^ (1 / 2 : ℝ)
  have hK : ∀ n, eLpNorm (fun p : ℝ × ℂ => γ (ωs n p.1 p.2)) 2 (volume.restrict (slab T)) ≤
      ENNReal.ofReal K.toReal := by
    intro n
    rw [ENNReal.ofReal_toReal (bound_ne_top B C M T)]
    exact eLpNorm_two_seq_le hseq n hC (fun _ => hγC _) (fun _ => hγB _)
  obtain ⟨φ, hφ, G, hGm, hGB, hG2, hw⟩ := exists_subseq_weak_bdd
    (fun n => memLp_two_seq hseq n hγc hC hγC hγB) hK hB
    (fun n => Eventually.of_forall fun p => hγB _)
  refine ⟨φ, hφ, G, hGm, hGB, hG2, hw, ae_slice_le_of_forall hGm fun E hE => ?_⟩
  exact setLIntegral_le_of_weak (fun n => memLp_two_seq hseq (φ n) hγc hC hγC hγB) hG2 hw
    (hE.prod MeasurableSet.univ) (fun n => lintegral_seq_le hseq (φ n) hC (fun p => hγC _) hE)

/-- A bounded measurable function with an a.e. `L¹` slice bound lies in
`L^∞(0,T; L¹) ∩ L^∞(0,T; L²)`. -/
theorem memLinfLp_of_slice {G : ℝ × ℂ → ℝ} (hGm : Measurable G) {B : ℝ} (hGB : ∀ p, |G p| ≤ B)
    {A : ℝ} (hA : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), ∫⁻ x, ‖G (t, x)‖ₑ ≤ ENNReal.ofReal A) :
    Prelim.MemLinfLp (Ioo 0 T) univ 1 (fun t x => G (t, x)) ∧
      Prelim.MemLinfLp (Ioo 0 T) univ 2 (fun t x => G (t, x)) := by
  have hm : AEStronglyMeasurable (Function.uncurry fun t x => G (t, x))
      (volume.restrict (Ioo 0 T ×ˢ univ)) := hGm.aestronglyMeasurable
  have hsl : ∀ t, AEStronglyMeasurable (fun x => G (t, x)) volume := fun t =>
    (hGm.comp measurable_prodMk_left).aestronglyMeasurable
  have h1 : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), eLpNorm (fun x => G (t, x)) 1 volume ≤
      ENNReal.ofReal (max A 0) := hA.mono fun t ht => by
    rw [eLpNorm_one_eq_lintegral_enorm]
    exact ht.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  set K := (ENNReal.ofReal B * ENNReal.ofReal (max A 0)) ^ (1 / 2 : ℝ)
  have hKt : K ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by norm_num)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  have h2 : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), eLpNorm (fun x => G (t, x)) 2 volume ≤ K :=
    h1.mono fun t ht => by
      refine (eLpNorm_two_le_of_bound (Eventually.of_forall fun x => hGB (t, x))).trans ?_
      rw [← eLpNorm_one_eq_lintegral_enorm]
      exact ENNReal.rpow_le_rpow (by gcongr) (by norm_num)
  refine ⟨⟨hm, max A 0, h1.mono fun t ht => ?_⟩, ⟨hm, K.toReal, h2.mono fun t ht => ?_⟩⟩
  · rw [Measure.restrict_univ]
    exact ⟨⟨hsl t, ht.trans_lt ENNReal.ofReal_lt_top⟩,
      ENNReal.toReal_le_of_le_ofReal (le_max_right _ _) ht⟩
  · rw [Measure.restrict_univ]
    exact ⟨⟨hsl t, ht.trans_lt hKt.lt_top⟩, ENNReal.toReal_mono hKt ht⟩

end NonUniqueEuler.Compact.WeakLimitAux
