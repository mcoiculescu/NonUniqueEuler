import NonUniqueEuler.H.Sec3.Stable.WeakLimit.Basic
import NonUniqueEuler.I.Sec2.BSBasic
import NonUniqueEuler.I.Infra.ConvMinkowski.Measurable

/-!
# Helpers for `prop:stable`, step 1a: integrability of the flux `ū v`

Helper file of `P/Sec3/Stable/WeakLimit.lean` (`03_compactness.tex:764-770`).

For a.e. `t`, since `|v(t)| ≤ |K| ∗ |ω(t)|` and `|K|` is even, Tonelli's theorem and
`lem:BS-basic`(b) give
`∫|ū(t)||v(t)| ≤ ∫|ω(t)| (|K| ∗ |ū(t)|) ≤ ‖ω(t)‖₁ (‖ū(t)‖_∞ + ‖ū(t)‖₁/(2π))`,
so `ū v ∈ L¹((0,T) × ℝ²)`.
* `lintegral_mul_convAbs_comm`: `∫ |f| (|K| ∗ |h|) = ∫ |h| (|K| ∗ |f|)`;
* `lintegral_mul_velocity_le`: the slice bound;
* `integrable_smul_velocityField`: the flux on the slab.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace NonUniqueEuler.Compact.WeakLimitAux

open Weak

theorem measurable_biotSavartKernel' : Measurable biotSavartKernel := by
  unfold biotSavartKernel
  fun_prop

theorem norm_biotSavartKernel_neg (z : ℂ) : ‖biotSavartKernel (-z)‖ = ‖biotSavartKernel z‖ := by
  have h : biotSavartKernel (-z) = -biotSavartKernel z := by
    simp only [biotSavartKernel, norm_neg, mul_neg, neg_div]
  rw [h, norm_neg]

theorem enorm_biotSavartKernel_sub_comm (x y : ℂ) :
    ‖biotSavartKernel (x - y)‖ₑ = ‖biotSavartKernel (y - x)‖ₑ := by
  rw [← neg_sub y x, enorm_eq_nnnorm, enorm_eq_nnnorm]
  congr 1
  ext
  simp only [coe_nnnorm, norm_biotSavartKernel_neg]

/-- `|K|` is even: `∫ |f| (|K| ∗ |h|) = ∫ |h| (|K| ∗ |f|)` (Tonelli). -/
theorem lintegral_mul_convAbs_comm {f h : ℂ → ℝ} (hf : AEMeasurable f volume)
    (hh : AEMeasurable h volume) :
    ∫⁻ x, ‖f x‖ₑ * Conv.convAbs biotSavartKernel h x =
      ∫⁻ y, ‖h y‖ₑ * Conv.convAbs biotSavartKernel f y := by
  have hK : Measurable fun p : ℂ × ℂ => ‖biotSavartKernel (p.1 - p.2)‖ₑ :=
    (measurable_biotSavartKernel'.comp measurable_sub).enorm
  have hmeas : AEMeasurable (Function.uncurry fun x y : ℂ =>
      ‖f x‖ₑ * (‖biotSavartKernel (x - y)‖ₑ * ‖h y‖ₑ)) (volume.prod volume) :=
    hf.enorm.comp_fst.mul (hK.aemeasurable.mul hh.enorm.comp_snd)
  calc ∫⁻ x, ‖f x‖ₑ * Conv.convAbs biotSavartKernel h x
      = ∫⁻ x, ∫⁻ y, ‖f x‖ₑ * (‖biotSavartKernel (x - y)‖ₑ * ‖h y‖ₑ) :=
        lintegral_congr fun x => (lintegral_const_mul' _ _ enorm_ne_top).symm
    _ = ∫⁻ y, ∫⁻ x, ‖f x‖ₑ * (‖biotSavartKernel (x - y)‖ₑ * ‖h y‖ₑ) :=
        lintegral_lintegral_swap hmeas
    _ = ∫⁻ y, ∫⁻ x, ‖h y‖ₑ * (‖biotSavartKernel (y - x)‖ₑ * ‖f x‖ₑ) := by
        refine lintegral_congr fun y => lintegral_congr fun x => ?_
        rw [enorm_biotSavartKernel_sub_comm x y]
        ring
    _ = ∫⁻ y, ‖h y‖ₑ * Conv.convAbs biotSavartKernel f y :=
        lintegral_congr fun y => lintegral_const_mul' _ _ enorm_ne_top

/-- `lem:BS-basic`(b) with `‖h‖_∞ ≤ B`, `‖h‖₁ ≤ C`: `|K| ∗ |h| ≤ B + C/(2π)` everywhere. -/
theorem convAbs_le_of_bounds {h : ℂ → ℝ} (hhm : AEStronglyMeasurable h volume) {B C : ℝ}
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hhB : ∀ x, |h x| ≤ B) (hh1 : ∫⁻ x, ‖h x‖ₑ ≤ ENNReal.ofReal C)
    (y : ℂ) :
    Conv.convAbs biotSavartKernel h y ≤ ENNReal.ofReal (B + C / (2 * Real.pi)) := by
  have h1 : eLpNorm h 1 volume ≤ ENNReal.ofReal C := by
    rw [eLpNorm_one_eq_lintegral_enorm]; exact hh1
  have hinf : eLpNorm h ⊤ volume ≤ ENNReal.ofReal B := by
    rw [eLpNorm_exponent_top]
    exact eLpNormEssSup_le_of_ae_bound (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hhB x)
  have hm1 : MemLp h 1 volume := ⟨hhm, h1.trans_lt ENNReal.ofReal_lt_top⟩
  have hminf : MemLp h ⊤ volume := ⟨hhm, hinf.trans_lt ENNReal.ofReal_lt_top⟩
  refine (BS.convAbs_le_sqrt_L1_Linf hm1 hminf y).trans (ENNReal.ofReal_le_ofReal ?_)
  have ha := ENNReal.toReal_le_of_le_ofReal hC h1
  have hb := ENNReal.toReal_le_of_le_ofReal hB hinf
  refine (BS.sqrt_two_mul_mul_div_pi_le ENNReal.toReal_nonneg ENNReal.toReal_nonneg).trans ?_
  have hpi : 0 < 2 * Real.pi := by positivity
  have : (eLpNorm h 1 volume).toReal / (2 * Real.pi) ≤ C / (2 * Real.pi) :=
    div_le_div_of_nonneg_right ha hpi.le
  linarith

/-- The slice bound `∫|h||v| ≤ ‖w‖₁ (B + C/(2π))` for `v = K ∗ w`. -/
theorem lintegral_mul_velocity_le {h : ℂ → ℝ} (hhm : AEStronglyMeasurable h volume) {B C : ℝ}
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hhB : ∀ x, |h x| ≤ B) (hh1 : ∫⁻ x, ‖h x‖ₑ ≤ ENNReal.ofReal C)
    {w : ℂ → ℝ} (hw : AEStronglyMeasurable w volume) :
    ∫⁻ x, ‖h x‖ₑ * ‖velocity w x‖ₑ ≤
      eLpNorm w 1 volume * ENNReal.ofReal (B + C / (2 * Real.pi)) := by
  calc ∫⁻ x, ‖h x‖ₑ * ‖velocity w x‖ₑ
      ≤ ∫⁻ x, ‖h x‖ₑ * Conv.convAbs biotSavartKernel w x :=
        lintegral_mono fun x => mul_le_mul_right (Conv.enorm_velocity_le w x) _
    _ = ∫⁻ y, ‖w y‖ₑ * Conv.convAbs biotSavartKernel h y :=
        lintegral_mul_convAbs_comm hhm.aemeasurable hw.aemeasurable
    _ ≤ ∫⁻ y, ‖w y‖ₑ * ENNReal.ofReal (B + C / (2 * Real.pi)) :=
        lintegral_mono fun y => by gcongr; exact convAbs_le_of_bounds hhm hB hC hhB hh1 y
    _ = eLpNorm w 1 volume * ENNReal.ofReal (B + C / (2 * Real.pi)) := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, eLpNorm_one_eq_lintegral_enorm]

/-- **Flux integrability** (`03_compactness.tex:764-770`): for `ω ∈ X₂(T)` and a measurable `G`
with `|G| ≤ B` and `‖G(t)‖_{L¹} ≤ C` for a.e. `t`, `G v ∈ L¹((0,T) × ℝ²)`, `v = K ∗ ω`. -/
theorem integrable_smul_velocityField {T : ℝ} {ω : ℝ → ℂ → ℝ} (hω : MemX 2 T ω)
    {G : ℝ × ℂ → ℝ} (hGm : Measurable G) {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hGB : ∀ p, |G p| ≤ B)
    (hGC : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), ∫⁻ x, ‖G (t, x)‖ₑ ≤ ENNReal.ofReal C) :
    Integrable (fun p : ℝ × ℂ => G p • velocityField ω p.1 p.2) (volume.restrict (slab T)) := by
  have hv := Conv.aestronglyMeasurable_velocityField_slab hω.aestronglyMeasurable
  refine ⟨hGm.aestronglyMeasurable.smul hv, ?_⟩
  obtain ⟨M', hM'⟩ := hω.essBounded
  set K₀ := ENNReal.ofReal M' * ENNReal.ofReal (B + C / (2 * Real.pi)) with hK₀
  have hslice : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      ∫⁻ x in univ, ‖G (t, x) • velocityField ω t x‖ₑ ≤ K₀ := by
    filter_upwards [hM', hGC] with t ht htC
    rw [Measure.restrict_univ]
    have hw1 : eLpNorm (ω t) 1 volume ≤ ENNReal.ofReal M' := by
      rw [← ENNReal.ofReal_toReal ht.1.eLpNorm_ne_top]
      exact ENNReal.ofReal_le_ofReal
        (le_trans (le_add_of_nonneg_right ENNReal.toReal_nonneg) ht.2.2)
    calc ∫⁻ x, ‖G (t, x) • velocityField ω t x‖ₑ
        = ∫⁻ x, ‖G (t, x)‖ₑ * ‖velocity (ω t) x‖ₑ :=
          lintegral_congr fun x => enorm_smul _ _
      _ ≤ eLpNorm (ω t) 1 volume * ENNReal.ofReal (B + C / (2 * Real.pi)) :=
          lintegral_mul_velocity_le (hGm.comp measurable_prodMk_left).aestronglyMeasurable
            hB hC (fun x => hGB (t, x)) htC ht.1.1
      _ ≤ K₀ := by rw [hK₀]; gcongr
  have h := lintegral_prodSet_le_of_ae_slice (Ioo 0 T) univ
    (fun p : ℝ × ℂ => ‖G p • velocityField ω p.1 p.2‖ₑ) hslice
  refine h.trans_lt (ENNReal.mul_lt_top ?_ ?_)
  · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  · rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top

end NonUniqueEuler.Compact.WeakLimitAux
