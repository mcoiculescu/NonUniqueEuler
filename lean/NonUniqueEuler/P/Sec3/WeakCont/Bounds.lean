import NonUniqueEuler.Defs.Sec2.Spaces
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Proof of `I/Sec3/WeakCont/Bounds.lean`: Hölder bounds for the flux term `∫ u w·∇ψ`

Manuscript: proof of `lem:weak-cont`, second paragraph (`03_compactness.tex:155-160`), with
`b = b' = 2` (D9).

* `abs_integral_mul_fderiv_le`: `|∫ f (v·∇ψ)| ≤ N W G`.
* `integrableOn_slab_mul_fderiv`: `u w·∇ψ` is integrable on `(0,T) × ℝ²`.

Both rest on the Hölder bound `eLpNorm_one_mul_fderiv_le`
(`‖f (∇ψ·v)‖_{L¹(μ)} ≤ ‖f‖_{L²(μ)} G ‖v‖_{L²(μ)}`, for every measure `μ`), and on the vanishing
of the integrand off `tsupport ψ`. The space–time bound uses Tonelli in the form
`lintegral_prod_le` (no measurability needed) on `(0,T) × B_R`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace NonUniqueEuler.Weak.WeakCont

/-! ### Helpers -/

/-- The flux integrand `f x (∇ψ(x)·v(x))` vanishes off `tsupport ψ`. -/
theorem mul_fderiv_eq_zero_of_notMem {f : ℂ → ℝ} {v : ℂ → ℂ} {ψ : ℂ → ℝ} {x : ℂ}
    (hx : x ∉ tsupport ψ) : f x * fderiv ℝ ψ x (v x) = 0 := by
  simp [fderiv_of_notMem_tsupport ℝ hx]

/-- Hölder (`p = q = 2`, `r = 1`): `‖f (∇ψ·v)‖_{L¹(μ)} ≤ ‖f‖_{L²(μ)} (G ‖v‖_{L²(μ)})`, for any
measure `μ` on `ℂ`, if `‖∇ψ‖ ≤ G` everywhere. -/
theorem eLpNorm_one_mul_fderiv_le {μ : Measure ℂ} {G : ℝ} {f : ℂ → ℝ} {v : ℂ → ℂ}
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 1 ψ) (hf : AEStronglyMeasurable f μ)
    (hv : AEStronglyMeasurable v μ) (hG : ∀ x, ‖fderiv ℝ ψ x‖ ≤ G) :
    eLpNorm (fun x => f x * fderiv ℝ ψ x (v x)) 1 μ ≤
      eLpNorm f 2 μ * (ENNReal.ofReal G * eLpNorm v 2 μ) := by
  have hcont : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv one_ne_zero
  have hh : AEStronglyMeasurable (fun x => fderiv ℝ ψ x (v x)) μ :=
    Continuous.comp_aestronglyMeasurable₂ (g := fun (L : ℂ →L[ℝ] ℝ) (y : ℂ) => L y)
      (continuous_fst.clm_apply continuous_snd) hcont.aestronglyMeasurable hv
  have h1 : eLpNorm (fun x => f x * fderiv ℝ ψ x (v x)) 1 μ ≤
      ((1 : NNReal) : ℝ≥0∞) * eLpNorm f 2 μ * eLpNorm (fun x => fderiv ℝ ψ x (v x)) 2 μ :=
    eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm hf hh (fun a b => a * b) 1
      (Filter.Eventually.of_forall fun x => by simp [norm_mul])
  have h2 : eLpNorm (fun x => fderiv ℝ ψ x (v x)) 2 μ ≤ ENNReal.ofReal G * eLpNorm v 2 μ :=
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      (Filter.Eventually.of_forall fun x => (fderiv ℝ ψ x).le_of_opNorm_le (hG x) (v x)) 2
  calc eLpNorm (fun x => f x * fderiv ℝ ψ x (v x)) 1 μ
      ≤ ((1 : NNReal) : ℝ≥0∞) * eLpNorm f 2 μ * eLpNorm (fun x => fderiv ℝ ψ x (v x)) 2 μ := h1
    _ ≤ eLpNorm f 2 μ * (ENNReal.ofReal G * eLpNorm v 2 μ) := by
      rw [ENNReal.coe_one, one_mul]
      gcongr

/-- An `L^p` norm whose real part is at most `M` is at most `ofReal M`. -/
theorem eLpNorm_le_ofReal_of_toReal_le {E : Type*} [NormedAddCommGroup E] {μ : Measure ℂ}
    {p : ℝ≥0∞} {g : ℂ → E} {M : ℝ} (hg : MemLp g p μ) (hM : (eLpNorm g p μ).toReal ≤ M) :
    eLpNorm g p μ ≤ ENNReal.ofReal M := by
  rw [← ENNReal.ofReal_toReal hg.eLpNorm_ne_top]
  exact ENNReal.ofReal_le_ofReal hM

/-! ### The interface statements -/

/-- Slice bound (`03_compactness.tex:157-158`, `b = 2`): `|∫ f (v·∇ψ)| ≤ N W G` if `‖f‖₂ ≤ N`,
`‖v‖_{L²(B_R)} ≤ W`, `tsupport ψ ⊆ B_R` and `‖∇ψ‖ ≤ G`. -/
theorem abs_integral_mul_fderiv_le {R N W G : ℝ} (hN : 0 ≤ N) (hW : 0 ≤ W) {f : ℂ → ℝ}
    {v : ℂ → ℂ} {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψR : tsupport ψ ⊆ ball (0 : ℂ) R)
    (hf : MemLp f 2 volume) (hfN : eLpNorm f 2 volume ≤ ENNReal.ofReal N)
    (hv : MemLp v 2 (volume.restrict (ball (0 : ℂ) R)))
    (hvW : eLpNorm v 2 (volume.restrict (ball (0 : ℂ) R)) ≤ ENNReal.ofReal W)
    (hG : ∀ x, ‖fderiv ℝ ψ x‖ ≤ G) :
    |∫ x, f x * fderiv ℝ ψ x (v x)| ≤ N * W * G := by
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0)
  have hzero : ∀ x, x ∉ ball (0 : ℂ) R → f x * fderiv ℝ ψ x (v x) = 0 := fun x hx =>
    mul_fderiv_eq_zero_of_notMem fun h => hx (hψR h)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have hfB : eLpNorm f 2 (volume.restrict (ball (0 : ℂ) R)) ≤ ENNReal.ofReal N :=
    (eLpNorm_restrict_le _ _ _ _).trans hfN
  have hbound : eLpNorm (fun x => f x * fderiv ℝ ψ x (v x)) 1
      (volume.restrict (ball (0 : ℂ) R)) ≤ ENNReal.ofReal (N * W * G) := by
    calc eLpNorm (fun x => f x * fderiv ℝ ψ x (v x)) 1 (volume.restrict (ball (0 : ℂ) R))
        ≤ eLpNorm f 2 (volume.restrict (ball (0 : ℂ) R)) *
            (ENNReal.ofReal G * eLpNorm v 2 (volume.restrict (ball (0 : ℂ) R))) :=
          eLpNorm_one_mul_fderiv_le hψ hf.1.restrict hv.1 hG
      _ ≤ ENNReal.ofReal N * (ENNReal.ofReal G * ENNReal.ofReal W) := by gcongr
      _ = ENNReal.ofReal (N * W * G) := by
        rw [← ENNReal.ofReal_mul hG0, ← ENNReal.ofReal_mul hN]
        ring_nf
  have h3 : ‖∫ x in ball (0 : ℂ) R, f x * fderiv ℝ ψ x (v x)‖ₑ ≤ ENNReal.ofReal (N * W * G) :=
    (enorm_integral_le_lintegral_enorm _).trans (by rw [← eLpNorm_one_eq_lintegral_enorm]; exact hbound)
  rw [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h3
  simpa [Real.norm_eq_abs] using h3

/-- Integrability of the flux integrand `u w·∇ψ` on `(0,T) × ℝ²` (`03_compactness.tex:155-158`):
`u ∈ L^∞(0,T; L²)`, `w ∈ L^∞(0,T; L²(B_R))` for every `R > 0`, `ψ ∈ C_c¹`. -/
theorem integrableOn_slab_mul_fderiv {T : ℝ} {u : ℝ → ℂ → ℝ} {w : ℝ → ℂ → ℂ}
    (hw : ∀ R : ℝ, 0 < R → Prelim.MemLinfLp (Ioo 0 T) (ball (0 : ℂ) R) 2 w)
    (hu : Prelim.MemLinfLp (Ioo 0 T) univ 2 u) {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) :
    IntegrableOn (fun p : ℝ × ℂ => u p.1 p.2 * fderiv ℝ ψ p.2 (w p.1 p.2)) (slab T) := by
  -- a ball containing the support, and a bound on `∇ψ`
  obtain ⟨r, hr⟩ := (isBounded_iff_subset_ball (0 : ℂ)).1 hψc.isCompact.isBounded
  set R : ℝ := max r 1 with hRdef
  have hR0 : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hψR : tsupport ψ ⊆ ball (0 : ℂ) R := hr.trans (ball_subset_ball (le_max_left _ _))
  have hcont : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv one_ne_zero
  obtain ⟨G, hG⟩ := hcont.bounded_above_of_compact_support (hψc.fderiv (𝕜 := ℝ))
  set B : Set ℂ := ball (0 : ℂ) R with hBdef
  set F : ℝ × ℂ → ℝ := fun p => u p.1 p.2 * fderiv ℝ ψ p.2 (w p.1 p.2) with hFdef
  have hwR := hw R hR0
  -- integrability on `(0,T) × B_R`
  have hS : IntegrableOn F (Ioo 0 T ×ˢ B) := by
    have hμ : (volume : Measure (ℝ × ℂ)).restrict (Ioo 0 T ×ˢ B) =
        ((volume : Measure ℝ).restrict (Ioo 0 T)).prod ((volume : Measure ℂ).restrict B) := by
      rw [Measure.volume_eq_prod, Measure.prod_restrict]
    have hum : AEStronglyMeasurable (Function.uncurry u)
        ((volume : Measure (ℝ × ℂ)).restrict (Ioo 0 T ×ˢ B)) :=
      hu.aestronglyMeasurable.mono_measure
        (Measure.restrict_mono (prod_mono subset_rfl (subset_univ _)) le_rfl)
    have hwm : AEStronglyMeasurable (Function.uncurry w)
        ((volume : Measure (ℝ × ℂ)).restrict (Ioo 0 T ×ˢ B)) := hwR.aestronglyMeasurable
    have hdm : AEStronglyMeasurable (fun p : ℝ × ℂ => fderiv ℝ ψ p.2)
        ((volume : Measure (ℝ × ℂ)).restrict (Ioo 0 T ×ˢ B)) :=
      (hcont.comp continuous_snd).aestronglyMeasurable
    have hFm : AEStronglyMeasurable F ((volume : Measure (ℝ × ℂ)).restrict (Ioo 0 T ×ˢ B)) :=
      hum.mul (Continuous.comp_aestronglyMeasurable₂
        (g := fun (L : ℂ →L[ℝ] ℝ) (y : ℂ) => L y)
        (continuous_fst.clm_apply continuous_snd) hdm hwm)
    refine ⟨hFm, ?_⟩
    obtain ⟨Mu, hMu⟩ := hu.essBounded
    obtain ⟨Mw, hMw⟩ := hwR.essBounded
    have hae : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Ioo 0 T)),
        ∫⁻ x, ‖F (t, x)‖ₑ ∂((volume : Measure ℂ).restrict B) ≤
          ENNReal.ofReal Mu * (ENNReal.ofReal G * ENNReal.ofReal Mw) := by
      filter_upwards [hMu, hMw] with t htu htw
      have hBle : (volume : Measure ℂ).restrict B ≤ (volume : Measure ℂ).restrict univ :=
        Measure.restrict_mono (subset_univ _) le_rfl
      have hu2 : eLpNorm (u t) 2 ((volume : Measure ℂ).restrict B) ≤ ENNReal.ofReal Mu :=
        (eLpNorm_mono_measure _ hBle).trans (eLpNorm_le_ofReal_of_toReal_le htu.1 htu.2)
      have hw2 : eLpNorm (w t) 2 ((volume : Measure ℂ).restrict B) ≤ ENNReal.ofReal Mw :=
        eLpNorm_le_ofReal_of_toReal_le htw.1 htw.2
      calc ∫⁻ x, ‖F (t, x)‖ₑ ∂((volume : Measure ℂ).restrict B)
          = eLpNorm (fun x => u t x * fderiv ℝ ψ x (w t x)) 1
              ((volume : Measure ℂ).restrict B) := by
            rw [eLpNorm_one_eq_lintegral_enorm]
        _ ≤ eLpNorm (u t) 2 ((volume : Measure ℂ).restrict B) *
              (ENNReal.ofReal G * eLpNorm (w t) 2 ((volume : Measure ℂ).restrict B)) :=
            eLpNorm_one_mul_fderiv_le hψ (htu.1.1.mono_measure hBle) htw.1.1 hG
        _ ≤ ENNReal.ofReal Mu * (ENNReal.ofReal G * ENNReal.ofReal Mw) := by gcongr
    show ∫⁻ p, ‖F p‖ₑ ∂((volume : Measure (ℝ × ℂ)).restrict (Ioo 0 T ×ˢ B)) < ⊤
    rw [hμ]
    calc ∫⁻ p, ‖F p‖ₑ ∂(((volume : Measure ℝ).restrict (Ioo 0 T)).prod
          ((volume : Measure ℂ).restrict B))
        ≤ ∫⁻ t, ∫⁻ x, ‖F (t, x)‖ₑ ∂((volume : Measure ℂ).restrict B)
            ∂((volume : Measure ℝ).restrict (Ioo 0 T)) := lintegral_prod_le _
      _ ≤ ∫⁻ _t, ENNReal.ofReal Mu * (ENNReal.ofReal G * ENNReal.ofReal Mw)
            ∂((volume : Measure ℝ).restrict (Ioo 0 T)) := lintegral_mono_ae hae
      _ = ENNReal.ofReal Mu * (ENNReal.ofReal G * ENNReal.ofReal Mw) * volume (Ioo (0 : ℝ) T) := by
        rw [lintegral_const, Measure.restrict_apply_univ]
      _ < ⊤ := by
        rw [Real.volume_Ioo]
        exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)) ENNReal.ofReal_lt_top
  -- the integrand vanishes on `slab T \ ((0,T) × B_R)`
  refine hS.of_forall_sdiff_eq_zero (measurableSet_Ioo.prod MeasurableSet.univ) ?_
  rintro ⟨t, x⟩ ⟨⟨ht, -⟩, hnot⟩
  have hx : x ∉ B := fun hx => hnot ⟨ht, hx⟩
  exact mul_fderiv_eq_zero_of_notMem fun h => hx (hψR h)

end NonUniqueEuler.Weak.WeakCont
