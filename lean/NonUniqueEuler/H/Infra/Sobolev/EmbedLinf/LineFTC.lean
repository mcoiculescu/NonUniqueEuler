import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Group.Integral

/-!
# Helper for `lem:embed` (E2): the fundamental theorem of calculus on lines, and Fubini

Helper of `P/Infra/Sobolev/EmbedLinf.lean` (manuscript `02_prelim.tex:604-606, 624-630`).

* `integral_Iic_fderiv_line`: for `H : ℂ → E` of class `C¹` with compact support and `v ≠ 0`,
  `H x = ∫_{t ≤ 0} DH(x + t v) v dt`;
* `abs_integral_Iic_Iic_le`: `|∫_{t ≤ 0} ∫_{s ≤ 0} F(x + t i + s) ds dt| ≤ ∫_ℂ |F|` for integrable
  `F : ℂ → ℝ` (Fubini on `ℂ ≃ ℝ × ℝ`).
-/

noncomputable section

open MeasureTheory Set Filter Complex
open scoped Topology

namespace NonUniqueEuler.Sob.EmbedLinfAux

variable {E : Type*} [NormedAddCommGroup E]

/-- A compactly supported function restricted to a line `t ↦ x + t • v`, `v ≠ 0`, has compact
support. -/
theorem hasCompactSupport_comp_line {H : ℂ → E} (hc : HasCompactSupport H) (x v : ℂ)
    (hv : v ≠ 0) : HasCompactSupport (fun t : ℝ => H (x + t • v)) := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) ((R + ‖x‖) / ‖v‖)) ?_
  intro t ht
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  apply ht
  have h1 := hR hmem
  rw [mem_closedBall_zero_iff] at h1 ⊢
  rw [le_div_iff₀ (norm_pos_iff.2 hv)]
  calc ‖t‖ * ‖v‖ = ‖t • v‖ := (norm_smul t v).symm
    _ = ‖(x + t • v) - x‖ := by rw [add_sub_cancel_left]
    _ ≤ ‖x + t • v‖ + ‖x‖ := norm_sub_le _ _
    _ ≤ R + ‖x‖ := by linarith

variable [NormedSpace ℝ E] [CompleteSpace E]

/-- The fundamental theorem of calculus along the half-line `{x + t v : t ≤ 0}`. -/
theorem integral_Iic_fderiv_line {H : ℂ → E} (hH : ContDiff ℝ 1 H) (hc : HasCompactSupport H)
    (x v : ℂ) (hv : v ≠ 0) :
    ∫ t in Iic (0 : ℝ), fderiv ℝ H (x + t • v) v = H x := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => H (x + t • v)) (fderiv ℝ H (x + t • v) v) t := by
    intro t
    have hl : HasDerivAt (fun t : ℝ => x + t • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    exact ((hH.differentiable one_ne_zero (x + t • v)).hasFDerivAt).comp_hasDerivAt t hl
  have hf : ContDiff ℝ 1 (fun t : ℝ => H (x + t • v)) :=
    hH.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have key := HasCompactSupport.integral_Iic_deriv_eq hf (hasCompactSupport_comp_line hc x v hv) 0
  simp only [zero_smul, add_zero] at key
  rw [← key]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  exact (hderiv t).deriv.symm

/-- The measurable equivalence `ℝ × ℝ ≃ ℂ`, `(t, s) ↦ s + t i`. -/
def swapEquiv : ℝ × ℝ ≃ᵐ ℂ :=
  MeasurableEquiv.prodComm.trans measurableEquivRealProd.symm

theorem swapEquiv_apply (p : ℝ × ℝ) : swapEquiv p = p.1 • I + p.2 • (1 : ℂ) := by
  apply Complex.ext <;> simp [swapEquiv, measurableEquivRealProd_symm_apply] <;> rfl

theorem measurePreserving_swapEquiv : MeasurePreserving swapEquiv volume volume := by
  have h1 : MeasurePreserving (MeasurableEquiv.prodComm : ℝ × ℝ ≃ᵐ ℝ × ℝ) volume volume := by
    rw [Measure.volume_eq_prod]
    exact Measure.measurePreserving_swap
  exact (MeasurePreserving.symm _ Complex.volume_preserving_equiv_real_prod).comp h1

/-- Fubini bound: `|∫_{t ≤ 0} ∫_{s ≤ 0} F(x + t i + s) ds dt| ≤ ∫_ℂ |F|`. -/
theorem abs_integral_Iic_Iic_le {F : ℂ → ℝ} (hF : Integrable F) (x : ℂ) :
    |∫ t in Iic (0 : ℝ), ∫ s in Iic (0 : ℝ), F (x + t • I + s • (1 : ℂ))| ≤ ∫ z, |F z| := by
  set G : ℂ → ℝ := fun z => F (x + z) with hG
  have hGint : Integrable G := hF.comp_add_left x
  set f : ℝ × ℝ → ℝ := fun p => F (x + p.1 • I + p.2 • (1 : ℂ)) with hf
  have hfG : f = G ∘ swapEquiv := by
    funext p
    simp only [hf, hG, Function.comp, swapEquiv_apply, add_assoc]
  have hfint : Integrable f (volume.prod volume) := by
    rw [← Measure.volume_eq_prod, hfG]
    exact measurePreserving_swapEquiv.integrable_comp_of_integrable hGint
  have hiter : ∫ t in Iic (0 : ℝ), ∫ s in Iic (0 : ℝ), F (x + t • I + s • (1 : ℂ)) =
      ∫ p in Iic (0 : ℝ) ×ˢ Iic (0 : ℝ), f p ∂(volume.prod volume) :=
    (setIntegral_prod f hfint.integrableOn).symm
  rw [hiter]
  calc |∫ p in Iic (0 : ℝ) ×ˢ Iic (0 : ℝ), f p ∂(volume.prod volume)|
      ≤ ∫ p in Iic (0 : ℝ) ×ˢ Iic (0 : ℝ), |f p| ∂(volume.prod volume) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ p, |f p| ∂(volume.prod volume) :=
        setIntegral_le_integral hfint.abs (ae_of_all _ fun p => abs_nonneg _)
    _ = ∫ p, |G (swapEquiv p)| := by
        rw [← Measure.volume_eq_prod, hfG]
        rfl
    _ = ∫ z, |G z| := measurePreserving_swapEquiv.integral_comp' (fun z => |G z|)
    _ = ∫ z, |F z| := integral_add_left_eq_self (fun z => |F z|) x

end NonUniqueEuler.Sob.EmbedLinfAux
