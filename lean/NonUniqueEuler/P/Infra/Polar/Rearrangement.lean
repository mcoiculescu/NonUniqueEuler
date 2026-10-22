import NonUniqueEuler.Defs.Infra.Polar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Group.Measure

/-!
# Proof: disk rearrangement for radially decreasing kernels (P-POLAR)

Proof of `NonUniqueEuler/I/Infra/Polar/Rearrangement.lean` (same declarations, same statements).

The argument is the manuscript's bathtub argument (`02_prelim.tex:258-266`, `lem:BS-basic`(e)):
with `B = ball 0 R`, `|D \ B| ≤ |B \ D|`, `φ ‖x‖ ≤ φ R` on `D \ B` and `φ ‖x‖ ≥ φ R` a.e. on
`B \ D`; hence `∫_D φ ≤ ∫_{D∩B} φ + φ R |B \ D| ≤ ∫_B φ`. The other two statements follow by
translation invariance of `volume` on `ℂ`.
-/

noncomputable section

open MeasureTheory Set Metric Real
open scoped ENNReal

namespace NonUniqueEuler.Polar

/-- Bathtub inequality for a radially nonincreasing weight. -/
theorem setLIntegral_le_setLIntegral_ball {φ : ℝ → ℝ≥0∞} (hφm : Measurable φ)
    (hφ : AntitoneOn φ (Ioi 0)) {D : Set ℂ} (hD : MeasurableSet D) {R : ℝ}
    (hvol : volume D ≤ volume (ball (0 : ℂ) R)) :
    ∫⁻ x in D, φ ‖x‖ ≤ ∫⁻ x in ball (0 : ℂ) R, φ ‖x‖ := by
  set B := ball (0 : ℂ) R with hBdef
  have hBm : MeasurableSet B := measurableSet_ball
  have hf : Measurable (fun x : ℂ => φ ‖x‖) := hφm.comp measurable_norm
  rcases le_or_gt R 0 with hR | hR
  · have hB0 : B = ∅ := ball_eq_empty.2 hR
    have hD0 : volume D = 0 := by
      rw [hB0, measure_empty] at hvol
      exact le_antisymm hvol bot_le
    rw [Measure.restrict_eq_zero.2 hD0, lintegral_zero_measure]
    exact bot_le
  -- `|D \ B| ≤ |B \ D|`
  have hfin : volume (D ∩ B) ≠ ∞ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono inter_subset_right)
  have hdiff : volume (D \ B) ≤ volume (B \ D) := by
    have h1 : volume (D ∩ B) + volume (D \ B) = volume D := measure_inter_add_sdiff D hBm
    have h2 : volume (D ∩ B) + volume (B \ D) = volume B := by
      rw [inter_comm]; exact measure_inter_add_sdiff B hD
    apply ENNReal.le_of_add_le_add_left hfin
    rw [h1, h2]; exact hvol
  -- splitting both integrals
  have hsplitD : ∫⁻ x in D, φ ‖x‖ = (∫⁻ x in D ∩ B, φ ‖x‖) + ∫⁻ x in D \ B, φ ‖x‖ :=
    (lintegral_inter_add_sdiff (μ := volume) (fun x : ℂ => φ ‖x‖) D hBm).symm
  have hsplitB : ∫⁻ x in B, φ ‖x‖ = (∫⁻ x in D ∩ B, φ ‖x‖) + ∫⁻ x in B \ D, φ ‖x‖ := by
    rw [inter_comm]
    exact (lintegral_inter_add_sdiff (μ := volume) (fun x : ℂ => φ ‖x‖) B hD).symm
  have hle1 : ∫⁻ x in D \ B, φ ‖x‖ ≤ φ R * volume (D \ B) := by
    rw [← setLIntegral_const]
    apply setLIntegral_mono measurable_const
    intro x hx
    have hxR : R ≤ ‖x‖ := by
      have := hx.2
      simpa [hBdef, mem_ball, dist_zero_right, not_lt] using this
    exact hφ (mem_Ioi.2 hR) (mem_Ioi.2 (hR.trans_le hxR)) hxR
  have hle2 : φ R * volume (B \ D) ≤ ∫⁻ x in B \ D, φ ‖x‖ := by
    rw [← setLIntegral_const]
    apply setLIntegral_mono_ae hf.aemeasurable
    filter_upwards [Measure.ae_ne volume (0 : ℂ)] with x hx0 hx
    have hxR : ‖x‖ < R := by
      have := hx.1
      simpa [hBdef, mem_ball, dist_zero_right] using this
    have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
    exact hφ (mem_Ioi.2 hxpos) (mem_Ioi.2 hR) hxR.le
  rw [hsplitD, hsplitB]
  refine add_le_add le_rfl ?_
  calc ∫⁻ x in D \ B, φ ‖x‖ ≤ φ R * volume (D \ B) := hle1
    _ ≤ φ R * volume (B \ D) := by gcongr
    _ ≤ ∫⁻ x in B \ D, φ ‖x‖ := hle2

/-- Among disks of radius `R`, the centred one maximizes `∫ φ(‖x‖)`. -/
theorem setLIntegral_ball_le_setLIntegral_ball_zero {φ : ℝ → ℝ≥0∞} (hφm : Measurable φ)
    (hφ : AntitoneOn φ (Ioi 0)) (c : ℂ) (R : ℝ) :
    ∫⁻ x in ball c R, φ ‖x‖ ≤ ∫⁻ x in ball (0 : ℂ) R, φ ‖x‖ :=
  setLIntegral_le_setLIntegral_ball hφm hφ measurableSet_ball
    (Measure.addHaar_ball_center volume c R).le

/-- Translated form: `∫_{B_R} φ(‖x - y‖) dx ≤ ∫_{B_R} φ(‖x‖) dx` for every `y`. -/
theorem setLIntegral_ball_sub_le {φ : ℝ → ℝ≥0∞} (hφm : Measurable φ)
    (hφ : AntitoneOn φ (Ioi 0)) (y : ℂ) (R : ℝ) :
    ∫⁻ x in ball (0 : ℂ) R, φ ‖x - y‖ ≤ ∫⁻ x in ball (0 : ℂ) R, φ ‖x‖ := by
  have hf : Measurable (fun x : ℂ => φ ‖x‖) := hφm.comp measurable_norm
  have hpre : (fun x : ℂ => x - y) ⁻¹' ball (-y) R = ball (0 : ℂ) R := by
    ext x
    simp [mem_ball, dist_eq_norm]
  have hcv : ∫⁻ x in ball (0 : ℂ) R, φ ‖x - y‖ = ∫⁻ z in ball (-y) R, φ ‖z‖ := by
    rw [← hpre]
    exact (measurePreserving_sub_right volume y).setLIntegral_comp_preimage
      measurableSet_ball hf
  rw [hcv]
  exact setLIntegral_ball_le_setLIntegral_ball_zero hφm hφ (-y) R

end NonUniqueEuler.Polar
