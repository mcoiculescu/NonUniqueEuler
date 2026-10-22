import NonUniqueEuler.Defs.Infra.Equimeasurable
import NonUniqueEuler.I.Infra.Equimeasurable.Distribution
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Proof: equimeasurable functions have equal `L^p` norms, integrals and signs (I-EQM)

Proof of `NonUniqueEuler/I/Infra/Equimeasurable/Norms.lean` (same declarations, statements
copied verbatim).

Everything reduces to `I/Infra/Equimeasurable/Distribution.lean`:
* `0 < p < ∞`: `lintegral_comp_eq` with `Φ s = ‖s‖ₑ ^ p.toReal` (`Φ 0 = 0` as `p.toReal > 0`);
* `p = ∞`: `essSup_eq_sInf`, and `{x | a < ‖g x‖ₑ} = g ⁻¹' {s | a < ‖s‖ₑ}` with a Borel set
  `{s | a < ‖s‖ₑ}` not containing `0`, so `volume_preimage_eq` applies for every `a`;
* `MemLp`: both functions are in `L¹`, hence a.e. strongly measurable;
* integral: `integral_comp_eq` with `Φ = id`;
* signs: `{h < 0} = h ⁻¹' Iio 0` and `volume_preimage_eq` with `A = Iio 0`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace NonUniqueEuler.Equimeasurable

variable {g h : ℂ → ℝ}

theorem eLpNorm_eq (H : Equimeasurable g h) (p : ℝ≥0∞) :
    eLpNorm g p volume = eLpNorm h p volume := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp only [eLpNorm_exponent_zero]
  rcases eq_or_ne p ∞ with rfl | hptop
  · rw [eLpNorm_exponent_top, eLpNorm_exponent_top, eLpNormEssSup, eLpNormEssSup,
      essSup_eq_sInf, essSup_eq_sInf]
    congr 1
    ext a
    simp only [mem_ofPred_eq]
    have hA : MeasurableSet {s : ℝ | a < ‖s‖ₑ} :=
      measurableSet_lt measurable_const measurable_enorm
    have h0 : (0 : ℝ) ∉ {s : ℝ | a < ‖s‖ₑ} := by simp
    have := volume_preimage_eq H hA h0
    simp only [preimage_ofPred_eq] at this
    rw [this]
  · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop]
    have hpos : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
    have hΦ : Measurable fun s : ℝ => ‖s‖ₑ ^ p.toReal :=
      measurable_enorm.pow_const _
    have hΦ0 : (fun s : ℝ => ‖s‖ₑ ^ p.toReal) 0 = 0 := by
      simp [ENNReal.zero_rpow_of_pos hpos]
    rw [lintegral_comp_eq H hΦ hΦ0]

theorem memLp_iff (H : Equimeasurable g h) (p : ℝ≥0∞) :
    MemLp g p volume ↔ MemLp h p volume := by
  constructor
  · intro hg
    exact ⟨H.memLp_one_right.1, (eLpNorm_eq H p) ▸ hg.2⟩
  · intro hh
    exact ⟨H.memLp_one_left.1, (eLpNorm_eq H p).symm ▸ hh.2⟩

theorem integral_eq (H : Equimeasurable g h) : ∫ x, g x = ∫ x, h x :=
  integral_comp_eq H (Φ := id) measurable_id rfl

theorem nonneg (H : Equimeasurable g h) (hg : 0 ≤ᵐ[volume] g) : 0 ≤ᵐ[volume] h := by
  have hA : MeasurableSet (Iio (0 : ℝ)) := measurableSet_Iio
  have h0 : (0 : ℝ) ∉ Iio (0 : ℝ) := by simp
  have hg' : volume (g ⁻¹' Iio 0) = 0 := by
    rw [Filter.EventuallyLE, ae_iff] at hg
    simpa [preimage, not_le] using hg
  rw [Filter.EventuallyLE, ae_iff]
  have := (volume_preimage_eq H hA h0).symm.trans hg'
  simpa [preimage, not_le] using this

end NonUniqueEuler.Equimeasurable
