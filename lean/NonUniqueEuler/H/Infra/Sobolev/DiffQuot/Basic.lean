import NonUniqueEuler.Defs.Infra.Sobolev
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Helper for `P/Infra/Sobolev/DiffQuot`: elementary facts about translated test functions

* `DiffQuotAux.clm_apply_eq`: `L h = h.re L 1 + h.im L I` for a real-linear `L : ℂ →L[ℝ] ℝ`;
* `DiffQuotAux.sub_eq_integral_fderiv`: `ψ(y + h) - ψ(y) = ∫_0^1 Dψ(y + s h) h ds` (FTC along
  the segment);
* `DiffQuotAux.isTestFn_translate`: for a real test function `ψ` supported in `B_R` and
  `R + |c| ≤ r`, the complex function `y ↦ ψ(y + c)` is a test function supported in `B_r`;
* `DiffQuotAux.fderiv_translate_apply`: its directional derivatives.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal ContDiff

namespace NonUniqueEuler.Sob.DiffQuotAux

/-- `h = h.re · 1 + h.im · I`, so `L h = h.re L 1 + h.im L I` for real-linear `L`. -/
theorem clm_apply_eq (L : ℂ →L[ℝ] ℝ) (h : ℂ) :
    L h = h.re * L 1 + h.im * L Complex.I := by
  have hh : h = h.re • (1 : ℂ) + h.im • Complex.I := by
    apply Complex.ext <;> simp
  calc L h = L (h.re • (1 : ℂ) + h.im • Complex.I) := by rw [← hh]
    _ = h.re * L 1 + h.im * L Complex.I := by
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- The fundamental theorem of calculus along the segment `[y, y + h]`. -/
theorem sub_eq_integral_fderiv {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 1 ψ) (y h : ℂ) :
    ψ (y + h) - ψ y = ∫ s in Ioc (0 : ℝ) 1, fderiv ℝ ψ (y + s • h) h := by
  rw [← intervalIntegral.integral_of_le zero_le_one]
  have hd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => ψ (y + s • h)) (fderiv ℝ ψ (y + s • h) h) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => y + s • h) h s := by
      simpa using ((hasDerivAt_id s).smul_const h).const_add y
    exact ((hψ.differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt s h1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)]
  · simp
  · apply Continuous.intervalIntegrable
    exact ((hψ.continuous_fderiv one_ne_zero).comp
      (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const

/-- A translate of a real test function supported in `B_R`, viewed as a complex function, is a
test function supported in `B_r` when `R + |c| ≤ r`. -/
theorem isTestFn_translate {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    {R r : ℝ} (hψR : tsupport ψ ⊆ ball 0 R) {c : ℂ} (hc : R + ‖c‖ ≤ r) :
    IsTestFn (ball (0 : ℂ) r) (fun y => (ψ (y + c) : ℂ)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp (hψ.comp (contDiff_id.add contDiff_const))
  · have : HasCompactSupport (fun y => ψ (y + c)) := hψc.comp_homeomorph (Homeomorph.addRight c)
    exact this.comp_left (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero
  · intro y hy
    have h1 : tsupport (fun y => (ψ (y + c) : ℂ)) ⊆ tsupport (fun y => ψ (y + c)) :=
      tsupport_comp_subset (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero _
    have h2 : tsupport (fun y => ψ (y + c)) ⊆ (fun y => y + c) ⁻¹' tsupport ψ :=
      tsupport_comp_subset_preimage ψ (continuous_id.add continuous_const)
    have h3 : y + c ∈ ball (0 : ℂ) R := hψR (h2 (h1 hy))
    rw [mem_ball_zero_iff] at h3
    rw [mem_ball_zero_iff]
    calc ‖y‖ = ‖(y + c) - c‖ := by simp
      _ ≤ ‖y + c‖ + ‖c‖ := norm_sub_le _ _
      _ < R + ‖c‖ := by linarith
      _ ≤ r := hc

/-- Directional derivatives of a translate. -/
theorem fderiv_translate_apply {ψ : ℂ → ℝ} (hψ : Differentiable ℝ ψ) (c y v : ℂ) :
    fderiv ℝ (fun y => (ψ (y + c) : ℂ)) y v = (fderiv ℝ ψ (y + c) v : ℂ) := by
  have h1 : HasFDerivAt (fun y => ψ (y + c)) (fderiv ℝ ψ (y + c)) y := by
    exact (hasFDerivAt_comp_add_right c).2 (hψ (y + c)).hasFDerivAt
  have h2 := Complex.ofRealCLM.hasFDerivAt.comp y h1
  have h3 : fderiv ℝ (fun y => (ψ (y + c) : ℂ)) y =
      Complex.ofRealCLM.comp (fderiv ℝ ψ (y + c)) := h2.fderiv
  rw [h3]
  simp

end NonUniqueEuler.Sob.DiffQuotAux
