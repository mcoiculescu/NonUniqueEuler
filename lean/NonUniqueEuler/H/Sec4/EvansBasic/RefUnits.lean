import NonUniqueEuler.Defs.Sec4.RingSetting
import NonUniqueEuler.I.Infra.Polar.Newton
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Helpers for `lem:evans-basic`, last assertion: the ring in reference units

Helper file of `P/Sec4/EvansBasic.lean` (`04_ring.tex:345-352`). For the ring in reference units
`ω̄_c(x) = ϖ(log|x|)`:

* `differentiable_prof`: `ϖ = χ H((·-a₀)/d) H(-·/d)` is differentiable;
* `ringRefSetting_omR`, `ringRefSetting_dom`: `ω̄_c(r) = ϖ(log r)` and
  `ω̄_c'(r) = ϖ'(log r)/r` for `r > 0`;
* `circ_ringRef_exp`: `Circ_{ω̄_c}(e^ξ) = 2π ∫_{-∞}^ξ ϖ(ξ') e^{2ξ'} dξ'` (polar coordinates,
  `Polar.circ_comp_norm`, then the substitution `ρ = e^{ξ'}`).

All lemmas are fully proved.
-/

noncomputable section

open Set Filter Topology MeasureTheory Real
open scoped ContDiff

namespace NonUniqueEuler

namespace EvansBasicH

open RingData

/-- `H(x) = (1 + e^{-2x})⁻¹` is differentiable. -/
theorem differentiable_H : Differentiable ℝ H := by
  intro x
  unfold H
  apply DifferentiableAt.inv
  · fun_prop
  · positivity

/-- The ring profile `ϖ = χ H((·-a₀)/d) H(-·/d)` is differentiable. -/
theorem differentiable_prof {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) :
    Differentiable ℝ (prof χ) := by
  have hc : Differentiable ℝ χ := hχ.contDiff.differentiable (by simp)
  have h1 : Differentiable ℝ fun ξ : ℝ => H ((ξ - a₀) / d) :=
    differentiable_H.comp (by fun_prop)
  have h2 : Differentiable ℝ fun ξ : ℝ => H (-ξ / d) :=
    differentiable_H.comp (by fun_prop)
  exact (hc.mul h1).mul h2

/-- `ω̄_c(r) = ϖ(log r)` for `r > 0`. -/
theorem ringRefSetting_omR (χ : ℝ → ℝ) {r : ℝ} (hr : 0 < r) :
    (ringRefSetting χ).omR r = prof χ (Real.log r) := by
  have h0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  simp only [SectorSetting.omR, ringRefSetting_om, ringRef, h0, ite_false, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hr]

/-- `ω̄_c'(r) = ϖ'(log r) / r` for `r > 0` (chain rule). -/
theorem ringRefSetting_dom {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {r : ℝ} (hr : 0 < r) :
    (ringRefSetting χ).dom r = deriv (prof χ) (Real.log r) * r⁻¹ := by
  have hev : (ringRefSetting χ).omR =ᶠ[𝓝 r] fun t => prof χ (Real.log t) := by
    filter_upwards [Ioi_mem_nhds hr] with t ht
    exact ringRefSetting_omR χ ht
  have hd : HasDerivAt (fun t => prof χ (Real.log t)) (deriv (prof χ) (Real.log r) * r⁻¹) r :=
    ((differentiable_prof hχ (Real.log r)).hasDerivAt).comp r (Real.hasDerivAt_log hr.ne')
  rw [SectorSetting.dom, hev.deriv_eq]
  exact hd.deriv

/-- `Circ_{ω̄_c}(e^ξ) = 2π ∫_{-∞}^ξ ϖ(ξ') e^{2ξ'} dξ'` (`04_ring.tex:348-350`). -/
theorem circ_ringRef_exp (χ : ℝ → ℝ) (ξ : ℝ) :
    Polar.circ (ringRef χ) (Real.exp ξ) =
      2 * π * ∫ ξ' in Iic ξ, prof χ ξ' * Real.exp (2 * ξ') := by
  set h₀ : ℝ → ℝ := fun t => if t = 0 then 0 else prof χ (Real.log t) with hh₀
  have hring : ringRef χ = fun y => h₀ ‖y‖ := by
    funext y
    simp only [ringRef, hh₀, norm_eq_zero]
  rw [hring, Polar.circ_comp_norm h₀ (Real.exp_pos ξ).le,
    intervalIntegral.integral_of_le (Real.exp_pos ξ).le, ← Real.image_exp_Iic,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Iic
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn]
  congr 1
  refine setIntegral_congr_fun measurableSet_Iic (fun x _ => ?_)
  simp only [hh₀, Real.exp_ne_zero, ite_false, Real.log_exp, smul_eq_mul,
    abs_of_pos (Real.exp_pos x)]
  rw [two_mul, Real.exp_add]
  ring

end EvansBasicH

end NonUniqueEuler
