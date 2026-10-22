import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Helpers for `P/Infra/SobolevOneD/CompLog`: the substitution `r = e^x`

Adapted from `H/Infra/SobolevOneD/LogVariable/Change.lean` (the helpers of another
proof may not be imported, so the few lemmas needed here are restated in the namespace
`CompLogH`).

* `integral_image_exp`, `integrableOn_image_exp_iff`, `integral_Ioi_eq`: the one-dimensional
  change of variables `r = e^x` (`dr = e^x dx`), for arbitrary integrands
  (`integral_image_eq_integral_abs_deriv_smul`);
* `memLp_comp_log_Icc`: for `V ∈ L²(ℝ)` and `0 < α ≤ β`, `r ↦ r^{-q} V(log r)` lies in
  `L²([α, β], dr)` (the substitution gives the weight `e^{(1-2q)x}`, bounded on
  `[log α, log β]`).

All proofs are complete.
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler.Sob.CompLogH

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem image_exp_Icc (a b : ℝ) : Real.exp '' Icc a b = Icc (Real.exp a) (Real.exp b) := by
  ext r
  constructor
  · rintro ⟨x, ⟨hxa, hxb⟩, rfl⟩
    exact ⟨Real.exp_le_exp.2 hxa, Real.exp_le_exp.2 hxb⟩
  · rintro ⟨hra, hrb⟩
    have hr : 0 < r := lt_of_lt_of_le (Real.exp_pos a) hra
    refine ⟨Real.log r, ⟨?_, ?_⟩, Real.exp_log hr⟩
    · rw [← Real.log_exp a]; exact Real.log_le_log (Real.exp_pos a) hra
    · rw [← Real.log_exp b]; exact Real.log_le_log hr hrb

theorem image_exp_Icc_log {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) :
    Real.exp '' Icc (Real.log α) (Real.log β) = Icc α β := by
  rw [image_exp_Icc, Real.exp_log hα, Real.exp_log (lt_of_lt_of_le hα hαβ)]

/-- `∫_{e^s} g = ∫_s e^x g(e^x) dx`, for any `g`. -/
theorem integral_image_exp {s : Set ℝ} (hs : MeasurableSet s) (g : ℝ → E) :
    ∫ r in Real.exp '' s, g r = ∫ x in s, Real.exp x • g (Real.exp x) := by
  rw [integral_image_eq_integral_abs_deriv_smul hs
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn g]
  refine setIntegral_congr_fun hs fun x _ => ?_
  simp only [abs_of_pos (Real.exp_pos x)]

theorem integrableOn_image_exp_iff {s : Set ℝ} (hs : MeasurableSet s) (g : ℝ → E) :
    IntegrableOn g (Real.exp '' s) ↔ IntegrableOn (fun x => Real.exp x • g (Real.exp x)) s := by
  rw [integrableOn_image_iff_integrableOn_abs_deriv_smul hs
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn g]
  have : ∀ x, |Real.exp x| = Real.exp x := fun x => abs_of_pos (Real.exp_pos x)
  simp only [this]

theorem integral_Ioi_eq (g : ℝ → E) :
    ∫ r in Ioi 0, g r = ∫ x, Real.exp x • g (Real.exp x) := by
  rw [← Real.range_exp, ← image_univ, integral_image_exp MeasurableSet.univ,
    Measure.restrict_univ]

/-- For `V ∈ L²(ℝ)` and `0 < α ≤ β`: `r ↦ r^{-q} V(log r)` lies in `L²([α, β], dr)`. -/
theorem memLp_comp_log_Icc {V : ℝ → ℂ} (hV : MemLp V 2 volume) {α β : ℝ} (hα : 0 < α)
    (hαβ : α ≤ β) (q : ℕ) :
    MemLp (fun r => (((r⁻¹ : ℝ) : ℂ)) ^ q * V (Real.log r)) 2 (volume.restrict (Icc α β)) := by
  set J := Icc (Real.log α) (Real.log β) with hJ
  have hVJ : MemLp V 2 (volume.restrict J) := hV.restrict J
  have hV1 : IntegrableOn V J := hVJ.integrable one_le_two
  have hV2 : IntegrableOn (fun x => ‖V x‖ ^ 2) J := hVJ.norm.integrable_sq
  have hinv : Continuous (fun x : ℝ => (Real.exp x)⁻¹) :=
    Real.continuous_exp.inv₀ fun x => (Real.exp_pos x).ne'
  -- integrability of the function itself (gives measurability)
  have h1 : IntegrableOn (fun r => (((r⁻¹ : ℝ) : ℂ)) ^ q * V (Real.log r)) (Icc α β) := by
    rw [← image_exp_Icc_log hα hαβ, integrableOn_image_exp_iff measurableSet_Icc]
    have hc : ContinuousOn (fun x : ℝ => ((Real.exp x * ((Real.exp x)⁻¹) ^ q : ℝ) : ℂ)) J :=
      (Complex.continuous_ofReal.comp (Real.continuous_exp.mul (hinv.pow q))).continuousOn
    refine (IntegrableOn.continuousOn_mul hc hV1 isCompact_Icc).congr_fun (fun x _ => ?_)
      measurableSet_Icc
    simp only [Real.log_exp, Complex.real_smul]
    push_cast
    ring
  -- integrability of the square of the norm
  have h2 : IntegrableOn (fun r => ‖(((r⁻¹ : ℝ) : ℂ)) ^ q * V (Real.log r)‖ ^ 2) (Icc α β) := by
    rw [← image_exp_Icc_log hα hαβ, integrableOn_image_exp_iff measurableSet_Icc]
    have hc : ContinuousOn (fun x : ℝ => Real.exp x * ((Real.exp x)⁻¹ ^ q) ^ 2) J :=
      (Real.continuous_exp.mul ((hinv.pow q).pow 2)).continuousOn
    refine (IntegrableOn.continuousOn_mul hc hV2 isCompact_Icc).congr_fun (fun x _ => ?_)
      measurableSet_Icc
    have he0 : 0 < Real.exp x := Real.exp_pos x
    simp only [Real.log_exp, smul_eq_mul, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_inv, abs_of_pos he0]
    ring
  exact (memLp_two_iff_integrable_sq_norm h1.aestronglyMeasurable).2 h2

end NonUniqueEuler.Sob.CompLogH
