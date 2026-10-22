import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Proof: exponentials of bounded operators, Duhamel formulas (library I-SECT)

Proof of `NonUniqueEuler/I/Infra/SectorSpace/BanachExp.lean`: same declarations, same
statements, now proved.

* `exp_smul_add`: `NormedSpace.exp_add_of_commute`.
* `norm_exp_smul_le`: `‖exp x‖ ≤ e^{‖x‖}` from the series (`norm_tsum_le_tsum_norm`,
  `norm_pow_le'`; the `n = 0` term is `‖1‖ ≤ 1`, valid also for the trivial space).
* `hasDerivAt_exp_smul`: `hasDerivAt_exp_smul_const(')` over `ℂ` composed with `ofReal`.
* Duhamel formulas: differentiate `τ ↦ exp((t-τ)A) exp(τ(A+B))` (resp.
  `τ ↦ exp((t-τ)(A+B)) exp(τA)`) and integrate (FTC).
* Variation of constants: differentiate `τ ↦ exp((t-τ)A) u(τ)` and integrate; converse via
  `∫₀ᵗ exp((t-τ)A) g = exp(tA) ∫₀ᵗ exp(-τA) g` and the FTC for the integral.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace NonUniqueEuler.BanachExp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Every operator lies in the (infinite) disc of convergence of the exponential series. -/
private theorem mem_eball_radius (x : E →L[ℂ] E) :
    x ∈ Metric.eball (0 : E →L[ℂ] E) (NormedSpace.expSeries ℂ (E →L[ℂ] E)).radius := by
  rw [NormedSpace.expSeries_radius_eq_top]
  exact edist_lt_top _ _

theorem exp_smul_add (A : E →L[ℂ] E) (s t : ℝ) :
    NormedSpace.exp (((s + t : ℝ) : ℂ) • A) =
      NormedSpace.exp ((s : ℂ) • A) * NormedSpace.exp ((t : ℂ) • A) := by
  rw [Complex.ofReal_add, add_smul]
  exact NormedSpace.exp_add_of_commute_of_mem_ball (((Commute.refl A).smul_left _).smul_right _)
    (mem_eball_radius _) (mem_eball_radius _)

omit [CompleteSpace E] in
/-- `‖exp x‖ ≤ e^{‖x‖}` in the Banach algebra of bounded operators. -/
private theorem norm_exp_le_exp_norm' (x : E →L[ℂ] E) :
    ‖NormedSpace.exp x‖ ≤ Real.exp ‖x‖ := by
  rw [NormedSpace.exp_eq_tsum ℂ]
  refine (norm_tsum_le_tsum_norm (NormedSpace.norm_expSeries_summable' (𝕂 := ℂ) x)).trans ?_
  rw [Real.exp_eq_exp_ℝ]
  refine hasSum_le (fun n => ?_) (NormedSpace.norm_expSeries_summable' (𝕂 := ℂ) x).hasSum
    (NormedSpace.expSeries_div_hasSum_exp ‖x‖)
  rw [norm_smul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
  gcongr
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [pow_zero]
    exact ContinuousLinearMap.norm_id_le
  · exact norm_pow_le' x hn

set_option linter.unusedSectionVars false in
theorem norm_exp_smul_le (A : E →L[ℂ] E) (t : ℝ) :
    ‖NormedSpace.exp ((t : ℂ) • A)‖ ≤ Real.exp (|t| * ‖A‖) := by
  refine (norm_exp_le_exp_norm' _).trans ?_
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]

/-- The real derivative of `s ↦ (s : ℂ)`. -/
private theorem hasDerivAt_ofReal_self (t : ℝ) : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
  simpa using (hasDerivAt_id t).ofReal_comp

theorem hasDerivAt_exp_smul (A : E →L[ℂ] E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp ((s : ℂ) • A)) (NormedSpace.exp ((t : ℂ) • A) * A) t ∧
      HasDerivAt (fun s : ℝ => NormedSpace.exp ((s : ℂ) • A))
        (A * NormedSpace.exp ((t : ℂ) • A)) t :=
  ⟨by simpa only [Function.comp_def, one_smul] using
      (hasDerivAt_exp_smul_const (𝕂 := ℂ) A (t : ℂ)).scomp t (hasDerivAt_ofReal_self t),
    by simpa only [Function.comp_def, one_smul] using
      (hasDerivAt_exp_smul_const' (𝕂 := ℂ) A (t : ℂ)).scomp t (hasDerivAt_ofReal_self t)⟩

/-- Continuity of `s ↦ exp(sA)`. -/
private theorem continuous_exp_smul (A : E →L[ℂ] E) :
    Continuous (fun s : ℝ => NormedSpace.exp ((s : ℂ) • A)) :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_exp_smul A s).1.continuousAt

/-- Derivative of `τ ↦ exp((t-τ)A)`. -/
private theorem hasDerivAt_exp_smul_sub (A : E →L[ℂ] E) (t τ : ℝ) :
    HasDerivAt (fun τ : ℝ => NormedSpace.exp (((t - τ : ℝ) : ℂ) • A))
      (-(NormedSpace.exp (((t - τ : ℝ) : ℂ) • A) * A)) τ := by
  have h := HasDerivAt.scomp τ (hasDerivAt_exp_smul A (t - τ)).1
    ((hasDerivAt_id τ).const_sub t)
  simpa only [neg_smul, one_smul, Function.comp_def, id] using h

/-- Continuity of `τ ↦ exp((t-τ)A)`. -/
private theorem continuous_exp_smul_sub (A : E →L[ℂ] E) (t : ℝ) :
    Continuous (fun τ : ℝ => NormedSpace.exp (((t - τ : ℝ) : ℂ) • A)) :=
  continuous_iff_continuousAt.2 fun τ => (hasDerivAt_exp_smul_sub A t τ).continuousAt

/-- The first Duhamel formula for bounded operators. -/
theorem exp_add_eq_duhamel (A B : E →L[ℂ] E) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • (A + B)) =
      NormedSpace.exp ((t : ℂ) • A) +
        ∫ τ in (0 : ℝ)..t,
          NormedSpace.exp (((t - τ : ℝ) : ℂ) • A) * B * NormedSpace.exp ((τ : ℂ) • (A + B)) := by
  have hderiv : ∀ τ : ℝ, HasDerivAt
      (fun τ : ℝ => NormedSpace.exp (((t - τ : ℝ) : ℂ) • A) * NormedSpace.exp ((τ : ℂ) • (A + B)))
      (NormedSpace.exp (((t - τ : ℝ) : ℂ) • A) * B * NormedSpace.exp ((τ : ℂ) • (A + B))) τ := by
    intro τ
    refine ((hasDerivAt_exp_smul_sub A t τ).fun_mul (hasDerivAt_exp_smul (A + B) τ).2).congr_deriv ?_
    noncomm_ring
  have hcont : Continuous (fun τ : ℝ =>
      NormedSpace.exp (((t - τ : ℝ) : ℂ) • A) * B * NormedSpace.exp ((τ : ℂ) • (A + B))) :=
    ((continuous_exp_smul_sub A t).mul continuous_const).mul (continuous_exp_smul (A + B))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hderiv τ)
    (hcont.intervalIntegrable 0 t)]
  simp

/-- The second Duhamel formula for bounded operators. -/
theorem exp_add_eq_duhamel' (A B : E →L[ℂ] E) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • (A + B)) =
      NormedSpace.exp ((t : ℂ) • A) +
        ∫ τ in (0 : ℝ)..t,
          NormedSpace.exp (((t - τ : ℝ) : ℂ) • (A + B)) * B * NormedSpace.exp ((τ : ℂ) • A) := by
  have hderiv : ∀ τ : ℝ, HasDerivAt
      (fun τ : ℝ => NormedSpace.exp (((t - τ : ℝ) : ℂ) • (A + B)) * NormedSpace.exp ((τ : ℂ) • A))
      (-(NormedSpace.exp (((t - τ : ℝ) : ℂ) • (A + B)) * B * NormedSpace.exp ((τ : ℂ) • A))) τ := by
    intro τ
    refine ((hasDerivAt_exp_smul_sub (A + B) t τ).fun_mul (hasDerivAt_exp_smul A τ).2).congr_deriv ?_
    noncomm_ring
  have hcont : Continuous (fun τ : ℝ =>
      NormedSpace.exp (((t - τ : ℝ) : ℂ) • (A + B)) * B * NormedSpace.exp ((τ : ℂ) • A)) :=
    ((continuous_exp_smul_sub (A + B) t).mul continuous_const).mul (continuous_exp_smul A)
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hderiv τ)
    (hcont.neg.intervalIntegrable 0 t)
  rw [intervalIntegral.integral_neg] at key
  simp only [sub_self, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, one_mul, sub_zero,
    mul_one] at key
  rw [← neg_eq_iff_eq_neg.mpr key.symm]
  abel

omit [CompleteSpace E] in
/-- Product rule for `y ↦ c(y) (u(y))` with `ℂ`-linear operators and real time (Mathlib's
`HasDerivWithinAt.clm_apply` needs operators linear over the base field `ℝ`). -/
private theorem hasDerivWithinAt_apply {c : ℝ → E →L[ℂ] E} {c' : E →L[ℂ] E}
    {u : ℝ → E} {u' : E} {s : Set ℝ} {x : ℝ}
    (hc : HasDerivWithinAt c c' s x) (hu : HasDerivWithinAt u u' s x) :
    HasDerivWithinAt (fun y => c y (u y)) (c' (u x) + c x u') s x := by
  have hc' : HasDerivWithinAt (fun y => (c y).restrictScalars ℝ) (c'.restrictScalars ℝ) s x :=
    (ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ).hasFDerivAt.comp_hasDerivWithinAt x hc
  exact hc'.clm_apply hu

omit [CompleteSpace E] in
private theorem hasDerivAt_apply {c : ℝ → E →L[ℂ] E} {c' : E →L[ℂ] E}
    {u : ℝ → E} {u' : E} {x : ℝ}
    (hc : HasDerivAt c c' x) (hu : HasDerivAt u u' x) :
    HasDerivAt (fun y => c y (u y)) (c' (u x) + c x u') x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hasDerivWithinAt_apply hc hu

/-- Variation of constants: every solution of `u' = A u + g` on `[0, T]` has the Duhamel
form. -/
theorem eq_duhamel_of_hasDerivWithinAt (A : E →L[ℂ] E) {u g : ℝ → E} {T : ℝ}
    (hg : ContinuousOn g (Icc 0 T))
    (hu : ∀ t ∈ Icc 0 T, HasDerivWithinAt u (A (u t) + g t) (Icc 0 T) t) :
    ∀ t ∈ Icc 0 T, u t = NormedSpace.exp ((t : ℂ) • A) (u 0) +
      ∫ τ in (0 : ℝ)..t, NormedSpace.exp (((t - τ : ℝ) : ℂ) • A) (g τ) := by
  intro t ht
  have hucont : ContinuousOn u (Icc 0 T) := fun s hs => (hu s hs).continuousWithinAt
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have hcont : ContinuousOn (fun τ => NormedSpace.exp (((t - τ : ℝ) : ℂ) • A) (u τ)) (Icc 0 t) :=
    (continuous_exp_smul_sub A t).continuousOn.clm_apply (hucont.mono hsub)
  have hderiv : ∀ τ ∈ Ioo 0 t, HasDerivWithinAt
      (fun τ => NormedSpace.exp (((t - τ : ℝ) : ℂ) • A) (u τ))
      (NormedSpace.exp (((t - τ : ℝ) : ℂ) • A) (g τ)) (Ioi τ) τ := by
    intro τ hτ
    have hτT : τ ∈ Ioo 0 T := ⟨hτ.1, hτ.2.trans_le ht.2⟩
    have hu' : HasDerivAt u (A (u τ) + g τ) τ :=
      (hu τ (Ioo_subset_Icc_self hτT)).hasDerivAt (Icc_mem_nhds hτT.1 hτT.2)
    refine ((hasDerivAt_apply (hasDerivAt_exp_smul_sub A t τ) hu').congr_deriv ?_).hasDerivWithinAt
    simp only [neg_apply, mul_apply_eq_comp, map_add]
    abel
  have hint : IntervalIntegrable
      (fun τ => NormedSpace.exp (((t - τ : ℝ) : ℂ) • A) (g τ)) volume 0 t :=
    ((continuous_exp_smul_sub A t).continuousOn.clm_apply (hg.mono hsub)).intervalIntegrable_of_Icc
      ht.1
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1 hcont hderiv hint]
  simp

/-- Conversely, the Duhamel formula defines a solution of `u' = A u + g` on `[0, T]`. -/
theorem hasDerivWithinAt_duhamel (A : E →L[ℂ] E) {g : ℝ → E} {T : ℝ}
    (hg : ContinuousOn g (Icc 0 T)) (u₀ : E) :
    ∀ t ∈ Icc 0 T, HasDerivWithinAt
      (fun t : ℝ => NormedSpace.exp ((t : ℂ) • A) u₀ +
        ∫ τ in (0 : ℝ)..t, NormedSpace.exp (((t - τ : ℝ) : ℂ) • A) (g τ))
      (A (NormedSpace.exp ((t : ℂ) • A) u₀ +
          ∫ τ in (0 : ℝ)..t, NormedSpace.exp (((t - τ : ℝ) : ℂ) • A) (g τ)) + g t)
      (Icc 0 T) t := by
  intro t ht
  set h : ℝ → E := fun τ => NormedSpace.exp (((-τ : ℝ) : ℂ) • A) (g τ) with hh
  have hcont_neg : Continuous (fun τ : ℝ => NormedSpace.exp (((-τ : ℝ) : ℂ) • A)) :=
    (continuous_exp_smul A).comp continuous_neg
  have hcont_h : ContinuousOn h (Icc 0 T) := hcont_neg.continuousOn.clm_apply hg
  have hint : ∀ s ∈ Icc 0 T, IntervalIntegrable h volume 0 s := fun s hs =>
    (hcont_h.mono (Icc_subset_Icc_right hs.2)).intervalIntegrable_of_Icc hs.1
  have heq : ∀ s ∈ Icc 0 T,
      (NormedSpace.exp ((s : ℂ) • A) u₀ +
        ∫ τ in (0 : ℝ)..s, NormedSpace.exp (((s - τ : ℝ) : ℂ) • A) (g τ)) =
      NormedSpace.exp ((s : ℂ) • A) (u₀ + ∫ τ in (0 : ℝ)..s, h τ) := by
    intro s hs
    rw [map_add, ← ContinuousLinearMap.intervalIntegral_comp_comm _ (hint s hs)]
    congr 1
    refine intervalIntegral.integral_congr (fun τ _ => ?_)
    simp only [hh]
    rw [← mul_apply_eq_comp, ← exp_smul_add, sub_eq_add_neg]
  have hG : HasDerivWithinAt (fun s => ∫ τ in (0 : ℝ)..s, h τ) (h t) (Icc 0 T) t := by
    have : Fact (t ∈ Icc (0 : ℝ) T) := ⟨ht⟩
    exact intervalIntegral.integral_hasDerivWithinAt_right (hint t ht)
      (hcont_h.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hcont_h t ht)
  have hV : HasDerivWithinAt
      (fun s : ℝ => NormedSpace.exp ((s : ℂ) • A) (u₀ + ∫ τ in (0 : ℝ)..s, h τ))
      ((NormedSpace.exp ((t : ℂ) • A) * A) (u₀ + ∫ τ in (0 : ℝ)..t, h τ) +
        NormedSpace.exp ((t : ℂ) • A) (0 + h t)) (Icc 0 T) t :=
    hasDerivWithinAt_apply (hasDerivAt_exp_smul A t).1.hasDerivWithinAt
      ((hasDerivWithinAt_const t (Icc 0 T) u₀).fun_add hG)
  have hcomm : NormedSpace.exp ((t : ℂ) • A) * A = A * NormedSpace.exp ((t : ℂ) • A) :=
    (((Commute.refl A).smul_right (t : ℂ)).exp_right).eq.symm
  have hinv : NormedSpace.exp ((t : ℂ) • A) (h t) = g t := by
    simp only [hh]
    rw [← mul_apply_eq_comp, ← exp_smul_add, add_neg_cancel, Complex.ofReal_zero,
      zero_smul, NormedSpace.exp_zero, one_apply_eq_self]
  refine (hV.congr (fun s hs => heq s hs) (heq t ht)).congr_deriv ?_
  rw [heq t ht, zero_add, hinv, hcomm, mul_apply_eq_comp]

end NonUniqueEuler.BanachExp
