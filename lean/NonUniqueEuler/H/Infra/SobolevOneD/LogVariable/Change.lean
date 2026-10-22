import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.Order.Chebyshev

/-!
# Helpers for `P/Infra/SobolevOneD/LogVariable`: the substitution `r = e^x`

* `integral_image_exp`, `integrableOn_image_exp_iff`, `integral_Ioi_eq`, `integrableOn_Ioi_iff`:
  the one-dimensional change of variables `r = e^x` (`dr = e^x dx`), for arbitrary integrands
  (`integral_image_eq_integral_abs_deriv_smul`);
* `locallyIntegrable_expMul_comp_exp`, `locallyIntegrableOn_comp_log`: local integrability is
  transported along `r = e^x`, with smooth weights;
* `memLp_expMul_comp_exp`: for `G ∈ L²((0,∞))` vanishing a.e. outside `[ρ₋, ρ₊]`,
  `e^{px} G(e^x) ∈ L²(ℝ)` with `∫ |e^{px} G(e^x)|² dx ≤ ρ₊^{2p} ρ₋^{-2} ∫_{ρ₋}^{ρ₊} |G|² r dr`;
* `setIntegral_comp_log_le`: `∫_α^β |r^{-q} V(log r)|² r dr ≤ β² α^{-2q} ∫_{log α}^{log β} |V|²`;
* `norm_sum_sq_le`, `integral_norm_sum_sq_le`: Cauchy–Schwarz for finite sums.

All proofs are complete.
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler.Sob.LogVarH

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

theorem integrableOn_Ioi_iff (g : ℝ → E) :
    IntegrableOn g (Ioi 0) ↔ Integrable (fun x => Real.exp x • g (Real.exp x)) := by
  rw [← Real.range_exp, ← image_univ, integrableOn_image_exp_iff MeasurableSet.univ,
    integrableOn_univ]

/-- Local integrability on `(0, ∞)` transfers to `x ↦ e^{cx} F(e^x)` on `ℝ`. -/
theorem locallyIntegrable_expMul_comp_exp {F : ℝ → ℂ} (hF : LocallyIntegrableOn F (Ioi 0))
    (c : ℝ) : LocallyIntegrable (fun x => ((Real.exp (c * x) : ℝ) : ℂ) * F (Real.exp x)) := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨a, ha⟩ := hK.bddBelow
  obtain ⟨b, hb⟩ := hK.bddAbove
  have hKab : K ⊆ Icc a b := fun x hx => ⟨ha hx, hb hx⟩
  refine IntegrableOn.mono_set ?_ hKab
  set G : ℝ → ℂ := fun r => ((r⁻¹ * Real.exp (c * Real.log r) : ℝ) : ℂ) * F r with hGdef
  have hsub : Icc (Real.exp a) (Real.exp b) ⊆ Ioi 0 := fun r hr =>
    lt_of_lt_of_le (Real.exp_pos a) hr.1
  have hG : IntegrableOn G (Icc (Real.exp a) (Real.exp b)) := by
    have h1 : IntegrableOn F (Icc (Real.exp a) (Real.exp b)) :=
      hF.integrableOn_compact_subset hsub isCompact_Icc
    have hc : ContinuousOn (fun r : ℝ => ((r⁻¹ * Real.exp (c * Real.log r) : ℝ) : ℂ))
        (Icc (Real.exp a) (Real.exp b)) := by
      refine Complex.continuous_ofReal.comp_continuousOn ?_
      refine ContinuousOn.mul (continuousOn_inv₀.mono fun r hr => (hsub hr).ne') ?_
      refine Real.continuous_exp.comp_continuousOn (continuousOn_const.mul ?_)
      exact Real.continuousOn_log.mono fun r hr => (hsub hr).ne'
    exact IntegrableOn.continuousOn_mul hc h1 isCompact_Icc
  rw [← image_exp_Icc, integrableOn_image_exp_iff measurableSet_Icc] at hG
  refine hG.congr_fun (fun x _ => ?_) measurableSet_Icc
  simp only [hGdef, Real.log_exp, Complex.real_smul]
  have hx : (Real.exp x : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos x).ne'
  push_cast
  field_simp

/-- Local integrability on `ℝ` transfers to `r ↦ r^{-q} V(log r)` on `(0, ∞)`. -/
theorem locallyIntegrableOn_comp_log {V : ℝ → ℂ} (hV : LocallyIntegrable V) (q : ℕ) :
    LocallyIntegrableOn (fun r => (((r⁻¹ : ℝ) : ℂ)) ^ q * V (Real.log r)) (Ioi 0) := by
  rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
  intro K hK hKc
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact integrableOn_empty
  obtain ⟨a, haK, ha⟩ := hKc.exists_isLeast hne
  obtain ⟨b, hb⟩ := hKc.bddAbove
  have ha0 : 0 < a := hK haK
  have hKab : K ⊆ Icc a b := fun x hx => ⟨ha hx, hb hx⟩
  refine IntegrableOn.mono_set ?_ hKab
  rw [← image_exp_Icc_log ha0 (hb haK), integrableOn_image_exp_iff measurableSet_Icc]
  have h1 : IntegrableOn V (Icc (Real.log a) (Real.log b)) := hV.integrableOn_isCompact isCompact_Icc
  have hc : ContinuousOn (fun x : ℝ => ((Real.exp x * ((Real.exp x)⁻¹) ^ q : ℝ) : ℂ))
      (Icc (Real.log a) (Real.log b)) := by
    have hinv : Continuous (fun x : ℝ => (Real.exp x)⁻¹) :=
      Real.continuous_exp.inv₀ fun x => (Real.exp_pos x).ne'
    exact (Complex.continuous_ofReal.comp (Real.continuous_exp.mul (hinv.pow q))).continuousOn
  refine (IntegrableOn.continuousOn_mul hc h1 isCompact_Icc).congr_fun (fun x _ => ?_)
    measurableSet_Icc
  simp only [Real.log_exp, Complex.real_smul]
  push_cast
  ring

/-- For `G ∈ L²((0,∞))` vanishing a.e. outside `[ρ₋, ρ₊]`: `e^{px} G(e^x) ∈ L²(ℝ)`, with
`∫ |e^{px} G(e^x)|² dx ≤ ρ₊^{2p} ρ₋^{-2} ∫_{ρ₋}^{ρ₊} |G|² r dr`. -/
theorem memLp_expMul_comp_exp {G : ℝ → ℂ} {ρm ρp : ℝ} (hρm : 0 < ρm)
    (hG : MemLp G 2 (volume.restrict (Ioi 0)))
    (hvan : ∀ᵐ r, r ∈ Ioi (0 : ℝ) → r ∉ Icc ρm ρp → G r = 0) (p : ℕ) :
    MemLp (fun x => ((Real.exp (p * x) : ℝ) : ℂ) * G (Real.exp x)) 2 volume ∧
      ∫ x, ‖((Real.exp (p * x) : ℝ) : ℂ) * G (Real.exp x)‖ ^ 2 ≤
        ρp ^ (2 * p) / ρm ^ 2 * ∫ r in Icc ρm ρp, ‖G r‖ ^ 2 * r := by
  have hsub : Icc ρm ρp ⊆ Ioi 0 := fun r hr => lt_of_lt_of_le hρm hr.1
  have hGI : MemLp G 2 (volume.restrict (Icc ρm ρp)) :=
    hG.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hG1 : IntegrableOn G (Icc ρm ρp) := hGI.integrable one_le_two
  have hG2 : IntegrableOn (fun r => ‖G r‖ ^ 2) (Icc ρm ρp) := hGI.norm.integrable_sq
  -- integrability of `A`
  set F₁ : ℝ → ℂ := fun r => ((r⁻¹ * r ^ p : ℝ) : ℂ) * G r with hF₁
  have hF₁I : IntegrableOn F₁ (Icc ρm ρp) := by
    have hc : ContinuousOn (fun r : ℝ => ((r⁻¹ * r ^ p : ℝ) : ℂ)) (Icc ρm ρp) := by
      refine Complex.continuous_ofReal.comp_continuousOn ?_
      exact ContinuousOn.mul (continuousOn_inv₀.mono fun r hr => (hsub hr).ne')
        (continuousOn_pow p)
    exact IntegrableOn.continuousOn_mul hc hG1 isCompact_Icc
  have hF₁Ioi : IntegrableOn F₁ (Ioi 0) := by
    refine hF₁I.of_ae_sdiff_eq_zero measurableSet_Ioi.nullMeasurableSet ?_
    filter_upwards [hvan] with r hr hr'
    simp [hF₁, hr hr'.1 hr'.2]
  have hA : Integrable (fun x => ((Real.exp (p * x) : ℝ) : ℂ) * G (Real.exp x)) := by
    have h := (integrableOn_Ioi_iff F₁).1 hF₁Ioi
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [hF₁, Complex.real_smul, Real.exp_nat_mul]
    have hx : (Real.exp x : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos x).ne'
    push_cast
    field_simp
  -- integrability of `|A|²`
  set F₂ : ℝ → ℝ := fun r => r⁻¹ * (r ^ p) ^ 2 * ‖G r‖ ^ 2 with hF₂
  have hF₂I : IntegrableOn F₂ (Icc ρm ρp) := by
    have hc : ContinuousOn (fun r : ℝ => r⁻¹ * (r ^ p) ^ 2) (Icc ρm ρp) :=
      ContinuousOn.mul (continuousOn_inv₀.mono fun r hr => (hsub hr).ne')
        ((continuousOn_pow p).pow 2)
    exact IntegrableOn.continuousOn_mul hc hG2 isCompact_Icc
  have hF₂Ioi : IntegrableOn F₂ (Ioi 0) := by
    refine hF₂I.of_ae_sdiff_eq_zero measurableSet_Ioi.nullMeasurableSet ?_
    filter_upwards [hvan] with r hr hr'
    simp [hF₂, hr hr'.1 hr'.2]
  have hnorm : ∀ x, Real.exp x • F₂ (Real.exp x) =
      ‖((Real.exp (p * x) : ℝ) : ℂ) * G (Real.exp x)‖ ^ 2 := by
    intro x
    simp only [hF₂, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_pow,
      abs_of_pos (Real.exp_pos x), Real.exp_nat_mul]
    have hx : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
    field_simp
  have hA2 : Integrable (fun x => ‖((Real.exp (p * x) : ℝ) : ℂ) * G (Real.exp x)‖ ^ 2) := by
    have h := (integrableOn_Ioi_iff F₂).1 hF₂Ioi
    exact h.congr (Filter.Eventually.of_forall hnorm)
  refine ⟨(memLp_two_iff_integrable_sq_norm hA.aestronglyMeasurable).2 hA2, ?_⟩
  -- the bound
  have e1 : ∫ x, ‖((Real.exp (p * x) : ℝ) : ℂ) * G (Real.exp x)‖ ^ 2 =
      ∫ r in Icc ρm ρp, F₂ r := by
    rw [← setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioi.nullMeasurableSet hsub,
      integral_Ioi_eq]
    · exact integral_congr_ae (Filter.Eventually.of_forall hnorm) |>.symm
    · filter_upwards [hvan] with r hr hr'
      simp [hF₂, hr hr'.1 hr'.2]
  rw [e1, ← integral_const_mul]
  have hrhs : IntegrableOn (fun r => ρp ^ (2 * p) / ρm ^ 2 * (‖G r‖ ^ 2 * r)) (Icc ρm ρp) := by
    have hc : ContinuousOn (fun r : ℝ => r) (Icc ρm ρp) := continuousOn_id
    exact ((IntegrableOn.mul_continuousOn hG2 hc isCompact_Icc)).const_mul _
  refine setIntegral_mono_on hF₂I hrhs measurableSet_Icc fun r hr => ?_
  have hr0 : 0 < r := hsub hr
  simp only [hF₂]
  have h1 : (r ^ p) ^ 2 ≤ ρp ^ (2 * p) := by
    rw [← pow_mul, mul_comm]
    exact pow_le_pow_left₀ hr0.le hr.2 _
  have h2 : r⁻¹ ≤ r / ρm ^ 2 := by
    have : r⁻¹ = r / r ^ 2 := by field_simp
    rw [this]
    exact div_le_div_of_nonneg_left hr0.le (by positivity)
      (pow_le_pow_left₀ hρm.le hr.1 2)
  have h3 : r⁻¹ * (r ^ p) ^ 2 ≤ ρp ^ (2 * p) / ρm ^ 2 * r := by
    calc r⁻¹ * (r ^ p) ^ 2 ≤ r / ρm ^ 2 * ρp ^ (2 * p) :=
          mul_le_mul h2 h1 (by positivity) (by positivity)
      _ = ρp ^ (2 * p) / ρm ^ 2 * r := by ring
  calc r⁻¹ * (r ^ p) ^ 2 * ‖G r‖ ^ 2 ≤ ρp ^ (2 * p) / ρm ^ 2 * r * ‖G r‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
    _ = ρp ^ (2 * p) / ρm ^ 2 * (‖G r‖ ^ 2 * r) := by ring

/-- `∫_α^β |r^{-q} V(log r)|² r dr ≤ β² α^{-2q} ∫_{log α}^{log β} |V|²`. -/
theorem setIntegral_comp_log_le {V : ℝ → ℂ} {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hV : IntegrableOn (fun x => ‖V x‖ ^ 2) (Icc (Real.log α) (Real.log β))) (q : ℕ) :
    ∫ r in Icc α β, ‖(((r⁻¹ : ℝ) : ℂ)) ^ q * V (Real.log r)‖ ^ 2 * r ≤
      β ^ 2 * α⁻¹ ^ (2 * q) * ∫ x in Icc (Real.log α) (Real.log β), ‖V x‖ ^ 2 := by
  rw [← image_exp_Icc_log hα hαβ, integral_image_exp measurableSet_Icc, ← integral_const_mul]
  refine integral_mono_of_nonneg ?_ (hV.const_mul _) ?_
  · refine Filter.Eventually.of_forall fun x => ?_
    simp only [smul_eq_mul]
    positivity
  · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hex : Real.exp x ∈ Icc α β := by
      rw [← image_exp_Icc_log hα hαβ]; exact mem_image_of_mem _ hx
    have he0 : 0 < Real.exp x := Real.exp_pos x
    simp only [smul_eq_mul, Real.log_exp, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_inv, abs_of_pos he0]
    have h1 : (Real.exp x)⁻¹ ≤ α⁻¹ := inv_anti₀ hα hex.1
    have h2 : ((Real.exp x)⁻¹ ^ q) ^ 2 ≤ α⁻¹ ^ (2 * q) := by
      rw [← pow_mul, mul_comm]
      exact pow_le_pow_left₀ (by positivity) h1 _
    have h3 : Real.exp x * Real.exp x ≤ β ^ 2 := by
      rw [sq]; exact mul_le_mul hex.2 hex.2 he0.le (hα.le.trans hαβ)
    calc Real.exp x * (((Real.exp x)⁻¹ ^ q * ‖V x‖) ^ 2 * Real.exp x)
        = (Real.exp x * Real.exp x) * ((Real.exp x)⁻¹ ^ q) ^ 2 * ‖V x‖ ^ 2 := by ring
      _ ≤ β ^ 2 * α⁻¹ ^ (2 * q) * ‖V x‖ ^ 2 := by
          gcongr

/-- Cauchy–Schwarz: `|∑_{p<n} c_p a_p|² ≤ n ∑_{p<n} |c_p|² |a_p|²`. -/
theorem norm_sum_sq_le (n : ℕ) (c a : ℕ → ℂ) :
    ‖∑ p ∈ Finset.range n, c p * a p‖ ^ 2 ≤
      n * ∑ p ∈ Finset.range n, ‖c p‖ ^ 2 * ‖a p‖ ^ 2 := by
  have h1 : ‖∑ p ∈ Finset.range n, c p * a p‖ ≤ ∑ p ∈ Finset.range n, ‖c p‖ * ‖a p‖ :=
    (norm_sum_le _ _).trans (le_of_eq (by simp))
  calc ‖∑ p ∈ Finset.range n, c p * a p‖ ^ 2
      ≤ (∑ p ∈ Finset.range n, ‖c p‖ * ‖a p‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (Finset.range n).card * ∑ p ∈ Finset.range n, (‖c p‖ * ‖a p‖) ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ = n * ∑ p ∈ Finset.range n, ‖c p‖ ^ 2 * ‖a p‖ ^ 2 := by
        simp [mul_pow]

/-- Integrated Cauchy–Schwarz for finite sums. -/
theorem integral_norm_sum_sq_le {μ : Measure ℝ} (n : ℕ) (c : ℕ → ℂ) (A : ℕ → ℝ → ℂ)
    (hA : ∀ p < n, Integrable (fun x => ‖A p x‖ ^ 2) μ) :
    ∫ x, ‖∑ p ∈ Finset.range n, c p * A p x‖ ^ 2 ∂μ ≤
      n * ∑ p ∈ Finset.range n, ‖c p‖ ^ 2 * ∫ x, ‖A p x‖ ^ 2 ∂μ := by
  have hint : Integrable (fun x => (n : ℝ) * ∑ p ∈ Finset.range n, ‖c p‖ ^ 2 * ‖A p x‖ ^ 2) μ :=
    (integrable_finsetSum _ fun p hp =>
      (hA p (Finset.mem_range.1 hp)).const_mul _).const_mul _
  calc ∫ x, ‖∑ p ∈ Finset.range n, c p * A p x‖ ^ 2 ∂μ
      ≤ ∫ x, (n : ℝ) * ∑ p ∈ Finset.range n, ‖c p‖ ^ 2 * ‖A p x‖ ^ 2 ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _) hint
          (Filter.Eventually.of_forall fun x => norm_sum_sq_le n c (fun p => A p x))
    _ = n * ∑ p ∈ Finset.range n, ‖c p‖ ^ 2 * ∫ x, ‖A p x‖ ^ 2 ∂μ := by
        rw [integral_const_mul, integral_finsetSum _ fun p hp =>
          (hA p (Finset.mem_range.1 hp)).const_mul _]
        simp only [integral_const_mul]

end NonUniqueEuler.Sob.LogVarH
