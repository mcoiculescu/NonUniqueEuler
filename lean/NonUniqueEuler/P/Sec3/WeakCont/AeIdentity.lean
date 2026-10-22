import NonUniqueEuler.Defs.Sec3.Transport
import NonUniqueEuler.Defs.Sec2.Spaces
import NonUniqueEuler.Defs.Infra.JointRep
import NonUniqueEuler.I.Sec3.WeakCont.Bounds
import NonUniqueEuler.I.Sec3.Dbr
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Proof of `I/Sec3/WeakCont/AeIdentity.lean`: the a.e. identity `a_ψ = A_ψ`

Manuscript: proof of `lem:weak-cont`, second paragraph (`03_compactness.tex:155-170`), `b = 2`.

* `integral_deriv_mul_primitive`: Fubini on `(0,T)²` with the integrand `1_{s<t} α'(t) c(s)`,
  then `∫_s^T α' = -α(s)` (`α(T) = 0`).
* `ae_integral_mul_eq`: test `(te)` with `α(t) ψ(x)`; split the slab integral into
  `∫ α' a_ψ + ∫ α c_ψ` (the flux part is integrable by `integrableOn_slab_mul_fderiv`, the time
  part as the difference), use `integral_deriv_mul_primitive` and `∫_0^T α' = -α(0)`, and apply
  `lem:dbr` (`duBoisReymond`, `t₀ = 0`, `b₀ = 0`) to `B = a_ψ - A_ψ ∈ L^∞(0,T)`
  (`|a_ψ(t)| ≤ ‖u(t)‖₂ ‖ψ‖₂` by Hölder, `|∫_0^t c_ψ| ≤ ‖c_ψ‖_{L¹(0,T)}`).

Helper lemmas live in the namespace `NonUniqueEuler.Weak.WeakCont.AeIdentityAux`, so that their
names do not clash with the helpers of sibling proof files in the full library.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace NonUniqueEuler.Weak.WeakCont

namespace AeIdentityAux

/-- `α(T) = 0` for `α ∈ C_c^∞((-∞,T))`. -/
theorem apply_eq_zero {T : ℝ} {α : ℝ → ℝ} (hα : IsTimeTestFn T α) : α T = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => lt_irrefl _ (hα.support_lt T h)

theorem differentiable {T : ℝ} {α : ℝ → ℝ} (hα : IsTimeTestFn T α) : Differentiable ℝ α :=
  hα.contDiff.differentiable (by simp)

theorem continuous_deriv {T : ℝ} {α : ℝ → ℝ} (hα : IsTimeTestFn T α) : Continuous (deriv α) :=
  hα.contDiff.continuous_deriv (by simp)

/-- `∫_s^T α' = -α(s)` for `α ∈ C_c^∞((-∞,T))` and `s ≤ T`. -/
theorem setIntegral_Ioo_deriv {T s : ℝ} {α : ℝ → ℝ} (hα : IsTimeTestFn T α) (hs : s ≤ T) :
    ∫ t in Ioo s T, deriv α t = -α s := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hs,
    intervalIntegral.integral_deriv_eq_sub (fun x _ => differentiable hα x)
      ((continuous_deriv hα).intervalIntegrable _ _), apply_eq_zero hα, zero_sub]

/-- A bound on `|α'|`. -/
theorem exists_bound_deriv {T : ℝ} {α : ℝ → ℝ} (hα : IsTimeTestFn T α) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t, |deriv α t| ≤ A := by
  obtain ⟨A, hA⟩ := (continuous_deriv hα).bounded_above_of_compact_support
    hα.hasCompactSupport.deriv
  exact ⟨A, (norm_nonneg _).trans (hA 0), fun t => by rw [← Real.norm_eq_abs]; exact hA t⟩

/-- A bound on `|α|`. -/
theorem exists_bound {T : ℝ} {α : ℝ → ℝ} (hα : IsTimeTestFn T α) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t, |α t| ≤ A := by
  obtain ⟨A, hA⟩ := hα.contDiff.continuous.bounded_above_of_compact_support hα.hasCompactSupport
  exact ⟨A, (norm_nonneg _).trans (hA 0), fun t => by rw [← Real.norm_eq_abs]; exact hA t⟩

/-- `∂_t (α(t) ψ(x)) = α'(t) ψ(x)`. -/
theorem timeDeriv_mul {α : ℝ → ℝ} (hα : Differentiable ℝ α) (ψ : ℂ → ℝ) (t : ℝ) (x : ℂ) :
    timeDeriv (fun p : ℝ × ℂ => α p.1 * ψ p.2) t x = deriv α t * ψ x := by
  simp only [timeDeriv]
  exact deriv_mul_const (hα t) _

/-- `w · ∇_x (α(t) ψ(x)) = α(t) (w · ∇ψ(x))`. -/
theorem spaceDeriv_mul (α : ℝ → ℝ) {ψ : ℂ → ℝ} (hψ : Differentiable ℝ ψ) (t : ℝ) (x v : ℂ) :
    spaceDeriv (fun p : ℝ × ℂ => α p.1 * ψ p.2) t x v = α t * fderiv ℝ ψ x v := by
  simp only [spaceDeriv]
  rw [fderiv_const_mul (hψ x)]
  rfl

end AeIdentityAux

open AeIdentityAux in
/-- Integration by parts against a primitive (`03_compactness.tex:164-166`): for
`α ∈ C_c^∞((-∞,T))` and `c ∈ L¹(0,T)`, `∫_0^T α'(t) (∫_0^t c) dt = -∫_0^T α c`. -/
theorem integral_deriv_mul_primitive {T : ℝ} {α c : ℝ → ℝ} (hα : IsTimeTestFn T α)
    (hc : IntegrableOn c (Ioo 0 T)) :
    ∫ t in Ioo 0 T, deriv α t * ∫ s in Ioo 0 t, c s = -∫ t in Ioo 0 T, α t * c t := by
  rcases le_or_gt T 0 with hT | hT
  · simp [Ioo_eq_empty_of_le hT]
  obtain ⟨A, hA0, hA⟩ := exists_bound_deriv hα
  set μ : Measure ℝ := volume.restrict (Ioo 0 T) with hμ
  set f : ℝ → ℝ → ℝ := fun t s => if s < t then deriv α t * c s else 0 with hf
  -- integrability on `(0,T)²`
  have hint : Integrable (Function.uncurry f) (μ.prod μ) := by
    have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => deriv α p.1 * c p.2) (μ.prod μ) :=
      ((continuous_deriv hα).comp continuous_fst).aestronglyMeasurable.mul
        hc.aestronglyMeasurable.comp_snd
    have hset : MeasurableSet {p : ℝ × ℝ | p.2 < p.1} := measurableSet_lt measurable_snd
      measurable_fst
    have heq : Function.uncurry f =
        {p : ℝ × ℝ | p.2 < p.1}.indicator (fun p : ℝ × ℝ => deriv α p.1 * c p.2) := by
      funext p
      simp only [Function.uncurry, hf, indicator_apply]
      rfl
    rw [heq]
    refine ((hc.norm.comp_snd μ).const_mul A).mono' (hm.indicator hset)
      (Filter.Eventually.of_forall fun p => ?_)
    rw [indicator_apply]
    split_ifs
    · simp only [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hA _) (abs_nonneg _)
    · simp only [norm_zero]
      positivity
  -- the two iterated integrals
  have hleft : ∀ t ∈ Ioo 0 T, ∫ s, f t s ∂μ = deriv α t * ∫ s in Ioo 0 t, c s := by
    intro t ht
    have h1 : (fun s => f t s) = (Iio t).indicator (fun s => deriv α t * c s) := by
      funext s
      simp only [hf, indicator_apply, mem_Iio]
    have h2 : Iio t ∩ Ioo 0 T = Ioo 0 t := by
      ext s
      simp only [mem_inter_iff, mem_Iio, mem_Ioo]
      constructor
      · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans ht.2⟩
    rw [h1, integral_indicator measurableSet_Iio, hμ, Measure.restrict_restrict measurableSet_Iio,
      h2, integral_const_mul]
  have hright : ∀ s ∈ Ioo 0 T, ∫ t, f t s ∂μ = -(α s * c s) := by
    intro s hs
    have h1 : (fun t => f t s) = (Ioi s).indicator (fun t => deriv α t * c s) := by
      funext t
      simp only [hf, indicator_apply, mem_Ioi]
    have h2 : Ioi s ∩ Ioo 0 T = Ioo s T := by
      ext t
      simp only [mem_inter_iff, mem_Ioi, mem_Ioo]
      constructor
      · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, hs.1.trans h1, h2⟩
    rw [h1, integral_indicator measurableSet_Ioi, hμ, Measure.restrict_restrict measurableSet_Ioi,
      h2, integral_mul_const, setIntegral_Ioo_deriv hα hs.2.le]
    ring
  calc ∫ t in Ioo 0 T, deriv α t * ∫ s in Ioo 0 t, c s
      = ∫ t, ∫ s, f t s ∂μ ∂μ := (setIntegral_congr_fun measurableSet_Ioo hleft).symm
    _ = ∫ s, ∫ t, f t s ∂μ ∂μ := integral_integral_swap hint
    _ = ∫ s in Ioo 0 T, -(α s * c s) := setIntegral_congr_fun measurableSet_Ioo hright
    _ = -∫ t in Ioo 0 T, α t * c t := integral_neg _

open AeIdentityAux in
/-- The a.e. identity of `lem:weak-cont` (`03_compactness.tex:155-170`, `b = 2`): for
`ψ ∈ C_c^∞`, `∫ u(t) ψ = ∫ u₀ ψ + ∫_0^t ∫ u w·∇ψ` for a.e. `t ∈ (0,T)`. -/
theorem ae_integral_mul_eq {T : ℝ} (hT : 0 < T) {u : ℝ → ℂ → ℝ} {w : ℝ → ℂ → ℂ}
    {u₀ : ℂ → ℝ} (hw : ∀ R : ℝ, 0 < R → Prelim.MemLinfLp (Ioo 0 T) (ball (0 : ℂ) R) 2 w)
    (hu : Prelim.MemLinfLp (Ioo 0 T) univ 2 u) (hte : SolvesTE 0 T u w u₀) {ψ : ℂ → ℝ}
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      ∫ x, u t x * ψ x =
        (∫ x, u₀ x * ψ x) + ∫ s in Ioo 0 t, ∫ x, u s x * fderiv ℝ ψ x (w s x) := by
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  have hψd : Differentiable ℝ ψ := hψ1.differentiable (by simp)
  have hμslab := JointRep.volume_restrict_slab T
  -- the flux `c_ψ(t) = ∫ u(t) w(t)·∇ψ` lies in `L¹(0,T)`
  have hflux : IntegrableOn (fun p : ℝ × ℂ => u p.1 p.2 * fderiv ℝ ψ p.2 (w p.1 p.2))
      (slabFrom 0 T) := integrableOn_slab_mul_fderiv hw hu hψ1 hψc
  have hcI : IntegrableOn (fun t => ∫ x, u t x * fderiv ℝ ψ x (w t x)) (Ioo 0 T) := by
    have h : Integrable (fun p : ℝ × ℂ => u p.1 p.2 * fderiv ℝ ψ p.2 (w p.1 p.2))
        ((volume.restrict (Ioo (0 : ℝ) T)).prod (volume : Measure ℂ)) := by
      rw [← hμslab]; exact hflux
    exact h.integral_prod_left
  -- the primitive `P(t) = ∫_0^t c_ψ` is continuous on `[0,T]` and bounded by `‖c_ψ‖_{L¹(0,T)}`
  have hPc : ContinuousOn (fun t => ∫ s in Ioo 0 t, ∫ x, u s x * fderiv ℝ ψ x (w s x))
      (Icc 0 T) := by
    have hc' : IntegrableOn (fun t => ∫ x, u t x * fderiv ℝ ψ x (w t x)) (Icc 0 T) :=
      by rw [integrableOn_Icc_iff_integrableOn_Ioo]; exact hcI
    refine (intervalIntegral.continuousOn_primitive hc').congr fun t _ => ?_
    exact integral_Ioc_eq_integral_Ioo.symm
  have hPm : AEStronglyMeasurable (fun t => ∫ s in Ioo 0 t, ∫ x, u s x * fderiv ℝ ψ x (w s x))
      (volume.restrict (Ioo 0 T)) :=
    (hPc.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  have hPb : ∀ t ∈ Ioo 0 T, ‖∫ s in Ioo 0 t, ∫ x, u s x * fderiv ℝ ψ x (w s x)‖ ≤
      ∫ s in Ioo 0 T, ‖∫ x, u s x * fderiv ℝ ψ x (w s x)‖ := by
    intro t ht
    refine (norm_integral_le_integral_norm _).trans ?_
    exact setIntegral_mono_set hcI.norm (Filter.Eventually.of_forall fun s => norm_nonneg _)
      (Ioo_subset_Ioo_right ht.2.le).eventuallyLE
  -- `a_ψ(t) = ∫ u(t) ψ` is a.e. strongly measurable and essentially bounded
  have hum : AEStronglyMeasurable (fun p : ℝ × ℂ => u p.1 p.2 * ψ p.2)
      ((volume.restrict (Ioo (0 : ℝ) T)).prod (volume : Measure ℂ)) := by
    rw [← hμslab]
    exact hu.aestronglyMeasurable.mul (hψ.continuous.comp continuous_snd).aestronglyMeasurable
  have ham : AEStronglyMeasurable (fun t => ∫ x, u t x * ψ x) (volume.restrict (Ioo 0 T)) :=
    hum.integral_prod_right'
  have hψ2 : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hψc
  obtain ⟨M, hM⟩ := hu.essBounded
  have hab : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      ‖∫ x, u t x * ψ x‖ ≤ M * (eLpNorm ψ 2 volume).toReal := by
    filter_upwards [hM] with t ht
    rw [Measure.restrict_univ] at ht
    have hM0 : 0 ≤ M := ENNReal.toReal_nonneg.trans ht.2
    have h1 : eLpNorm (fun x => u t x * ψ x) 1 volume ≤
        eLpNorm (u t) 2 volume * eLpNorm ψ 2 volume := by
      have h := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm (p := 2) (q := 2) (r := 1) ht.1.1 hψ2.1
        (fun a b => a * b) 1 (Filter.Eventually.of_forall fun x => by simp [norm_mul])
      simpa using h
    have h2 : ‖∫ x, u t x * ψ x‖ₑ ≤ ENNReal.ofReal (M * (eLpNorm ψ 2 volume).toReal) := by
      calc ‖∫ x, u t x * ψ x‖ₑ ≤ ∫⁻ x, ‖u t x * ψ x‖ₑ := enorm_integral_le_lintegral_enorm _
        _ = eLpNorm (fun x => u t x * ψ x) 1 volume := eLpNorm_one_eq_lintegral_enorm.symm
        _ ≤ eLpNorm (u t) 2 volume * eLpNorm ψ 2 volume := h1
        _ ≤ ENNReal.ofReal M * ENNReal.ofReal (eLpNorm ψ 2 volume).toReal := by
          gcongr
          · rw [← ENNReal.ofReal_toReal ht.1.eLpNorm_ne_top]
            exact ENNReal.ofReal_le_ofReal ht.2
          · rw [ENNReal.ofReal_toReal hψ2.eLpNorm_ne_top]
        _ = ENNReal.ofReal (M * (eLpNorm ψ 2 volume).toReal) := (ENNReal.ofReal_mul hM0).symm
    rw [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
    exact h2
  -- `B = a_ψ - A_ψ ∈ L^∞(0,T)`
  have hB : MemLp (fun t => (∫ x, u t x * ψ x) - ((∫ x, u₀ x * ψ x) +
      ∫ s in Ioo 0 t, ∫ x, u s x * fderiv ℝ ψ x (w s x))) ⊤ (volume.restrict (Ioo 0 T)) := by
    refine memLp_top_of_bound (ham.sub (aestronglyMeasurable_const.add hPm))
      (M * (eLpNorm ψ 2 volume).toReal + (|∫ x, u₀ x * ψ x| +
        ∫ s in Ioo 0 T, ‖∫ x, u s x * fderiv ℝ ψ x (w s x)‖)) ?_
    filter_upwards [hab, ae_restrict_mem measurableSet_Ioo] with t ht htI
    have h1 := abs_le.1 ((Real.norm_eq_abs _).symm.le.trans ht)
    have h2 := abs_le.1 ((Real.norm_eq_abs _).symm.le.trans (hPb t htI))
    have h3 := neg_abs_le (∫ x, u₀ x * ψ x)
    have h4 := le_abs_self (∫ x, u₀ x * ψ x)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  -- the hypothesis of `lem:dbr`
  have key : ∀ α : ℝ → ℝ, IsTimeTestFn T α →
      (∫ t in Ioo 0 T, deriv α t * ((∫ x, u t x * ψ x) - ((∫ x, u₀ x * ψ x) +
        ∫ s in Ioo 0 t, ∫ x, u s x * fderiv ℝ ψ x (w s x)))) + α 0 * 0 = 0 := by
    intro α hα
    obtain ⟨A₀, -, hA₀⟩ := exists_bound hα
    have hαd := differentiable hα
    have hα'c := continuous_deriv hα
    have hφ := isTestFunction_mul hα hψ hψc
    -- split the transport integrand
    have hTI : transportIntegrand u w (fun p : ℝ × ℂ => α p.1 * ψ p.2) =
        fun p => deriv α p.1 * (u p.1 p.2 * ψ p.2) +
          α p.1 * (u p.1 p.2 * fderiv ℝ ψ p.2 (w p.1 p.2)) := by
      funext p
      simp only [transportIntegrand, timeDeriv_mul hαd, spaceDeriv_mul _ hψd]
      ring
    have hF₂I : IntegrableOn (fun p : ℝ × ℂ => α p.1 * (u p.1 p.2 * fderiv ℝ ψ p.2 (w p.1 p.2)))
        (slabFrom 0 T) :=
      Integrable.bdd_mul (c := A₀) hflux
        ((hα.contDiff.continuous.comp continuous_fst).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hA₀ p.1)
    have hTIi : IntegrableOn (fun p : ℝ × ℂ => deriv α p.1 * (u p.1 p.2 * ψ p.2) +
          α p.1 * (u p.1 p.2 * fderiv ℝ ψ p.2 (w p.1 p.2))) (slabFrom 0 T) := by
      rw [← hTI]; exact hte.integrableOn _ hφ
    have hF₁I : IntegrableOn (fun p : ℝ × ℂ => deriv α p.1 * (u p.1 p.2 * ψ p.2))
        (slabFrom 0 T) :=
      (hTIi.sub hF₂I).congr (Filter.Eventually.of_forall fun p => by simp)
    -- the identity `(te)` with `φ = α ψ`
    have hid : (∫ p in slabFrom 0 T, transportIntegrand u w (fun p : ℝ × ℂ => α p.1 * ψ p.2) p) +
        ∫ x, u₀ x * (α 0 * ψ x) = 0 := by
      have h := hte.identity _ hφ
      rwa [integral_Ioo_integral_eq (hte.integrableOn _ hφ)] at h
    rw [hTI, integral_add hF₁I hF₂I, ← integral_Ioo_integral_eq hF₁I,
      ← integral_Ioo_integral_eq hF₂I] at hid
    simp only [integral_const_mul] at hid
    have hdatum : ∫ x, u₀ x * (α 0 * ψ x) = α 0 * ∫ x, u₀ x * ψ x := by
      rw [← integral_const_mul]
      congr 1
      funext x
      ring
    rw [hdatum] at hid
    -- integrability of the three pieces of `α' B`
    have hμslab' : (volume : Measure (ℝ × ℂ)).restrict (slabFrom 0 T) =
        (volume.restrict (Ioo (0 : ℝ) T)).prod (volume : Measure ℂ) := hμslab
    have hI₁ : IntegrableOn (fun t => deriv α t * ∫ x, u t x * ψ x) (Ioo 0 T) := by
      have h : Integrable (fun p : ℝ × ℂ => deriv α p.1 * (u p.1 p.2 * ψ p.2))
          ((volume.restrict (Ioo (0 : ℝ) T)).prod (volume : Measure ℂ)) := by
        rw [← hμslab']; exact hF₁I
      refine h.integral_prod_left.congr (Filter.Eventually.of_forall fun t => ?_)
      exact integral_const_mul (deriv α t) (fun x => u t x * ψ x)
    have hα'I : IntegrableOn (deriv α) (Ioo 0 T) :=
      hα'c.integrableOn_Icc.mono_set Ioo_subset_Icc_self
    have hI₂ : IntegrableOn (fun t => deriv α t * ∫ x, u₀ x * ψ x) (Ioo 0 T) :=
      hα'I.mul_const _
    have hI₃ : IntegrableOn
        (fun t => deriv α t * ∫ s in Ioo 0 t, ∫ x, u s x * fderiv ℝ ψ x (w s x)) (Ioo 0 T) :=
      Integrable.mul_bdd hα'I hPm (Filter.mp_mem (ae_restrict_mem measurableSet_Ioo)
        (Filter.Eventually.of_forall fun t ht => hPb t ht))
    have hsplit : (fun t => deriv α t * ((∫ x, u t x * ψ x) - ((∫ x, u₀ x * ψ x) +
          ∫ s in Ioo 0 t, ∫ x, u s x * fderiv ℝ ψ x (w s x)))) =
        fun t => (deriv α t * (∫ x, u t x * ψ x) - deriv α t * ∫ x, u₀ x * ψ x) -
          deriv α t * ∫ s in Ioo 0 t, ∫ x, u s x * fderiv ℝ ψ x (w s x) := by
      funext t; ring
    have hI₁₂ : IntegrableOn (fun t => deriv α t * (∫ x, u t x * ψ x) -
        deriv α t * ∫ x, u₀ x * ψ x) (Ioo 0 T) := hI₁.sub hI₂
    rw [hsplit, integral_sub hI₁₂ hI₃, integral_sub hI₁ hI₂, integral_mul_const,
      setIntegral_Ioo_deriv hα hT.le, integral_deriv_mul_primitive hα hcI]
    linarith
  have h := duBoisReymond hT hB key
  filter_upwards [h] with t ht
  have ht' := sub_eq_zero.1 ht
  exact ht'

end NonUniqueEuler.Weak.WeakCont
