import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Proof of the interface (I-ODE): integration by parts against an integrated-form derivative

Proves the declaration of `NonUniqueEuler/I/Infra/ODE/WeakIBP.lean` (statement copied
verbatim): `integral_mul_eq_of_integrated`.

Proof (the Fubini route of the interface docstring).
* `WeakIBPAux.integral_mul_primitive_swap`: for `a ≤ b` and `f g` interval integrable,
  `∫_a^b f(s) (∫_a^s g) ds = ∫_a^b (∫_t^b f) g(t) dt`. This is Fubini
  (`MeasureTheory.integral_integral_swap`) on `(a, b]²` for the integrand
  `1_{t ≤ s} f(s) g(t)`, integrable as an indicator of the product `f ⊗ g`
  (`Integrable.mul_prod`).
* `WeakIBPAux.integral_mul_eq_of_integrated_of_le`: the case `a ≤ b`. Substituting
  `U = U a + ∫_a^· H` in `∫ v' U`, using the swap with `f = v'`, `g = H`, and the fundamental
  theorem of calculus `∫_t^b v' = v b - v t` (`intervalIntegral.integral_eq_sub_of_hasDerivAt`).
* The case `b < a` follows from the case `a ≤ b` with the roles of `a` and `b` exchanged,
  since `U t = U b + ∫_b^t H` on the same interval.
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler.LinODE

namespace WeakIBPAux

/-- **Fubini on the triangle.** For `a ≤ b` and `f g` interval integrable on `[a, b]`,
`∫_a^b f(s) (∫_a^s g) ds = ∫_a^b (∫_t^b f) g(t) dt`. -/
theorem integral_mul_primitive_swap {f g : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b) :
    ∫ s in a..b, f s * ∫ t in a..s, g t = ∫ t in a..b, (∫ s in t..b, f s) * g t := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  have hfi : Integrable f (volume.restrict (Ioc a b)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hf
  have hgi : Integrable g (volume.restrict (Ioc a b)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hg
  have hS : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} := measurableSet_le measurable_snd measurable_fst
  set F : ℝ → ℝ → ℂ := fun s t =>
    {p : ℝ × ℝ | p.2 ≤ p.1}.indicator (fun p : ℝ × ℝ => f p.1 * g p.2) (s, t) with hF
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b))) :=
    (hfi.mul_prod hgi).indicator hS
  have hswap := integral_integral_swap hint
  -- the inner integral in `t`
  have hL : ∀ s ∈ Ioc a b, ∫ t in Ioc a b, F s t = f s * ∫ t in a..s, g t := by
    intro s hs
    have h1 : ∀ t, F s t = (Iic s).indicator (fun t => f s * g t) t := by
      intro t
      simp only [hF, Set.indicator_apply, mem_ofPred_eq, mem_Iic]
    simp_rw [h1]
    have h2 : Iic s ∩ Ioc a b = Ioc a s := by
      ext t
      simp only [mem_inter_iff, mem_Iic, mem_Ioc]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans hs.2⟩
    rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
      integral_const_mul, intervalIntegral.integral_of_le hs.1.le, h2]
  -- the inner integral in `s`
  have hR : ∀ t ∈ Ioc a b, ∫ s in Ioc a b, F s t = (∫ s in t..b, f s) * g t := by
    intro t ht
    have h1 : ∀ s, F s t = (Ici t).indicator (fun s => f s * g t) s := by
      intro s
      simp only [hF, Set.indicator_apply, mem_ofPred_eq, mem_Ici]
    simp_rw [h1]
    rw [integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
      integral_mul_const, intervalIntegral.integral_of_le ht.2]
    have h2 : Ici t ∩ Ioc a b = Icc t b := by
      ext s
      simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
      constructor
      · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, ht.1.trans_le h1, h2⟩
    rw [h2, integral_Icc_eq_integral_Ioc]
  calc ∫ s in Ioc a b, f s * ∫ t in a..s, g t
      = ∫ s in Ioc a b, ∫ t in Ioc a b, F s t :=
        (setIntegral_congr_fun measurableSet_Ioc (fun s hs => (hL s hs).symm))
    _ = ∫ t in Ioc a b, ∫ s in Ioc a b, F s t := hswap
    _ = ∫ t in Ioc a b, (∫ s in t..b, f s) * g t :=
        setIntegral_congr_fun measurableSet_Ioc (fun t ht => hR t ht)

/-- The case `a ≤ b` of `integral_mul_eq_of_integrated`. -/
theorem integral_mul_eq_of_integrated_of_le {U H v v' : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hH : IntervalIntegrable H volume a b)
    (hU : ∀ t ∈ Icc a b, U t = U a + ∫ s in a..t, H s)
    (hv : ∀ t ∈ Icc a b, HasDerivAt v (v' t) t) (hv' : ContinuousOn v' (Icc a b)) :
    ∫ t in a..b, v t * H t = v b * U b - v a * U a - ∫ t in a..b, v' t * U t := by
  have huIcc : uIcc a b = Icc a b := uIcc_of_le hab
  have hv'i : IntervalIntegrable v' volume a b :=
    ContinuousOn.intervalIntegrable (huIcc ▸ hv')
  have hvc : ContinuousOn v (Icc a b) :=
    fun t ht => (hv t ht).continuousAt.continuousWithinAt
  -- the fundamental theorem of calculus for `v` on `[t, b]`
  have hFTC : ∀ t ∈ Icc a b, ∫ s in t..b, v' s = v b - v t := by
    intro t ht
    have hsub : uIcc t b ⊆ Icc a b := by
      rw [uIcc_of_le ht.2]
      exact Icc_subset_Icc ht.1 le_rfl
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hv x (hsub hx))
      ((hv'.mono hsub).intervalIntegrable)
  have hprim : ContinuousOn (fun s => ∫ t in a..s, H t) (uIcc a b) :=
    intervalIntegral.continuousOn_primitive_interval' hH left_mem_uIcc
  have hswap := integral_mul_primitive_swap hab hv'i hH
  -- `∫ (v b - v t) H t = v b (U b - U a) - ∫ v H`
  have hHU : ∫ t in a..b, H t = U b - U a := by
    have := hU b ⟨hab, le_rfl⟩
    rw [this]; ring
  have h1 : ∫ t in a..b, (∫ s in t..b, v' s) * H t
      = v b * (U b - U a) - ∫ t in a..b, v t * H t := by
    have h1a : ∫ t in a..b, (∫ s in t..b, v' s) * H t = ∫ t in a..b, (v b * H t - v t * H t) := by
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      rw [hFTC t (huIcc ▸ ht)]
      ring
    rw [h1a, intervalIntegral.integral_sub (hH.const_mul _)
      (hH.continuousOn_mul (huIcc ▸ hvc)), intervalIntegral.integral_const_mul, hHU]
  -- `∫ v' U = (v b - v a) U a + ∫ v'(s) ∫_a^s H`
  have h2 : ∫ t in a..b, v' t * U t
      = (v b - v a) * U a + ∫ s in a..b, v' s * ∫ t in a..s, H t := by
    have h2a : ∫ t in a..b, v' t * U t
        = ∫ t in a..b, (v' t * U a + v' t * ∫ s in a..t, H s) := by
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      rw [hU t (huIcc ▸ ht)]
      ring
    rw [h2a, intervalIntegral.integral_add (hv'i.mul_const _) (hv'i.mul_continuousOn hprim),
      intervalIntegral.integral_mul_const, hFTC a ⟨le_rfl, hab⟩]
  rw [h2, hswap, h1]
  ring

end WeakIBPAux

/-- **Integration by parts against an integrated-form derivative.** If `U t = U a + ∫_a^t H`
on `[a, b]` with `H` interval integrable, and `v` has a continuous derivative `v'` on `[a, b]`,
then `∫_a^b v H = v(b)U(b) - v(a)U(a) - ∫_a^b v' U`. -/
theorem integral_mul_eq_of_integrated {U H v v' : ℝ → ℂ} {a b : ℝ}
    (hH : IntervalIntegrable H volume a b)
    (hU : ∀ t ∈ uIcc a b, U t = U a + ∫ s in a..t, H s)
    (hv : ∀ t ∈ uIcc a b, HasDerivAt v (v' t) t) (hv' : ContinuousOn v' (uIcc a b)) :
    ∫ t in a..b, v t * H t = v b * U b - v a * U a - ∫ t in a..b, v' t * U t := by
  rcases le_total a b with hab | hba
  · rw [uIcc_of_le hab] at hU hv hv'
    exact WeakIBPAux.integral_mul_eq_of_integrated_of_le hab hH hU hv hv'
  · rw [uIcc_of_ge hba] at hU hv hv'
    -- re-base the integrated form at `b`
    have hU' : ∀ t ∈ Icc b a, U t = U b + ∫ s in b..t, H s := by
      intro t ht
      have hsub : uIcc a t ⊆ uIcc a b := by
        rw [uIcc_of_ge ht.2, uIcc_of_ge hba]
        exact Icc_subset_Icc ht.1 le_rfl
      have hat : IntervalIntegrable H volume a t := hH.mono_set hsub
      rw [hU t ht, hU b ⟨le_rfl, hba⟩, ← intervalIntegral.integral_interval_sub_left hat hH]
      ring
    have key := WeakIBPAux.integral_mul_eq_of_integrated_of_le hba hH.symm hU' hv hv'
    rw [intervalIntegral.integral_symm b a, intervalIntegral.integral_symm b a]
    linear_combination -key

end NonUniqueEuler.LinODE
