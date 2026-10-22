import NonUniqueEuler.Defs.Sec3.Auxiliary
import NonUniqueEuler.I.Sec3.Dbr
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Proof: the one-dimensional chain rule for a weak time equation (step 2)

Proof of `I/Sec3/Transport/Mollified/ChainRule.lean` (`03_compactness.tex:500-505`, time part
of the chain rule in the proof of `lem:transport`(i)).

Put `D̃ = 1_{(t₀,T)} D ∈ L¹(ℝ)` and `V(s) = U₀ - ∫_{t₀}^s D̃`.
1. `V` is absolutely continuous on every `[t₀,T']`, with `V' = -D̃` a.e. (Lebesgue
   differentiation). Integration by parts against a time test function `β` (which vanishes,
   with `β'`, beyond some `T' < T`) gives `∫_{t₀}^T β' V = -β(t₀) U₀ + ∫_{t₀}^T β D`. With the
   hypothesis, `∫ β'(U - V) = 0` for every `β`, and `lem:dbr` (`duBoisReymond`, `b₀ = 0`) gives
   `U = V` a.e. on `(t₀,T)`.
2. `Υ` is Lipschitz on a compact interval containing `V([t₀,T'])`, so `Υ ∘ V` is absolutely
   continuous there (`ChainRuleH.absolutelyContinuousOnInterval_comp`), with
   `(Υ ∘ V)' = -Υ'(V) D̃` a.e. (chain rule).
3. Integration by parts again gives the claim for `V`, and `U = V` a.e. gives it for `U`.

Helper lemmas are in the namespace `NonUniqueEuler.Weak.ChainRuleH`.
-/

noncomputable section

open MeasureTheory Set
open scoped NNReal

namespace NonUniqueEuler.Weak

namespace ChainRuleH

/-- A Lipschitz function composed with an absolutely continuous function is absolutely
continuous. -/
theorem absolutelyContinuousOnInterval_comp {f g : ℝ → ℝ} {a b : ℝ} {K : ℝ≥0} {S : Set ℝ}
    (hg : LipschitzOnWith K g S) (hf : AbsolutelyContinuousOnInterval f a b)
    (hfS : MapsTo f (uIcc a b) S) : AbsolutelyContinuousOnInterval (fun x => g (f x)) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  have hK : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  obtain ⟨δ, hδ, hδε⟩ := hf (ε / ((K : ℝ) + 1)) (div_pos hε hK)
  refine ⟨δ, hδ, fun E hE hEδ => ?_⟩
  have hsum := hδε E hE hEδ
  calc ∑ i ∈ Finset.range E.1, dist (g (f (E.2 i).1)) (g (f (E.2 i).2))
      ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (f (E.2 i).1) (f (E.2 i).2) := by
        apply Finset.sum_le_sum
        intro i hi
        exact hg.dist_le_mul _ (hfS (hE.1 i hi).1) _ (hfS (hE.1 i hi).2)
    _ = (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ (K : ℝ) * (ε / ((K : ℝ) + 1)) := by gcongr
    _ < ((K : ℝ) + 1) * (ε / ((K : ℝ) + 1)) := by
        gcongr
        linarith
    _ = ε := by field_simp

/-- A time test function vanishes, together with its derivative, beyond some `T' ∈ (t₀,T)`. -/
theorem exists_cut {t₀ T : ℝ} (hT : t₀ < T) {β : ℝ → ℝ} (hβ : IsTimeTestFn T β) :
    ∃ T', t₀ < T' ∧ T' < T ∧ ∀ t, T' ≤ t → β t = 0 ∧ deriv β t = 0 := by
  obtain ⟨m, hmT, hm⟩ : ∃ m, m < T ∧ ∀ t ∈ tsupport β, t ≤ m := by
    rcases (tsupport β).eq_empty_or_nonempty with he | hne
    · exact ⟨t₀, hT, fun t ht => by simp [he] at ht⟩
    · obtain ⟨m, hm, hmax⟩ := hβ.hasCompactSupport.isCompact.exists_isGreatest hne
      exact ⟨m, hβ.support_lt m hm, fun t ht => hmax ht⟩
  have h1 : t₀ ≤ max t₀ m := le_max_left t₀ m
  have h2 : m ≤ max t₀ m := le_max_right t₀ m
  have h3 : max t₀ m < T := max_lt hT hmT
  refine ⟨(max t₀ m + T) / 2, by linarith, by linarith, fun t ht => ?_⟩
  have hmt : m < t := by linarith
  have hnot : t ∉ tsupport β := fun h => absurd (hm t h) (not_le.2 hmt)
  refine ⟨image_eq_zero_of_notMem_tsupport hnot, ?_⟩
  exact Function.notMem_support.1 (fun h => hnot (support_deriv_subset h))

/-- A set integral over `(t₀,T)` of a function vanishing on `[T',∞)` is an interval integral
over `[t₀,T']`. -/
theorem setIntegral_Ioo_eq_intervalIntegral {t₀ T T' : ℝ} (h1 : t₀ ≤ T') (h2 : T' ≤ T)
    {g : ℝ → ℝ} (hg : ∀ t, T' ≤ t → g t = 0) :
    ∫ s in Ioo t₀ T, g s = ∫ s in t₀..T', g s := by
  rw [intervalIntegral.integral_of_le h1, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo
    (Ioo_subset_Ioo_right h2) (fun t ht => hg t ?_)
  simp only [mem_sdiff, mem_Ioo, not_and, not_lt] at ht
  exact ht.2 ht.1.1

/-- Integration by parts against a time test function, for a function `W` absolutely
continuous on every `[t₀,T']` with `T' < T` and with derivative `W'` a.e. on `(t₀,T)`. -/
theorem integral_deriv_mul_eq {t₀ T : ℝ} (hT : t₀ < T) {β : ℝ → ℝ} (hβ : IsTimeTestFn T β)
    {W W' : ℝ → ℝ} (hW : ∀ T', T' < T → AbsolutelyContinuousOnInterval W t₀ T')
    (hW' : ∀ᵐ x, x ∈ Ioo t₀ T → HasDerivAt W (W' x) x) :
    ∫ s in Ioo t₀ T, deriv β s * W s = -(β t₀ * W t₀) - ∫ s in Ioo t₀ T, β s * W' s := by
  obtain ⟨T', h1, h2, h3⟩ := exists_cut hT hβ
  have hβac : AbsolutelyContinuousOnInterval β t₀ T' :=
    ((hβ.contDiff.of_le (by exact_mod_cast le_top)).contDiffOn).absolutelyContinuousOnInterval
  have key := (hW T' h2).integral_mul_deriv_eq_deriv_mul hβac
  rw [setIntegral_Ioo_eq_intervalIntegral h1.le h2.le (g := fun s => deriv β s * W s)
      (fun t ht => by simp [(h3 t ht).2]),
    setIntegral_Ioo_eq_intervalIntegral h1.le h2.le (g := fun s => β s * W' s)
      (fun t ht => by simp [(h3 t ht).1])]
  have e1 : ∫ x in t₀..T', deriv β x * W x = ∫ x in t₀..T', W x * deriv β x := by
    simp_rw [mul_comm]
  have e2 : ∫ x in t₀..T', deriv W x * β x = ∫ x in t₀..T', β x * W' x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hW'] with x hx hxI
    rw [uIoc_of_le h1.le] at hxI
    rw [(hx ⟨hxI.1, lt_of_le_of_lt hxI.2 h2⟩).deriv, mul_comm]
  rw [e1, key, e2, (h3 T' le_rfl).1]
  ring

/-- A continuous function is a.e. bounded on `(t₀,T)`. -/
theorem ae_bound_of_continuous {t₀ T : ℝ} {f : ℝ → ℝ} (hf : Continuous f) :
    ∃ C, ∀ᵐ s ∂(volume.restrict (Ioo t₀ T)), ‖f s‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := t₀) (b := T)).exists_bound_of_continuousOn
    hf.continuousOn
  exact ⟨C, ae_restrict_of_forall_mem measurableSet_Ioo fun s hs =>
    hC s (Ioo_subset_Icc_self hs)⟩

/-- A continuous function is integrable on `(t₀,T)`. -/
theorem integrableOn_Ioo_of_continuous {t₀ T : ℝ} {f : ℝ → ℝ} (hf : Continuous f) :
    IntegrableOn f (Ioo t₀ T) :=
  (hf.integrableOn_Icc (a := t₀) (b := T)).mono_set Ioo_subset_Icc_self

/-- The product of a continuous function and an integrable function on `(t₀,T)`. -/
theorem integrableOn_continuous_mul {t₀ T : ℝ} {f g : ℝ → ℝ} (hf : Continuous f)
    (hg : IntegrableOn g (Ioo t₀ T)) : IntegrableOn (fun s => f s * g s) (Ioo t₀ T) := by
  obtain ⟨C, hC⟩ := ae_bound_of_continuous (t₀ := t₀) (T := T) hf
  exact Integrable.bdd_mul hg hf.aestronglyMeasurable hC

theorem continuous_deriv_of_test {T : ℝ} {β : ℝ → ℝ} (hβ : IsTimeTestFn T β) :
    Continuous (deriv β) :=
  hβ.contDiff.continuous_deriv (by exact_mod_cast le_top)

end ChainRuleH

open ChainRuleH in
/-- The one-dimensional chain rule in weak form (`03_compactness.tex:500-505`, time part): if
`U ∈ L^∞(t₀,T)` satisfies `U' = -D` weakly on `[t₀,T)` with `D ∈ L¹(t₀,T)` and datum `U₀`, then
for every `Υ ∈ C¹`, `Υ(U)' = -Υ'(U) D` weakly on `[t₀,T)` with datum `Υ(U₀)`. -/
theorem renorm_timeEq {t₀ T : ℝ} (hT : t₀ < T) {U D : ℝ → ℝ} {U₀ : ℝ}
    (hU : MemLp U ⊤ (volume.restrict (Ioo t₀ T))) (hD : IntegrableOn D (Ioo t₀ T))
    (h : ∀ α : ℝ → ℝ, IsTimeTestFn T α →
      (∫ s in Ioo t₀ T, (deriv α s * U s - α s * D s)) + α t₀ * U₀ = 0)
    {Υ : ℝ → ℝ} (hΥ : ContDiff ℝ 1 Υ) {α : ℝ → ℝ} (hα : IsTimeTestFn T α) :
    (∫ s in Ioo t₀ T, (deriv α s * Υ (U s) - α s * deriv Υ (U s) * D s)) +
      α t₀ * Υ U₀ = 0 := by
  classical
  -- the extended source `D̃ = 1_{(t₀,T)} D` and the primitive `V`
  set Dt : ℝ → ℝ := (Ioo t₀ T).indicator D with hDt
  have hDti : Integrable Dt := hD.integrable_indicator measurableSet_Ioo
  have hDtD : ∀ s ∈ Ioo t₀ T, Dt s = D s := fun s hs => indicator_of_mem hs D
  set V : ℝ → ℝ := fun s => U₀ - ∫ r in t₀..s, Dt r with hV
  have hVc : Continuous V := continuous_const.sub (hDti.continuous_primitive t₀)
  have hVt₀ : V t₀ = U₀ := by simp [V]
  have hVac : ∀ T', AbsolutelyContinuousOnInterval V t₀ T' := fun T' =>
    (LipschitzWith.const U₀).lipschitzOnWith.absolutelyContinuousOnInterval.sub
      (hDti.intervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc)
  have hVd : ∀ᵐ x, HasDerivAt V (-Dt x) x := by
    filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral hDti.locallyIntegrable]
      with x hx
    exact (hx t₀).const_sub U₀
  have hVmem : MemLp V ⊤ (volume.restrict (Ioo t₀ T)) := by
    obtain ⟨M, hM⟩ := ae_bound_of_continuous (t₀ := t₀) (T := T) hVc
    exact memLp_top_of_bound hVc.aestronglyMeasurable M hM
  have hUint : Integrable U (volume.restrict (Ioo t₀ T)) := hU.integrable le_top
  -- step 1: `U = V` a.e. on `(t₀,T)`
  have hUV : U =ᵐ[volume.restrict (Ioo t₀ T)] V := by
    have hdbr := duBoisReymond hT (B := fun s => U s - V s) (b₀ := 0) (hU.sub hVmem)
      (fun β hβ => by
        show (∫ t in Ioo t₀ T, deriv β t * (U t - V t)) + β t₀ * 0 = 0
        have hβc : Continuous (deriv β) := continuous_deriv_of_test hβ
        have i1 : Integrable (fun s => deriv β s * U s) (volume.restrict (Ioo t₀ T)) := by
          obtain ⟨C, hC⟩ := ae_bound_of_continuous (t₀ := t₀) (T := T) hβc
          exact Integrable.bdd_mul hUint hβc.aestronglyMeasurable hC
        have i2 : Integrable (fun s => deriv β s * V s) (volume.restrict (Ioo t₀ T)) :=
          integrableOn_Ioo_of_continuous (hβc.mul hVc)
        have i3 : Integrable (fun s => β s * D s) (volume.restrict (Ioo t₀ T)) :=
          integrableOn_continuous_mul hβ.contDiff.continuous hD
        have hβeq := h β hβ
        rw [integral_sub i1 i3] at hβeq
        have hibp := integral_deriv_mul_eq hT hβ (W := V) (W' := fun x => -Dt x)
          (fun T' _ => hVac T') (hVd.mono fun x hx _ => hx)
        have e3 : ∫ s in Ioo t₀ T, β s * -Dt s = -∫ s in Ioo t₀ T, β s * D s := by
          rw [← integral_neg]
          refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
          simp only [hDtD s hs, mul_neg]
        have e4 : (fun t => deriv β t * (U t - V t)) =
            fun t => deriv β t * U t - deriv β t * V t := by
          funext t; ring
        rw [e4, integral_sub i1 i2, mul_zero, add_zero, hibp, e3, hVt₀]
        linarith)
    filter_upwards [hdbr] with s hs
    exact sub_eq_zero.1 hs
  -- step 2: the chain rule for `Υ ∘ V`
  have hΥd : Differentiable ℝ Υ := hΥ.differentiable one_ne_zero
  have hΥ'c : Continuous (deriv Υ) := hΥ.continuous_deriv le_rfl
  have hWac : ∀ T', AbsolutelyContinuousOnInterval (fun s => Υ (V s)) t₀ T' := by
    intro T'
    obtain ⟨M, hM⟩ := (isCompact_uIcc (a := t₀) (b := T')).exists_bound_of_continuousOn
      hVc.continuousOn
    obtain ⟨K, hK⟩ := hΥ.contDiffOn.exists_lipschitzOnWith (s := Icc (-M) M) one_ne_zero
      (convex_Icc _ _) isCompact_Icc
    refine absolutelyContinuousOnInterval_comp hK (hVac T') fun s hs => ?_
    have := hM s hs
    rw [Real.norm_eq_abs, abs_le] at this
    exact ⟨this.1, this.2⟩
  have hWd : ∀ᵐ x, HasDerivAt (fun s => Υ (V s)) (deriv Υ (V x) * -Dt x) x := by
    filter_upwards [hVd] with x hx
    exact (hΥd (V x)).hasDerivAt.comp x hx
  -- step 3: integration by parts, then replace `V` by `U`
  have hibp := integral_deriv_mul_eq hT hα (W := fun s => Υ (V s))
    (W' := fun x => deriv Υ (V x) * -Dt x) (fun T' _ => hWac T') (hWd.mono fun x hx _ => hx)
  have hαc : Continuous (deriv α) := continuous_deriv_of_test hα
  have j1 : Integrable (fun s => deriv α s * Υ (V s)) (volume.restrict (Ioo t₀ T)) :=
    integrableOn_Ioo_of_continuous (hαc.mul (hΥ.continuous.comp hVc))
  have j2 : Integrable (fun s => α s * deriv Υ (V s) * D s) (volume.restrict (Ioo t₀ T)) :=
    integrableOn_continuous_mul (hα.contDiff.continuous.mul (hΥ'c.comp hVc)) hD
  have e1 : (∫ s in Ioo t₀ T, (deriv α s * Υ (U s) - α s * deriv Υ (U s) * D s)) =
      ∫ s in Ioo t₀ T, (deriv α s * Υ (V s) - α s * deriv Υ (V s) * D s) := by
    refine integral_congr_ae ?_
    filter_upwards [hUV] with s hs
    rw [hs]
  have e2 : ∫ s in Ioo t₀ T, α s * (deriv Υ (V s) * -Dt s) =
      -∫ s in Ioo t₀ T, α s * deriv Υ (V s) * D s := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
    simp only [hDtD s hs]
    ring
  rw [e1, integral_sub j1 j2, hibp, e2, hVt₀]
  ring

end NonUniqueEuler.Weak
