import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Proof: Minkowski's integral inequality (I-CONV)

Proof of `NonUniqueEuler/I/Infra/ConvMinkowski/Minkowski.lean`.

For σ-finite `(α, μ)`, `(β, ν)` and `1 ≤ p < ∞`:
* `lintegral_lintegral_rpow_le`:
  `(∫ (∫ F(x,y) dν(y))^p dμ(x))^{1/p} ≤ ∫ (∫ F(x,y)^p dμ(x))^{1/p} dν(y)`;
* `eLpNorm_lintegral_le`: the same in `eLpNorm` form;
* `eLpNorm_integral_le`: the Bochner form `‖∫ F(·,y) dν(y)‖_{L^p(μ)} ≤ ∫ ‖F(·,y)‖_{L^p(μ)} dν(y)`.

Proof (duality-free, as in the interface docstring). Reduce to measurable `F` (a.e. modification).
`p = 1` is Tonelli. For `p > 1` put `G x = ∫⁻ y, F x y ∂ν` and truncate:
`Hₙ = 1_{Sₙ} · min (G, n)` with `Sₙ = spanningSets μ n`, so `∫⁻ Hₙ^p < ∞`. Then
`∫⁻ Hₙ^p ≤ ∫⁻ Hₙ^{p-1} G = ∫⁻_y ∫⁻_x Hₙ^{p-1} F ≤ (∫⁻ Hₙ^p)^{1/q} · RHS` (Tonelli and Hölder with
`q = p/(p-1)`), whence `(∫⁻ Hₙ^p)^{1/p} ≤ RHS`; finally monotone convergence (`lintegral_iSup`).
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace NonUniqueEuler.Conv

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
  [SigmaFinite μ] [SigmaFinite ν]

namespace MinkowskiAux

/-- The core estimate: for a measurable `H ≤ ∫⁻ F(·, y) dν(y)` with `∫⁻ H^p < ∞` and `p > 1`,
`(∫⁻ H^p)^{1/p}` is bounded by the right-hand side of Minkowski's inequality. -/
theorem core_le {F : α → β → ℝ≥0∞} (hF : Measurable (Function.uncurry F)) {p : ℝ} (hp : 1 < p)
    {H : α → ℝ≥0∞} (hH : Measurable H) (hHG : ∀ x, H x ≤ ∫⁻ y, F x y ∂ν)
    (hfin : ∫⁻ x, H x ^ p ∂μ ≠ ∞) :
    (∫⁻ x, H x ^ p ∂μ) ^ (1 / p) ≤ ∫⁻ y, (∫⁻ x, F x y ^ p ∂μ) ^ (1 / p) ∂ν := by
  set q : ℝ := Real.conjExponent p with hq_def
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hqp : q.HolderConjugate p := hpq.symm
  set A : ℝ≥0∞ := ∫⁻ x, H x ^ p ∂μ with hA
  set R : ℝ≥0∞ := ∫⁻ y, (∫⁻ x, F x y ^ p ∂μ) ^ (1 / p) ∂ν with hR
  have hp0 : 0 < p := by linarith
  have hp1 : 0 ≤ p - 1 := by linarith
  have h1q : 0 ≤ 1 / q := one_div_nonneg.mpr hqp.pos.le
  have h1p : 0 ≤ 1 / p := one_div_nonneg.mpr hp0.le
  have hFy : ∀ y, Measurable fun x => F x y := fun y => hF.of_uncurry_right
  have hFx : ∀ x, Measurable fun y => F x y := fun x => hF.of_uncurry_left
  have hpq_mul : (p - 1) * q = p := by
    rw [hq_def, Real.conjExponent]
    have : p - 1 ≠ 0 := by linarith
    field_simp
  have key : A ≤ A ^ (1 / q) * R := by
    calc A = ∫⁻ x, H x ^ (p - 1) * H x ∂μ := by
          refine lintegral_congr fun x => ?_
          conv_lhs => rw [show p = (p - 1) + 1 by ring]
          rw [ENNReal.rpow_add_of_nonneg _ _ hp1 zero_le_one, ENNReal.rpow_one]
      _ ≤ ∫⁻ x, H x ^ (p - 1) * ∫⁻ y, F x y ∂ν ∂μ :=
          lintegral_mono fun x => mul_le_mul_right (hHG x) _
      _ = ∫⁻ x, ∫⁻ y, H x ^ (p - 1) * F x y ∂ν ∂μ := by
          refine lintegral_congr fun x => ?_
          rw [lintegral_const_mul _ (hFx x)]
      _ = ∫⁻ y, ∫⁻ x, H x ^ (p - 1) * F x y ∂μ ∂ν := by
          apply lintegral_lintegral_swap
          exact (((hH.pow_const _).comp measurable_fst).mul hF).aemeasurable
      _ ≤ ∫⁻ y, A ^ (1 / q) * (∫⁻ x, F x y ^ p ∂μ) ^ (1 / p) ∂ν := by
          refine lintegral_mono fun y => ?_
          have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hqp
            (hH.pow_const (p - 1)).aemeasurable (hFy y).aemeasurable
          simp only [Pi.mul_apply] at h
          refine h.trans_eq ?_
          congr 2
          refine lintegral_congr fun x => ?_
          rw [← ENNReal.rpow_mul, hpq_mul]
      _ = A ^ (1 / q) * R := by
          rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg h1q hfin)]
  by_cases hA0 : A = 0
  · rw [hA0, ENNReal.zero_rpow_of_pos (by positivity)]
    exact zero_le
  have hsum : 1 / q + 1 / p = 1 := by
    rw [one_div, one_div]
    exact hqp.inv_add_inv_eq_one
  have hsplit : A ^ (1 / q) * A ^ (1 / p) = A := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ h1q h1p, hsum, ENNReal.rpow_one]
  have hq0 : A ^ (1 / q) ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hA0) hfin).ne'
  have hqt : A ^ (1 / q) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg h1q hfin
  rw [← ENNReal.mul_le_mul_iff_right hq0 hqt, hsplit]
  exact key

/-- Minkowski's integral inequality for lower integrals, measurable integrand. -/
theorem lintegral_lintegral_rpow_le_of_measurable {F : α → β → ℝ≥0∞}
    (hF : Measurable (Function.uncurry F)) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ x, (∫⁻ y, F x y ∂ν) ^ p ∂μ) ^ (1 / p) ≤ ∫⁻ y, (∫⁻ x, F x y ^ p ∂μ) ^ (1 / p) ∂ν := by
  rcases hp.eq_or_lt with rfl | hp1
  · simp only [ENNReal.rpow_one, div_one]
    exact (lintegral_lintegral_swap hF.aemeasurable).le
  set G : α → ℝ≥0∞ := fun x => ∫⁻ y, F x y ∂ν with hG_def
  have hG : Measurable G := hF.lintegral_prod_right'
  set R : ℝ≥0∞ := ∫⁻ y, (∫⁻ x, F x y ^ p ∂μ) ^ (1 / p) ∂ν with hR
  have hp0 : 0 < p := by linarith
  let H : ℕ → α → ℝ≥0∞ := fun n => (spanningSets μ n).indicator (fun x => min (G x) n)
  have hHm : ∀ n, Measurable (H n) := fun n =>
    (hG.min measurable_const).indicator (measurableSet_spanningSets μ n)
  have hHG : ∀ n x, H n x ≤ G x := fun n x => by
    by_cases hx : x ∈ spanningSets μ n
    · simp only [H, Set.indicator_of_mem hx]
      exact min_le_left _ _
    · simp only [H, Set.indicator_of_notMem hx]
      exact zero_le
  have hfin : ∀ n, ∫⁻ x, H n x ^ p ∂μ ≠ ∞ := by
    intro n
    refine ne_top_of_le_ne_top ?_
      (lintegral_mono (g := (spanningSets μ n).indicator fun _ => (n : ℝ≥0∞) ^ p) ?_)
    · rw [lintegral_indicator_const (measurableSet_spanningSets μ n)]
      exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp0.le (ENNReal.natCast_ne_top n))
        (measure_spanningSets_lt_top μ n).ne
    · intro x
      by_cases hx : x ∈ spanningSets μ n
      · simp only [H, Set.indicator_of_mem hx]
        exact ENNReal.rpow_le_rpow (min_le_right _ _) hp0.le
      · simp only [H, Set.indicator_of_notMem hx, ENNReal.zero_rpow_of_pos hp0]
        exact le_rfl
  have hbound : ∀ n, ∫⁻ x, H n x ^ p ∂μ ≤ R ^ p := fun n => by
    have h := core_le hF hp1 (hHm n) (hHG n) (hfin n)
    have := ENNReal.rpow_le_rpow h hp0.le
    rwa [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one] at this
  have hmono : Monotone H := by
    intro m n hmn x
    by_cases hx : x ∈ spanningSets μ m
    · have hxn : x ∈ spanningSets μ n := monotone_spanningSets μ hmn hx
      simp only [H, Set.indicator_of_mem hx, Set.indicator_of_mem hxn]
      exact min_le_min_left _ (Nat.cast_le.2 hmn)
    · simp only [H, Set.indicator_of_notMem hx]
      exact zero_le
  have hsup : ∀ x, ⨆ n, H n x = G x := by
    intro x
    refine le_antisymm (iSup_le fun n => hHG n x) ?_
    obtain ⟨N, hN⟩ : ∃ N, x ∈ spanningSets μ N := by
      have hx := Set.mem_univ x
      rw [← iUnion_spanningSets μ] at hx
      exact Set.mem_iUnion.1 hx
    have hG_eq : G x = ⨆ n : ℕ, G x ⊓ (n : ℝ≥0∞) := by
      rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
    rw [hG_eq]
    refine iSup_le fun n => le_iSup_of_le (max n N) ?_
    have hx : x ∈ spanningSets μ (max n N) := monotone_spanningSets μ (le_max_right _ _) hN
    simp only [H, Set.indicator_of_mem hx]
    exact min_le_min_left _ (Nat.cast_le.2 (le_max_left _ _))
  have hGp : ∀ x, G x ^ p = ⨆ n, H n x ^ p := by
    intro x
    rw [← hsup x]
    exact Monotone.map_iSup_of_continuousAt (f := fun t : ℝ≥0∞ => t ^ p)
      ENNReal.continuous_rpow_const.continuousAt (ENNReal.monotone_rpow_of_nonneg hp0.le)
      (ENNReal.zero_rpow_of_pos hp0)
  have hint : ∫⁻ x, G x ^ p ∂μ ≤ R ^ p := by
    rw [lintegral_congr hGp, lintegral_iSup (fun n => (hHm n).pow_const p)
      (fun m n hmn x => ENNReal.rpow_le_rpow (hmono hmn x) hp0.le)]
    exact iSup_le hbound
  calc (∫⁻ x, G x ^ p ∂μ) ^ (1 / p) ≤ (R ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hint (by positivity)
    _ = R := by rw [← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one]

end MinkowskiAux

/-- Minkowski's integral inequality for lower integrals. -/
theorem lintegral_lintegral_rpow_le {F : α → β → ℝ≥0∞}
    (hF : AEMeasurable (Function.uncurry F) (μ.prod ν)) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ x, (∫⁻ y, F x y ∂ν) ^ p ∂μ) ^ (1 / p) ≤ ∫⁻ y, (∫⁻ x, F x y ^ p ∂μ) ^ (1 / p) ∂ν := by
  set F' : α → β → ℝ≥0∞ := fun x y => hF.mk _ (x, y) with hF'_def
  have hF' : Measurable (Function.uncurry F') := hF.measurable_mk
  have hae : ∀ᵐ z ∂μ.prod ν, Function.uncurry F z = Function.uncurry F' z := hF.ae_eq_mk
  have h1 : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, F x y = F' x y := Measure.ae_ae_of_ae_prod hae
  have h2 : ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, F x y = F' x y :=
    Measure.ae_ae_of_ae_prod
      ((Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae hae)
  have hL : ∫⁻ x, (∫⁻ y, F x y ∂ν) ^ p ∂μ = ∫⁻ x, (∫⁻ y, F' x y ∂ν) ^ p ∂μ := by
    refine lintegral_congr_ae (h1.mono fun x hx => ?_)
    show (∫⁻ y, F x y ∂ν) ^ p = (∫⁻ y, F' x y ∂ν) ^ p
    rw [lintegral_congr_ae hx]
  have hR : ∫⁻ y, (∫⁻ x, F x y ^ p ∂μ) ^ (1 / p) ∂ν =
      ∫⁻ y, (∫⁻ x, F' x y ^ p ∂μ) ^ (1 / p) ∂ν := by
    refine lintegral_congr_ae (h2.mono fun y hy => ?_)
    show (∫⁻ x, F x y ^ p ∂μ) ^ (1 / p) = (∫⁻ x, F' x y ^ p ∂μ) ^ (1 / p)
    rw [lintegral_congr_ae (hy.mono fun x hx => by rw [hx])]
  rw [hL, hR]
  exact MinkowskiAux.lintegral_lintegral_rpow_le_of_measurable hF' hp

/-- Minkowski's integral inequality, `eLpNorm` form, `[0,∞]`-valued. -/
theorem eLpNorm_lintegral_le {F : α → β → ℝ≥0∞}
    (hF : AEMeasurable (Function.uncurry F) (μ.prod ν)) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hp' : p ≠ ∞) :
    eLpNorm (fun x => ∫⁻ y, F x y ∂ν) p μ ≤ ∫⁻ y, eLpNorm (fun x => F x y) p μ ∂ν := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hpr : 1 ≤ p.toReal := by
    have := ENNReal.toReal_mono hp' hp
    rwa [ENNReal.toReal_one] at this
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp', enorm_eq_self]
  exact lintegral_lintegral_rpow_le hF hpr

/-- Minkowski's integral inequality for Bochner integrals. -/
theorem eLpNorm_integral_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : α → β → E} (hF : AEStronglyMeasurable (Function.uncurry F) (μ.prod ν))
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    eLpNorm (fun x => ∫ y, F x y ∂ν) p μ ≤ ∫⁻ y, eLpNorm (fun x => F x y) p μ ∂ν := by
  have hF' : AEMeasurable (Function.uncurry fun x y => ‖F x y‖ₑ) (μ.prod ν) := hF.enorm
  calc eLpNorm (fun x => ∫ y, F x y ∂ν) p μ
      ≤ eLpNorm (fun x => ∫⁻ y, ‖F x y‖ₑ ∂ν) p μ :=
        eLpNorm_mono_enorm fun x =>
          (enorm_integral_le_lintegral_enorm _).trans_eq (enorm_eq_self _).symm
    _ ≤ ∫⁻ y, eLpNorm (fun x => ‖F x y‖ₑ) p μ ∂ν := eLpNorm_lintegral_le hF' hp hp'
    _ = ∫⁻ y, eLpNorm (fun x => F x y) p μ ∂ν := by simp_rw [eLpNorm_enorm]

end NonUniqueEuler.Conv
