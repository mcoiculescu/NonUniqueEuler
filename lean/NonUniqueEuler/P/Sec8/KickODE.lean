import NonUniqueEuler.Defs.Sec8.All
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Convex.Basic

/-!
# Proof of `I/Sec8/KickODE.lean` (`eq:kick-A`, the kick ODE and the amplitude formula)

Manuscript `08_kick.tex:156-167`. Same declarations as the interface file, now proved.

* `Kick.coef_hasDerivWithinAt`: `c = e^{ζ₀τ}A` solves `c' = ζ₀c + βq` within `I`
  (fundamental theorem of calculus within `I` plus the product rule);
* `Kick.amp_of_ode`: every solution `c` with `c(τ₀) = 0` has `e^{-ζ₀τ}c(τ) = A(τ)` on `I`
  (the difference has zero derivative within the convex set `I` and vanishes at `τ₀`;
  mean value theorem `norm_image_sub_le_of_norm_hasDerivWithin_le` with bound `0`).

Private helpers (in this file): `interval_convex`, `exists_Icc_mem_nhdsWithin` (every point of
`I` has a closed neighbourhood `[τ₀, b]` within `I`; this handles `τ₁ = ∞`),
`hasDerivWithinAt_integral_interval` (FTC within `I`), `amp_hasDerivWithinAt`,
`hasDerivAt_exp_mul`.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace NonUniqueEuler

namespace Kick

/-- The interval `I` is order-connected, hence convex. -/
private theorem interval_convex (τ₀ : ℝ) (τ₁ : EReal) : Convex ℝ (interval τ₀ τ₁) := by
  have h : (interval τ₀ τ₁).OrdConnected :=
    ⟨fun _ hx _ hy _ ht => ⟨hx.1.trans ht.1, (EReal.coe_le_coe_iff.2 ht.2).trans hy.2⟩⟩
  exact h.convex

/-- Every point `τ ∈ I` has a closed interval `[τ₀, b] ∋ τ` contained in `I` that is a
neighbourhood of `τ` within `I`. -/
private theorem exists_Icc_mem_nhdsWithin {τ₀ : ℝ} {τ₁ : EReal} {τ : ℝ}
    (hτ : τ ∈ interval τ₀ τ₁) :
    ∃ b : ℝ, τ ∈ Icc τ₀ b ∧ Icc τ₀ b ⊆ interval τ₀ τ₁ ∧ Icc τ₀ b ∈ 𝓝[interval τ₀ τ₁] τ := by
  induction τ₁ using EReal.rec with
  | bot => exact absurd hτ.2 (by simp)
  | coe r =>
    have hI : interval τ₀ (r : EReal) = Icc τ₀ r := by
      ext t; simp [interval, EReal.coe_le_coe_iff]
    rw [hI] at hτ ⊢
    exact ⟨r, hτ, subset_rfl, self_mem_nhdsWithin⟩
  | top =>
    rw [interval_top] at hτ ⊢
    refine ⟨τ + 1, ⟨hτ, by linarith⟩, Icc_subset_Ici_self, ?_⟩
    have hmem : Ici τ₀ ∩ Iio (τ + 1) ∈ 𝓝[Ici τ₀] τ :=
      inter_mem_nhdsWithin _ (Iio_mem_nhds (by linarith))
    exact mem_of_superset hmem (fun t ht => ⟨ht.1, ht.2.le⟩)

/-- Fundamental theorem of calculus within `I`: for `g` continuous on `I`,
`u ↦ ∫_{τ₀}^u g` has derivative `g τ` within `I` at every `τ ∈ I`. -/
private theorem hasDerivWithinAt_integral_interval {τ₀ : ℝ} {τ₁ : EReal} {g : ℝ → ℂ}
    (hg : ContinuousOn g (interval τ₀ τ₁)) {τ : ℝ} (hτ : τ ∈ interval τ₀ τ₁) :
    HasDerivWithinAt (fun u => ∫ s in τ₀..u, g s) (g τ) (interval τ₀ τ₁) τ := by
  obtain ⟨b, hτb, hsub, hmem⟩ := exists_Icc_mem_nhdsWithin hτ
  have hgb : ContinuousOn g (Icc τ₀ b) := hg.mono hsub
  have : Fact (τ ∈ Icc τ₀ b) := ⟨hτb⟩
  have hint : IntervalIntegrable g volume τ₀ τ :=
    (hgb.mono (uIcc_subset_Icc ⟨le_rfl, hτb.1.trans hτb.2⟩ hτb)).intervalIntegrable
  have h := intervalIntegral.integral_hasDerivWithinAt_right (s := Icc τ₀ b) (t := Icc τ₀ b)
    hint (hgb.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc τ) (hgb τ hτb)
  exact h.mono_of_mem_nhdsWithin hmem

/-- `t ↦ e^{a t}` (`t` real, `a ∈ ℂ`) has derivative `e^{a τ} a`. -/
private theorem hasDerivAt_exp_mul (a : ℂ) (τ : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (a * t)) (Complex.exp (a * τ) * a) τ := by
  have h1 : HasDerivAt (fun t : ℝ => a * (t : ℂ)) a τ := by
    simpa using ((hasDerivAt_id τ).ofReal_comp).const_mul a
  exact h1.cexp

/-- The amplitude `A = Kick.amp` has derivative `β e^{-ζ₀τ} q(τ)` within `I`. -/
private theorem amp_hasDerivWithinAt {ζ₀ β : ℂ} {τ₀ : ℝ} {τ₁ : EReal} {q : ℝ → ℂ}
    (hq : ContinuousOn q (interval τ₀ τ₁)) {τ : ℝ} (hτ : τ ∈ interval τ₀ τ₁) :
    HasDerivWithinAt (amp ζ₀ β τ₀ q) (β * (Complex.exp (-(ζ₀ * τ)) * q τ))
      (interval τ₀ τ₁) τ := by
  have hg : ContinuousOn (fun s : ℝ => Complex.exp (-(ζ₀ * s)) * q s) (interval τ₀ τ₁) := by
    refine ContinuousOn.mul ?_ hq
    exact (Complex.continuous_exp.comp
      ((continuous_const.mul Complex.continuous_ofReal).neg)).continuousOn
  exact (hasDerivWithinAt_integral_interval hg hτ).const_mul β

/-- **The kick setting, existence** (`08_kick.tex:161-163`). `c = e^{ζ₀τ}A`, with `A` given by
`eq:kick-A`, solves `c' = ζ₀c + βq` on `I` (derivatives within `I`); `c(τ₀) = 0` is
`Kick.coef_self`. -/
theorem coef_hasDerivWithinAt {ζ₀ β : ℂ} {τ₀ : ℝ} {τ₁ : EReal} {q : ℝ → ℂ}
    (h : IsSetting ζ₀ β τ₀ τ₁ q) :
    ∀ τ ∈ interval τ₀ τ₁, HasDerivWithinAt (coef ζ₀ β τ₀ q)
      (ζ₀ * coef ζ₀ β τ₀ q τ + β * q τ) (interval τ₀ τ₁) τ := by
  intro τ hτ
  have he := (hasDerivAt_exp_mul ζ₀ τ).hasDerivWithinAt (s := interval τ₀ τ₁)
  have hA := amp_hasDerivWithinAt (ζ₀ := ζ₀) (β := β) h.continuousOn hτ
  have hprod := he.mul hA
  refine hprod.congr_deriv ?_
  have hexp : Complex.exp (ζ₀ * τ) * Complex.exp (-(ζ₀ * τ)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  simp only [coef]
  linear_combination (β * q τ) * hexp

/-- **`eq:kick-A`** (`08_kick.tex:161-167`). If `c' = ζ₀c + βq` on `I` (derivatives within `I`)
and `c(τ₀) = 0`, then `A(τ) = e^{-ζ₀τ}c(τ) = β∫_{τ₀}^τ e^{-ζ₀s}q(s)ds` for every `τ ∈ I`. -/
theorem amp_of_ode {ζ₀ β : ℂ} {τ₀ : ℝ} {τ₁ : EReal} {q : ℝ → ℂ}
    (h : IsSetting ζ₀ β τ₀ τ₁ q) {c : ℝ → ℂ}
    (hc : ∀ τ ∈ interval τ₀ τ₁, HasDerivWithinAt c (ζ₀ * c τ + β * q τ) (interval τ₀ τ₁) τ)
    (hc0 : c τ₀ = 0) :
    ∀ τ ∈ interval τ₀ τ₁, Complex.exp (-(ζ₀ * τ)) * c τ = amp ζ₀ β τ₀ q τ := by
  set B : ℝ → ℂ := fun t => Complex.exp (-(ζ₀ * t)) * c t - amp ζ₀ β τ₀ q t with hB
  have hderiv : ∀ t ∈ interval τ₀ τ₁, HasDerivWithinAt B 0 (interval τ₀ τ₁) t := by
    intro t ht
    have he := (hasDerivAt_exp_mul (-ζ₀) t).hasDerivWithinAt (s := interval τ₀ τ₁)
    have he' : HasDerivWithinAt (fun s : ℝ => Complex.exp (-(ζ₀ * s)))
        (Complex.exp (-(ζ₀ * t)) * (-ζ₀)) (interval τ₀ τ₁) t := by
      simpa only [neg_mul] using he
    have hA := amp_hasDerivWithinAt (ζ₀ := ζ₀) (β := β) h.continuousOn ht
    have hB' := (he'.mul (hc t ht)).sub hA
    refine hB'.congr_deriv ?_
    ring
  have hτ₀ : τ₀ ∈ interval τ₀ τ₁ := ⟨le_rfl, h.lt.le⟩
  intro τ hτ
  have hle := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (C := 0) hderiv
    (fun _ _ => by simp) (interval_convex τ₀ τ₁) hτ₀ hτ
  have hBτ₀ : B τ₀ = 0 := by simp [hB, hc0, amp_self]
  have hzero : B τ = 0 := by
    rw [zero_mul, norm_le_zero_iff, sub_eq_zero, hBτ₀] at hle
    exact hle
  simpa [hB, sub_eq_zero] using hzero

end Kick

end NonUniqueEuler
