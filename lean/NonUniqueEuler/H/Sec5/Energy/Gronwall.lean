import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Helper for `lem:energy`: the Grönwall comparison of the last step

Helper of `P/Sec5/Energy.lean` (`05_single_ring.tex:366-372`). If `y ≥ 0` on `[0,t]`, `y²` has
(one-sided) derivative `q` within `[0,t]` with `q ≤ 2(Λy² + r y)`, `Λ ≥ 0`, and `r ≥ 0` is
continuous on `[0,t]`, then `y(τ) ≤ e^{Λτ} y(0) + ∫₀^τ e^{Λ(τ-σ)} r(σ) dσ`.

Proof as in the manuscript: `y_ε = (y² + ε²)^{1/2}` is differentiable within `[0,t]` with
`y_ε' ≤ Λ y_ε + r`, so `e^{-Λτ}y_ε(τ) - ∫₀^τ e^{-Λσ} r(σ) dσ` is antitone on `[0,t]`
(`antitoneOn_of_hasDerivWithinAt_nonpos`, the fundamental theorem of calculus at interior
points); then `ε → 0`.
-/

noncomputable section

open Set Filter Topology MeasureTheory

namespace NonUniqueEuler.OneRing.EnergyH

/-- `e^{Λτ} ∫₀^τ e^{-Λσ} r(σ) dσ = ∫₀^τ e^{Λ(τ-σ)} r(σ) dσ`. -/
theorem exp_mul_integral_eq (Λ τ : ℝ) (r : ℝ → ℝ) :
    Real.exp (Λ * τ) * ∫ σ in (0 : ℝ)..τ, Real.exp (-(Λ * σ)) * r σ =
      ∫ σ in (0 : ℝ)..τ, Real.exp (Λ * (τ - σ)) * r σ := by
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun σ _ => ?_
  rw [← mul_assoc, ← Real.exp_add]
  ring_nf

/-- The comparison step for a fixed `ε > 0`. -/
theorem le_of_hasDerivWithinAt_sq_eps {y q r : ℝ → ℝ} {t Λ ε : ℝ} (hΛ : 0 ≤ Λ) (hε : 0 < ε)
    (hy : ∀ τ ∈ Icc (0 : ℝ) t, HasDerivWithinAt (fun σ => y σ ^ 2) (q τ) (Icc 0 t) τ)
    (hq : ∀ τ ∈ Icc (0 : ℝ) t, q τ ≤ 2 * (Λ * y τ ^ 2 + r τ * y τ))
    (hr : ContinuousOn r (Icc 0 t)) (hr0 : ∀ τ ∈ Icc (0 : ℝ) t, 0 ≤ r τ) :
    ∀ τ ∈ Icc (0 : ℝ) t, Real.exp (-(Λ * τ)) * Real.sqrt (y τ ^ 2 + ε ^ 2) ≤
      Real.sqrt (y 0 ^ 2 + ε ^ 2) + ∫ σ in (0 : ℝ)..τ, Real.exp (-(Λ * σ)) * r σ := by
  set z : ℝ → ℝ := fun σ => Real.sqrt (y σ ^ 2 + ε ^ 2) with hz
  have hzpos : ∀ σ, 0 < y σ ^ 2 + ε ^ 2 := fun σ => by positivity
  -- derivative of `z` within `[0,t]`
  have hzd : ∀ τ ∈ Icc (0 : ℝ) t,
      HasDerivWithinAt z (q τ / (2 * Real.sqrt (y τ ^ 2 + ε ^ 2))) (Icc 0 t) τ := by
    intro τ hτ
    have h1 : HasDerivWithinAt (fun σ => y σ ^ 2 + ε ^ 2) (q τ) (Icc 0 t) τ :=
      (hy τ hτ).add_const _
    exact h1.sqrt (hzpos τ).ne'
  -- the differential inequality `z' ≤ Λ z + r`
  have hzle : ∀ τ ∈ Icc (0 : ℝ) t,
      q τ / (2 * Real.sqrt (y τ ^ 2 + ε ^ 2)) ≤ Λ * z τ + r τ := by
    intro τ hτ
    have hs := Real.sqrt_pos.2 (hzpos τ)
    have hsq : Real.sqrt (y τ ^ 2 + ε ^ 2) ^ 2 = y τ ^ 2 + ε ^ 2 := Real.sq_sqrt (hzpos τ).le
    have hyz : y τ ≤ Real.sqrt (y τ ^ 2 + ε ^ 2) :=
      (le_abs_self _).trans (Real.abs_le_sqrt (by nlinarith))
    rw [div_le_iff₀ (by positivity)]
    have h1 := hq τ hτ
    have h2 : Λ * y τ ^ 2 ≤ Λ * Real.sqrt (y τ ^ 2 + ε ^ 2) ^ 2 := by
      rw [hsq]; exact mul_le_mul_of_nonneg_left (by nlinarith) hΛ
    have h3 : r τ * y τ ≤ r τ * Real.sqrt (y τ ^ 2 + ε ^ 2) :=
      mul_le_mul_of_nonneg_left hyz (hr0 τ hτ)
    simp only [hz]
    nlinarith
  -- the primitive of `e^{-Λσ} r(σ)`
  set g : ℝ → ℝ := fun σ => Real.exp (-(Λ * σ)) * r σ with hg
  have hgc : ContinuousOn g (Icc 0 t) :=
    ((Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg)).continuousOn).mul hr
  intro τ hτ
  have ht : 0 ≤ t := hτ.1.trans hτ.2
  set F : ℝ → ℝ := fun σ => ∫ u in (0 : ℝ)..σ, g u with hF
  have hFc : ContinuousOn F (Icc 0 t) := by
    have : IntegrableOn g (uIcc 0 t) := by
      rw [uIcc_of_le ht]; exact hgc.integrableOn_compact isCompact_Icc
    have h := intervalIntegral.continuousOn_primitive_interval this
    rwa [uIcc_of_le ht] at h
  set φ : ℝ → ℝ := fun σ => Real.exp (-(Λ * σ)) * z σ - F σ with hφ
  have hzc : ContinuousOn z (Icc 0 t) := fun σ hσ => (hzd σ hσ).continuousWithinAt
  have hφc : ContinuousOn φ (Icc 0 t) :=
    (((Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg)).continuousOn).mul
      hzc).sub hFc
  have hint : interior (Icc (0 : ℝ) t) = Ioo 0 t := interior_Icc
  have hφd : ∀ x ∈ interior (Icc (0 : ℝ) t), HasDerivWithinAt φ
      (-(Λ * Real.exp (-(Λ * x))) * z x +
          Real.exp (-(Λ * x)) * (q x / (2 * Real.sqrt (y x ^ 2 + ε ^ 2))) - g x)
      (interior (Icc 0 t)) x := by
    intro x hx
    rw [hint] at hx
    have hxI : x ∈ Icc (0 : ℝ) t := Ioo_subset_Icc_self hx
    have hnhds : Icc (0 : ℝ) t ∈ 𝓝 x := Icc_mem_nhds hx.1 hx.2
    have hz' : HasDerivAt z (q x / (2 * Real.sqrt (y x ^ 2 + ε ^ 2))) x :=
      (hzd x hxI).hasDerivAt hnhds
    have hexp : HasDerivAt (fun σ => Real.exp (-(Λ * σ))) (Real.exp (-(Λ * x)) * (-(Λ * 1))) x :=
      (((hasDerivAt_id x).const_mul Λ).neg).exp
    have hgx : ContinuousAt g x := (hgc x hxI).continuousAt hnhds
    have hgi : IntervalIntegrable g volume 0 x := by
      refine (hgc.mono ?_).intervalIntegrable
      rw [uIcc_of_le hx.1.le]
      exact Icc_subset_Icc le_rfl hx.2.le
    have hgm : StronglyMeasurableAtFilter g (𝓝 x) volume :=
      (hgc.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo x hx
    have hF' : HasDerivAt F (g x) x := intervalIntegral.integral_hasDerivAt_right hgi hgm hgx
    have := ((hexp.mul hz').sub hF').congr_deriv (show _ = -(Λ * Real.exp (-(Λ * x))) * z x +
          Real.exp (-(Λ * x)) * (q x / (2 * Real.sqrt (y x ^ 2 + ε ^ 2))) - g x by ring)
    exact this.hasDerivWithinAt
  have hφ' : ∀ x ∈ interior (Icc (0 : ℝ) t),
      -(Λ * Real.exp (-(Λ * x))) * z x +
          Real.exp (-(Λ * x)) * (q x / (2 * Real.sqrt (y x ^ 2 + ε ^ 2))) - g x ≤ 0 := by
    intro x hx
    rw [hint] at hx
    have hxI : x ∈ Icc (0 : ℝ) t := Ioo_subset_Icc_self hx
    have h1 := hzle x hxI
    have he := Real.exp_pos (-(Λ * x))
    have h2 : Real.exp (-(Λ * x)) * (q x / (2 * Real.sqrt (y x ^ 2 + ε ^ 2))) ≤
        Real.exp (-(Λ * x)) * (Λ * z x + r x) := mul_le_mul_of_nonneg_left h1 he.le
    simp only [hg]
    nlinarith
  have hanti := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 t) hφc hφd hφ'
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) t := ⟨le_rfl, ht⟩
  have hle := hanti h0 hτ hτ.1
  simp only [hφ, hF, hz, mul_zero, neg_zero, Real.exp_zero, one_mul,
    intervalIntegral.integral_same, sub_zero] at hle
  linarith

/-- **The Grönwall comparison of `lem:energy`** (`05_single_ring.tex:366-372`). -/
theorem le_of_hasDerivWithinAt_sq {y q r : ℝ → ℝ} {t Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hy0 : ∀ τ ∈ Icc (0 : ℝ) t, 0 ≤ y τ)
    (hy : ∀ τ ∈ Icc (0 : ℝ) t, HasDerivWithinAt (fun σ => y σ ^ 2) (q τ) (Icc 0 t) τ)
    (hq : ∀ τ ∈ Icc (0 : ℝ) t, q τ ≤ 2 * (Λ * y τ ^ 2 + r τ * y τ))
    (hr : ContinuousOn r (Icc 0 t)) (hr0 : ∀ τ ∈ Icc (0 : ℝ) t, 0 ≤ r τ) :
    ∀ τ ∈ Icc (0 : ℝ) t,
      y τ ≤ Real.exp (Λ * τ) * y 0 + ∫ σ in (0 : ℝ)..τ, Real.exp (Λ * (τ - σ)) * r σ := by
  intro τ hτ
  have ht : 0 ≤ t := hτ.1.trans hτ.2
  have hy00 := hy0 0 ⟨le_rfl, ht⟩
  have hE := Real.exp_pos (Λ * τ)
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set ε := δ / Real.exp (Λ * τ) with hεdef
  have hε : 0 < ε := div_pos hδ hE
  have hmain := le_of_hasDerivWithinAt_sq_eps hΛ hε hy hq hr hr0 τ hτ
  have hzτ : y τ ≤ Real.sqrt (y τ ^ 2 + ε ^ 2) :=
    (le_abs_self _).trans (Real.abs_le_sqrt (by nlinarith))
  have hz0 : Real.sqrt (y 0 ^ 2 + ε ^ 2) ≤ y 0 + ε := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  -- multiply `hmain` by `e^{Λτ}`
  have hmul := mul_le_mul_of_nonneg_left hmain hE.le
  rw [← mul_assoc, ← Real.exp_add, show Λ * τ + -(Λ * τ) = 0 by ring, Real.exp_zero, one_mul,
    mul_add, exp_mul_integral_eq] at hmul
  have hεE : Real.exp (Λ * τ) * ε = δ := by
    rw [hεdef]; field_simp
  have h4 : Real.exp (Λ * τ) * Real.sqrt (y 0 ^ 2 + ε ^ 2) ≤ Real.exp (Λ * τ) * (y 0 + ε) :=
    mul_le_mul_of_nonneg_left hz0 hE.le
  nlinarith

end NonUniqueEuler.OneRing.EnergyH
