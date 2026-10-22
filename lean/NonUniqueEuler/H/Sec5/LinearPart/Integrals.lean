import NonUniqueEuler.Defs.Sec2.Conventions
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Helpers for `lem:linear-part`: the elementary integrals

Helper of `P/Sec5/LinearPart.lean` (fully proved). Namespace
`NonUniqueEuler.OneRing.LinearPartH`. Manuscript `05_single_ring.tex:646-649`:
`∫₀ᵘ e^{σ'(u-v)}⟨v⟩^p dv ≤ ⟨u⟩^pe^{σ'u}/σ'` and
`∫₀ᵘ e^{σ'(u-v)}e^{σv} dv ≤ e^{σu}/(σ - σ') ≤ e^{σu}/(σ_b - σ')`.

* `jap_le_jap`: `⟨v⟩ ≤ ⟨u⟩` for `0 ≤ v ≤ u`;
* `integral_exp_sub`, `integral_exp_mul`: `∫₀ᵘ e^{c(u-v)} dv = ∫₀ᵘ e^{cv} dv = (e^{cu} - 1)/c`;
* `pointwise_bound`: `e^{σ'(u-v)}(A⟨v⟩^p + E e^{σv}) ≤ A⟨u⟩^p e^{σ'(u-v)} + E e^{σ'u}e^{(σ-σ')v}`
  for `0 ≤ v ≤ u`;
* `scalar_bound`: the integral of the right side is at most
  `A⟨u⟩^pe^{σ'u}/σ' + E e^{σu}/(σ_b - σ')` when `0 < σ' < σ_b ≤ σ`.
-/

noncomputable section

open MeasureTheory Set intervalIntegral

namespace NonUniqueEuler.OneRing.LinearPartH

/-- `⟨v⟩ ≤ ⟨u⟩` for `0 ≤ v ≤ u`. -/
theorem jap_le_jap {u v : ℝ} (hv : 0 ≤ v) (hvu : v ≤ u) : Prelim.jap v ≤ Prelim.jap u := by
  unfold Prelim.jap
  apply Real.sqrt_le_sqrt
  nlinarith

/-- `∫₀ᵘ e^{c(u-v)} dv = (e^{cu} - 1)/c`. -/
theorem integral_exp_sub {c : ℝ} (hc : c ≠ 0) (u : ℝ) :
    ∫ v in (0 : ℝ)..u, Real.exp (c * (u - v)) = (Real.exp (c * u) - 1) / c := by
  have hd : ∀ v ∈ uIcc (0 : ℝ) u, HasDerivAt (fun v => -Real.exp (c * (u - v)) / c)
      (Real.exp (c * (u - v))) v := by
    intro v _
    have h1 : HasDerivAt (fun v => c * (u - v)) (c * (-1)) v := by
      simpa using ((hasDerivAt_id v).const_sub u).const_mul c
    have h2 : HasDerivAt (fun v => -Real.exp (c * (u - v)) / c)
        (-(Real.exp (c * (u - v)) * (c * -1)) / c) v := (h1.exp.neg).div_const c
    exact h2.congr_deriv (by field_simp)
  rw [integral_eq_sub_of_hasDerivAt hd]
  · simp only [sub_self, mul_zero, Real.exp_zero, sub_zero]
    ring
  · exact (by fun_prop : Continuous fun v => Real.exp (c * (u - v))).intervalIntegrable _ _

/-- `∫₀ᵘ e^{cv} dv = (e^{cu} - 1)/c`. -/
theorem integral_exp_mul {c : ℝ} (hc : c ≠ 0) (u : ℝ) :
    ∫ v in (0 : ℝ)..u, Real.exp (c * v) = (Real.exp (c * u) - 1) / c := by
  have hd : ∀ v ∈ uIcc (0 : ℝ) u, HasDerivAt (fun v => Real.exp (c * v) / c)
      (Real.exp (c * v)) v := by
    intro v _
    have h1 : HasDerivAt (fun v => c * v) (c * 1) v := (hasDerivAt_id v).const_mul c
    have h2 : HasDerivAt (fun v => Real.exp (c * v) / c) (Real.exp (c * v) * (c * 1) / c) v :=
      h1.exp.div_const c
    exact h2.congr_deriv (by field_simp)
  rw [integral_eq_sub_of_hasDerivAt hd]
  · simp only [mul_zero, Real.exp_zero]
    ring
  · exact (by fun_prop : Continuous fun v => Real.exp (c * v)).intervalIntegrable _ _

/-- The pointwise bound of the Duhamel integrand (`05_single_ring.tex:646-649`). -/
theorem pointwise_bound {σ' σ u v A E : ℝ} (p : ℕ) (hv : 0 ≤ v) (hvu : v ≤ u) (hA : 0 ≤ A) :
    Real.exp (σ' * (u - v)) * (A * Prelim.jap v ^ p + E * Real.exp (σ * v)) ≤
      A * Prelim.jap u ^ p * Real.exp (σ' * (u - v)) +
        E * Real.exp (σ' * u) * Real.exp ((σ - σ') * v) := by
  have hj : Prelim.jap v ^ p ≤ Prelim.jap u ^ p :=
    pow_le_pow_left₀ (Prelim.jap_nonneg v) (jap_le_jap hv hvu) p
  have he : Real.exp (σ' * (u - v)) * Real.exp (σ * v) =
      Real.exp (σ' * u) * Real.exp ((σ - σ') * v) := by
    rw [← Real.exp_add, ← Real.exp_add]
    ring_nf
  have hpos := (Real.exp_pos (σ' * (u - v))).le
  have h1 : Real.exp (σ' * (u - v)) * (A * Prelim.jap v ^ p) ≤
      A * Prelim.jap u ^ p * Real.exp (σ' * (u - v)) := by
    have : A * Prelim.jap v ^ p ≤ A * Prelim.jap u ^ p := mul_le_mul_of_nonneg_left hj hA
    nlinarith
  calc Real.exp (σ' * (u - v)) * (A * Prelim.jap v ^ p + E * Real.exp (σ * v))
      = Real.exp (σ' * (u - v)) * (A * Prelim.jap v ^ p) +
          E * (Real.exp (σ' * (u - v)) * Real.exp (σ * v)) := by ring
    _ ≤ A * Prelim.jap u ^ p * Real.exp (σ' * (u - v)) +
          E * Real.exp (σ' * u) * Real.exp ((σ - σ') * v) := by
        rw [he]
        linarith

/-- The integral of the majorant of `pointwise_bound` (`05_single_ring.tex:646-649`): for
`0 < σ' < σ_b ≤ σ`, `0 ≤ u`, `A, E ≥ 0`,
`∫₀ᵘ (A⟨u⟩^pe^{σ'(u-v)} + E e^{σ'u}e^{(σ-σ')v}) dv ≤ A⟨u⟩^pe^{σ'u}/σ' + E e^{σu}/(σ_b - σ')`. -/
theorem scalar_bound {σ' σb σ u A E : ℝ} (p : ℕ) (h1 : 0 < σ') (h2 : σ' < σb) (h3 : σb ≤ σ)
    (hu : 0 ≤ u) (hA : 0 ≤ A) (hE : 0 ≤ E) :
    IntervalIntegrable (fun v => A * Prelim.jap u ^ p * Real.exp (σ' * (u - v)) +
        E * Real.exp (σ' * u) * Real.exp ((σ - σ') * v)) volume 0 u ∧
      ∫ v in (0 : ℝ)..u, (A * Prelim.jap u ^ p * Real.exp (σ' * (u - v)) +
          E * Real.exp (σ' * u) * Real.exp ((σ - σ') * v)) ≤
        A * Prelim.jap u ^ p * Real.exp (σ' * u) / σ' +
          E * Real.exp (σ * u) / (σb - σ') := by
  have hc1 : Continuous fun v : ℝ => A * Prelim.jap u ^ p * Real.exp (σ' * (u - v)) := by
    fun_prop
  have hc2 : Continuous fun v : ℝ => E * Real.exp (σ' * u) * Real.exp ((σ - σ') * v) := by
    fun_prop
  refine ⟨(hc1.add hc2).intervalIntegrable _ _, ?_⟩
  have hd : 0 < σ - σ' := by linarith
  have hd' : 0 < σb - σ' := by linarith
  rw [integral_add (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_exp_sub h1.ne', integral_exp_mul hd.ne']
  have hJ : 0 ≤ A * Prelim.jap u ^ p := mul_nonneg hA (pow_nonneg (Prelim.jap_nonneg u) p)
  have i1 : A * Prelim.jap u ^ p * ((Real.exp (σ' * u) - 1) / σ') ≤
      A * Prelim.jap u ^ p * Real.exp (σ' * u) / σ' := by
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hJ
    exact div_le_div_of_nonneg_right (by linarith) h1.le
  have hx1 : 1 ≤ Real.exp ((σ - σ') * u) := Real.one_le_exp (mul_nonneg hd.le hu)
  have hx0 : 0 ≤ (Real.exp ((σ - σ') * u) - 1) / (σ - σ') := div_nonneg (by linarith) hd.le
  have hx : (Real.exp ((σ - σ') * u) - 1) / (σ - σ') ≤ Real.exp ((σ - σ') * u) / (σb - σ') := by
    calc (Real.exp ((σ - σ') * u) - 1) / (σ - σ') ≤ Real.exp ((σ - σ') * u) / (σ - σ') :=
          div_le_div_of_nonneg_right (by linarith) hd.le
      _ ≤ Real.exp ((σ - σ') * u) / (σb - σ') :=
          div_le_div_of_nonneg_left (Real.exp_pos _).le hd' (by linarith)
  have hexp : Real.exp (σ' * u) * Real.exp ((σ - σ') * u) = Real.exp (σ * u) := by
    rw [← Real.exp_add]
    ring_nf
  have i2 : E * Real.exp (σ' * u) * ((Real.exp ((σ - σ') * u) - 1) / (σ - σ')) ≤
      E * Real.exp (σ * u) / (σb - σ') := by
    have hE' : 0 ≤ E * Real.exp (σ' * u) := mul_nonneg hE (Real.exp_pos _).le
    calc E * Real.exp (σ' * u) * ((Real.exp ((σ - σ') * u) - 1) / (σ - σ'))
        ≤ E * Real.exp (σ' * u) * (Real.exp ((σ - σ') * u) / (σb - σ')) :=
          mul_le_mul_of_nonneg_left hx hE'
      _ = E * (Real.exp (σ' * u) * Real.exp ((σ - σ') * u)) / (σb - σ') := by ring
      _ = E * Real.exp (σ * u) / (σb - σ') := by rw [hexp]
  linarith

end NonUniqueEuler.OneRing.LinearPartH
