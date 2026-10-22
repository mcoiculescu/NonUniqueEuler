import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# Helper for `lem:sector-sum`(2): the resolvent as a Laplace transform

Generic Banach-algebra fact (`04_ring.tex:1087-1093`): if a bounded operator `A` on a complex
Banach space satisfies `‖exp(tA)‖ ≤ C e^{γt}` for `t ≥ 0`, then every `z` with `Re z > γ` lies in
the resolvent set of `A`, and `‖(z - A)⁻¹‖ ≤ C/(Re z - γ)`.

Proof: with `B = A - z`, `exp(tB) = e^{-zt} exp(tA)` has norm `≤ C e^{-(Re z - γ)t}`, so
`R = ∫_0^∞ exp(tB) dt` converges absolutely in the operator norm. Since
`d/dt exp(tB) = exp(tB) B = B exp(tB)` and `exp(tB) → 0`, the fundamental theorem of calculus on
`(0, ∞)` gives `R B = B R = -1`; hence `z - A = -B` is a unit with inverse `R`, and
`‖R‖ ≤ ∫_0^∞ C e^{-(Re z - γ)t} dt = C/(Re z - γ)`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace NonUniqueEuler.SectorSumH

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- `exp(t(A - z)) = e^{-tz} exp(tA)`. -/
theorem exp_smul_sub_algebraMap (A : E →L[ℂ] E) (z : ℂ) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • (A - algebraMap ℂ (E →L[ℂ] E) z)) =
      Complex.exp (-((t : ℂ) * z)) • NormedSpace.exp ((t : ℂ) • A) := by
  have h1 : (t : ℂ) • (A - algebraMap ℂ (E →L[ℂ] E) z) =
      (t : ℂ) • A + algebraMap ℂ (E →L[ℂ] E) (-((t : ℂ) * z)) := by
    rw [smul_sub, Algebra.smul_def ((t : ℂ)) (algebraMap ℂ (E →L[ℂ] E) z), ← map_mul, map_neg,
      sub_eq_add_neg]
  have hcomm : Commute ((t : ℂ) • A) (algebraMap ℂ (E →L[ℂ] E) (-((t : ℂ) * z))) :=
    (Algebra.commutes _ _).symm
  let +nondep : NormedAlgebra ℚ (E →L[ℂ] E) := .restrictScalars ℚ ℂ _
  rw [h1, NormedSpace.exp_add_of_commute hcomm, ← NormedSpace.algebraMap_exp_comm,
    ← Complex.exp_eq_exp_ℂ, ← Algebra.commutes, ← Algebra.smul_def]

/-- The norm bound for `exp(t(A - z))`. -/
theorem norm_exp_smul_sub_le (A : E →L[ℂ] E) {γ C : ℝ}
    (hA : ∀ t : ℝ, 0 ≤ t → ‖NormedSpace.exp ((t : ℂ) • A)‖ ≤ C * Real.exp (γ * t))
    (z : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    ‖NormedSpace.exp ((t : ℂ) • (A - algebraMap ℂ (E →L[ℂ] E) z))‖ ≤
      C * Real.exp (-(z.re - γ) * t) := by
  rw [exp_smul_sub_algebraMap, norm_smul, Complex.norm_exp]
  have hre : (-((t : ℂ) * z)).re = -(t * z.re) := by simp
  rw [hre]
  calc Real.exp (-(t * z.re)) * ‖NormedSpace.exp ((t : ℂ) • A)‖
      ≤ Real.exp (-(t * z.re)) * (C * Real.exp (γ * t)) :=
        mul_le_mul_of_nonneg_left (hA t ht) (Real.exp_pos _).le
    _ = C * Real.exp (-(z.re - γ) * t) := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        ring

/-- The derivative of `t ↦ exp(tB)` along the reals, on both sides. -/
theorem hasDerivAt_exp_ofReal_smul (B : E →L[ℂ] E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp ((s : ℂ) • B))
        (NormedSpace.exp ((t : ℂ) • B) * B) t ∧
      HasDerivAt (fun s : ℝ => NormedSpace.exp ((s : ℂ) • B))
        (B * NormedSpace.exp ((t : ℂ) • B)) t := by
  have hof := Complex.ofRealCLM.hasDerivAt (x := t)
  constructor
  · simpa [Function.comp_def, Complex.ofRealCLM_apply] using!
      (hasDerivAt_exp_smul_const (𝕂 := ℂ) B (t : ℂ)).scomp t hof
  · simpa [Function.comp_def, Complex.ofRealCLM_apply] using!
      (hasDerivAt_exp_smul_const' (𝕂 := ℂ) B (t : ℂ)).scomp t hof

/-- **The resolvent as a Laplace transform.** If `‖exp(tA)‖ ≤ C e^{γt}` for `t ≥ 0` and
`Re z > γ`, then `z` is in the resolvent set of `A` and `‖(z - A)⁻¹‖ ≤ C/(Re z - γ)`. -/
theorem mem_resolventSet_and_norm_resolvent_le (A : E →L[ℂ] E) {γ C : ℝ}
    (hA : ∀ t : ℝ, 0 ≤ t → ‖NormedSpace.exp ((t : ℂ) • A)‖ ≤ C * Real.exp (γ * t))
    {z : ℂ} (hz : γ < z.re) :
    z ∈ resolventSet ℂ A ∧ ‖resolvent A z‖ ≤ C / (z.re - γ) := by
  set B : E →L[ℂ] E := A - algebraMap ℂ (E →L[ℂ] E) z with hB
  set F : ℝ → (E →L[ℂ] E) := fun s => NormedSpace.exp ((s : ℂ) • B) with hF
  set lam : ℝ := z.re - γ with hlam
  have hlam_pos : 0 < lam := sub_pos.mpr hz
  have hderiv : ∀ t : ℝ, HasDerivAt F (F t * B) t ∧ HasDerivAt F (B * F t) t :=
    fun t => hasDerivAt_exp_ofReal_smul B t
  have hcont : Continuous F := continuous_iff_continuousAt.mpr fun t => (hderiv t).1.continuousAt
  have hbound : ∀ t ∈ Ioi (0 : ℝ), ‖F t‖ ≤ C * Real.exp (-lam * t) := fun t ht =>
    norm_exp_smul_sub_le A hA z (le_of_lt ht)
  have hdom : IntegrableOn (fun t : ℝ => C * Real.exp (-lam * t)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hlam_pos).const_mul C
  have hFint : IntegrableOn F (Ioi 0) := by
    refine Integrable.mono' hdom hcont.aestronglyMeasurable ?_
    exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hbound)
  have hF0 : F 0 = 1 := by simp [hF]
  have hlim : Tendsto F atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => C * Real.exp (-lam * t)) atTop (𝓝 0) := by
      have h2 : Tendsto (fun t : ℝ => -lam * t) atTop atBot :=
        tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hlam_pos)
      simpa using (Real.tendsto_exp_atBot.comp h2).const_mul C
    refine squeeze_zero_norm' ?_ h1
    filter_upwards [eventually_gt_atTop 0] with t ht using hbound t ht
  -- `∫_0^∞ exp(tB) B = -1` and `∫_0^∞ B exp(tB) = -1`.
  have hI1 : ∫ t in Ioi (0 : ℝ), F t * B = -1 := by
    rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont.continuousWithinAt
      (fun t _ => (hderiv t).1) (hFint.mul_const B) hlim, hF0, zero_sub]
  have hI2 : ∫ t in Ioi (0 : ℝ), B * F t = -1 := by
    rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont.continuousWithinAt
      (fun t _ => (hderiv t).2) (hFint.const_mul B) hlim, hF0, zero_sub]
  set R : E →L[ℂ] E := ∫ t in Ioi (0 : ℝ), F t with hR
  have hRB : R * B = -1 := by
    rw [hR, ← integral_mul_const_of_integrable hFint, hI1]
  have hBR : B * R = -1 := by
    rw [hR, ← integral_const_mul_of_integrable hFint, hI2]
  have hzA : algebraMap ℂ (E →L[ℂ] E) z - A = -B := by rw [hB, neg_sub]
  let u : (E →L[ℂ] E)ˣ :=
    ⟨-B, R, by rw [neg_mul, hBR, neg_neg], by rw [mul_neg, hRB, neg_neg]⟩
  have hu : IsUnit (algebraMap ℂ (E →L[ℂ] E) z - A) := ⟨u, hzA.symm⟩
  have hres : resolvent A z = R := by
    rw [resolvent, hzA]
    exact Ring.inverse_unit u
  refine ⟨spectrum.mem_resolventSet_iff.mpr hu, ?_⟩
  rw [hres]
  calc ‖R‖ ≤ ∫ t in Ioi (0 : ℝ), C * Real.exp (-lam * t) :=
        norm_integral_le_of_norm_le hdom
          ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hbound))
    _ = C / lam := by
        rw [integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr hlam_pos) 0]
        simp only [mul_zero, Real.exp_zero]
        field_simp

end NonUniqueEuler.SectorSumH
