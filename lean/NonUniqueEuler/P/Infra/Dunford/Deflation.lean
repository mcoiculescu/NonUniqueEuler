import Mathlib.Analysis.SpecialFunctions.Exponential
import NonUniqueEuler.Defs.Infra.Dunford
import NonUniqueEuler.I.Infra.Dunford.Uniform

/-!
# Proof (I-DUNF): deflation of a simple eigenvalue and the spectral-gap bound

Proof of `NonUniqueEuler/I/Infra/Dunford/Deflation.lean` (same declarations, same statements).

Let `X` be a complex Banach space, `A, P : X →L[ℂ] X` with `P² = P` and `A P = P A = z₀ P`,
and `Ã = deflate A P z₀ μ₀ = A - (z₀ - μ₀) P`.

* Spectrum (D5). For `z ≠ μ₀`, if some `R` satisfies `(z - A) R = R (z - A) = 1 - P` and
  `P R = R P = 0`, then `R + (z - μ₀)⁻¹ P` is a two-sided inverse of `z - Ã`
  (`Deflation.isUnit_sub_deflate`). For `z ∉ spectrum A`, `z ≠ z₀`, the operator
  `R = (z - A)⁻¹ - (z - z₀)⁻¹ P` has these properties (`Deflation.laurent_identities`); at
  `z = z₀` the Laurent limit `R₀` of this operator has them as well, by passing to the limit
  `z → z₀` (`𝓝[≠] z₀`).
* `exp(B) Q = e^c Q` whenever `B Q = c Q`, in any complex Banach algebra
  (`Deflation.exp_mul_of_mul_eq_smul`; termwise on the exponential series).
* `exp(tA)(1 - P) = exp(tÃ)(1 - P)` since `tA = tÃ + t(z₀ - μ₀)P` with commuting summands and
  `P (1 - P) = 0`; then `exp(tÃ) P = e^{tμ₀} P`.
* Gap bounds: `μ₀ = σ - 1`, the spectrum of `Ã` lies in `{Re < σ}`, and the exponential bounds
  of `I/Infra/Dunford/Uniform.lean` are applied to `Ã` (to `k ↦ Ã k`, continuous on `K`, in
  the uniform case, with `sup_K ‖P k‖ < ∞` by compactness).
-/

noncomputable section

open Filter Topology Metric Set

namespace NonUniqueEuler.Dunford

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable {A P : X →L[ℂ] X} {z₀ : ℂ}

namespace Deflation

/-- In a complex Banach algebra, `B Q = c Q` implies `exp(B) Q = e^c Q`. -/
theorem exp_mul_of_mul_eq_smul {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸]
    [CompleteSpace 𝔸] {B Q : 𝔸} {c : ℂ} (h : B * Q = c • Q) :
    NormedSpace.exp B * Q = Complex.exp c • Q := by
  have hpow : ∀ n : ℕ, B ^ n * Q = c ^ n • Q := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', mul_assoc, ih, mul_smul_comm, h, smul_smul, pow_succ]
  rw [NormedSpace.exp_eq_tsum ℂ, ← (NormedSpace.expSeries_summable' (𝕂 := ℂ) B).tsum_mul_right]
  simp_rw [smul_mul_assoc, hpow, smul_smul]
  rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum ℂ]
  simp only [smul_eq_mul]
  exact (NormedSpace.expSeries_summable' (𝕂 := ℂ) c).tsum_smul_const Q

/-- `exp (x + y) = exp x * exp y` for commuting elements of a complex Banach algebra. -/
theorem exp_add_of_commute {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸]
    [CompleteSpace 𝔸] {x y : 𝔸} (hxy : Commute x y) :
    NormedSpace.exp (x + y) = NormedSpace.exp x * NormedSpace.exp y :=
  NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ) hxy
    ((NormedSpace.expSeries_radius_eq_top ℂ 𝔸).symm ▸ edist_lt_top _ _)
    ((NormedSpace.expSeries_radius_eq_top ℂ 𝔸).symm ▸ edist_lt_top _ _)

omit [CompleteSpace X] in
/-- `algebraMap z * T = z • T`. -/
theorem algebraMap_mul (z : ℂ) (T : X →L[ℂ] X) : algebraMap ℂ (X →L[ℂ] X) z * T = z • T :=
  (Algebra.smul_def z T).symm

omit [CompleteSpace X] in
/-- `T * algebraMap z = z • T`. -/
theorem mul_algebraMap (z : ℂ) (T : X →L[ℂ] X) : T * algebraMap ℂ (X →L[ℂ] X) z = z • T := by
  rw [← Algebra.commutes, algebraMap_mul]

omit [CompleteSpace X] in
/-- `(z - A) P = (z - z₀) P`. -/
theorem sub_mul_proj (hAP : A * P = z₀ • P) (z : ℂ) :
    (algebraMap ℂ (X →L[ℂ] X) z - A) * P = (z - z₀) • P := by
  rw [sub_mul, algebraMap_mul, hAP, sub_smul]

omit [CompleteSpace X] in
/-- `P (z - A) = (z - z₀) P`. -/
theorem proj_mul_sub (hPA : P * A = z₀ • P) (z : ℂ) :
    P * (algebraMap ℂ (X →L[ℂ] X) z - A) = (z - z₀) • P := by
  rw [mul_sub, mul_algebraMap, hPA, sub_smul]

omit [CompleteSpace X] in
/-- `(z - Ã) P = (z - μ₀) P`. -/
theorem sub_deflate_mul_proj (hP : P * P = P) (hAP : A * P = z₀ • P) (z μ₀ : ℂ) :
    (algebraMap ℂ (X →L[ℂ] X) z - deflate A P z₀ μ₀) * P = (z - μ₀) • P := by
  have : algebraMap ℂ (X →L[ℂ] X) z - deflate A P z₀ μ₀ =
      (algebraMap ℂ (X →L[ℂ] X) z - A) + (z₀ - μ₀) • P := by
    simp only [deflate]; abel
  rw [this, add_mul, sub_mul_proj hAP, smul_mul_assoc, hP]
  module

omit [CompleteSpace X] in
/-- `P (z - Ã) = (z - μ₀) P`. -/
theorem proj_mul_sub_deflate (hP : P * P = P) (hPA : P * A = z₀ • P) (z μ₀ : ℂ) :
    P * (algebraMap ℂ (X →L[ℂ] X) z - deflate A P z₀ μ₀) = (z - μ₀) • P := by
  have : algebraMap ℂ (X →L[ℂ] X) z - deflate A P z₀ μ₀ =
      (algebraMap ℂ (X →L[ℂ] X) z - A) + (z₀ - μ₀) • P := by
    simp only [deflate]; abel
  rw [this, mul_add, proj_mul_sub hPA, mul_smul_comm, hP]
  module

omit [CompleteSpace X] in
/-- **Inverse of the deflated resolvent**: if `R` inverts `z - A` on the range of `1 - P` and
kills the range of `P` on both sides, then `z - Ã` is invertible for `z ≠ μ₀`, with inverse
`R + (z - μ₀)⁻¹ P`. -/
theorem isUnit_sub_deflate (hP : P * P = P) (hAP : A * P = z₀ • P) (hPA : P * A = z₀ • P)
    {μ₀ z : ℂ} (hz : z ≠ μ₀) {R : X →L[ℂ] X}
    (h1 : (algebraMap ℂ (X →L[ℂ] X) z - A) * R = 1 - P)
    (h2 : R * (algebraMap ℂ (X →L[ℂ] X) z - A) = 1 - P)
    (h3 : P * R = 0) (h4 : R * P = 0) :
    IsUnit (algebraMap ℂ (X →L[ℂ] X) z - deflate A P z₀ μ₀) := by
  have hzμ : z - μ₀ ≠ 0 := sub_ne_zero.mpr hz
  have hsplit : algebraMap ℂ (X →L[ℂ] X) z - deflate A P z₀ μ₀ =
      (algebraMap ℂ (X →L[ℂ] X) z - A) + (z₀ - μ₀) • P := by
    simp only [deflate]; abel
  have hDP := sub_deflate_mul_proj hP hAP z μ₀
  have hPD := proj_mul_sub_deflate hP hPA z μ₀
  refine ⟨⟨algebraMap ℂ (X →L[ℂ] X) z - deflate A P z₀ μ₀, R + (z - μ₀)⁻¹ • P, ?_, ?_⟩, rfl⟩
  · rw [mul_add, mul_smul_comm, hDP, smul_smul, inv_mul_cancel₀ hzμ, one_smul, hsplit,
      add_mul, h1, smul_mul_assoc, h3, smul_zero, add_zero, sub_add_cancel]
  · rw [add_mul, smul_mul_assoc, hPD, smul_smul, inv_mul_cancel₀ hzμ, one_smul, hsplit,
      mul_add, h2, mul_smul_comm, h4, smul_zero, add_zero, sub_add_cancel]

omit [CompleteSpace X] in
/-- For `z` in the resolvent set of `A`, `z ≠ z₀`, the operator
`R = (z - A)⁻¹ - (z - z₀)⁻¹ P` satisfies `(z - A) R = R (z - A) = 1 - P` and `P R = R P = 0`. -/
theorem laurent_identities (hP : P * P = P) (hAP : A * P = z₀ • P) (hPA : P * A = z₀ • P)
    {z : ℂ} (hz : z ∈ resolventSet ℂ A) (hz₀ : z ≠ z₀) :
    (algebraMap ℂ (X →L[ℂ] X) z - A) * (resolvent A z - (z - z₀)⁻¹ • P) = 1 - P ∧
      (resolvent A z - (z - z₀)⁻¹ • P) * (algebraMap ℂ (X →L[ℂ] X) z - A) = 1 - P ∧
      P * (resolvent A z - (z - z₀)⁻¹ • P) = 0 ∧
      (resolvent A z - (z - z₀)⁻¹ • P) * P = 0 := by
  set T := algebraMap ℂ (X →L[ℂ] X) z - A with hT
  set S := resolvent A z with hS
  have hzz : z - z₀ ≠ 0 := sub_ne_zero.mpr hz₀
  have hu : IsUnit T := spectrum.mem_resolventSet_iff.mp hz
  have hTS : T * S = 1 := Ring.mul_inverse_cancel T hu
  have hST : S * T = 1 := Ring.inverse_mul_cancel T hu
  have hTP : T * P = (z - z₀) • P := sub_mul_proj hAP z
  have hPT : P * T = (z - z₀) • P := proj_mul_sub hPA z
  -- `S P = (z - z₀)⁻¹ P` and `P S = (z - z₀)⁻¹ P`
  have hSP : S * P = (z - z₀)⁻¹ • P := by
    have : S * (T * P) = P := by rw [← mul_assoc, hST, one_mul]
    rw [hTP, mul_smul_comm] at this
    calc S * P = (z - z₀)⁻¹ • ((z - z₀) • (S * P)) := by
          rw [smul_smul, inv_mul_cancel₀ hzz, one_smul]
      _ = (z - z₀)⁻¹ • P := by rw [this]
  have hPS : P * S = (z - z₀)⁻¹ • P := by
    have : (P * T) * S = P := by rw [mul_assoc, hTS, mul_one]
    rw [hPT, smul_mul_assoc] at this
    calc P * S = (z - z₀)⁻¹ • ((z - z₀) • (P * S)) := by
          rw [smul_smul, inv_mul_cancel₀ hzz, one_smul]
      _ = (z - z₀)⁻¹ • P := by rw [this]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mul_sub, hTS, mul_smul_comm, hTP, smul_smul, inv_mul_cancel₀ hzz, one_smul]
  · rw [sub_mul, hST, smul_mul_assoc, hPT, smul_smul, inv_mul_cancel₀ hzz, one_smul]
  · rw [mul_sub, hPS, mul_smul_comm, hP, sub_self]
  · rw [sub_mul, hSP, smul_mul_assoc, hP, sub_self]

omit [CompleteSpace X] in
/-- At `z = z₀`, the Laurent limit `R₀` of `(z - A)⁻¹ - (z - z₀)⁻¹ P` satisfies
`(z₀ - A) R₀ = R₀ (z₀ - A) = 1 - P` and `P R₀ = R₀ P = 0`. -/
theorem laurent_limit_identities (h : IsSimpleSpectralProj A P z₀) {R₀ : X →L[ℂ] X}
    (hR₀ : Tendsto (fun z => resolvent A z - (z - z₀)⁻¹ • P) (𝓝[≠] z₀) (𝓝 R₀)) :
    (algebraMap ℂ (X →L[ℂ] X) z₀ - A) * R₀ = 1 - P ∧
      R₀ * (algebraMap ℂ (X →L[ℂ] X) z₀ - A) = 1 - P ∧
      P * R₀ = 0 ∧ R₀ * P = 0 := by
  have hev : ∀ᶠ z in 𝓝[≠] z₀, z ∈ resolventSet ℂ A ∧ z ≠ z₀ :=
    h.eventually_mem_resolventSet.and self_mem_nhdsWithin
  have hId : ∀ᶠ z in 𝓝[≠] z₀,
      (algebraMap ℂ (X →L[ℂ] X) z - A) * (resolvent A z - (z - z₀)⁻¹ • P) = 1 - P ∧
      (resolvent A z - (z - z₀)⁻¹ • P) * (algebraMap ℂ (X →L[ℂ] X) z - A) = 1 - P ∧
      P * (resolvent A z - (z - z₀)⁻¹ • P) = 0 ∧
      (resolvent A z - (z - z₀)⁻¹ • P) * P = 0 :=
    hev.mono fun z hz => laurent_identities h.idem h.mul_proj h.proj_mul hz.1 hz.2
  have hT : Tendsto (fun z : ℂ => algebraMap ℂ (X →L[ℂ] X) z - A) (𝓝[≠] z₀)
      (𝓝 (algebraMap ℂ (X →L[ℂ] X) z₀ - A)) :=
    (((continuous_algebraMap ℂ (X →L[ℂ] X)).sub continuous_const).tendsto z₀).mono_left
      nhdsWithin_le_nhds
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact tendsto_nhds_unique ((hT.mul hR₀).congr' (hId.mono fun z hz => hz.1))
      tendsto_const_nhds
  · exact tendsto_nhds_unique ((hR₀.mul hT).congr' (hId.mono fun z hz => hz.2.1))
      tendsto_const_nhds
  · exact tendsto_nhds_unique ((tendsto_const_nhds.mul hR₀).congr'
      (hId.mono fun z hz => hz.2.2.1)) tendsto_const_nhds
  · exact tendsto_nhds_unique ((hR₀.mul tendsto_const_nhds).congr'
      (hId.mono fun z hz => hz.2.2.2)) tendsto_const_nhds

omit [CompleteSpace X] in
/-- `‖e^{t(σ - 1)} P‖ ≤ e^{σ t} ‖P‖` for `t ≥ 0`. -/
theorem norm_cexp_smul_le (Q : X →L[ℂ] X) (σ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ‖Complex.exp ((t : ℂ) * ((σ - 1 : ℝ) : ℂ)) • Q‖ ≤ Real.exp (σ * t) * ‖Q‖ := by
  rw [norm_smul, Complex.norm_exp]
  gcongr
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    nlinarith

end Deflation

open Deflation

set_option linter.unusedSectionVars false in
/-- **(D5) Deflation**: the deflated operator has the spectrum of `A` with `z₀` replaced by
`μ₀`. -/
theorem IsSimpleSpectralProj.spectrum_deflate_subset (h : IsSimpleSpectralProj A P z₀)
    (μ₀ : ℂ) : spectrum ℂ (deflate A P z₀ μ₀) ⊆ (spectrum ℂ A \ {z₀}) ∪ {μ₀} := by
  intro z hz
  by_contra hcon
  simp only [mem_union, Set.mem_sdiff, mem_singleton_iff, not_or, not_and, not_not] at hcon
  obtain ⟨hzA, hzμ⟩ := hcon
  rw [spectrum.mem_iff] at hz
  apply hz
  by_cases hzz : z = z₀
  · subst hzz
    obtain ⟨R₀, hR₀⟩ := h.laurent
    obtain ⟨h1, h2, h3, h4⟩ := laurent_limit_identities h hR₀
    exact isUnit_sub_deflate h.idem h.mul_proj h.proj_mul hzμ h1 h2 h3 h4
  · have hzr : z ∈ resolventSet ℂ A := Classical.not_not.mp fun hs => hzz (hzA hs)
    obtain ⟨h1, h2, h3, h4⟩ := laurent_identities h.idem h.mul_proj h.proj_mul hzr hzz
    exact isUnit_sub_deflate h.idem h.mul_proj h.proj_mul hzμ h1 h2 h3 h4

/-- On the range of `P`, `exp(tA)` acts as `e^{t z₀}`. -/
theorem exp_mul_proj (hAP : A * P = z₀ • P) (t : ℂ) :
    NormedSpace.exp (t • A) * P = Complex.exp (t * z₀) • P :=
  exp_mul_of_mul_eq_smul (by rw [smul_mul_assoc, hAP, smul_smul])

/-- `exp(tA)(1 - P) = exp(tÃ) - e^{t μ₀} P` for the deflated operator `Ã`. -/
theorem exp_mul_one_sub_proj (hP : P * P = P) (hAP : A * P = z₀ • P) (hPA : P * A = z₀ • P)
    (μ₀ t : ℂ) :
    NormedSpace.exp (t • A) * (1 - P) =
      NormedSpace.exp (t • deflate A P z₀ μ₀) - Complex.exp (t * μ₀) • P := by
  have hDP : deflate A P z₀ μ₀ * P = μ₀ • P := by
    rw [deflate, sub_mul, hAP, smul_mul_assoc, hP]; module
  have hPD : P * deflate A P z₀ μ₀ = μ₀ • P := by
    rw [deflate, mul_sub, hPA, mul_smul_comm, hP]; module
  have hcomm : Commute (t • deflate A P z₀ μ₀) (t • ((z₀ - μ₀) • P)) := by
    refine ((Commute.smul_left ?_ t).smul_right t)
    refine (Commute.smul_right ?_ (z₀ - μ₀))
    exact hDP.trans hPD.symm
  have hsplit : t • A = t • deflate A P z₀ μ₀ + t • ((z₀ - μ₀) • P) := by
    rw [deflate, ← smul_add, sub_add_cancel]
  have h0 : NormedSpace.exp (t • ((z₀ - μ₀) • P)) * (1 - P) = 1 - P := by
    have := exp_mul_of_mul_eq_smul (B := t • ((z₀ - μ₀) • P)) (Q := 1 - P) (c := 0)
      (by rw [smul_mul_assoc, smul_mul_assoc, mul_sub, mul_one, hP, sub_self, smul_zero,
        smul_zero, zero_smul])
    rwa [Complex.exp_zero, one_smul] at this
  rw [hsplit, Deflation.exp_add_of_commute hcomm, mul_assoc, h0, mul_sub, mul_one,
    exp_mul_of_mul_eq_smul (B := t • deflate A P z₀ μ₀) (Q := P) (c := t * μ₀)
      (by rw [smul_mul_assoc, hDP, smul_smul])]

/-- **Spectral-gap bound** for a single operator: `‖exp(tA)(1 - P)‖ ≤ C e^{σt}` for `t ≥ 0` if
the spectrum of `A` other than `z₀` lies in `{Re < σ}`. -/
theorem IsSimpleSpectralProj.exists_norm_exp_mul_one_sub_le (h : IsSimpleSpectralProj A P z₀)
    {σ : ℝ} (hσ : ∀ z ∈ spectrum ℂ A, z ≠ z₀ → z.re < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      ‖NormedSpace.exp ((t : ℂ) • A) * (1 - P)‖ ≤ C * Real.exp (σ * t) := by
  set μ₀ : ℂ := ((σ - 1 : ℝ) : ℂ) with hμ₀
  have hspec : ∀ z ∈ spectrum ℂ (deflate A P z₀ μ₀), z.re < σ := by
    intro z hz
    rcases h.spectrum_deflate_subset μ₀ hz with ⟨hzA, hz0⟩ | hzμ
    · exact hσ z hzA hz0
    · rw [mem_singleton_iff.mp hzμ, hμ₀, Complex.ofReal_re]
      linarith
  obtain ⟨C, hC, hCb⟩ := exists_norm_exp_le_of_spectrum_re_lt (deflate A P z₀ μ₀) hspec
  refine ⟨C + ‖P‖, by positivity, fun t ht => ?_⟩
  rw [exp_mul_one_sub_proj h.idem h.mul_proj h.proj_mul μ₀]
  calc ‖NormedSpace.exp ((t : ℂ) • deflate A P z₀ μ₀) - Complex.exp ((t : ℂ) * μ₀) • P‖
      ≤ ‖NormedSpace.exp ((t : ℂ) • deflate A P z₀ μ₀)‖ + ‖Complex.exp ((t : ℂ) * μ₀) • P‖ :=
        norm_sub_le _ _
    _ ≤ C * Real.exp (σ * t) + Real.exp (σ * t) * ‖P‖ :=
        add_le_add (hCb t ht) (norm_cexp_smul_le P σ ht)
    _ = (C + ‖P‖) * Real.exp (σ * t) := by ring

/-- **Uniform spectral-gap bound** for continuous families on a compact set. -/
theorem exists_norm_exp_mul_one_sub_le_uniform {κ : Type*} [TopologicalSpace κ] {K : Set κ}
    (hK : IsCompact K) {A P : κ → X →L[ℂ] X} {z₀ : κ → ℂ} (hA : ContinuousOn A K)
    (hP : ContinuousOn P K) (hz₀ : ContinuousOn z₀ K)
    (h : ∀ k ∈ K, IsSimpleSpectralProj (A k) (P k) (z₀ k)) {σ : ℝ}
    (hσ : ∀ k ∈ K, ∀ z ∈ spectrum ℂ (A k), z ≠ z₀ k → z.re < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k ∈ K, ∀ t : ℝ, 0 ≤ t →
      ‖NormedSpace.exp ((t : ℂ) • A k) * (1 - P k)‖ ≤ C * Real.exp (σ * t) := by
  set μ₀ : ℂ := ((σ - 1 : ℝ) : ℂ) with hμ₀
  have hD : ContinuousOn (fun k => deflate (A k) (P k) (z₀ k) μ₀) K := by
    simp only [deflate]
    exact hA.sub ((hz₀.sub continuousOn_const).smul hP)
  have hspec : ∀ k ∈ K, ∀ z ∈ spectrum ℂ (deflate (A k) (P k) (z₀ k) μ₀), z.re < σ := by
    intro k hk z hz
    rcases (h k hk).spectrum_deflate_subset μ₀ hz with ⟨hzA, hz0⟩ | hzμ
    · exact hσ k hk z hzA hz0
    · rw [mem_singleton_iff.mp hzμ, hμ₀, Complex.ofReal_re]
      linarith
  obtain ⟨C, hC, hCb⟩ := exists_norm_exp_le_of_spectrum_re_lt_uniform hK hD hspec
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hP
  refine ⟨C + max M 0, by positivity, fun k hk t ht => ?_⟩
  rw [exp_mul_one_sub_proj (h k hk).idem (h k hk).mul_proj (h k hk).proj_mul μ₀]
  calc ‖NormedSpace.exp ((t : ℂ) • deflate (A k) (P k) (z₀ k) μ₀) -
          Complex.exp ((t : ℂ) * μ₀) • P k‖
      ≤ ‖NormedSpace.exp ((t : ℂ) • deflate (A k) (P k) (z₀ k) μ₀)‖ +
          ‖Complex.exp ((t : ℂ) * μ₀) • P k‖ := norm_sub_le _ _
    _ ≤ C * Real.exp (σ * t) + Real.exp (σ * t) * max M 0 := by
        refine add_le_add (hCb k hk t ht) ((norm_cexp_smul_le (P k) σ ht).trans ?_)
        gcongr
        exact (hM k hk).trans (le_max_left _ _)
    _ = (C + max M 0) * Real.exp (σ * t) := by ring

end NonUniqueEuler.Dunford
