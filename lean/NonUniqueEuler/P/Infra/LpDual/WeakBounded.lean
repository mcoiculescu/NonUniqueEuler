import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.ConjExponents

/-!
# Proof: weak convergence in `L^p`: boundedness and `L¹` bounds of weak limits (I-LPDUAL)

Proof of `NonUniqueEuler/I/Infra/LpDual/WeakBounded.lean`.

Manuscript: `lem:velocity`(b), `02_prelim.tex:345-357`.

* `exists_eLpNorm_le_of_forall_bdd`: Banach–Steinhaus on the functionals
  `Λₙ φ = ∫ fₙ φ` on the Banach space `Lp ℝ p' μ` (built with Mathlib's `lpPairing`), then the
  norming function `ψ = f |f|^{p-2}` (`‖ψ‖_{p'} = ‖f‖_p^{p-1}`, `∫ f ψ = ‖f‖_p^p`).
* `eLpNorm_one_le_of_tendsto_integral_mul`: test against `φ = 1_A g/|g|` for every measurable `A`
  of finite measure, then exhaust (`lintegral_le_of_forall_fin_meas_le`).
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.LpDual

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-! ### The norming function -/

/-- `|t |t|^{p-2}| = |t|^{p-1}` for `1 < p`. -/
private lemma abs_mul_abs_rpow_sub_two {p : ℝ} (hp : 1 < p) (t : ℝ) :
    |t * |t| ^ (p - 2)| = |t| ^ (p - 1) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [Real.zero_rpow (by linarith : p - 1 ≠ 0)]
  · have ht' : 0 < |t| := abs_pos.mpr ht
    have h : |t| ^ (p - 1) = |t| ^ (1 : ℝ) * |t| ^ (p - 2) := by
      rw [← Real.rpow_add ht']; congr 1; ring
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg t) _), h, Real.rpow_one]

/-- `t (t |t|^{p-2}) = |t|^p` for `1 < p`. -/
private lemma mul_mul_abs_rpow_sub_two {p : ℝ} (hp : 1 < p) (t : ℝ) :
    t * (t * |t| ^ (p - 2)) = |t| ^ p := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [Real.zero_rpow (by linarith : p ≠ 0)]
  · have ht' : 0 < |t| := abs_pos.mpr ht
    have h : |t| ^ p = |t| ^ (2 : ℝ) * |t| ^ (p - 2) := by
      rw [← Real.rpow_add ht']; congr 1; ring
    rw [h, Real.rpow_two, sq_abs, ← mul_assoc, sq]

/-- **Norming.** If `|∫ f ψ| ≤ C ‖ψ‖_{p'}` for every `ψ ∈ L^{p'}`, then `‖f‖_p ≤ C`. -/
private lemma eLpNorm_le_of_forall_abs_integral_mul_le {p : ℝ} (hp : 1 < p) {f : α → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) μ) {C : ℝ}
    (hC : ∀ ψ : α → ℝ, MemLp ψ (ENNReal.ofReal p.conjExponent) μ →
      |∫ x, f x * ψ x ∂μ| ≤ C * (eLpNorm ψ (ENNReal.ofReal p.conjExponent) μ).toReal) :
    eLpNorm f (ENNReal.ofReal p) μ ≤ ENNReal.ofReal C := by
  have hpq : p.HolderConjugate p.conjExponent := Real.HolderConjugate.conjExponent hp
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hqp : p.conjExponent * (p - 1) = p := by rw [mul_comm]; exact hpq.sub_one_mul_conj
  -- the norming function
  set ψ : α → ℝ := fun x => f x * ‖f x‖ ^ (p - 2) with hψ_def
  have hψ_norm : ∀ x, ‖‖f x‖ ^ (p - 1)‖ = ‖ψ x‖ := fun x => by
    simp only [ψ, Real.norm_eq_abs]
    rw [abs_mul_abs_rpow_sub_two hp (f x), abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  have hψ_meas : AEStronglyMeasurable ψ μ :=
    hf.1.mul (hf.1.norm.aemeasurable.pow_const _).aestronglyMeasurable
  have hnorm_rpow : MemLp (fun x => ‖f x‖ ^ (p - 1)) (ENNReal.ofReal p.conjExponent) μ := by
    have h := hf.norm_rpow_div (ENNReal.ofReal (p - 1))
    rwa [ENNReal.toReal_ofReal hp1.le, ← ENNReal.ofReal_div_of_pos hp1] at h
  have hψ_memLp : MemLp ψ (ENNReal.ofReal p.conjExponent) μ :=
    hnorm_rpow.congr_norm hψ_meas (Eventually.of_forall hψ_norm)
  have hψ_eLpNorm : eLpNorm ψ (ENNReal.ofReal p.conjExponent) μ =
      eLpNorm f (ENNReal.ofReal p) μ ^ (p - 1) := by
    rw [← eLpNorm_congr_norm_ae (Eventually.of_forall hψ_norm), eLpNorm_norm_rpow f hp1,
      ← ENNReal.ofReal_mul (by linarith [hpq.symm.lt]), hqp]
  -- `∫ f ψ = ∫ |f|^p = ‖f‖_p^p`
  have hint : ∫ x, f x * ψ x ∂μ = ∫ x, ‖f x‖ ^ p ∂μ :=
    integral_congr_ae (Eventually.of_forall fun x => by
      simp only [ψ, Real.norm_eq_abs]; exact mul_mul_abs_rpow_sub_two hp (f x))
  have hI : eLpNorm f (ENNReal.ofReal p) μ =
      ENNReal.ofReal ((∫ x, ‖f x‖ ^ p ∂μ) ^ p⁻¹) := by
    have h := hf.eLpNorm_eq_integral_rpow_norm (by simpa using hp0) ENNReal.ofReal_ne_top
    rwa [ENNReal.toReal_ofReal hp0.le] at h
  set I : ℝ := ∫ x, ‖f x‖ ^ p ∂μ with hI_def
  have hI0 : 0 ≤ I := integral_nonneg fun x => by positivity
  have hfin : eLpNorm f (ENNReal.ofReal p) μ ≠ ∞ := hf.2.ne
  set a : ℝ := (eLpNorm f (ENNReal.ofReal p) μ).toReal with ha_def
  have ha : a = I ^ p⁻¹ := by
    rw [ha_def, hI, ENNReal.toReal_ofReal (by positivity)]
  have haI : a ^ p = I := by
    rw [ha, ← Real.rpow_mul hI0, inv_mul_cancel₀ hp0.ne', Real.rpow_one]
  have key : a ^ p ≤ C * a ^ (p - 1) := by
    have h1 := hC ψ hψ_memLp
    rw [hint, abs_of_nonneg hI0, hψ_eLpNorm, ← ENNReal.toReal_rpow] at h1
    rw [haI]; exact h1
  rw [← ENNReal.ofReal_toReal hfin]
  rcases (ENNReal.toReal_nonneg (a := eLpNorm f (ENNReal.ofReal p) μ)).eq_or_lt with h0 | hpos
  · rw [← h0, ENNReal.ofReal_zero]; exact bot_le
  · apply ENNReal.ofReal_le_ofReal
    rw [← ha_def] at hpos ⊢
    have hsplit : a ^ p = a * a ^ (p - 1) := by
      conv_lhs => rw [show p = 1 + (p - 1) by ring]
      rw [Real.rpow_add hpos, Real.rpow_one]
    rw [hsplit] at key
    exact le_of_mul_le_mul_right key (Real.rpow_pos_of_pos hpos _)

/-- **Uniform boundedness in `L^p`**, `1 < p < ∞`: if every pairing `n ↦ ∫ fₙ φ`,
`φ ∈ L^{p'}`, is bounded, then `sup_n ‖fₙ‖_{L^p} < ∞`. -/
theorem exists_eLpNorm_le_of_forall_bdd {p : ℝ} (hp : 1 < p) {f : ℕ → α → ℝ}
    (hf : ∀ n, MemLp (f n) (ENNReal.ofReal p) μ)
    (hbdd : ∀ φ : α → ℝ, MemLp φ (ENNReal.ofReal p.conjExponent) μ →
      ∃ C : ℝ, ∀ n, |∫ x, f n x * φ x ∂μ| ≤ C) :
    ∃ N : ℝ≥0∞, N ≠ ∞ ∧ ∀ n, eLpNorm (f n) (ENNReal.ofReal p) μ ≤ N := by
  have hpq : p.HolderConjugate p.conjExponent := Real.HolderConjugate.conjExponent hp
  have : ENNReal.HolderConjugate (ENNReal.ofReal p) (ENNReal.ofReal p.conjExponent) :=
    hpq.ennrealOfReal
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.2 hp.le⟩
  have : Fact (1 ≤ ENNReal.ofReal p.conjExponent) := ⟨ENNReal.one_le_ofReal.2 hpq.symm.lt.le⟩
  let B : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.mul ℝ ℝ
  let Λ : ℕ → Lp ℝ (ENNReal.ofReal p.conjExponent) μ →L[ℝ] ℝ := fun n =>
    B.lpPairing μ (ENNReal.ofReal p) (ENNReal.ofReal p.conjExponent) ((hf n).toLp (f n))
  have hΛ : ∀ n (φ : Lp ℝ (ENNReal.ofReal p.conjExponent) μ),
      Λ n φ = ∫ x, f n x * φ x ∂μ := by
    intro n φ
    simp only [Λ]
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [(hf n).coeFn_toLp] with x hx
    simp [B, hx]
  obtain ⟨C, hC⟩ := banach_steinhaus (g := Λ) fun φ => by
    obtain ⟨C, hC⟩ := hbdd φ (Lp.memLp φ)
    exact ⟨C, fun n => by rw [Real.norm_eq_abs, hΛ]; exact hC n⟩
  refine ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, fun n => ?_⟩
  refine eLpNorm_le_of_forall_abs_integral_mul_le hp (hf n) fun ψ hψ => ?_
  have h1 := (Λ n).le_opNorm (hψ.toLp ψ)
  rw [hΛ, Lp.norm_toLp, Real.norm_eq_abs] at h1
  have h2 : ∫ x, f n x * (hψ.toLp ψ) x ∂μ = ∫ x, f n x * ψ x ∂μ :=
    integral_congr_ae (by filter_upwards [hψ.coeFn_toLp] with x hx; rw [hx])
  rw [h2] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right (hC n) ENNReal.toReal_nonneg)

/-! ### `L¹` bounds of weak limits -/

/-- The `L¹` bound on a set of finite measure, by testing against `1_A g/|g|`. -/
private lemma setLIntegral_enorm_le_of_tendsto_integral_mul {p : ℝ} (hp : 1 < p)
    {f : ℕ → α → ℝ} {g : α → ℝ} (hg : MemLp g (ENNReal.ofReal p) μ)
    (hconv : ∀ φ : α → ℝ, MemLp φ (ENNReal.ofReal p.conjExponent) μ →
      Tendsto (fun n => ∫ x, f n x * φ x ∂μ) atTop (𝓝 (∫ x, g x * φ x ∂μ)))
    {M : ℝ≥0∞} (hM : ∀ n, eLpNorm (f n) 1 μ ≤ M) {A : Set α} (hA : MeasurableSet A)
    (hμA : μ A ≠ ∞) :
    ∫⁻ x in A, ‖g x‖ₑ ∂μ ≤ M := by
  set φ : α → ℝ := A.indicator (fun x => g x / ‖g x‖) with hφ_def
  have hφ_meas : AEStronglyMeasurable φ μ := (hg.1.div₀ hg.1.norm).indicator hA
  have hφ_le_one : ∀ x, ‖φ x‖ ≤ 1 := by
    intro x
    by_cases hx : x ∈ A
    · simp only [φ, Set.indicator_of_mem hx, norm_div, norm_norm]
      exact div_self_le_one _
    · simp [φ, Set.indicator_of_notMem hx]
  have hφ_le : ∀ x, ‖φ x‖ ≤ A.indicator (fun _ => (1 : ℝ)) x := by
    intro x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]; exact hφ_le_one x
    · simp [φ, Set.indicator_of_notMem hx]
  have hφ_memLp : MemLp φ (ENNReal.ofReal p.conjExponent) μ :=
    (memLp_indicator_const _ hA (1 : ℝ) (Or.inr hμA)).mono' hφ_meas
      (Eventually.of_forall hφ_le)
  have hgφ : ∀ x, g x * φ x = A.indicator (fun x => ‖g x‖) x := by
    intro x
    by_cases hx : x ∈ A
    · simp only [φ, Set.indicator_of_mem hx]
      rcases eq_or_ne (g x) 0 with h | h
      · simp [h]
      · have hn : ‖g x‖ ≠ 0 := norm_ne_zero_iff.mpr h
        rw [Real.norm_eq_abs] at hn ⊢
        rw [← mul_div_assoc, ← abs_mul_abs_self, mul_div_assoc, div_self hn, mul_one]
    · simp [φ, Set.indicator_of_notMem hx]
  have hbound : ∀ n, ‖∫ x, f n x * φ x ∂μ‖ₑ ≤ M := by
    intro n
    refine (enorm_integral_le_lintegral_enorm _).trans (le_trans ?_ (hM n))
    rw [eLpNorm_one_eq_lintegral_enorm]
    refine lintegral_mono fun x => ?_
    rw [enorm_mul]
    calc ‖f n x‖ₑ * ‖φ x‖ₑ ≤ ‖f n x‖ₑ * 1 := by
          gcongr
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_one.2 (hφ_le_one x)
      _ = ‖f n x‖ₑ := mul_one _
  have hlim : ‖∫ x, g x * φ x ∂μ‖ₑ ≤ M :=
    le_of_tendsto' ((continuous_enorm.tendsto _).comp (hconv φ hφ_memLp)) hbound
  have hgA : Integrable g (μ.restrict A) := by
    have : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.2 hμA
    exact (hg.restrict A).integrable (ENNReal.one_le_ofReal.2 hp.le)
  have heq : ∫ x, g x * φ x ∂μ = ∫ x in A, ‖g x‖ ∂μ := by
    simp_rw [hgφ]; exact integral_indicator hA
  rwa [heq, Real.enorm_of_nonneg (integral_nonneg fun x => norm_nonneg _),
    ofReal_integral_norm_eq_lintegral_enorm hgA] at hlim

/-- **`L¹` bounds pass to weak `L^p` limits**, `1 < p < ∞`: if `∫ fₙ φ → ∫ g φ` for every
`φ ∈ L^{p'}`, `g ∈ L^p`, and `‖fₙ‖_{L¹} ≤ M`, then `‖g‖_{L¹} ≤ M`. -/
theorem eLpNorm_one_le_of_tendsto_integral_mul [SigmaFinite μ] {p : ℝ} (hp : 1 < p)
    {f : ℕ → α → ℝ} {g : α → ℝ} (hg : MemLp g (ENNReal.ofReal p) μ)
    (hconv : ∀ φ : α → ℝ, MemLp φ (ENNReal.ofReal p.conjExponent) μ →
      Tendsto (fun n => ∫ x, f n x * φ x ∂μ) atTop (𝓝 (∫ x, g x * φ x ∂μ)))
    {M : ℝ≥0∞} (hM : ∀ n, eLpNorm (f n) 1 μ ≤ M) :
    eLpNorm g 1 μ ≤ M := by
  rw [eLpNorm_one_eq_lintegral_enorm]
  exact lintegral_le_of_forall_fin_meas_le M fun A hA hμA =>
    setLIntegral_enorm_le_of_tendsto_integral_mul hp hg hconv hM hA hμA

end NonUniqueEuler.LpDual
