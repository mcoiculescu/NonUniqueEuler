import NonUniqueEuler.Defs.Sec3.Compact
import NonUniqueEuler.Defs.Sec3.Transport
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Helpers for `prop:stable`, step 3 (the limit is renormalized): generic lemmas

Helper file of `P/Sec3/Stable/RenormLimit.lean` (`03_compactness.tex:802-815`).

* Derivatives of a test function: bounds, vanishing outside the support, a ball containing the
  spatial projection of the support (adapted from `H/Sec3/Transport/Basic.lean`).
* Renormalizations are Lipschitz with `|Υ(s)| ≤ L|s|`.
* The pointwise estimate of the difference of two transport integrands
  (`abs_renorm_integrand_sub_le`).
* Tonelli's inequality on `I × s` (`lintegral_prodSet_le`), the squared `L²` norm as a
  `lintegral` (`lintegral_enorm_rpow_two`), Hölder with exponents `(2,2)` in `eLpNorm` form
  (`lintegral_enorm_mul_le`).
* `tendsto_lintegral_mul_of_L1_L2`: if `aₙ → 0` in `L¹(μ)`, `aₙ` is bounded in `L²(μ)` and
  `h ∈ L²(μ)`, then `∫ aₙ h → 0` (the weak `L²` convergence step of the manuscript: approximate
  `h` by the bounded function `min(h, K)`).
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace NonUniqueEuler.Compact.RenormLimitAux

/-! ### Derivatives of a test function -/

theorem timeDeriv_eq_fderiv {φ : ℝ × ℂ → ℝ} (hφ : Differentiable ℝ φ) (t : ℝ) (x : ℂ) :
    timeDeriv φ t x = fderiv ℝ φ (t, x) ((1 : ℝ), (0 : ℂ)) := by
  have h1 : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : ℂ)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  exact ((hφ (t, x)).hasFDerivAt.comp_hasDerivAt t h1).deriv

theorem fderiv_slice_eq {φ : ℝ × ℂ → ℝ} (hφ : Differentiable ℝ φ) (t : ℝ) (x : ℂ) :
    fderiv ℝ (fun y => φ (t, y)) x = (fderiv ℝ φ (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ ℂ) :=
  ((hφ (t, x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)).fderiv

theorem spaceDeriv_eq_fderiv {φ : ℝ × ℂ → ℝ} (hφ : Differentiable ℝ φ) (t : ℝ) (x w : ℂ) :
    spaceDeriv φ t x w = fderiv ℝ φ (t, x) ((0 : ℝ), w) := by
  simp only [spaceDeriv, fderiv_slice_eq hφ t x, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply]

theorem differentiable_of_isTestFunction {T : ℝ} {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) :
    Differentiable ℝ φ :=
  hφ.contDiff.differentiable (by simp)

/-- A test function has a bounded derivative. -/
theorem exists_bound_fderiv_of_isTestFunction {T : ℝ} {φ : ℝ × ℂ → ℝ}
    (hφ : IsTestFunction T φ) : ∃ D : ℝ, 0 ≤ D ∧ ∀ p, ‖fderiv ℝ φ p‖ ≤ D := by
  obtain ⟨D, hD⟩ :=
    (hφ.contDiff.continuous_fderiv (by simp)).bounded_above_of_compact_support
      (hφ.hasCompactSupport.fderiv (𝕜 := ℝ))
  exact ⟨D, (norm_nonneg _).trans (hD 0), hD⟩

/-- A test function is bounded. -/
theorem exists_bound_of_isTestFunction {T : ℝ} {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ p, |φ p| ≤ A := by
  obtain ⟨A, hA⟩ := hφ.contDiff.continuous.bounded_above_of_compact_support hφ.hasCompactSupport
  exact ⟨A, (norm_nonneg _).trans (hA 0), fun p => by rw [← Real.norm_eq_abs]; exact hA p⟩

theorem abs_timeDeriv_le {T : ℝ} {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) {D : ℝ}
    (hD : ∀ p, ‖fderiv ℝ φ p‖ ≤ D) (t : ℝ) (x : ℂ) : |timeDeriv φ t x| ≤ D := by
  rw [timeDeriv_eq_fderiv (differentiable_of_isTestFunction hφ), ← Real.norm_eq_abs]
  refine ((fderiv ℝ φ (t, x)).le_opNorm _).trans ?_
  have h1 : ‖((1 : ℝ), (0 : ℂ))‖ = 1 := by simp [Prod.norm_def]
  rw [h1, mul_one]
  exact hD _

theorem abs_spaceDeriv_le {T : ℝ} {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) {D : ℝ}
    (hD : ∀ p, ‖fderiv ℝ φ p‖ ≤ D) (t : ℝ) (x w : ℂ) : |spaceDeriv φ t x w| ≤ D * ‖w‖ := by
  rw [spaceDeriv_eq_fderiv (differentiable_of_isTestFunction hφ), ← Real.norm_eq_abs]
  refine ((fderiv ℝ φ (t, x)).le_opNorm _).trans ?_
  have h1 : ‖((0 : ℝ), w)‖ = ‖w‖ := by simp [Prod.norm_def]
  rw [h1]
  exact mul_le_mul_of_nonneg_right (hD _) (norm_nonneg _)

/-- The operator norm of the spatial derivative is bounded by the bound of `Dφ`. -/
theorem norm_fderiv_slice_le {T : ℝ} {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) {D : ℝ}
    (hD0 : 0 ≤ D) (hD : ∀ p, ‖fderiv ℝ φ p‖ ≤ D) (t : ℝ) (x : ℂ) :
    ‖fderiv ℝ (fun y => φ (t, y)) x‖ ≤ D :=
  ContinuousLinearMap.opNorm_le_bound _ hD0 fun w => by
    rw [Real.norm_eq_abs]; exact abs_spaceDeriv_le hφ hD t x w

/-- The spatial projection of the support of a test function lies in a ball. -/
theorem exists_ball_of_isTestFunction {T : ℝ} {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) :
    ∃ R : ℝ, 0 < R ∧ ∀ p ∈ tsupport φ, p.2 ∈ ball (0 : ℂ) R := by
  obtain ⟨R, hR⟩ :=
    (hφ.hasCompactSupport.isCompact.image continuous_snd).isBounded.subset_ball (0 : ℂ)
  exact ⟨max R 1, lt_of_lt_of_le one_pos (le_max_right _ _),
    fun p hp => ball_subset_ball (le_max_left _ _) (hR (mem_image_of_mem _ hp))⟩

theorem fderiv_eq_zero_of_notMem_tsupport {φ : ℝ × ℂ → ℝ} {p : ℝ × ℂ} (hp : p ∉ tsupport φ) :
    fderiv ℝ φ p = 0 := by
  have : p ∉ tsupport (fderiv ℝ φ) := fun h => hp (tsupport_fderiv_subset ℝ h)
  exact image_eq_zero_of_notMem_tsupport this

/-- Outside the support of `φ`, `∂_tφ + w·∇φ = 0`. -/
theorem timeDeriv_add_spaceDeriv_eq_zero {T : ℝ} {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ)
    {t : ℝ} {x : ℂ} (hp : (t, x) ∉ tsupport φ) (v : ℂ) :
    timeDeriv φ t x + spaceDeriv φ t x v = 0 := by
  have hd := differentiable_of_isTestFunction hφ
  rw [timeDeriv_eq_fderiv hd, spaceDeriv_eq_fderiv hd, fderiv_eq_zero_of_notMem_tsupport hp]
  simp

/-! ### Renormalizations -/

/-- A renormalization satisfies `|Υ(a) - Υ(b)| ≤ L|a - b|` and `|Υ(s)| ≤ L|s|`. -/
theorem exists_lipschitz_of_isRenormalization {Υ : ℝ → ℝ} (hΥ : IsRenormalization Υ) :
    ∃ L : ℝ, 0 ≤ L ∧ (∀ a b, |Υ a - Υ b| ≤ L * |a - b|) ∧ ∀ s, |Υ s| ≤ L * |s| := by
  obtain ⟨C, hC⟩ := hΥ.deriv_bounded
  have hd : Differentiable ℝ Υ := hΥ.contDiff.differentiable one_ne_zero
  have hlip : ∀ a b, |Υ a - Υ b| ≤ C * |a - b| := fun a b => by
    have h := convex_univ.norm_image_sub_le_of_norm_deriv_le (f := Υ) (fun x _ => hd x)
      (fun x _ => by rw [Real.norm_eq_abs]; exact hC x) (mem_univ b) (mem_univ a)
    simpa [Real.norm_eq_abs] using h
  refine ⟨C, (abs_nonneg _).trans (hC 0), hlip, fun s => ?_⟩
  simpa [hΥ.map_zero] using hlip s 0

/-- The pointwise estimate behind `03_compactness.tex:808-813`:
`Υ(a)(τ + ℓw) - Υ(b)(τ + ℓw') = (Υ(a) - Υ(b))τ + Υ(a)ℓ(w - w') + (Υ(a) - Υ(b))ℓw'`. -/
theorem abs_renorm_integrand_sub_le {Υ : ℝ → ℝ} {L D : ℝ} (hL : 0 ≤ L) (_hD : 0 ≤ D)
    (hlip : ∀ a b, |Υ a - Υ b| ≤ L * |a - b|) (hlin : ∀ s, |Υ s| ≤ L * |s|) {τ : ℝ}
    (hτ : |τ| ≤ D) (ℓ : ℂ →L[ℝ] ℝ) (hℓ : ‖ℓ‖ ≤ D) (a b : ℝ) (w w' : ℂ) :
    |Υ a * (τ + ℓ w) - Υ b * (τ + ℓ w')| ≤
      L * D * (|a - b| + |a| * ‖w - w'‖ + |a - b| * ‖w'‖) := by
  have hℓw : ∀ u : ℂ, |ℓ u| ≤ D * ‖u‖ := fun u => by
    rw [← Real.norm_eq_abs]
    exact (ℓ.le_opNorm u).trans (mul_le_mul_of_nonneg_right hℓ (norm_nonneg _))
  have heq : Υ a * (τ + ℓ w) - Υ b * (τ + ℓ w') =
      (Υ a - Υ b) * τ + Υ a * ℓ (w - w') + (Υ a - Υ b) * ℓ w' := by
    rw [map_sub]; ring
  have h1 : |(Υ a - Υ b) * τ| ≤ L * D * |a - b| := by
    rw [abs_mul]
    calc |Υ a - Υ b| * |τ| ≤ (L * |a - b|) * D :=
          mul_le_mul (hlip a b) hτ (abs_nonneg _) (by positivity)
      _ = L * D * |a - b| := by ring
  have h2 : |Υ a * ℓ (w - w')| ≤ L * D * (|a| * ‖w - w'‖) := by
    rw [abs_mul]
    calc |Υ a| * |ℓ (w - w')| ≤ (L * |a|) * (D * ‖w - w'‖) :=
          mul_le_mul (hlin a) (hℓw _) (abs_nonneg _) (by positivity)
      _ = L * D * (|a| * ‖w - w'‖) := by ring
  have h3 : |(Υ a - Υ b) * ℓ w'| ≤ L * D * (|a - b| * ‖w'‖) := by
    rw [abs_mul]
    calc |Υ a - Υ b| * |ℓ w'| ≤ (L * |a - b|) * (D * ‖w'‖) :=
          mul_le_mul (hlip a b) (hℓw _) (abs_nonneg _) (by positivity)
      _ = L * D * (|a - b| * ‖w'‖) := by ring
  rw [heq]
  calc _ ≤ |(Υ a - Υ b) * τ + Υ a * ℓ (w - w')| + |(Υ a - Υ b) * ℓ w'| := abs_add_le _ _
    _ ≤ |(Υ a - Υ b) * τ| + |Υ a * ℓ (w - w')| + |(Υ a - Υ b) * ℓ w'| := by
        gcongr; exact abs_add_le _ _
    _ ≤ L * D * |a - b| + L * D * (|a| * ‖w - w'‖) + L * D * (|a - b| * ‖w'‖) := by
        gcongr
    _ = _ := by ring

/-- The `ℝ≥0∞` form of `abs_renorm_integrand_sub_le`. -/
theorem enorm_renorm_integrand_sub_le {Υ : ℝ → ℝ} {L D : ℝ} (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hlip : ∀ a b, |Υ a - Υ b| ≤ L * |a - b|) (hlin : ∀ s, |Υ s| ≤ L * |s|) {τ : ℝ}
    (hτ : |τ| ≤ D) (ℓ : ℂ →L[ℝ] ℝ) (hℓ : ‖ℓ‖ ≤ D) (a b : ℝ) (w w' : ℂ) :
    ‖Υ a * (τ + ℓ w) - Υ b * (τ + ℓ w')‖ₑ ≤
      ENNReal.ofReal (L * D) * (‖a - b‖ₑ + ‖a‖ₑ * ‖w - w'‖ₑ + ‖a - b‖ₑ * ‖w'‖ₑ) := by
  have h := abs_renorm_integrand_sub_le hL hD hlip hlin hτ ℓ hℓ a b w w'
  rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
    ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (abs_nonneg _),
    ← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_add (abs_nonneg _) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal h

/-! ### Lebesgue integrals -/

/-- Tonelli's inequality on a product set `I × s` (no measurability needed). -/
theorem lintegral_prodSet_le (I : Set ℝ) (s : Set ℂ) (F : ℝ × ℂ → ℝ≥0∞) :
    ∫⁻ p in I ×ˢ s, F p ≤ ∫⁻ t in I, ∫⁻ x in s, F (t, x) := by
  rw [Measure.volume_eq_prod ℝ ℂ, ← Measure.prod_restrict]
  exact lintegral_prod_le F

/-- `∫ ‖f‖² = ‖f‖_{L²}²`. -/
theorem lintegral_enorm_rpow_two {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] (f : α → E) :
    ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ = eLpNorm f 2 μ ^ (2 : ℝ) := by
  rw [eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat,
    lintegral_rpow_enorm_eq_rpow_eLpNorm' two_pos]

/-- Hölder's inequality with exponents `(2, 2)`. -/
theorem lintegral_enorm_mul_le {α E F : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedAddCommGroup F] {f : α → E} {g : α → F}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    ∫⁻ x, ‖f x‖ₑ * ‖g x‖ₑ ∂μ ≤ eLpNorm f 2 μ * eLpNorm g 2 μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf.enorm hg.enorm
  simp only [Pi.mul_apply] at h
  refine h.trans (le_of_eq ?_)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat]

/-- **Weak `L²` convergence from `L¹` convergence and an `L²` bound.** If `aₙ → 0` in `L¹(μ)`,
`∫ aₙ² ≤ C`, and `h ∈ L²(μ)`, then `∫ aₙ h → 0`. For `K ≥ 0`,
`∫ aₙ h ≤ K ∫ aₙ + C^{1/2} (∫ (h - K)₊²)^{1/2}` (Hölder), and `∫ (h - K)₊² → 0` as `K → ∞`
(dominated convergence). -/
theorem tendsto_lintegral_mul_of_L1_L2 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {a : ℕ → α → ℝ≥0∞} {h : α → ℝ≥0∞} {C : ℝ≥0∞} (hC : C ≠ ∞)
    (ha : ∀ n, AEMeasurable (a n) μ) (hh : AEMeasurable h μ)
    (h1 : Tendsto (fun n => ∫⁻ x, a n x ∂μ) atTop (𝓝 0))
    (h2 : ∀ n, ∫⁻ x, a n x ^ (2 : ℝ) ∂μ ≤ C)
    (hh2 : ∫⁻ x, h x ^ (2 : ℝ) ∂μ ≠ ∞) :
    Tendsto (fun n => ∫⁻ x, a n x * h x ∂μ) atTop (𝓝 0) := by
  have hfin : ∀ᵐ x ∂μ, h x ≠ ∞ := by
    filter_upwards [ae_lt_top' (hh.pow_const (2 : ℝ)) hh2] with x hx hx'
    rw [hx', ENNReal.top_rpow_of_pos (by norm_num)] at hx
    exact lt_irrefl _ hx
  have htail : Tendsto (fun K : ℕ => ∫⁻ x, (h x - K) ^ (2 : ℝ) ∂μ) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence'
      (F := fun (K : ℕ) x => (h x - (K : ℝ≥0∞)) ^ (2 : ℝ)) (f := fun _ => 0)
      (fun x => h x ^ (2 : ℝ)) (fun K => (hh.sub_const _).pow_const _)
      (fun K => Eventually.of_forall fun x => ENNReal.rpow_le_rpow tsub_le_self (by norm_num))
      hh2 (hfin.mono fun x hx => ?_)
    · simpa using this
    · obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hx
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop N] with K hK
      have hK' : h x - (K : ℝ≥0∞) = 0 :=
        tsub_eq_zero_of_le (hN.le.trans (by exact_mod_cast hK))
      rw [hK', ENNReal.zero_rpow_of_pos (by norm_num)]
  have hbound : ∀ (K : ℝ≥0∞) n, ∫⁻ x, a n x * h x ∂μ ≤
      (∫⁻ x, a n x ∂μ) * K +
        C ^ (1 / 2 : ℝ) * (∫⁻ x, (h x - K) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
    intro K n
    calc ∫⁻ x, a n x * h x ∂μ ≤ ∫⁻ x, (a n x * K + a n x * (h x - K)) ∂μ := by
          refine lintegral_mono fun x => ?_
          rw [← mul_add]
          gcongr
          exact le_add_tsub
      _ = (∫⁻ x, a n x ∂μ) * K + ∫⁻ x, a n x * (h x - K) ∂μ := by
          rw [lintegral_add_left' ((ha n).mul_const K), lintegral_mul_const'' K (ha n)]
      _ ≤ _ := by
          gcongr
          calc ∫⁻ x, a n x * (h x - K) ∂μ ≤ (∫⁻ x, a n x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
                (∫⁻ x, (h x - K) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) :=
                ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two (ha n)
                  (hh.sub_const K)
            _ ≤ _ := by gcongr; exact h2 n
  have hδ : Tendsto (fun K : ℕ =>
      C ^ (1 / 2 : ℝ) * (∫⁻ x, (h x - K) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun K : ℕ => (∫⁻ x, (h x - K) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)) atTop
        (𝓝 0) := by
      have := ((ENNReal.continuous_rpow_const (y := 1 / 2)).tendsto 0).comp htail
      simpa [Function.comp_def, ENNReal.zero_rpow_of_pos] using this
    have := ENNReal.Tendsto.const_mul h0
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg (y := 1 / 2) (by norm_num) hC))
    simpa using this
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε2 : (0 : ℝ≥0∞) < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨K, hK⟩ := (hδ.eventually (eventually_le_nhds hε2)).exists
  have hA : Tendsto (fun n => (∫⁻ x, a n x ∂μ) * (K : ℝ≥0∞)) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inr (ENNReal.natCast_ne_top K))
  filter_upwards [hA.eventually (eventually_le_nhds hε2)] with n hn
  calc _ ≤ _ := hbound K n
    _ ≤ ε / 2 + ε / 2 := add_le_add hn hK
    _ = ε := ENNReal.add_halves ε

end NonUniqueEuler.Compact.RenormLimitAux
