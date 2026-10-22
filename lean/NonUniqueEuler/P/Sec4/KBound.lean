import NonUniqueEuler.Defs.Sec4.Operators
import NonUniqueEuler.I.Sec4.Elliptic
import NonUniqueEuler.I.Infra.SobolevOneD.MultiplierLocal
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Proof: `cor:K-bound` (the coupling `k_ℓ𝒢_ℓ` gains `(1+ℓ²)^{-1/2}`)

Proof of `NonUniqueEuler/I/Sec4/KBound.lean` (same declaration, same statement).
Manuscript `04_ring.tex:900-922`.

Write `k_ℓ(r) = (ℓ i)·b(r)` with `b(r) = ω̄'(r)/r`, smooth on `(0, ∞)`, vanishing on `(0, ∞)`
outside `[r₁, r₂] ⊂ [ρ₋, ρ₊]`, with `|b^{(i)}| ≤ M₁` on `[ρ₋, ρ₊]` for `i ≤ s` (compactness).
For `ψ = 𝒢_ℓ g`:
* `lem:elliptic` (`SectorSetting.elliptic` with `k = s`, `I = [ρ₋, ρ₊]`):
  `ψ ∈ H^{s+2}((0,∞))` and `‖ψ‖²_{s+2,ℓ} ≤ C_E ‖g‖²_{s,ℓ}`;
* the multiplier bound for multipliers vanishing off `[ρ₋, ρ₊]`
  (`Sob.secNormSq_mul_le_of_vanish`, `I/Infra/SobolevOneD/MultiplierLocal.lean`):
  `k_ℓψ ∈ H^s((0,∞))` and `‖k_ℓψ‖²_{s,ℓ} ≤ 4^{s+1} ℓ² M₁² ‖ψ‖²_{s,ℓ}`;
* the weights: `(1+ℓ²)² ‖ψ‖²_{s,ℓ} ≤ ‖ψ‖²_{s+2,ℓ}` (`secNormSq_mul_le_add_two`), since
  `(1+ℓ²)^{s+2-j} = (1+ℓ²)²(1+ℓ²)^{s-j}` for `j ≤ s`;
* `ℓ²(1+ℓ²)^{-2} ≤ (1+ℓ²)^{-1}`.
So `C_K = 4^{s+1} (M₁² + 1) C_E`.
-/

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace NonUniqueEuler

namespace SectorSetting

namespace KBoundAux

/-- `ω̄'` is smooth on the line. -/
theorem dom_contDiff {S : SectorSetting} (hS : S.Valid) : ContDiff ℝ ∞ S.dom := by
  have h : ContDiff ℝ ∞ S.omR := hS.contDiff.comp Complex.ofRealCLM.contDiff
  exact (contDiff_infty_iff_deriv.mp h).2

/-- The real profile `b(r) = ω̄'(r)/r` of the coupling coefficient. -/
def bfun (S : SectorSetting) (r : ℝ) : ℂ := ((S.dom r / r : ℝ) : ℂ)

theorem kcoef_eq (S : SectorSetting) (ℓ : ℤ) :
    S.kcoef ℓ = fun r => ((ℓ : ℂ) * Complex.I) * bfun S r := by
  funext r
  simp only [kcoef, bfun, Complex.ofReal_div]
  ring

theorem bfun_contDiffOn {S : SectorSetting} (hS : S.Valid) (n : ℕ) :
    ContDiffOn ℝ n (bfun S) (Ioi 0) := by
  have h1 : ContDiffOn ℝ n (fun r : ℝ => S.dom r / r) (Ioi 0) :=
    ((dom_contDiff hS).of_le (by exact_mod_cast le_top)).contDiffOn.div contDiffOn_id
      (fun r hr => ne_of_gt hr)
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn h1

theorem kcoef_contDiffOn {S : SectorSetting} (hS : S.Valid) (ℓ : ℤ) (n : ℕ) :
    ContDiffOn ℝ n (S.kcoef ℓ) (Ioi 0) := by
  rw [kcoef_eq]
  exact contDiffOn_const.mul (bfun_contDiffOn hS n)

theorem iteratedDeriv_kcoef (S : SectorSetting) (ℓ : ℤ) (i : ℕ) (r : ℝ) :
    iteratedDeriv i (S.kcoef ℓ) r = ((ℓ : ℂ) * Complex.I) * iteratedDeriv i (bfun S) r := by
  rw [kcoef_eq]
  exact iteratedDeriv_const_mul_field _ _

/-- Uniform bounds of the derivatives of `b` on `[ρ₋, ρ₊]`. -/
theorem exists_bfun_bound {S : SectorSetting} (hS : S.Valid) (s : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i ≤ s, ∀ r ∈ Icc S.ρm S.ρp, ‖iteratedDeriv i (bfun S) r‖ ≤ M := by
  have hsub : Icc S.ρm S.ρp ⊆ Ioi 0 := fun r hr => lt_of_lt_of_le hS.ρm_pos hr.1
  have hcont : ∀ i ≤ s, ContinuousOn (iteratedDeriv i (bfun S)) (Ioi 0) := by
    intro i hi
    have h := (bfun_contDiffOn hS s).continuousOn_iteratedDerivWithin (m := i)
      (by exact_mod_cast hi) (isOpen_Ioi.uniqueDiffOn)
    exact h.congr fun r hr => (iteratedDerivWithin_of_isOpen isOpen_Ioi hr).symm
  have hF : ContinuousOn
      (fun r => ∑ i ∈ Finset.range (s + 1), ‖iteratedDeriv i (bfun S) r‖) (Icc S.ρm S.ρp) := by
    refine continuousOn_finsetSum _ fun i hi => ?_
    exact ((hcont i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).mono hsub).norm
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hF
  refine ⟨max C 0, le_max_right _ _, fun i hi r hr => ?_⟩
  have h1 : ‖iteratedDeriv i (bfun S) r‖ ≤
      ∑ j ∈ Finset.range (s + 1), ‖iteratedDeriv j (bfun S) r‖ :=
    Finset.single_le_sum (f := fun j => ‖iteratedDeriv j (bfun S) r‖)
      (fun j _ => norm_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  have h2 := hC r hr
  rw [Real.norm_eq_abs] at h2
  exact h1.trans ((le_abs_self _).trans (h2.trans (le_max_left _ _)))

/-- `k_ℓ` vanishes on `(0, ∞)` off `[r₁, r₂]`. -/
theorem kcoef_eq_zero {S : SectorSetting} (hS : S.Valid) (ℓ : ℤ) {r : ℝ} (hr : 0 < r)
    (hrI : r ∉ Icc S.r₁ S.r₂) : S.kcoef ℓ r = 0 := by
  simp only [kcoef, hS.dom_eq_zero r hr hrI, Complex.ofReal_zero, mul_zero, zero_div]

/-- The weight gain `(1+ℓ²)² ‖ψ‖²_{s,ℓ;I} ≤ ‖ψ‖²_{s+2,ℓ;I}`. -/
theorem secNormSq_mul_le_add_two (s : ℕ) (ℓ : ℤ) {I : Set ℝ} (hIm : MeasurableSet I)
    (hI : I ⊆ Ici 0) (f : ℝ → ℂ) :
    (1 + (ℓ : ℝ) ^ 2) ^ 2 * Sob.secNormSq s ℓ I f ≤ Sob.secNormSq (s + 2) ℓ I f := by
  have hX : ∀ j, 0 ≤ ∫ r in I, ‖Sob.weakDeriv1On (Ioi 0) j f r‖ ^ 2 * r := fun j =>
    setIntegral_nonneg hIm fun r hr => mul_nonneg (sq_nonneg _) (hI hr)
  unfold Sob.secNormSq
  rw [Finset.mul_sum]
  calc ∑ j ∈ Finset.range (s + 1), (1 + (ℓ : ℝ) ^ 2) ^ 2 *
        (Sob.secWeight s j ℓ * ∫ r in I, ‖Sob.weakDeriv1On (Ioi 0) j f r‖ ^ 2 * r)
      = ∑ j ∈ Finset.range (s + 1),
          Sob.secWeight (s + 2) j ℓ * ∫ r in I, ‖Sob.weakDeriv1On (Ioi 0) j f r‖ ^ 2 * r := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjs : j ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hexp : s + 2 - j = 2 + (s - j) := by omega
        simp only [Sob.secWeight, hexp, pow_add]
        ring
    _ ≤ ∑ j ∈ Finset.range (s + 2 + 1),
          Sob.secWeight (s + 2) j ℓ * ∫ r in I, ‖Sob.weakDeriv1On (Ioi 0) j f r‖ ^ 2 * r := by
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr (by omega)) fun j _ _ => ?_
        exact mul_nonneg (Sob.secWeight_nonneg _ _ _) (hX j)

/-- The final arithmetic: `A (|ℓ|M)² X ≤ A (M²+1) C_E (1+ℓ²)⁻¹ Z` from
`(1+ℓ²)² X ≤ Y ≤ C_E Z`. -/
theorem arith {A M CE q X Y Z : ℝ} (hA : 0 ≤ A) (hq : 0 ≤ q) (hCE : 0 < CE)
    (hZ0 : 0 ≤ Z) (h2 : (1 + q) ^ 2 * X ≤ Y) (h3 : Y ≤ CE * Z) :
    A * (q * M ^ 2) * X ≤ A * (M ^ 2 + 1) * CE * (1 + q)⁻¹ * Z := by
  have hL : 0 < 1 + q := by linarith
  have hXb : X ≤ CE * Z / (1 + q) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hm : 0 ≤ M ^ 2 := sq_nonneg M
  have key : q * M ^ 2 * X ≤ (M ^ 2 + 1) * CE * (1 + q)⁻¹ * Z := by
    calc q * M ^ 2 * X ≤ q * M ^ 2 * (CE * Z / (1 + q) ^ 2) :=
          mul_le_mul_of_nonneg_left hXb (by positivity)
      _ = (q / (1 + q)) * (M ^ 2 * CE * (1 + q)⁻¹ * Z) := by
          field_simp
      _ ≤ 1 * (M ^ 2 * CE * (1 + q)⁻¹ * Z) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [div_le_one hL]
          linarith
      _ ≤ (M ^ 2 + 1) * CE * (1 + q)⁻¹ * Z := by
          rw [one_mul]
          have h0 : 0 ≤ CE * (1 + q)⁻¹ * Z := by positivity
          nlinarith
  calc A * (q * M ^ 2) * X = A * (q * M ^ 2 * X) := by ring
    _ ≤ A * ((M ^ 2 + 1) * CE * (1 + q)⁻¹ * Z) := mul_le_mul_of_nonneg_left key hA
    _ = A * (M ^ 2 + 1) * CE * (1 + q)⁻¹ * Z := by ring

end KBoundAux

open KBoundAux in
/-- `cor:K-bound`: there is `C_K` with `‖k_ℓ𝒢_ℓ g‖²_{s,ℓ} ≤ C_K (1+ℓ²)⁻¹ ‖g‖²_{s,ℓ}` for every
`ℓ ≠ 0` and every `g ∈ H^s((0,∞))` supported in `[ρ₋,ρ₊]`; moreover `k_ℓ𝒢_ℓ g ∈ H^s((0,∞))` and
it vanishes off `[r₁, r₂]`. -/
theorem K_bound (S : SectorSetting) (hS : S.Valid) (s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ℓ : ℤ, ℓ ≠ 0 → ∀ g : ℝ → ℂ, Sob.MemH1On s (Ioi 0) g →
      (∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), r ∉ Icc S.ρm S.ρp → g r = 0) →
        Sob.MemH1On s (Ioi 0) (S.KsecFn ℓ g) ∧
          (∀ r : ℝ, 0 < r → r ∉ Icc S.r₁ S.r₂ → S.KsecFn ℓ g r = 0) ∧
          S.secNormSq s ℓ (S.KsecFn ℓ g) ≤ C * (1 + (ℓ : ℝ) ^ 2)⁻¹ * S.secNormSq s ℓ g := by
  obtain ⟨CE, hCE, hell⟩ :=
    elliptic s hS.ρm_pos hS.ρm_lt_ρp hS.ρm_pos hS.ρm_lt_ρp.le
  obtain ⟨M, hM0, hM⟩ := exists_bfun_bound hS s
  refine ⟨4 ^ (s + 1) * (M ^ 2 + 1) * CE, by positivity, ?_⟩
  intro ℓ hℓ g hg hsupp
  obtain ⟨hψ, hψn⟩ := hell ℓ hℓ g hg hsupp
  have hψs : Sob.MemH1On s (Ioi 0) (green ℓ g) := hψ.mono_order (by omega)
  have hsubI : Icc S.r₁ S.r₂ ⊆ Icc S.ρm S.ρp :=
    Icc_subset_Icc hS.ρm_lt_r₁.le hS.r₂_lt_ρp.le
  have hvan : ∀ r : ℝ, 0 < r → r ∉ Icc S.ρm S.ρp → S.kcoef ℓ r = 0 := fun r hr hrI =>
    kcoef_eq_zero hS ℓ hr fun h => hrI (hsubI h)
  have hbd : ∀ i ≤ s, ∀ r ∈ Icc S.ρm S.ρp, ‖iteratedDeriv i (S.kcoef ℓ) r‖ ≤ |(ℓ : ℝ)| * M := by
    intro i hi r hr
    rw [iteratedDeriv_kcoef, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_intCast]
    exact mul_le_mul_of_nonneg_left (hM i hi r hr) (abs_nonneg _)
  obtain ⟨hmem, hnorm⟩ := Sob.secNormSq_mul_le_of_vanish (k := s) hS.ρm_pos
    (kcoef_contDiffOn hS ℓ s) hvan hbd hψs ℓ
  refine ⟨hmem, fun r hr hrI => ?_, ?_⟩
  · simp only [KsecFn, kcoef_eq_zero hS ℓ hr hrI, zero_mul]
  · have hIm : MeasurableSet (Icc S.ρm S.ρp) := measurableSet_Icc
    have hI0 : Icc S.ρm S.ρp ⊆ Ici 0 := fun r hr => hS.ρm_pos.le.trans hr.1
    have h2 := secNormSq_mul_le_add_two s ℓ hIm hI0 (green ℓ g)
    have hZ0 := Sob.secNormSq_nonneg s ℓ hIm hI0 g
    have hsq : (|(ℓ : ℝ)| * M) ^ 2 = (ℓ : ℝ) ^ 2 * M ^ 2 := by
      rw [mul_pow, sq_abs]
    have h1 : S.secNormSq s ℓ (S.KsecFn ℓ g) ≤
        4 ^ (s + 1) * ((ℓ : ℝ) ^ 2 * M ^ 2) * Sob.secNormSq s ℓ (Icc S.ρm S.ρp) (green ℓ g) := by
      rw [← hsq]
      exact hnorm
    exact h1.trans (arith (by positivity) (sq_nonneg _) hCE hZ0 h2 hψn)

end SectorSetting

end NonUniqueEuler
