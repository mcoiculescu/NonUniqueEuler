import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import NonUniqueEuler.Defs.Infra.Sobolev
import NonUniqueEuler.I.Infra.Sobolev.Smooth
import NonUniqueEuler.H.Infra.Sobolev.TaylorFamily.Joint

/-!
# Proof: second-order Taylor expansion in `H^k` of a smooth one-parameter family
(library I-HK)

Proof of `I/Infra/Sobolev/TaylorFamily.lean` (same declaration, same statement).

* The remainder family `W(s, y) = F(s, y) - F(0, y) - s ∂_tF(0, y)` (complexified) is jointly
  `C^∞`, vanishes for `y ∉ K` (there `t ↦ F(t, y)` is constant), and satisfies `W(0, ·) = 0`,
  `∂_tW(0, ·) = 0`.
* For every multi-index `γ`, `∂^γ_y W(s, ·)` is the slice of a jointly smooth `H_γ`, with
  `∂_t H_γ = ∂^γ_y ∂_t W` (`TaylorFamilyH.exists_joint_iterDirDeriv`), so `H_γ(0, ·) = 0` and
  `∂_t H_γ(0, ·) = 0`, and `|H_γ(κ, x)| ≤ B_γ κ² 1_K(x)` (`TaylorFamilyH.exists_bound_sq`).
* `‖∂^γ W(κ, ·)‖_{L²} ≤ B_γ κ² vol(K)^{1/2}`, and the `H^k` norm is computed classically
  (`memH_of_contDiff_hasCompactSupport`).

Restructuring (as announced in the interface docstring): sup bounds of the `y`-derivatives,
uniform in `t ∈ [0,1]`, replace the composition estimate `‖g∘Y_t‖_{H^k} ≤ C^Y_k‖g‖_{H^k}` of
`05_single_ring.tex:1193-1209`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace NonUniqueEuler.Sob

namespace TaylorFamilyH

/-- `L²` bound of a function dominated by `B · 1_K`. -/
theorem l2_le_of_le_indicator {f : ℂ → ℂ} {K : Set ℂ} (hK : IsCompact K) {b : ℝ} (hb : 0 ≤ b)
    (hf : ∀ x, ‖f x‖ ≤ K.indicator (fun _ => b) x) :
    l2 f ≤ b * (volume K ^ (1 / (2 : ℝ))).toReal := by
  have hle := eLpNorm_mono_real (p := 2) (μ := (volume : Measure ℂ)) hf
  rw [eLpNorm_indicator_const hK.measurableSet two_ne_zero ENNReal.ofNat_ne_top] at hle
  have hfin : ‖b‖ₑ * volume K ^ (1 / (2 : ℝ≥0∞).toReal) ≠ (⊤ : ℝ≥0∞) := by
    refine ENNReal.mul_ne_top enorm_ne_top ?_
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hK.measure_lt_top.ne
  have h2 : (1 / (2 : ℝ≥0∞).toReal) = 1 / (2 : ℝ) := by norm_num
  refine (ENNReal.toReal_mono hfin hle).trans_eq ?_
  rw [ENNReal.toReal_mul, toReal_enorm, h2, Real.norm_eq_abs, abs_of_nonneg hb]

/-- The per-multi-index bound: for a jointly smooth `W` vanishing for `y ∉ K`, with
`W(0, ·) = 0` and `∂_t W(0, ·) = 0`, `‖∂^γ W(κ, ·)‖_{L²} ≤ B κ²` for `κ ∈ [0,1]`. -/
theorem exists_l2_partialD_le {W : ℝ × ℂ → ℂ} (hW : ContDiff ℝ ∞ W) {K : Set ℂ}
    (hK : IsCompact K) (hWU : ∀ p ∈ (univ : Set ℝ) ×ˢ Kᶜ, W p = 0) (hW0 : ∀ y, W (0, y) = 0)
    (hW1 : ∀ y, fderiv ℝ W (0, y) (1, 0) = 0) (γ : ℕ × ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ κ ∈ Icc (0 : ℝ) 1, l2 (partialD γ (fun y => W (κ, y))) ≤ B * κ ^ 2 := by
  have hU : IsOpen ((univ : Set ℝ) ×ˢ Kᶜ) := isOpen_univ.prod hK.isClosed.isOpen_compl
  obtain ⟨H, hH, hHU, hsl, htm⟩ := exists_joint_iterDirDeriv hW hU hWU (pdList γ)
  have hz0 : (fun y => W (0, y)) = fun _ => (0 : ℂ) := funext hW0
  have hz1 : (fun y => fderiv ℝ W (0, y) (1, 0)) = fun _ => (0 : ℂ) := funext hW1
  have hH0 : ∀ x, H (0, x) = 0 := fun x => by
    rw [← hsl 0 x, hz0, iterDirDeriv_zero]
  have hH1 : ∀ x, fderiv ℝ H (0, x) (1, 0) = 0 := fun x => by
    rw [← htm 0 x, hz1, iterDirDeriv_zero]
  obtain ⟨B, hB, hBb⟩ := exists_bound_sq hH hK hH0 hH1
  set cK : ℝ := (volume K ^ (1 / (2 : ℝ))).toReal with hcK
  refine ⟨B * cK, mul_nonneg hB ENNReal.toReal_nonneg, fun κ hκ => ?_⟩
  have hpt : ∀ x, ‖partialD γ (fun y => W (κ, y)) x‖ ≤ K.indicator (fun _ => B * κ ^ 2) x := by
    intro x
    rw [partialD, hsl κ x]
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx]
      exact hBb κ hκ x hx
    · rw [indicator_of_notMem hx, hHU (κ, x) ⟨mem_univ _, hx⟩, norm_zero]
  calc l2 (partialD γ (fun y => W (κ, y))) ≤ B * κ ^ 2 * cK :=
        l2_le_of_le_indicator hK (by positivity) hpt
    _ = B * cK * κ ^ 2 := by ring

end TaylorFamilyH

open TaylorFamilyH in
/-- **Second-order Taylor expansion in `H^k`** of a smooth family that is constant in `t` outside
a compact set (`05_single_ring.tex:1193-1209`, generic form). -/
theorem normH_taylor_two_le {F : ℝ → ℂ → ℝ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℂ => F p.1 p.2))
    {K : Set ℂ} (hK : IsCompact K) (hoff : ∀ t : ℝ, ∀ y ∉ K, F t y = F 0 y) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ κ ∈ Icc (0 : ℝ) 1,
      MemH k (fun y => ((F κ y - F 0 y - κ * deriv (fun t => F t y) 0 : ℝ) : ℂ)) ∧
        normH k (fun y => ((F κ y - F 0 y - κ * deriv (fun t => F t y) 0 : ℝ) : ℂ)) ≤
          C * κ ^ 2 := by
  have hdF : ∀ p : ℝ × ℂ, DifferentiableAt ℝ (fun p : ℝ × ℂ => F p.1 p.2) p := fun p =>
    (hF.differentiable (by simp)) p
  -- the time derivative at `0`
  have hderiv : ∀ y, HasDerivAt (fun t => F t y) (deriv (fun t => F t y) 0) 0 := fun y =>
    (hasDerivAt_time_slice (hdF (0, y))).differentiableAt.hasDerivAt
  have hd0 : ContDiff ℝ ∞ (fun y => deriv (fun t => F t y) 0) := by
    have h : (fun y => deriv (fun t => F t y) 0) =
        fun y => fderiv ℝ (fun p : ℝ × ℂ => F p.1 p.2) (0, y) (1, 0) :=
      funext fun y => (hasDerivAt_time_slice (hdF (0, y))).deriv
    rw [h]
    exact (contDiff_fderiv_apply hF (1, 0)).comp (contDiff_const.prodMk contDiff_id)
  -- the remainder family
  set W : ℝ × ℂ → ℂ := fun p =>
    ((F p.1 p.2 - F 0 p.2 - p.1 * deriv (fun t => F t p.2) 0 : ℝ) : ℂ) with hWdef
  have hWs : ContDiff ℝ ∞ W := by
    have hr : ContDiff ℝ ∞ (fun p : ℝ × ℂ =>
        F p.1 p.2 - F 0 p.2 - p.1 * deriv (fun t => F t p.2) 0) :=
      (hF.sub (hF.comp (contDiff_const.prodMk contDiff_snd))).sub
        (contDiff_fst.mul (hd0.comp contDiff_snd))
    exact Complex.ofRealCLM.contDiff.comp hr
  have hWU : ∀ p ∈ (univ : Set ℝ) ×ˢ Kᶜ, W p = 0 := by
    rintro ⟨s, y⟩ ⟨-, hy⟩
    have hc : (fun t => F t y) = fun _ => F 0 y := funext fun t => hoff t y hy
    simp only [hWdef, hc, deriv_const, mul_zero, hoff s y hy, sub_self, Complex.ofReal_zero]
  have hW0 : ∀ y, W (0, y) = 0 := fun y => by simp [hWdef]
  have hW1 : ∀ y, fderiv ℝ W (0, y) (1, 0) = 0 := by
    intro y
    have h1 : HasDerivAt (fun s => W (s, y)) (fderiv ℝ W (0, y) (1, 0)) 0 :=
      hasDerivAt_time_slice ((hWs.differentiable (by simp)) _)
    have h2 : HasDerivAt (fun s => W (s, y))
        (((deriv (fun t => F t y) 0 - 1 * deriv (fun t => F t y) 0 : ℝ)) : ℂ) 0 :=
      (((hderiv y).sub_const (F 0 y)).sub
        ((hasDerivAt_id (0 : ℝ)).mul_const (deriv (fun t => F t y) 0))).ofReal_comp
    rw [h1.unique h2, one_mul, sub_self, Complex.ofReal_zero]
  -- the per-multi-index bounds
  choose B hB hBb using exists_l2_partialD_le hWs hK hWU hW0 hW1
  set S : ℝ := ∑ γ ∈ multiIdx k, B γ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun γ _ => hB γ
  set N : ℝ := ((multiIdx k).card : ℝ) with hN
  refine ⟨Real.sqrt N * S, mul_nonneg (Real.sqrt_nonneg _) hS0, fun κ hκ => ?_⟩
  have hR : (fun y => ((F κ y - F 0 y - κ * deriv (fun t => F t y) 0 : ℝ) : ℂ)) =
      fun y => W (κ, y) := rfl
  rw [hR]
  have hRs : ContDiff ℝ ∞ (fun y => W (κ, y)) := hWs.comp (contDiff_const.prodMk contDiff_id)
  have hRc : HasCompactSupport (fun y => W (κ, y)) :=
    HasCompactSupport.intro hK fun y hy => hWU (κ, y) ⟨mem_univ _, hy⟩
  obtain ⟨hmem, -, hnorm⟩ := memH_of_contDiff_hasCompactSupport hRs hRc k
  refine ⟨hmem, ?_⟩
  rw [hnorm]
  have hb : 0 ≤ S * κ ^ 2 := mul_nonneg hS0 (sq_nonneg _)
  calc Real.sqrt (∑ γ ∈ multiIdx k, l2 (partialD γ (fun y => W (κ, y))) ^ 2)
      ≤ Real.sqrt (∑ _γ ∈ multiIdx k, (S * κ ^ 2) ^ 2) := by
        apply Real.sqrt_le_sqrt
        apply Finset.sum_le_sum
        intro γ hγ
        have hBS : B γ ≤ S := Finset.single_le_sum (fun γ _ => hB γ) hγ
        have hl : l2 (partialD γ (fun y => W (κ, y))) ≤ S * κ ^ 2 :=
          (hBb γ κ hκ).trans (mul_le_mul_of_nonneg_right hBS (sq_nonneg _))
        exact pow_le_pow_left₀ (l2_nonneg _) hl 2
    _ = Real.sqrt N * (S * κ ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul, Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hb]
    _ = Real.sqrt N * S * κ ^ 2 := by ring

end NonUniqueEuler.Sob
