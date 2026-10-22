import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Real.Sqrt
import NonUniqueEuler.Defs.Infra.SectorSpace
import NonUniqueEuler.I.Infra.SectorSpace.Decomposition
import NonUniqueEuler.I.Infra.SectorSpace.Projection

/-!
# Proof: direct sums `⊕_ℓ A_ℓ` of uniformly bounded sector operators (library I-SECT)

Proof of `I/Infra/SectorSpace/DirectSum.lean` (restructuring R1, decision D8).

* For uniformly bounded `A`, the sum `∑_ℓ A_ℓ (P_ℓ w)` converges in `Y^s` by synthesis
  (`exists_Y_of_summable`), since `‖A_ℓ P_ℓ w‖² ≤ M² ‖P_ℓ w‖²` is summable. The limit is linear
  (uniqueness of limits) and bounded by `(C/c)^{1/2} M ‖w‖` by the two-sided norm equivalence
  `exists_norm_equiv_Y`, so it is a continuous linear map satisfying the specification of the
  `choose` in `sectorSum`; hence `sectorSum` is that map.
* A sum `∑_ℓ g_ℓ` (`g_ℓ ∈ Y^s_ℓ`) has `P_m`-component `g_m` (`secProj_inclSec`), and `w` is
  determined by its components (`hasSum_secProj`). Uniqueness, composition, identity, linearity
  and the invariance of `Y^s_𝒵` follow.
* Strong continuity: dominated convergence for series (`tendsto_tsum_of_dominated_convergence`)
  on `∑_ℓ ‖(A t ℓ - A t₀ ℓ) P_ℓ w‖²`, dominated by `4 M² ‖P_ℓ w‖²`, and the norm equivalence.
-/

noncomputable section

open MeasureTheory Set Real Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.Sect

open Sob Ang

namespace DirectSumP

variable {s : ℕ} {ρm ρp : ℝ}

/-- The `P_m`-component of a convergent sum `∑_ℓ g_ℓ` of sector elements is `g_m`. -/
theorem secProj_eq_of_hasSum {K : Set ℂ} (hK : IsRotInvariant K) {g : ∀ ℓ : ℤ, Ysec s K ℓ}
    {v : Y s K} (h : HasSum (fun ℓ : ℤ => inclSec s K ℓ (g ℓ)) v) (m : ℤ) :
    secProj s K m v = g m := by
  have h1 := h.mapL (secProj s K m)
  have hm : secProj s K m (inclSec s K m (g m)) = g m := by
    apply Subtype.ext
    rw [secProj_inclSec hK m m (g m), ite_eq_left rfl]
  have h2 : HasSum (fun ℓ : ℤ => secProj s K m (inclSec s K ℓ (g ℓ)))
      (secProj s K m (inclSec s K m (g m))) := by
    refine hasSum_single m fun ℓ hℓ => ?_
    apply Subtype.ext
    rw [secProj_inclSec hK ℓ m (g ℓ), ite_eq_right (Ne.symm hℓ)]
    rfl
  rw [hm] at h2
  exact h1.unique h2

/-- An element of `Y^s` is determined by its sector components. -/
theorem ext_secProj (hρm : 0 < ρm) (hρ : ρm < ρp) {v v' : Y s (closedAnnulus ρm ρp)}
    (h : ∀ ℓ, secProj s _ ℓ v = secProj s _ ℓ v') : v = v' := by
  have h1 := hasSum_secProj hρm hρ v
  have h2 := hasSum_secProj hρm hρ v'
  simp only [h] at h1
  exact h1.unique h2

/-- If some operator satisfies the specification of `sectorSum`, then `sectorSum` is that
operator. -/
theorem sectorSum_eq_of_hasSum {K : Set ℂ} {A : ∀ ℓ : ℤ, Ysec s K ℓ →L[ℂ] Ysec s K ℓ}
    {T : Y s K →L[ℂ] Y s K}
    (hT : ∀ w, HasSum (fun ℓ : ℤ => inclSec s K ℓ (A ℓ (secProj s K ℓ w))) (T w)) :
    sectorSum s K A = T := by
  have hex : ∃ T : Y s K →L[ℂ] Y s K,
      ∀ w, HasSum (fun ℓ : ℤ => inclSec s K ℓ (A ℓ (secProj s K ℓ w))) (T w) := ⟨T, hT⟩
  rw [sectorSum, dite_eq_left hex]
  ext1 w
  exact (hex.choose_spec w).unique (hT w)

/-- `M ≥ 0` when `M` bounds the norms of the family. -/
theorem nonneg_of_bound {K : Set ℂ} {A : ∀ ℓ : ℤ, Ysec s K ℓ →L[ℂ] Ysec s K ℓ} {M : ℝ}
    (hA : ∀ ℓ, ‖A ℓ‖ ≤ M) : 0 ≤ M :=
  (A 0).opNorm_nonneg.trans (hA 0)

/-- `‖A_ℓ g‖² ≤ M² ‖g‖²`. -/
theorem sq_norm_apply_le {K : Set ℂ} {ℓ : ℤ} {A : Ysec s K ℓ →L[ℂ] Ysec s K ℓ} {M : ℝ}
    (hA : ‖A‖ ≤ M) (g : Ysec s K ℓ) : ‖A g‖ ^ 2 ≤ M ^ 2 * ‖g‖ ^ 2 := by
  have h1 : ‖A g‖ ≤ M * ‖g‖ := (A.le_opNorm g).trans (by gcongr)
  have h0 : 0 ≤ M := A.opNorm_nonneg.trans hA
  calc ‖A g‖ ^ 2 ≤ (M * ‖g‖) ^ 2 := by gcongr
    _ = M ^ 2 * ‖g‖ ^ 2 := by ring

/-- The construction: for uniformly bounded `A`, a continuous linear map with the specification
of `sectorSum` and norm at most `(C/c)^{1/2} M`. -/
theorem exists_clm (hρm : 0 < ρm) (hρ : ρm < ρp) {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hequiv : ∀ w : Y s (closedAnnulus ρm ρp),
      Summable (fun ℓ : ℤ => ‖secProj s _ ℓ w‖ ^ 2) ∧
        c * ∑' ℓ : ℤ, ‖secProj s _ ℓ w‖ ^ 2 ≤ ‖w‖ ^ 2 ∧
        ‖w‖ ^ 2 ≤ C * ∑' ℓ : ℤ, ‖secProj s _ ℓ w‖ ^ 2)
    (A : ∀ ℓ : ℤ, Ysec s (closedAnnulus ρm ρp) ℓ →L[ℂ] Ysec s (closedAnnulus ρm ρp) ℓ) (M : ℝ)
    (hA : ∀ ℓ, ‖A ℓ‖ ≤ M) :
    ∃ T : Y s (closedAnnulus ρm ρp) →L[ℂ] Y s (closedAnnulus ρm ρp),
      (∀ w, HasSum (fun ℓ : ℤ => inclSec s _ ℓ (A ℓ (secProj s _ ℓ w))) (T w)) ∧
        ‖T‖ ≤ Real.sqrt (C / c) * M := by
  have hK := isRotInvariant_closedAnnulus ρm ρp
  have hM : 0 ≤ M := nonneg_of_bound hA
  have hsum : ∀ w : Y s (closedAnnulus ρm ρp),
      Summable (fun ℓ : ℤ => ‖A ℓ (secProj s _ ℓ w)‖ ^ 2) := fun w =>
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun ℓ => sq_norm_apply_le (hA ℓ) _)
      ((hequiv w).1.mul_left (M ^ 2))
  have hex : ∀ w : Y s (closedAnnulus ρm ρp), ∃ v : Y s (closedAnnulus ρm ρp),
      HasSum (fun ℓ : ℤ => inclSec s _ ℓ (A ℓ (secProj s _ ℓ w))) v := fun w =>
    ⟨(exists_Y_of_summable hρm hρ _ (hsum w)).choose,
      (exists_Y_of_summable hρm hρ _ (hsum w)).choose_spec.2⟩
  choose F hF using hex
  have hadd : ∀ w w', F (w + w') = F w + F w' := fun w w' => by
    refine (hF (w + w')).unique ?_
    simpa only [map_add] using (hF w).add (hF w')
  have hsmul : ∀ (a : ℂ) w, F (a • w) = a • F w := fun a w => by
    refine (hF (a • w)).unique ?_
    simpa only [map_smul] using (hF w).const_smul a
  let Fl : Y s (closedAnnulus ρm ρp) →ₗ[ℂ] Y s (closedAnnulus ρm ρp) :=
    { toFun := F, map_add' := hadd, map_smul' := hsmul }
  have hB : 0 ≤ Real.sqrt (C / c) * M := mul_nonneg (Real.sqrt_nonneg _) hM
  have hbound : ∀ w, ‖Fl w‖ ≤ Real.sqrt (C / c) * M * ‖w‖ := fun w => by
    show ‖F w‖ ≤ _
    have hP : ∀ ℓ, secProj s _ ℓ (F w) = A ℓ (secProj s _ ℓ w) :=
      secProj_eq_of_hasSum hK (hF w)
    have h1 : ‖F w‖ ^ 2 ≤ C * ∑' ℓ : ℤ, ‖A ℓ (secProj s _ ℓ w)‖ ^ 2 := by
      have := (hequiv (F w)).2.2
      simpa only [hP] using this
    have h2 : ∑' ℓ : ℤ, ‖A ℓ (secProj s _ ℓ w)‖ ^ 2 ≤
        M ^ 2 * ∑' ℓ : ℤ, ‖secProj s _ ℓ w‖ ^ 2 := by
      rw [← tsum_mul_left]
      exact (hsum w).tsum_le_tsum (fun ℓ => sq_norm_apply_le (hA ℓ) _)
        ((hequiv w).1.mul_left (M ^ 2))
    have h3 : ∑' ℓ : ℤ, ‖secProj s _ ℓ w‖ ^ 2 ≤ ‖w‖ ^ 2 / c := by
      rw [le_div_iff₀ hc, mul_comm]
      exact (hequiv w).2.1
    have h4 : ‖F w‖ ^ 2 ≤ (Real.sqrt (C / c) * M * ‖w‖) ^ 2 := by
      have hsq : (Real.sqrt (C / c)) ^ 2 = C / c := Real.sq_sqrt (div_nonneg hC.le hc.le)
      calc ‖F w‖ ^ 2 ≤ C * (M ^ 2 * (‖w‖ ^ 2 / c)) := by
            refine h1.trans ?_
            gcongr
            exact h2.trans (by gcongr)
        _ = (Real.sqrt (C / c) * M * ‖w‖) ^ 2 := by
            rw [mul_pow, mul_pow, hsq]
            field_simp
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hB (norm_nonneg _))
      two_ne_zero).1 h4
  refine ⟨Fl.mkContinuous _ hbound, fun w => hF w, ?_⟩
  exact LinearMap.mkContinuous_norm_le _ hB hbound

end DirectSumP

open DirectSumP

/-- The specification of `sectorSum` and the bound `‖⊕A‖ ≤ B sup_ℓ ‖A_ℓ‖`. -/
theorem exists_sectorSum_spec (s : ℕ) {ρm ρp : ℝ} (hρm : 0 < ρm) (hρ : ρm < ρp) :
    ∃ B : ℝ, 0 < B ∧ ∀ (A : ∀ ℓ : ℤ, Ysec s (closedAnnulus ρm ρp) ℓ →L[ℂ]
        Ysec s (closedAnnulus ρm ρp) ℓ) (M : ℝ), (∀ ℓ, ‖A ℓ‖ ≤ M) →
      (∀ w, HasSum (fun ℓ : ℤ => inclSec s _ ℓ (A ℓ (secProj s _ ℓ w)))
          (sectorSum s (closedAnnulus ρm ρp) A w)) ∧
        ‖sectorSum s (closedAnnulus ρm ρp) A‖ ≤ B * M := by
  obtain ⟨c, C, hc, hC, hequiv⟩ := exists_norm_equiv_Y s hρm hρ
  refine ⟨Real.sqrt (C / c), Real.sqrt_pos.2 (div_pos hC hc), fun A M hA => ?_⟩
  obtain ⟨T, hT, hTn⟩ := exists_clm hρm hρ hc hC hequiv A M hA
  rw [sectorSum_eq_of_hasSum hT]
  exact ⟨hT, hTn⟩

/-- `P_ℓ ∘ ⊕A = A_ℓ ∘ P_ℓ`. -/
theorem secProj_sectorSum {s : ℕ} {ρm ρp : ℝ} (hρm : 0 < ρm) (hρ : ρm < ρp)
    {A : ∀ ℓ : ℤ, Ysec s (closedAnnulus ρm ρp) ℓ →L[ℂ] Ysec s (closedAnnulus ρm ρp) ℓ} {M : ℝ}
    (hA : ∀ ℓ, ‖A ℓ‖ ≤ M) (ℓ : ℤ) (w : Y s (closedAnnulus ρm ρp)) :
    secProj s _ ℓ (sectorSum s _ A w) = A ℓ (secProj s _ ℓ w) := by
  obtain ⟨B, -, hB⟩ := exists_sectorSum_spec s hρm hρ
  exact secProj_eq_of_hasSum (isRotInvariant_closedAnnulus ρm ρp) ((hB A M hA).1 w) ℓ

/-- Uniqueness: an operator acting sector-wise by `A` is `⊕A`. -/
theorem eq_sectorSum_of_secProj {s : ℕ} {ρm ρp : ℝ} (hρm : 0 < ρm) (hρ : ρm < ρp)
    {A : ∀ ℓ : ℤ, Ysec s (closedAnnulus ρm ρp) ℓ →L[ℂ] Ysec s (closedAnnulus ρm ρp) ℓ}
    (T : Y s (closedAnnulus ρm ρp) →L[ℂ] Y s (closedAnnulus ρm ρp))
    (hT : ∀ ℓ w, secProj s _ ℓ (T w) = A ℓ (secProj s _ ℓ w)) :
    T = sectorSum s _ A := by
  refine (sectorSum_eq_of_hasSum fun w => ?_).symm
  have h := hasSum_secProj hρm hρ (T w)
  simpa only [hT] using h

theorem sectorSum_comp {s : ℕ} {ρm ρp : ℝ} (hρm : 0 < ρm) (hρ : ρm < ρp)
    {A A' : ∀ ℓ : ℤ, Ysec s (closedAnnulus ρm ρp) ℓ →L[ℂ] Ysec s (closedAnnulus ρm ρp) ℓ}
    {M M' : ℝ} (hA : ∀ ℓ, ‖A ℓ‖ ≤ M) (hA' : ∀ ℓ, ‖A' ℓ‖ ≤ M') :
    sectorSum s _ (fun ℓ => (A ℓ).comp (A' ℓ)) = (sectorSum s _ A).comp (sectorSum s _ A') := by
  refine (eq_sectorSum_of_secProj hρm hρ _ fun ℓ w => ?_).symm
  rw [ContinuousLinearMap.comp_apply, secProj_sectorSum hρm hρ hA,
    secProj_sectorSum hρm hρ hA', ContinuousLinearMap.comp_apply]

theorem sectorSum_one {s : ℕ} {ρm ρp : ℝ} (hρm : 0 < ρm) (hρ : ρm < ρp) :
    sectorSum s (closedAnnulus ρm ρp) (fun _ => ContinuousLinearMap.id ℂ _) =
      ContinuousLinearMap.id ℂ _ := by
  refine (eq_sectorSum_of_secProj hρm hρ _ fun ℓ w => ?_).symm
  rfl

theorem sectorSum_add {s : ℕ} {ρm ρp : ℝ} (hρm : 0 < ρm) (hρ : ρm < ρp)
    {A A' : ∀ ℓ : ℤ, Ysec s (closedAnnulus ρm ρp) ℓ →L[ℂ] Ysec s (closedAnnulus ρm ρp) ℓ}
    {M M' : ℝ} (hA : ∀ ℓ, ‖A ℓ‖ ≤ M) (hA' : ∀ ℓ, ‖A' ℓ‖ ≤ M') (c : ℂ) :
    sectorSum s _ (fun ℓ => A ℓ + c • A' ℓ) = sectorSum s _ A + c • sectorSum s _ A' := by
  refine (eq_sectorSum_of_secProj hρm hρ _ fun ℓ w => ?_).symm
  rw [add_apply, smul_apply, map_add, map_smul,
    secProj_sectorSum hρm hρ hA, secProj_sectorSum hρm hρ hA',
    add_apply, smul_apply]

/-- `⊕A` preserves `Y^s_𝒵`. -/
theorem sectorSum_mem_YZSub {s : ℕ} {ρm ρp : ℝ} (hρm : 0 < ρm) (hρ : ρm < ρp)
    {A : ∀ ℓ : ℤ, Ysec s (closedAnnulus ρm ρp) ℓ →L[ℂ] Ysec s (closedAnnulus ρm ρp) ℓ} {M : ℝ}
    (hA : ∀ ℓ, ‖A ℓ‖ ≤ M) (Z : Set ℤ) {w : Y s (closedAnnulus ρm ρp)}
    (hw : (w : SobTuple s) ∈ YZSub s (closedAnnulus ρm ρp) Z) :
    ((sectorSum s _ A w : Y s (closedAnnulus ρm ρp)) : SobTuple s) ∈
      YZSub s (closedAnnulus ρm ρp) Z := by
  have hK := isRotInvariant_closedAnnulus ρm ρp
  rw [mem_YZSub_iff hK] at hw ⊢
  intro ℓ hℓ
  rw [secProj_sectorSum hρm hρ hA, hw ℓ hℓ, map_zero]

/-- Strong continuity of `t ↦ ⊕A(t)` from sector-wise strong continuity and uniform bounds. -/
theorem continuousOn_sectorSum {s : ℕ} {ρm ρp : ℝ} (hρm : 0 < ρm) (hρ : ρm < ρp) {J : Set ℝ}
    {A : ℝ → ∀ ℓ : ℤ, Ysec s (closedAnnulus ρm ρp) ℓ →L[ℂ] Ysec s (closedAnnulus ρm ρp) ℓ}
    {M : ℝ} (hA : ∀ t ∈ J, ∀ ℓ, ‖A t ℓ‖ ≤ M)
    (hcont : ∀ ℓ g, ContinuousOn (fun t => A t ℓ g) J) (w : Y s (closedAnnulus ρm ρp)) :
    ContinuousOn (fun t => sectorSum s _ (A t) w) J := by
  obtain ⟨c, C, hc, hC, hequiv⟩ := exists_norm_equiv_Y s hρm hρ
  intro t₀ ht₀
  have hM : 0 ≤ M := (A t₀ 0).opNorm_nonneg.trans (hA t₀ ht₀ 0)
  -- the sector-wise squared differences
  set S : ℝ → ℤ → ℝ := fun t ℓ =>
    ‖A t ℓ (secProj s _ ℓ w) - A t₀ ℓ (secProj s _ ℓ w)‖ ^ 2 with hS
  have hdom : Summable (fun ℓ : ℤ => (2 * M) ^ 2 * ‖secProj s _ ℓ w‖ ^ 2) :=
    (hequiv w).1.mul_left _
  have hlim : Tendsto (fun t => ∑' ℓ, S t ℓ) (𝓝[J] t₀) (𝓝 (∑' _ℓ : ℤ, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence hdom (fun ℓ => ?_) ?_
    · have h1 : Tendsto (fun t => A t ℓ (secProj s _ ℓ w)) (𝓝[J] t₀)
          (𝓝 (A t₀ ℓ (secProj s _ ℓ w))) := hcont ℓ _ t₀ ht₀
      have h2 := ((h1.sub_const (A t₀ ℓ (secProj s _ ℓ w))).norm).pow 2
      simpa [hS] using h2
    · filter_upwards [self_mem_nhdsWithin] with t ht ℓ
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have h1 : ‖A t ℓ (secProj s _ ℓ w) - A t₀ ℓ (secProj s _ ℓ w)‖ ≤
          2 * M * ‖secProj s _ ℓ w‖ := by
        calc _ ≤ ‖A t ℓ (secProj s _ ℓ w)‖ + ‖A t₀ ℓ (secProj s _ ℓ w)‖ := norm_sub_le _ _
          _ ≤ M * ‖secProj s _ ℓ w‖ + M * ‖secProj s _ ℓ w‖ := by
              gcongr
              · exact ((A t ℓ).le_opNorm _).trans (by gcongr; exact hA t ht ℓ)
              · exact ((A t₀ ℓ).le_opNorm _).trans (by gcongr; exact hA t₀ ht₀ ℓ)
          _ = 2 * M * ‖secProj s _ ℓ w‖ := by ring
      calc S t ℓ ≤ (2 * M * ‖secProj s _ ℓ w‖) ^ 2 := by
            simp only [hS]
            gcongr
        _ = (2 * M) ^ 2 * ‖secProj s _ ℓ w‖ ^ 2 := by ring
  rw [tsum_zero] at hlim
  have hlim' : Tendsto (fun t => Real.sqrt (C * ∑' ℓ, S t ℓ)) (𝓝[J] t₀) (𝓝 0) := by
    have h : Tendsto (fun t => Real.sqrt (C * ∑' ℓ, S t ℓ)) (𝓝[J] t₀)
        (𝓝 (Real.sqrt (C * 0))) := (Real.continuous_sqrt.tendsto _).comp (hlim.const_mul C)
    rwa [mul_zero, Real.sqrt_zero] at h
  show Tendsto (fun t => sectorSum s _ (A t) w) (𝓝[J] t₀) (𝓝 (sectorSum s _ (A t₀) w))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim'
  filter_upwards [self_mem_nhdsWithin] with t ht
  set v := sectorSum s _ (A t) w - sectorSum s _ (A t₀) w with hv
  have hP : ∀ ℓ, ‖secProj s _ ℓ v‖ ^ 2 = S t ℓ := fun ℓ => by
    rw [hv, map_sub, secProj_sectorSum hρm hρ (hA t ht), secProj_sectorSum hρm hρ (hA t₀ ht₀)]
  have h1 : ‖v‖ ^ 2 ≤ C * ∑' ℓ, S t ℓ := by
    have := (hequiv v).2.2
    simpa only [hP] using this
  calc ‖v‖ = Real.sqrt (‖v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (C * ∑' ℓ, S t ℓ) := Real.sqrt_le_sqrt h1

end NonUniqueEuler.Sect
