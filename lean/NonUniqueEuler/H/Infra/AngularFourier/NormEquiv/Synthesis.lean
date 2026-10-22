import NonUniqueEuler.H.Infra.AngularFourier.NormEquiv.Sectors
import NonUniqueEuler.I.Infra.AngularFourier.NormEquiv.FiniteSum
import NonUniqueEuler.I.Infra.Sobolev.Space
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Helper for `P/Infra/AngularFourier/NormEquiv`: synthesis of `H^k` functions from sectors

For profiles `h_ℓ ∈ H^k((0,∞))` vanishing outside `[ρ₋, ρ₊]` with `∑_ℓ ‖h_ℓ‖²_{k,ℓ} < ∞`, the
partial sums `w_N = ∑_{|ℓ| ≤ N} h_ℓ(r)e^{iℓθ}` are Cauchy in `Sob.Hk k`
(`exists_normH_sum_ofProfile_le` applied to the blocks `N' < |ℓ| ≤ N`); their limit `w` lies in
`H^k`, vanishes outside `N_*`, has sectors `h_ℓ`, and `‖w‖²_{H^k} ≤ C ∑_ℓ ‖h_ℓ‖²_{k,ℓ}`.
-/

noncomputable section

open MeasureTheory Set Real Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.Ang.NormEquivAux

open Sob

theorem toHk_sub {k : ℕ} {f g : ℂ → ℂ} (hf : MemH k f) (hg : MemH k g) :
    toHk k (f - g) = toHk k f - toHk k g := by
  have e : f - g = f + (-1 : ℂ) • g := by
    funext x
    simp [sub_eq_add_neg]
  rw [e, toHk_add hf (hg.const_smul (-1)).1, toHk_smul hg (-1), neg_one_smul, ← sub_eq_add_neg]

theorem mem_Icc_natAbs (ℓ : ℤ) {N : ℕ} (hN : ℓ.natAbs ≤ N) : ℓ ∈ Finset.Icc (-(N : ℤ)) N := by
  have h1 : |ℓ| ≤ (N : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hN
  rw [Finset.mem_Icc]
  exact ⟨by linarith [neg_abs_le ℓ], (le_abs_self ℓ).trans h1⟩

/-- The synthesis statement (`exists_memH_of_summable`). -/
theorem synthesis (k : ℕ) {ρm ρp : ℝ} (hρm : 0 < ρm) (hρ : ρm < ρp) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℤ → ℝ → ℂ, (∀ ℓ, Sob.MemH1On k (Ioi 0) (h ℓ)) →
      (∀ ℓ, ∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc ρm ρp → h ℓ r = 0) →
      Summable (fun ℓ : ℤ => Sob.secNormSq k ℓ (Icc ρm ρp) (h ℓ)) →
      ∃ w : ℂ → ℂ, Sob.MemH k w ∧ (∀ᵐ x, ¬ (ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp) → w x = 0) ∧
        (∀ ℓ, Polar.angularSector w ℓ =ᵐ[volume.restrict (Ioi 0)] h ℓ) ∧
        Tendsto (fun N : ℕ => Sob.l2 (w - ∑ ℓ ∈ Finset.Icc (-(N : ℤ)) N, ofProfile ℓ (h ℓ)))
          atTop (𝓝 0) ∧
        Sob.normH k w ^ 2 ≤ C * ∑' ℓ : ℤ, Sob.secNormSq k ℓ (Icc ρm ρp) (h ℓ) := by
  obtain ⟨C, hC, hFS⟩ := exists_normH_sum_ofProfile_le k hρm hρ
  refine ⟨C, hC, fun h hh hhI hsum => ?_⟩
  set s : ℤ → ℝ := fun ℓ => secNormSq k ℓ (Icc ρm ρp) (h ℓ) with hsdef
  have hs0 : ∀ ℓ, 0 ≤ s ℓ := fun ℓ =>
    secNormSq_nonneg k ℓ measurableSet_Icc (fun r hr => mem_Ici.2 (hρm.le.trans hr.1)) _
  set I : ℕ → Finset ℤ := fun N => Finset.Icc (-(N : ℤ)) N with hIdef
  set W : ℕ → ℂ → ℂ := fun N => ∑ ℓ ∈ I N, ofProfile ℓ (h ℓ) with hWdef
  set P : ℕ → ℝ := fun N => ∑ ℓ ∈ I N, s ℓ with hPdef
  set σ : ℝ := ∑' ℓ, s ℓ with hσdef
  have hW : ∀ N, MemH k (W N) ∧ normH k (W N) ^ 2 ≤ C * P N := fun N =>
    hFS (I N) h (fun ℓ _ => hh ℓ) (fun ℓ _ => hhI ℓ)
  have hWL2 : ∀ N, MemLp (W N) 2 volume := fun N => (memH_iff.1 (hW N).1).1
  have hWK : ∀ N, ∀ᵐ x, ¬ (ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp) → W N x = 0 := by
    intro N
    filter_upwards [(eventually_all_finset (I N)).2
      (fun ℓ _ => ofProfile_eq_zero_outside (ℓ := ℓ) (hhI ℓ))] with x hx hxK
    simp only [hWdef, Finset.sum_apply]
    exact Finset.sum_eq_zero fun ℓ hℓ => hx ℓ hℓ hxK
  have hImono : Monotone I := fun a b hab =>
    Finset.Icc_subset_Icc (neg_le_neg (by exact_mod_cast hab)) (by exact_mod_cast hab)
  have hItend : Tendsto I atTop atTop :=
    tendsto_atTop_finset_of_monotone hImono fun ℓ => ⟨ℓ.natAbs, mem_Icc_natAbs ℓ le_rfl⟩
  have hP : Tendsto P atTop (𝓝 σ) := hsum.hasSum.comp hItend
  have hPmono : Monotone P := fun a b hab =>
    Finset.sum_le_sum_of_subset_of_nonneg (hImono hab) (fun ℓ _ _ => hs0 ℓ)
  have hPle : ∀ N, P N ≤ σ := fun N => hsum.sum_le_tsum _ (fun ℓ _ => hs0 ℓ)
  -- the blocks
  have hdiff : ∀ M N, M ≤ N → MemH k (W N - W M) ∧ normH k (W N - W M) ^ 2 ≤ C * (σ - P M) := by
    intro M N hMN
    have hsub := hImono hMN
    have e : W N - W M = ∑ ℓ ∈ I N \ I M, ofProfile ℓ (h ℓ) := by
      rw [sub_eq_iff_eq_add]
      exact (Finset.sum_sdiff hsub).symm
    have es : ∑ ℓ ∈ I N \ I M, s ℓ = P N - P M := by
      rw [eq_sub_iff_add_eq]
      exact Finset.sum_sdiff hsub
    obtain ⟨hm, hn⟩ := hFS (I N \ I M) h (fun ℓ _ => hh ℓ) (fun ℓ _ => hhI ℓ)
    rw [e]
    refine ⟨hm, hn.trans ?_⟩
    have : ∑ ℓ ∈ I N \ I M, secNormSq k ℓ (Icc ρm ρp) (h ℓ) ≤ σ - P M := by
      rw [show ∑ ℓ ∈ I N \ I M, secNormSq k ℓ (Icc ρm ρp) (h ℓ) = ∑ ℓ ∈ I N \ I M, s ℓ from rfl,
        es]
      linarith [hPle N]
    exact mul_le_mul_of_nonneg_left this hC.le
  set Fs : ℕ → Hk k := fun N => toHk k (W N) with hFsdef
  have hdist : ∀ M N, M ≤ N → ‖Fs N - Fs M‖ ≤ Real.sqrt (C * (σ - P M)) := by
    intro M N hMN
    rw [hFsdef, ← toHk_sub (hW N).1 (hW M).1, norm_toHk (hdiff M N hMN).1]
    have := Real.abs_le_sqrt (hdiff M N hMN).2
    rwa [abs_of_nonneg (normH_nonneg _ _)] at this
  have hb : ∀ M N, M ≤ N → Real.sqrt (C * (σ - P N)) ≤ Real.sqrt (C * (σ - P M)) := by
    intro M N hMN
    refine Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left ?_ hC.le)
    linarith [hPmono hMN]
  have hcauchy : CauchySeq Fs := by
    refine cauchySeq_of_le_tendsto_0 (fun M => Real.sqrt (C * (σ - P M))) ?_ ?_
    · intro n m N hn hm
      rcases le_total n m with h1 | h1
      · rw [dist_comm, dist_eq_norm]
        exact (hdist n m h1).trans (hb N n hn)
      · rw [dist_eq_norm]
        exact (hdist m n h1).trans (hb N m hm)
    · have h1 : Tendsto (fun M => C * (σ - P M)) atTop (𝓝 (C * (σ - σ))) :=
        (tendsto_const_nhds.sub hP).const_mul C
      rw [sub_self, mul_zero] at h1
      simpa using h1.sqrt
  obtain ⟨F, hF⟩ := cauchySeq_tendsto_of_complete hcauchy
  obtain ⟨hwmem, hwnorm⟩ := Hk.memH_fn F
  set w : ℂ → ℂ := F.fn with hwdef
  have hwL2 : MemLp w 2 volume := (memH_iff.1 hwmem).1
  -- `L²` convergence
  have hconv : Tendsto (fun N => l2 (w - W N)) atTop (𝓝 0) := by
    have hle : ∀ N, l2 (w - W N) ≤ ‖Fs N - F‖ := by
      intro N
      have hsub := toHk_sub hwmem (hW N).1
      rw [hwdef, toHk_fn_self] at hsub
      have hm := (MemH.sub hwmem (hW N).1).1
      calc l2 (w - W N) ≤ normH k (w - W N) := hm.l2_le
        _ = ‖toHk k (w - W N)‖ := (norm_toHk hm).symm
        _ = ‖Fs N - F‖ := by rw [hwdef, hsub, norm_sub_rev]
    exact squeeze_zero (fun N => l2_nonneg _) hle (tendsto_iff_norm_sub_tendsto_zero.1 hF)
  have hconvE : Tendsto (fun N => ENNReal.ofReal (l2 (w - W N))) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hconv
  have hofReal : ∀ N, ENNReal.ofReal (l2 (w - W N)) = eLpNorm (w - W N) 2 volume := fun N =>
    ENNReal.ofReal_toReal (hwL2.sub (hWL2 N)).eLpNorm_ne_top
  -- support
  have hsupp : ∀ᵐ x, ¬ (ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp) → w x = 0 := by
    set Kc : Set ℂ := {x : ℂ | ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp}ᶜ with hKc
    have hKcm : MeasurableSet Kc := (isClosed_ann ρm ρp).measurableSet.compl
    have hle : ∀ N, eLpNorm (Kc.indicator w) 2 volume ≤ ENNReal.ofReal (l2 (w - W N)) := by
      intro N
      have he : Kc.indicator w =ᵐ[volume] Kc.indicator (w - W N) := by
        filter_upwards [hWK N] with x hx
        by_cases hxK : x ∈ Kc
        · simp only [indicator_of_mem hxK, Pi.sub_apply, hx hxK, sub_zero]
        · simp only [indicator_of_notMem hxK]
      rw [eLpNorm_congr_ae he, hofReal]
      exact eLpNorm_indicator_le _
    have h0 : eLpNorm (Kc.indicator w) 2 volume = 0 :=
      le_antisymm (ge_of_tendsto' hconvE hle) (by simp)
    have hz := (eLpNorm_eq_zero_iff (hwL2.aestronglyMeasurable.indicator hKcm)
      two_ne_zero).1 h0
    filter_upwards [hz] with x hx hxK
    have hxK' : x ∈ Kc := hxK
    simpa [indicator_of_mem hxK'] using hx
  -- sectors
  have hsec : ∀ ℓ, Polar.angularSector w ℓ =ᵐ[volume.restrict (Ioi 0)] h ℓ := by
    intro ℓ
    have hWsec : ∀ N, ℓ.natAbs ≤ N → sectorProj ℓ (W N) = ofProfile ℓ (h ℓ) := by
      intro N hN
      rw [hWdef]
      simp only
      have hmem : ℓ ∈ I N := mem_Icc_natAbs ℓ hN
      rw [sectorProj_sum_ofProfile]
      simp [hmem]
    have hae : ∀ N, ℓ.natAbs ≤ N →
        sectorProj ℓ w - ofProfile ℓ (h ℓ) =ᵐ[volume] sectorProj ℓ (w - W N) := by
      intro N hN
      have e1 := sectorProj_sub_ae ℓ hwL2 (hWL2 N)
      rw [hWsec N hN] at e1
      exact e1.symm
    have hkey : ∀ N, ℓ.natAbs ≤ N →
        eLpNorm (sectorProj ℓ w - ofProfile ℓ (h ℓ)) 2 volume ≤ ENNReal.ofReal (l2 (w - W N)) := by
      intro N hN
      rw [eLpNorm_congr_ae (hae N hN), hofReal]
      exact (memLp_sectorProj (hwL2.sub (hWL2 N)) ℓ).2
    have h0 : eLpNorm (sectorProj ℓ w - ofProfile ℓ (h ℓ)) 2 volume = 0 :=
      le_antisymm (ge_of_tendsto hconvE (eventually_atTop.2 ⟨ℓ.natAbs, hkey⟩)) (by simp)
    have hmeas : AEStronglyMeasurable (sectorProj ℓ w - ofProfile ℓ (h ℓ)) volume :=
      (memLp_sectorProj (hwL2.sub (hWL2 ℓ.natAbs)) ℓ).1.aestronglyMeasurable.congr
        (hae ℓ.natAbs le_rfl).symm
    have hA := (eLpNorm_eq_zero_iff hmeas two_ne_zero).1 h0
    have hD0 : ofProfile ℓ (fun r => Polar.angularSector w ℓ r - h ℓ r) =ᵐ[volume] 0 := by
      filter_upwards [hA, sectorProj_ae_eq_ofProfile ℓ w] with x h1 h2
      rw [ofProfile_sub, Pi.zero_apply]
      dsimp only
      rw [← h2]
      simpa [sub_eq_zero] using h1
    have hDm : AEStronglyMeasurable (fun r => Polar.angularSector w ℓ r - h ℓ r)
        (volume.restrict (Ioi 0)) :=
      (aesm_angularSector hρm hwmem hsupp ℓ).sub (hh ℓ).memLp.aestronglyMeasurable
    filter_upwards [profile_ae_zero hDm hD0] with r hr
    simpa [sub_eq_zero] using hr
  -- norm bound
  have hbound : normH k w ^ 2 ≤ C * σ := by
    rw [hwdef, hwnorm]
    have h1 : Tendsto (fun N => ‖Fs N‖ ^ 2) atTop (𝓝 (‖F‖ ^ 2)) := (hF.norm).pow 2
    refine le_of_tendsto' h1 fun N => ?_
    rw [hFsdef, norm_toHk (hW N).1]
    exact (hW N).2.trans (mul_le_mul_of_nonneg_left (hPle N) hC.le)
  exact ⟨w, hwmem, hsupp, hsec, hconv, hbound⟩

end NonUniqueEuler.Ang.NormEquivAux
