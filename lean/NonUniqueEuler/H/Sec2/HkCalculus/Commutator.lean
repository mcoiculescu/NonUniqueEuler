import NonUniqueEuler.H.Sec2.HkCalculus.Product
import NonUniqueEuler.H.Sec2.HkCalculus.Cutoff
import NonUniqueEuler.I.Infra.Sobolev.ReIm

/-!
# Helper for `P/Sec2/HkCalculus`: the commutator bound of `lem:Hk-calculus`(1)

`02_prelim.tex:690-731`. For a real vector field `Ũ ∈ W^{1,∞}(ℝ²) ∩ H^k(ℝ²)` equal to `U` on a
neighborhood `V` of `N` and `w ∈ H^{k+1}` vanishing outside `N`:
* `∂^α(Ũ·∇w) = Σ_l Σ_{β ≤ α} C(α,β) ∂^β Ũ_l ∂^{α-β} ∂_l w` weakly (the weak Leibniz rule
  `hasWeakDerivOn_mul_of_memH` applied to `Ũ_l ∈ H^k` and `∂_l w ∈ H^k`);
* `eq:Leibniz-comm`: `[∂^α, U·∇]w = Σ_l Σ_{0 < β ≤ α} C(α,β) ∂^β Ũ_l ∂^{α-β} ∂_l w` a.e.
  (`leibSum_split`; weak derivatives commute);
* `comm_main`: the existence of `∂^α(U·∇w)` in `L²(N₁)` and
  `‖[∂^α, U·∇]w‖_{L²} ≤ 2·2^k (‖Ũ‖_{W^{1,∞}} + ‖Ũ‖_{H^k}) ‖w‖_{H^k}` (`commRem_bound`, from the
  term bounds `commTerm_bound`).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace NonUniqueEuler.Sob.HkCalcAux

/-- The remainder `Σ_{0 < β ≤ α} C(α,β) ∂^β G ∂^{α-β} ∂_e w` of `eq:Leibniz-comm`. -/
def commRem (α : ℕ × ℕ) (G w : ℂ → ℂ) (e : ℕ × ℕ) (x : ℂ) : ℂ :=
  ∑ β ∈ (leIdx α).erase (0, 0), ((α.1.choose β.1 * α.2.choose β.2 : ℕ) : ℂ) *
    weakPartial β G x * weakPartial (α.1 - β.1, α.2 - β.2) (weakPartial e w) x

theorem commRem_bound {k : ℕ} (hk : 3 ≤ k) {G w : ℂ → ℂ} (hG : MemH k G) {M : ℝ}
    (hM : 0 ≤ M)
    (hGinf : ∀ β : ℕ × ℕ, β.1 + β.2 = 1 → eLpNorm (weakPartial β G) ⊤ volume ≤ ENNReal.ofReal M)
    (hw : MemH (k + 1) w) {e : ℕ × ℕ} (he : e.1 + e.2 = 1) {α : ℕ × ℕ}
    (hα : α ∈ multiIdx k) :
    MemLp (commRem α G w e) 2 volume ∧
      l2 (commRem α G w e) ≤ 2 ^ k * ((M + normH k G) * normH k w) := by
  set F : ℕ × ℕ → ℂ → ℂ := fun β x =>
    ((α.1.choose β.1 * α.2.choose β.2 : ℕ) : ℂ) *
      (weakPartial β G x * weakPartial (α.1 - β.1, α.2 - β.2) (weakPartial e w) x) with hF
  have hS : commRem α G w e = fun x => ∑ β ∈ (leIdx α).erase (0, 0), F β x := by
    funext x
    simp only [commRem, hF, mul_assoc]
  have hB : 0 ≤ (M + normH k G) * normH k w :=
    mul_nonneg (add_nonneg hM (normH_nonneg k G)) (normH_nonneg k w)
  have hFb : ∀ β ∈ (leIdx α).erase (0, 0), MemLp (F β) 2 volume ∧
      l2 (F β) ≤ ((α.1.choose β.1 * α.2.choose β.2 : ℕ) : ℝ) *
        ((M + normH k G) * normH k w) := by
    intro β hβ
    obtain ⟨hβ0, hβ'⟩ := Finset.mem_erase.1 hβ
    obtain ⟨h1, h2⟩ := commTerm_bound hk hG hM hGinf hw he hα hβ' hβ0
    refine ⟨h1.const_mul _, ?_⟩
    rw [hF, l2_const_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
  obtain ⟨h1, h2⟩ := l2_finset_sum ((leIdx α).erase (0, 0)) F fun β hβ => (hFb β hβ).1
  rw [hS]
  refine ⟨h1, h2.trans ?_⟩
  calc ∑ β ∈ (leIdx α).erase (0, 0), l2 (F β) ≤
        ∑ β ∈ (leIdx α).erase (0, 0), ((α.1.choose β.1 * α.2.choose β.2 : ℕ) : ℝ) *
          ((M + normH k G) * normH k w) :=
        Finset.sum_le_sum fun β hβ => (hFb β hβ).2
    _ ≤ ∑ β ∈ leIdx α, ((α.1.choose β.1 * α.2.choose β.2 : ℕ) : ℝ) *
          ((M + normH k G) * normH k w) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          fun β _ _ => mul_nonneg (Nat.cast_nonneg _) hB
    _ = 2 ^ (α.1 + α.2) * ((M + normH k G) * normH k w) := by
        rw [← Finset.sum_mul, sum_leIdx_choose]
    _ ≤ 2 ^ k * ((M + normH k G) * normH k w) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (mem_multiIdx.1 hα)) hB

/-- The term `β = 0` of the Leibniz sum is the transport term `G ∂_e ∂^α w`. -/
theorem leibSum_split {k : ℕ} {G w : ℂ → ℂ} (hG : MemLp G 2 volume) (hw : MemH (k + 1) w)
    {e : ℕ × ℕ} (he : e.1 + e.2 = 1) {α : ℕ × ℕ} (hα : α ∈ multiIdx k) :
    leibSum α G (weakPartial e w) =ᵐ[volume]
      fun x => G x * weakPartial e (weakPartial α w) x + commRem α G w e x := by
  have hα' := mem_multiIdx.1 hα
  have h0 := weakPartial_zero_ae_eq (hG.locallyIntegrable (by norm_num))
  have h1 := weakPartial_weakPartial_ae_eq hw (α := α) (β := e) (by omega)
  have h2 := weakPartial_weakPartial_ae_eq hw (α := e) (β := α) (by omega)
  filter_upwards [h0, h1, h2] with x hx0 hx1 hx2
  have hmem : ((0 : ℕ), (0 : ℕ)) ∈ leIdx α := mem_leIdx.2 ⟨Nat.zero_le _, Nat.zero_le _⟩
  rw [leibSum, ← Finset.add_sum_erase _ _ hmem]
  simp only [Nat.choose_zero_right, mul_one, Nat.cast_one, one_mul, Nat.sub_zero, Prod.mk.eta]
  rw [hx0, hx1, hx2, add_comm α e]
  rfl

/-- `lem:Hk-calculus`(1), commutator part, for the cut-off field `Ũ`. -/
theorem comm_main {k : ℕ} (hk : 3 ≤ k) {N N₁ V : Set ℂ} (hN : IsClosed N) (hN₁ : IsOpen N₁)
    (hNV : N ⊆ V) {U Ũ w : ℂ → ℂ} (hUV : ∀ x ∈ V, Ũ x = U x) (hŨ : MemH k Ũ)
    (hŨw : MemW1infOn univ Ũ) (hw : MemH (k + 1) w) (hwN : ∀ᵐ x, x ∉ N → w x = 0)
    {α : ℕ × ℕ} (hα : α ∈ multiIdx k) :
    (∃ G : ℂ → ℂ, MemLp G 2 (volume.restrict N₁) ∧
        HasWeakDerivOn N₁ (pdList α) (dotGrad U w) G) ∧
      MemLp (hkComm N₁ α U w) 2 volume ∧
      l2 (hkComm N₁ α U w) ≤ 2 * 2 ^ k * (normW1infOn univ Ũ + normH k Ũ) * normH k w := by
  have hα' := mem_multiIdx.1 hα
  have hk2 : 2 ≤ k := by omega
  set U₁ : ℂ → ℂ := fun x => ((Ũ x).re : ℂ) with hU₁
  set U₂ : ℂ → ℂ := fun x => ((Ũ x).im : ℂ) with hU₂
  obtain ⟨hU₁k, hU₂k, hnorm⟩ := hŨ.re_im
  have hn₁ : normH k U₁ ≤ normH k Ũ := by
    refine (pow_le_pow_iff_left₀ (normH_nonneg _ _) (normH_nonneg _ _) two_ne_zero).1 ?_
    nlinarith [sq_nonneg (normH k U₂)]
  have hn₂ : normH k U₂ ≤ normH k Ũ := by
    refine (pow_le_pow_iff_left₀ (normH_nonneg _ _) (normH_nonneg _ _) two_ne_zero).1 ?_
    nlinarith [sq_nonneg (normH k U₁)]
  set M := normW1infOn univ Ũ with hMdef
  have hM : 0 ≤ M := add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hinf₁ := fun (β : ℕ × ℕ) (hβ : β.1 + β.2 = 1) => eLpNorm_weakPartial_re_le hŨw hβ
  have hinf₂ := fun (β : ℕ × ℕ) (hβ : β.1 + β.2 = 1) => eLpNorm_weakPartial_im_le hŨw hβ
  -- derivatives of `w`
  have he₁ : ((1 : ℕ), (0 : ℕ)).1 + ((1 : ℕ), (0 : ℕ)).2 = 1 := rfl
  have he₂ : ((0 : ℕ), (1 : ℕ)).1 + ((0 : ℕ), (1 : ℕ)).2 = 1 := rfl
  have hw₁ : MemH k (weakPartial (1, 0) w) := (MemH.weakPartial (k := k) (γ := (1, 0)) hw).1
  have hw₂ : MemH k (weakPartial (0, 1) w) := (MemH.weakPartial (k := k) (γ := (0, 1)) hw).1
  have hz : ∀ e ∈ multiIdx (k + 1), ∀ᵐ x, x ∉ N → weakPartial e w x = 0 :=
    fun e he => MemH.weakPartial_eq_zero_outside hN hw hwN he
  have hαw : MemH 1 (weakPartial α w) :=
    (MemH.weakPartial (k := 1) (γ := α) (hw.mono_order (by omega))).1
  have hzα : ∀ e ∈ multiIdx 1, ∀ᵐ x, x ∉ N → weakPartial e (weakPartial α w) x = 0 :=
    fun e he => MemH.weakPartial_eq_zero_outside hN hαw (hz α (mem_multiIdx.2 (by omega))) he
  -- the weak derivative `S` of `Ũ·∇w` on the plane
  have hD₁ := hasWeakDerivOn_mul_of_memH hk2 hU₁k hw₁ hα
  have hD₂ := hasWeakDerivOn_mul_of_memH hk2 hU₂k hw₂ hα
  obtain ⟨hS₁, -⟩ := leibSum_bound hk2 hU₁k hw₁ hα
  obtain ⟨hS₂, -⟩ := leibSum_bound hk2 hU₂k hw₂ hα
  have hP₁ := (l2_mul_le_of_H2_left (hU₁k.mono_order hk2) (memLp_of_memH hw₁)).1
  have hP₂ := (l2_mul_le_of_H2_left (hU₂k.mono_order hk2) (memLp_of_memH hw₂)).1
  set S : ℂ → ℂ := fun x => leibSum α U₁ (weakPartial (1, 0) w) x +
    leibSum α U₂ (weakPartial (0, 1) w) x with hSdef
  have hSmem : MemLp S 2 volume := hS₁.add hS₂
  have hSD : HasWeakDerivOn univ (pdList α) (dotGrad Ũ w) S :=
    HasWeakDerivOn.add isOpen_univ
      ((hP₁.locallyIntegrable (by norm_num)).locallyIntegrableOn univ)
      ((hP₂.locallyIntegrable (by norm_num)).locallyIntegrableOn univ)
      ((hS₁.locallyIntegrable (by norm_num)).locallyIntegrableOn univ)
      ((hS₂.locallyIntegrable (by norm_num)).locallyIntegrableOn univ) hD₁ hD₂
  have hUw : dotGrad U w =ᵐ[volume] dotGrad Ũ w :=
    dotGrad_ae_eq_of_eqOn hNV hUV (hz (1, 0) (mem_multiIdx.2 (by simp only; omega)))
      (hz (0, 1) (mem_multiIdx.2 (by simp only; omega)))
  have hSN₁ : HasWeakDerivOn N₁ (pdList α) (dotGrad U w) S :=
    (hSD.mono (subset_univ N₁)).congr_ae (hUw.mono fun x hx _ => hx.symm)
      (Filter.Eventually.of_forall fun _ _ => rfl)
  refine ⟨⟨S, hSmem.restrict N₁, hSN₁⟩, ?_⟩
  -- the commutator
  have hA : ∀ᵐ x, x ∈ N₁ → weakPartialOn N₁ α (dotGrad U w) x = S x :=
    weakDerivOn_ae_eq hN₁ ((hSmem.locallyIntegrable (by norm_num)).locallyIntegrableOn N₁) hSN₁
  have hB : dotGrad U (weakPartial α w) =ᵐ[volume] dotGrad Ũ (weakPartial α w) :=
    dotGrad_ae_eq_of_eqOn hNV hUV (hzα (1, 0) (mem_multiIdx.2 (by simp)))
      (hzα (0, 1) (mem_multiIdx.2 (by simp)))
  have hsp₁ := leibSum_split (memLp_of_memH hU₁k) hw he₁ hα
  have hsp₂ := leibSum_split (memLp_of_memH hU₂k) hw he₂ hα
  have hC : hkComm N₁ α U w =ᵐ[volume]
      N₁.indicator (fun x => commRem α U₁ w (1, 0) x + commRem α U₂ w (0, 1) x) := by
    filter_upwards [hA, hB, hsp₁, hsp₂] with x hxA hxB hx₁ hx₂
    unfold hkComm
    by_cases hx : x ∈ N₁
    · rw [indicator_of_mem hx, indicator_of_mem hx, hxA hx, hxB, hSdef]
      simp only
      rw [hx₁, hx₂]
      simp only [dotGrad, hU₁, hU₂]
      ring
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]
  obtain ⟨hR₁, hR₁b⟩ := commRem_bound hk hU₁k hM hinf₁ hw he₁ hα
  obtain ⟨hR₂, hR₂b⟩ := commRem_bound hk hU₂k hM hinf₂ hw he₂ hα
  have hR : MemLp (fun x => commRem α U₁ w (1, 0) x + commRem α U₂ w (0, 1) x) 2 volume :=
    hR₁.add hR₂
  refine ⟨(hR.indicator hN₁.measurableSet).ae_eq hC.symm, ?_⟩
  rw [l2_congr_ae hC]
  have hwn := normH_nonneg k w
  calc l2 (N₁.indicator fun x => commRem α U₁ w (1, 0) x + commRem α U₂ w (0, 1) x)
      ≤ l2 (fun x => commRem α U₁ w (1, 0) x + commRem α U₂ w (0, 1) x) :=
        l2_indicator_le N₁ hR
    _ ≤ l2 (commRem α U₁ w (1, 0)) + l2 (commRem α U₂ w (0, 1)) := l2_add_le hR₁ hR₂
    _ ≤ 2 ^ k * ((M + normH k U₁) * normH k w) + 2 ^ k * ((M + normH k U₂) * normH k w) :=
        add_le_add hR₁b hR₂b
    _ ≤ 2 ^ k * ((M + normH k Ũ) * normH k w) + 2 ^ k * ((M + normH k Ũ) * normH k w) := by
        gcongr
    _ = 2 * 2 ^ k * (M + normH k Ũ) * normH k w := by ring

end NonUniqueEuler.Sob.HkCalcAux
