import NonUniqueEuler.H.Infra.Sobolev.DotGradSharp.Count
import NonUniqueEuler.H.Infra.Sobolev.DotGradSharp.L2
import NonUniqueEuler.H.Infra.Sobolev.DotGradSharp.Cutoff
import NonUniqueEuler.H.Infra.Sobolev.DotGradSharp.Deriv
import NonUniqueEuler.I.Infra.Sobolev.Leibniz
import NonUniqueEuler.I.Infra.Sobolev.Smooth
import NonUniqueEuler.I.Infra.Sobolev.Norm
import NonUniqueEuler.I.Infra.Sobolev.NormDeriv

/-!
# Proof: the transport term `h·∇w` in `H^k` with the sharp constant (library I-HK)

Proof of `NonUniqueEuler/I/Infra/Sobolev/DotGradSharp.lean` (same declaration, same statement),
following `04_ring.tex:1558-1567`.

1. Cutoff (`exists_cutoff_compact`): `g = ζ h` is `C^k` with compact support and `g = h` on an
   open `W ⊇ K`; since `∂_j w = 0` a.e. off `K`, `h·∇w = g·∇w` a.e.
2. `g·∇w = Re g · ∂₁w + Im g · ∂₂w`; `Re g`, `Im g ∈ C^k(ℝ²)` and `∂_j w ∈ H^k`. By the weak
   Leibniz formula (`MemH.weakPartial_mul_ae_eq`) and `∂^δ ∂₁ w = ∂^{δ+(1,0)} w`,
   `∂^δ ∂₂ w = ∂^{δ+(0,1)} w` (helper `Deriv.lean`), a.e.
   `∂^γ(g·∇w) = ∑_{β ≤ γ} C(γ,β) (Re ∂^β g · ∂^{γ-β+(1,0)} w + Im ∂^β g · ∂^{γ-β+(0,1)} w)`.
3. Pointwise Cauchy–Schwarz (`norm_re_mul_add_im_mul_le`): the `β` term is at most
   `C(γ,β) N F_{γ-β}` with `N = ‖h‖_{C^k(K)}`, `F_δ = (|∂^{δ+(1,0)}w|² + |∂^{δ+(0,1)}w|²)^{1/2}`;
   it vanishes a.e. off `K`.
4. `‖F_δ‖₂² = ‖∂^{δ+(1,0)}w‖₂² + ‖∂^{δ+(0,1)}w‖₂² ≤ ‖w‖²_{H^{k+1}}` (`memLp_pairNorm`); Minkowski
   (`memLp_l2_le_of_ae_bound`) and `∑_β C(γ,β) = 2^{|γ|}` give
   `‖∂^γ(h·∇w)‖₂ ≤ 2^{|γ|} N ‖w‖_{H^{k+1}}`.
5. Summing the squares over the `#multiIdx k = (k+1)(k+2)/2` multi-indices (`card_multiIdx`).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff

namespace NonUniqueEuler.Sob

namespace DotGradSharpAux

theorem mem_leIdx {γ β : ℕ × ℕ} : β ∈ leIdx γ ↔ β.1 ≤ γ.1 ∧ β.2 ≤ γ.2 := by
  simp [leIdx, Finset.mem_product]

theorem leIdx_sub_mem {k : ℕ} {γ β : ℕ × ℕ} (hγ : γ ∈ multiIdx k) (hβ : β ∈ leIdx γ) :
    (γ.1 - β.1, γ.2 - β.2) ∈ multiIdx k ∧ β.1 + β.2 ≤ k := by
  have h1 := mem_multiIdx.1 hγ
  have h2 := mem_leIdx.1 hβ
  exact ⟨mem_multiIdx.2 (by simp only; omega), by omega⟩

/-- Two distinct derivatives of order `≤ k` are controlled by the `H^k` norm. -/
theorem l2_sq_add_le_normH_sq {k : ℕ} {w : ℂ → ℂ} {α₁ α₂ : ℕ × ℕ} (h1 : α₁ ∈ multiIdx k)
    (h2 : α₂ ∈ multiIdx k) (hne : α₁ ≠ α₂) :
    l2 (weakPartial α₁ w) ^ 2 + l2 (weakPartial α₂ w) ^ 2 ≤ normH k w ^ 2 := by
  rw [normH_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    ← Finset.sum_pair (f := fun α => l2 (weakPartial α w) ^ 2) hne]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => sq_nonneg _
  intro α hα
  rw [Finset.mem_insert, Finset.mem_singleton] at hα
  rcases hα with rfl | rfl <;> assumption

/-- `‖F_δ‖₂ ≤ ‖w‖_{H^{k+1}}` for `F_δ = (|∂^{δ+(1,0)}w|² + |∂^{δ+(0,1)}w|²)^{1/2}`, `|δ| ≤ k`. -/
theorem l2_pairNorm_le {k : ℕ} {w : ℂ → ℂ} (hw : MemH (k + 1) w) {δ : ℕ × ℕ}
    (hδ : δ ∈ multiIdx k) :
    MemLp (pairNorm (weakPartial (δ.1 + 1, δ.2) w) (weakPartial (δ.1, δ.2 + 1) w)) 2 volume ∧
    l2 (pairNorm (weakPartial (δ.1 + 1, δ.2) w) (weakPartial (δ.1, δ.2 + 1) w)) ≤
      normH (k + 1) w := by
  have hδk := mem_multiIdx.1 hδ
  have h1 : (δ.1 + 1, δ.2) ∈ multiIdx (k + 1) := mem_multiIdx.2 (by simp only; omega)
  have h2 : (δ.1, δ.2 + 1) ∈ multiIdx (k + 1) := mem_multiIdx.2 (by simp only; omega)
  have hne : ((δ.1 + 1, δ.2) : ℕ × ℕ) ≠ (δ.1, δ.2 + 1) := by
    intro h
    have := congrArg Prod.fst h
    simp at this
  obtain ⟨hm, hsq⟩ := memLp_pairNorm (MemH.memLp_weakPartial hw h1).1
    (MemH.memLp_weakPartial hw h2).1
  refine ⟨hm, ?_⟩
  have := l2_sq_add_le_normH_sq (w := w) h1 h2 hne
  rw [← hsq] at this
  exact (pow_le_pow_iff_left₀ (l2_nonneg _) (normH_nonneg _ _) two_ne_zero).1 this

theorem partialD_re {k : ℕ} {g : ℂ → ℂ} (hg : ContDiff ℝ k g) {β : ℕ × ℕ}
    (hβ : β.1 + β.2 ≤ k) (x : ℂ) :
    partialD β (fun y => ((g y).re : ℂ)) x = ((partialD β g x).re : ℂ) :=
  partialD_clm_comp hg (Complex.ofRealCLM.comp Complex.reCLM) hβ x

theorem partialD_im {k : ℕ} {g : ℂ → ℂ} (hg : ContDiff ℝ k g) {β : ℕ × ℕ}
    (hβ : β.1 + β.2 ≤ k) (x : ℂ) :
    partialD β (fun y => ((g y).im : ℂ)) x = ((partialD β g x).im : ℂ) :=
  partialD_clm_comp hg (Complex.ofRealCLM.comp Complex.imCLM) hβ x

theorem memCk_re {k : ℕ} {g : ℂ → ℂ} (hg : ContDiff ℝ k g) (hgc : HasCompactSupport g) :
    MemCk k univ (fun y => ((g y).re : ℂ)) :=
  memCk_univ_of_contDiff ((Complex.ofRealCLM.comp Complex.reCLM).contDiff.comp hg)
    (hgc.comp_left (g := fun z : ℂ => ((z.re : ℝ) : ℂ)) (by simp))

theorem memCk_im {k : ℕ} {g : ℂ → ℂ} (hg : ContDiff ℝ k g) (hgc : HasCompactSupport g) :
    MemCk k univ (fun y => ((g y).im : ℂ)) :=
  memCk_univ_of_contDiff ((Complex.ofRealCLM.comp Complex.imCLM).contDiff.comp hg)
    (hgc.comp_left (g := fun z : ℂ => ((z.im : ℝ) : ℂ)) (by simp))

/-- One term of the Leibniz sum: `|C Re z A + C Im z B| ≤ C N (|A|² + |B|²)^{1/2}` when
`|z| ≤ N`. -/
theorem term_bound (c : ℕ) (z A B : ℂ) {N : ℝ} (hz : ‖z‖ ≤ N) :
    ‖(c : ℂ) * (z.re : ℂ) * A + (c : ℂ) * (z.im : ℂ) * B‖ ≤
      ((c : ℝ) * N) * Real.sqrt (‖A‖ ^ 2 + ‖B‖ ^ 2) := by
  have he : (c : ℂ) * (z.re : ℂ) * A + (c : ℂ) * (z.im : ℂ) * B =
      (c : ℂ) * ((z.re : ℂ) * A + (z.im : ℂ) * B) := by ring
  rw [he, norm_mul, Complex.norm_natCast, mul_assoc]
  gcongr
  exact (norm_re_mul_add_im_mul_le z A B).trans (by gcongr)

theorem ae_not_mem_univ (f : ℂ → ℂ) : ∀ᵐ x, x ∉ (univ : Set ℂ) → f x = 0 :=
  Eventually.of_forall fun x hx => absurd (mem_univ x) hx

/-- Step 2–4: the bound `‖∂^γ(g·∇w)‖₂ ≤ 2^{|γ|} N ‖w‖_{H^{k+1}}` for a compactly supported `C^k`
field `g` whose derivatives of order `≤ k` are bounded by `N` on `K`. -/
theorem l2_weakPartial_dotGrad_le {k : ℕ} {w g : ℂ → ℂ} {K : Set ℂ} (hK : IsClosed K)
    (hw : MemH (k + 1) w) (hwK : ∀ᵐ x, x ∉ K → w x = 0) (hg : ContDiff ℝ k g)
    (hgc : HasCompactSupport g) {N : ℝ} (hN0 : 0 ≤ N)
    (hN : ∀ β : ℕ × ℕ, β.1 + β.2 ≤ k → ∀ x ∈ K, ‖partialD β g x‖ ≤ N)
    (hmem : MemH k (dotGrad g w)) {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx k) :
    l2 (weakPartial γ (dotGrad g w)) ≤ 2 ^ (γ.1 + γ.2) * N * normH (k + 1) w := by
  have hc1 := memCk_re hg hgc
  have hc2 := memCk_im hg hgc
  obtain ⟨hw1, -⟩ := memH_e1 hw
  obtain ⟨hw2, -⟩ := memH_e2 hw
  obtain ⟨hm1, -⟩ := hw1.mul_of_memCk isClosed_univ (ae_not_mem_univ _) hc1
  obtain ⟨hm2, -⟩ := hw2.mul_of_memCk isClosed_univ (ae_not_mem_univ _) hc2
  have hsum := weakPartial_add_ae_eq hm1 hm2 hγ
  have hL1 := MemH.weakPartial_mul_ae_eq hw1 hc1 hγ
  have hL2 := MemH.weakPartial_mul_ae_eq hw2 hc2 hγ
  have hA : ∀ᵐ x, ∀ β ∈ leIdx γ,
      weakPartial (γ.1 - β.1, γ.2 - β.2) (weakPartial (1, 0) w) x =
        weakPartial (γ.1 - β.1 + 1, γ.2 - β.2) w x := by
    rw [eventually_all_finset]
    intro β hβ
    exact weakPartial_e1_ae_eq hw (leIdx_sub_mem hγ hβ).1
  have hB : ∀ᵐ x, ∀ β ∈ leIdx γ,
      weakPartial (γ.1 - β.1, γ.2 - β.2) (weakPartial (0, 1) w) x =
        weakPartial (γ.1 - β.1, γ.2 - β.2 + 1) w x := by
    rw [eventually_all_finset]
    intro β hβ
    exact weakPartial_e2_ae_eq hw (leIdx_sub_mem hγ hβ).1
  have hzA : ∀ᵐ x, ∀ β ∈ leIdx γ, x ∉ K → weakPartial (γ.1 - β.1 + 1, γ.2 - β.2) w x = 0 := by
    rw [eventually_all_finset]
    intro β hβ
    have := mem_multiIdx.1 (leIdx_sub_mem hγ hβ).1
    exact MemH.weakPartial_eq_zero_outside hK hw hwK (mem_multiIdx.2 (by simp only at this ⊢; omega))
  have hzB : ∀ᵐ x, ∀ β ∈ leIdx γ, x ∉ K → weakPartial (γ.1 - β.1, γ.2 - β.2 + 1) w x = 0 := by
    rw [eventually_all_finset]
    intro β hβ
    have := mem_multiIdx.1 (leIdx_sub_mem hγ hβ).1
    exact MemH.weakPartial_eq_zero_outside hK hw hwK (mem_multiIdx.2 (by simp only at this ⊢; omega))
  have hpt : ∀ᵐ x, ‖weakPartial γ (dotGrad g w) x‖ ≤ ∑ β ∈ leIdx γ,
      (((γ.1.choose β.1 * γ.2.choose β.2 : ℕ) : ℝ) * N) *
        ‖pairNorm (weakPartial (γ.1 - β.1 + 1, γ.2 - β.2) w)
          (weakPartial (γ.1 - β.1, γ.2 - β.2 + 1) w) x‖ := by
    filter_upwards [hsum, hL1, hL2, hA, hB, hzA, hzB] with x hs h1 h2 hAx hBx hzAx hzBx
    have hs' : weakPartial γ (dotGrad g w) x =
        weakPartial γ (fun x => ((g x).re : ℂ) * weakPartial (1, 0) w x) x +
          weakPartial γ (fun x => ((g x).im : ℂ) * weakPartial (0, 1) w x) x := hs
    rw [hs', h1, h2, ← Finset.sum_add_distrib]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun β hβ => ?_)
    have hβk := (leIdx_sub_mem hγ hβ).2
    rw [hAx β hβ, hBx β hβ, partialD_re hg hβk, partialD_im hg hβk, norm_pairNorm]
    by_cases hxK : x ∈ K
    · exact term_bound _ _ _ _ (hN β hβk x hxK)
    · rw [hzAx β hβ hxK, hzBx β hβ hxK]
      simp only [mul_zero, add_zero, norm_zero]
      positivity
  have hGm : AEStronglyMeasurable (weakPartial γ (dotGrad g w)) volume :=
    (MemH.memLp_weakPartial hmem hγ).1.1
  obtain ⟨-, hl⟩ := memLp_l2_le_of_ae_bound (leIdx γ)
    (fun β => ((γ.1.choose β.1 * γ.2.choose β.2 : ℕ) : ℝ) * N) (fun β _ => by positivity)
    (fun β hβ => (l2_pairNorm_le hw (leIdx_sub_mem hγ hβ).1).1) hGm hpt
  refine hl.trans ?_
  calc ∑ β ∈ leIdx γ, ((γ.1.choose β.1 * γ.2.choose β.2 : ℕ) : ℝ) * N *
        l2 (pairNorm (weakPartial (γ.1 - β.1 + 1, γ.2 - β.2) w)
          (weakPartial (γ.1 - β.1, γ.2 - β.2 + 1) w))
      ≤ ∑ β ∈ leIdx γ, ((γ.1.choose β.1 * γ.2.choose β.2 : ℕ) : ℝ) * N * normH (k + 1) w := by
        refine Finset.sum_le_sum fun β hβ => ?_
        gcongr
        exact (l2_pairNorm_le hw (leIdx_sub_mem hγ hβ).1).2
    _ = 2 ^ (γ.1 + γ.2) * N * normH (k + 1) w := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, sum_choose_leIdx]

/-- The sharp estimate for a compactly supported `C^k` field `g` whose derivatives of order
`≤ k` are bounded by `N` on `K`. -/
theorem sharp_aux {k : ℕ} {w g : ℂ → ℂ} {K : Set ℂ} (hK : IsClosed K)
    (hw : MemH (k + 1) w) (hwK : ∀ᵐ x, x ∉ K → w x = 0) (hg : ContDiff ℝ k g)
    (hgc : HasCompactSupport g) {N : ℝ} (hN0 : 0 ≤ N)
    (hN : ∀ β : ℕ × ℕ, β.1 + β.2 ≤ k → ∀ x ∈ K, ‖partialD β g x‖ ≤ N) :
    MemH k (dotGrad g w) ∧
      normH k (dotGrad g w) ≤
        2 ^ k * Real.sqrt (((k : ℝ) + 1) * ((k : ℝ) + 2) / 2) * N * normH (k + 1) w := by
  obtain ⟨hw1, -⟩ := memH_e1 hw
  obtain ⟨hw2, -⟩ := memH_e2 hw
  obtain ⟨hm1, -⟩ := hw1.mul_of_memCk isClosed_univ (ae_not_mem_univ _) (memCk_re hg hgc)
  obtain ⟨hm2, -⟩ := hw2.mul_of_memCk isClosed_univ (ae_not_mem_univ _) (memCk_im hg hgc)
  have hmem : MemH k (dotGrad g w) := (hm1.add hm2).1
  refine ⟨hmem, ?_⟩
  have hH := normH_nonneg (k + 1) w
  have hB : 0 ≤ 2 ^ k * N * normH (k + 1) w := by positivity
  have hbound : ∀ γ ∈ multiIdx k,
      l2 (weakPartial γ (dotGrad g w)) ≤ 2 ^ k * N * normH (k + 1) w := by
    intro γ hγ
    refine (l2_weakPartial_dotGrad_le hK hw hwK hg hgc hN0 hN hmem hγ).trans ?_
    gcongr
    · norm_num
    · exact mem_multiIdx.1 hγ
  rw [normH_eq]
  calc Real.sqrt (∑ γ ∈ multiIdx k, l2 (weakPartial γ (dotGrad g w)) ^ 2)
      ≤ Real.sqrt (∑ _γ ∈ multiIdx k, (2 ^ k * N * normH (k + 1) w) ^ 2) := by
        apply Real.sqrt_le_sqrt
        exact Finset.sum_le_sum fun γ hγ => pow_le_pow_left₀ (l2_nonneg _) (hbound γ hγ) 2
    _ = Real.sqrt ((multiIdx k).card) * (2 ^ k * N * normH (k + 1) w) := by
        rw [Finset.sum_const, nsmul_eq_mul, Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hB]
    _ = 2 ^ k * Real.sqrt (((k : ℝ) + 1) * ((k : ℝ) + 2) / 2) * N * normH (k + 1) w := by
        rw [card_multiIdx]
        ring

end DotGradSharpAux

open DotGradSharpAux

/-- The transport term `h·∇w` of a vector field `h ∈ C^k(K)` and `w ∈ H^{k+1}` vanishing a.e.
outside the compact set `K`, with the sharp constant `2^k ((k+1)(k+2)/2)^{1/2}` of `lem:uniform`
(`04_ring.tex:1532`, `:1555-1567`). -/
theorem MemH.dotGrad_of_memCk_sharp {k : ℕ} {w h : ℂ → ℂ} {K : Set ℂ} (hK : IsCompact K)
    (hw : MemH (k + 1) w) (hwK : ∀ᵐ x, x ∉ K → w x = 0) (hh : MemCk k K h) :
    MemH k (dotGrad h w) ∧
      normH k (dotGrad h w) ≤
        2 ^ k * Real.sqrt (((k : ℝ) + 1) * ((k : ℝ) + 2) / 2) * normCk k K h *
          normH (k + 1) w := by
  obtain ⟨V, hVo, hKV, hcd⟩ := hh.near
  obtain ⟨ζ, hζ, hζc, hζV, W, hWo, hKW, hζW⟩ := exists_cutoff_compact hK hVo hKV
  have hg : ContDiff ℝ k (fun x => (ζ x : ℂ) * h x) := contDiff_cutoff_mul hVo hζ hζV hcd
  have hgc : HasCompactSupport (fun x => (ζ x : ℂ) * h x) :=
    (hζc.comp_left (g := fun t : ℝ => (t : ℂ)) Complex.ofReal_zero).mul_right
  have hEq : EqOn (fun x => (ζ x : ℂ) * h x) h W := fun x hx => by simp [hζW hx]
  have hN : ∀ β : ℕ × ℕ, β.1 + β.2 ≤ k → ∀ x ∈ K,
      ‖partialD β (fun x => (ζ x : ℂ) * h x) x‖ ≤ normCk k K h := by
    intro β hβ x hx
    rw [partialD_eqOn hWo hEq β (hKW hx)]
    exact norm_partialD_le_normCk hh hβ hx
  obtain ⟨hm, hb⟩ := sharp_aux hK.isClosed hw hwK hg hgc (normCk_nonneg k K h) hN
  have h10 : ((1 : ℕ), (0 : ℕ)) ∈ multiIdx (k + 1) := mem_multiIdx.2 (by simp)
  have h01 : ((0 : ℕ), (1 : ℕ)) ∈ multiIdx (k + 1) := mem_multiIdx.2 (by simp)
  have hz1 := MemH.weakPartial_eq_zero_outside hK.isClosed hw hwK h10
  have hz2 := MemH.weakPartial_eq_zero_outside hK.isClosed hw hwK h01
  have hae : dotGrad (fun x => (ζ x : ℂ) * h x) w =ᵐ[volume] dotGrad h w := by
    filter_upwards [hz1, hz2] with x hx1 hx2
    by_cases hx : x ∈ K
    · have he : (ζ x : ℂ) * h x = h x := hEq (hKW hx)
      simp only [dotGrad, he]
    · simp only [dotGrad, hx1 hx, hx2 hx, mul_zero, add_zero]
  obtain ⟨hm', hn'⟩ := hm.congr_ae hae
  exact ⟨hm', hn'.trans_le hb⟩

end NonUniqueEuler.Sob
