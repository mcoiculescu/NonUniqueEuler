import Mathlib.Analysis.Complex.OperatorNorm
import NonUniqueEuler.H.Infra.Sobolev.Leibniz.Product
import NonUniqueEuler.H.Infra.Sobolev.Leibniz.Cutoff
import NonUniqueEuler.H.Infra.Sobolev.Leibniz.L2
import NonUniqueEuler.H.Infra.Sobolev.Leibniz.Deriv
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv
import NonUniqueEuler.I.Infra.Sobolev.Norm
import NonUniqueEuler.I.Infra.Sobolev.Smooth

/-!
# Proof: products with `C^k` functions in `H^k` (library I-HK)

Proof of `NonUniqueEuler/I/Infra/Sobolev/Leibniz.lean` (same declarations, same statements).

* The weak Leibniz formula is `LeibnizAux.leibniz_2d` (helper `Product.lean`) applied to the
  family `F δ = ∂^δ f` of weak derivatives of `f ∈ H^k` (`family_facts`: `∂₁ ∂^δ f = ∂^{δ+e₁} f`
  weakly, by `HasWeakDerivOn.of_append` and `HasWeakDerivOn.perm`), followed by uniqueness of
  weak derivatives (`weakDerivOn_ae_eq`). It only needs `χ ∈ C^k(ℝ²)`; the `C¹` test functions
  `χ φ` are handled by mollification (helper `Mollify.lean`).
* Vanishing outside `K`: on the open set `Kᶜ` both `∂^γ f` and `0` are weak derivatives of `f`.
* Local multipliers `χ ∈ C^k(K)`: replace `χ` by `ζ χ` with a smooth cutoff `ζ = 1` near `K`,
  `tsupport ζ ⊆ V` (helper `Cutoff.lean`); then `χ f = (ζχ) f` a.e., the Leibniz formula holds
  for `ζ χ`, and on `K` the derivatives of `ζ χ` are those of `χ`, bounded by `‖χ‖_{C^k(K)}`,
  while the `∂^{γ-β} f` vanish a.e. outside `K`. Then `∑_{β ≤ γ} C(γ,β) = 2^{|γ|}` and
  `#multiIdx k ≤ (k+1)²` (helper `L2.lean`).
* The transport term: `h·∇w = Re h ∂₁w + Im h ∂₂w`, with `‖Re h‖_{C^k(K)}, ‖Im h‖_{C^k(K)} ≤
  ‖h‖_{C^k(K)}` and `‖∂_i w‖_{H^k} ≤ ‖w‖_{H^{k+1}}`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff

namespace NonUniqueEuler.Sob

namespace LeibnizAux

/-- The weak derivatives of an `H^k` function form a family to which `leibniz_2d` applies. -/
theorem family_facts {k : ℕ} {f : ℂ → ℂ} (hf : MemH k f) :
    (∀ δ ∈ multiIdx k, LocallyIntegrable (weakPartial δ f)) ∧
    (∀ δ : ℕ × ℕ, δ.1 + δ.2 < k →
      HasWeakDerivOn univ [1] (weakPartial δ f) (weakPartial (δ.1 + 1, δ.2) f)) ∧
    (∀ δ : ℕ × ℕ, δ.1 + δ.2 < k →
      HasWeakDerivOn univ [Complex.I] (weakPartial δ f) (weakPartial (δ.1, δ.2 + 1) f)) := by
  refine ⟨fun δ hδ => (memLp_wp hf hδ).1.locallyIntegrable (by norm_num),
    fun δ hδ => ?_, fun δ hδ => ?_⟩
  · have hδk : δ ∈ multiIdx k := mem_multiIdx.2 hδ.le
    have hδk' : (δ.1 + 1, δ.2) ∈ multiIdx k := mem_multiIdx.2 (by simp; omega)
    have a := (memLp_wp hf hδk).2
    have b := (memLp_wp hf hδk').2
    have e : pdList (δ.1 + 1, δ.2) = 1 :: pdList δ := by
      simp [pdList, List.replicate_succ]
    rw [e] at b
    exact HasWeakDerivOn.of_append a (b.perm (List.perm_append_singleton _ _).symm)
  · have hδk : δ ∈ multiIdx k := mem_multiIdx.2 hδ.le
    have hδk' : (δ.1, δ.2 + 1) ∈ multiIdx k := mem_multiIdx.2 (by simp; omega)
    have a := (memLp_wp hf hδk).2
    have b := (memLp_wp hf hδk').2
    have e : pdList (δ.1, δ.2 + 1) = pdList δ ++ [Complex.I] := by
      simp [pdList, List.replicate_succ', List.append_assoc]
    rw [e] at b
    exact HasWeakDerivOn.of_append a b

theorem weakPartial_zero_ae_eq {k : ℕ} {f : ℂ → ℂ} (hf : MemH k f) :
    weakPartial (0, 0) f =ᵐ[volume] f :=
  wp_ae_eq ((memH_iff.1 hf).1.locallyIntegrable (by norm_num)) (hasWeakDerivOn_nil_self f)

/-- The Leibniz sum `∑_{β ≤ γ} C(γ,β) ∂^β χ ∂^{γ-β} f`. -/
def leibnizSum (γ : ℕ × ℕ) (χ f : ℂ → ℂ) (x : ℂ) : ℂ :=
  ∑ β ∈ leIdx γ, ((γ.1.choose β.1 * γ.2.choose β.2 : ℕ) : ℂ) * partialD β χ x *
    weakPartial (γ.1 - β.1, γ.2 - β.2) f x

theorem mem_leIdx {γ β : ℕ × ℕ} : β ∈ leIdx γ ↔ β.1 ≤ γ.1 ∧ β.2 ≤ γ.2 := by
  simp [leIdx, Finset.mem_product]

theorem leIdx_sub_mem {k : ℕ} {γ β : ℕ × ℕ} (hγ : γ ∈ multiIdx k) (hβ : β ∈ leIdx γ) :
    (γ.1 - β.1, γ.2 - β.2) ∈ multiIdx k ∧ β.1 + β.2 ≤ k := by
  have h1 := mem_multiIdx.1 hγ
  have h2 := mem_leIdx.1 hβ
  exact ⟨mem_multiIdx.2 (by simp; omega), by omega⟩

theorem locallyIntegrable_leibnizSum {k : ℕ} {f χ : ℂ → ℂ} (hf : MemH k f)
    (hχ : ContDiff ℝ k χ) {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx k) :
    LocallyIntegrable (leibnizSum γ χ f) := by
  obtain ⟨hFl, -, -⟩ := family_facts hf
  refine locallyIntegrable_finsetSum _ fun β hβ => ?_
  obtain ⟨h1, h2⟩ := leIdx_sub_mem hγ hβ
  exact (hFl _ h1).continuous_mul
    (continuous_const.mul (continuous_iterDirDeriv hχ (by simpa using h2)))

/-- The weak Leibniz rule for globally `C^k` multipliers (no bound on the derivatives). -/
theorem hasWeakDerivOn_mul_leibnizSum {k : ℕ} {f χ : ℂ → ℂ} (hf : MemH k f)
    (hχ : ContDiff ℝ k χ) {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx k) :
    HasWeakDerivOn univ (pdList γ) (fun x => χ x * weakPartial (0, 0) f x)
      (leibnizSum γ χ f) := by
  obtain ⟨hFl, h1, h2⟩ := family_facts hf
  exact leibniz_2d hχ hFl h1 h2 hγ

/-- Weak derivatives of a function vanishing a.e. outside a closed set vanish a.e. outside
it. -/
theorem weakPartial_eq_zero_outside_aux {k : ℕ} {f : ℂ → ℂ} {K : Set ℂ} (hK : IsClosed K)
    (hf : MemH k f) (hfK : ∀ᵐ x, x ∉ K → f x = 0) {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx k) :
    ∀ᵐ x, x ∉ K → weakPartial γ f x = 0 := by
  obtain ⟨hm, hw⟩ := memLp_wp hf hγ
  have hV : IsOpen Kᶜ := hK.isOpen_compl
  have h1 : HasWeakDerivOn Kᶜ (pdList γ) f (weakPartial γ f) := hw.mono (subset_univ _)
  have h2 : HasWeakDerivOn Kᶜ (pdList γ) f 0 := by
    intro φ hφ
    simp only [Pi.zero_apply, zero_mul, integral_zero, mul_zero]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hfK] with x hx
    by_cases hxK : x ∈ K
    · have hd := hφ.iterDirDeriv (pdList γ)
      have : iterDirDeriv (pdList γ) φ x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hd.subset h hxK)
      simp [this]
    · simp [hx hxK]
  have := HasWeakDerivOn.ae_eq hV ((hm.locallyIntegrable (by norm_num)).locallyIntegrableOn _)
    (locallyIntegrable_zero.locallyIntegrableOn _) h1 h2
  filter_upwards [this] with x hx hxK
  exact hx hxK

/-- The product estimate for a multiplier that is `C^k` on an open `V ⊇ K` with derivatives
of order `≤ k` bounded by `N` on `K`. -/
theorem mul_aux {k : ℕ} {f χ : ℂ → ℂ} {K V : Set ℂ} (hK : IsClosed K) (hV : IsOpen V)
    (hKV : K ⊆ V) (hf : MemH k f) (hfK : ∀ᵐ x, x ∉ K → f x = 0) (hχ : ContDiffOn ℝ k χ V)
    {N : ℝ} (hN0 : 0 ≤ N) (hN : ∀ β : ℕ × ℕ, β.1 + β.2 ≤ k → ∀ x ∈ K, ‖partialD β χ x‖ ≤ N) :
    MemH k (fun x => χ x * f x) ∧
      normH k (fun x => χ x * f x) ≤ (k + 1) * 2 ^ k * N * normH k f := by
  obtain ⟨ζ, hζ, hζV, W, hWo, hKW, hζW⟩ := exists_cutoff hK hV hKV
  set χ' : ℂ → ℂ := fun x => (ζ x : ℂ) * χ x with hχ'def
  have hχ' : ContDiff ℝ k χ' := contDiff_cutoff_mul hV hζ hζV hχ
  have hEq : EqOn χ' χ W := fun x hx => by simp [hχ'def, hζW hx]
  have hpd : ∀ β, ∀ x ∈ K, partialD β χ' x = partialD β χ x := fun β x hx =>
    partialD_eqOn hWo hEq β (hKW hx)
  have hF0 := weakPartial_zero_ae_eq hf
  have hmulEq : (fun x => χ' x * weakPartial (0, 0) f x) =ᵐ[volume] (fun x => χ x * f x) := by
    filter_upwards [hF0, hfK] with x hx0 hxK
    by_cases hx : x ∈ K
    · simp only [hx0]
      rw [hEq (hKW hx)]
    · simp [hx0, hxK hx]
  have hweak : ∀ γ ∈ multiIdx k,
      HasWeakDerivOn univ (pdList γ) (fun x => χ x * f x) (leibnizSum γ χ' f) := fun γ hγ =>
    (hasWeakDerivOn_mul_leibnizSum hf hχ' hγ).congr_ae (hmulEq.mono fun x hx _ => hx)
      (Eventually.of_forall fun _ _ => rfl)
  have hbound : ∀ γ ∈ multiIdx k,
      MemLp (leibnizSum γ χ' f) 2 volume ∧ l2 (leibnizSum γ χ' f) ≤ 2 ^ k * N * normH k f := by
    intro γ hγ
    have hγk := mem_multiIdx.1 hγ
    have hall : ∀ᵐ x, ∀ β ∈ leIdx γ, x ∉ K → weakPartial (γ.1 - β.1, γ.2 - β.2) f x = 0 := by
      rw [eventually_all_finset]
      intro β hβ
      exact weakPartial_eq_zero_outside_aux hK hf hfK (leIdx_sub_mem hγ hβ).1
    have hae : ∀ᵐ x, ‖leibnizSum γ χ' f x‖ ≤ ∑ β ∈ leIdx γ,
        ((γ.1.choose β.1 * γ.2.choose β.2 : ℕ) : ℝ) * N *
          ‖weakPartial (γ.1 - β.1, γ.2 - β.2) f x‖ := by
      filter_upwards [hall] with x hx
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun β hβ => ?_)
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      by_cases hxK : x ∈ K
      · rw [hpd β x hxK]
        gcongr
        exact hN β (leIdx_sub_mem hγ hβ).2 x hxK
      · rw [hx β hβ hxK]
        simp
    obtain ⟨hGL, hGl⟩ := memLp_l2_le_of_ae_bound (leIdx γ)
      (fun β => ((γ.1.choose β.1 * γ.2.choose β.2 : ℕ) : ℝ) * N)
      (fun β _ => by positivity)
      (fun β hβ => (memLp_wp hf (leIdx_sub_mem hγ hβ).1).1)
      (locallyIntegrable_leibnizSum hf hχ' hγ).aestronglyMeasurable hae
    refine ⟨hGL, hGl.trans ?_⟩
    calc ∑ β ∈ leIdx γ, ((γ.1.choose β.1 * γ.2.choose β.2 : ℕ) : ℝ) * N *
          l2 (weakPartial (γ.1 - β.1, γ.2 - β.2) f)
        ≤ ∑ β ∈ leIdx γ, ((γ.1.choose β.1 * γ.2.choose β.2 : ℕ) : ℝ) * N * normH k f := by
          refine Finset.sum_le_sum fun β hβ => ?_
          gcongr
          exact l2_wp_le (leIdx_sub_mem hγ hβ).1
      _ = 2 ^ (γ.1 + γ.2) * N * normH k f := by
          rw [← Finset.sum_mul, ← Finset.sum_mul, sum_choose_leIdx]
      _ ≤ 2 ^ k * N * normH k f := by
          have := normH_nonneg k f
          gcongr
          · norm_num
  -- membership
  have hG00 : leibnizSum (0, 0) χ' f = fun x => χ' x * weakPartial (0, 0) f x := by
    funext x
    simp [leibnizSum, leIdx, partialD, pdList]
  have hmemLp : MemLp (fun x => χ x * f x) 2 volume := by
    have := (hbound (0, 0) (zero_mem_multiIdx k)).1
    rw [hG00] at this
    exact this.ae_eq hmulEq
  have hmem : MemH k (fun x => χ x * f x) :=
    memH_iff.2 ⟨hmemLp, fun γ hγ => ⟨leibnizSum γ χ' f, (hbound γ hγ).1, hweak γ hγ⟩⟩
  refine ⟨hmem, ?_⟩
  -- the norm
  have hl2 : ∀ γ ∈ multiIdx k, l2 (weakPartial γ (fun x => χ x * f x)) ≤
      2 ^ k * N * normH k f := by
    intro γ hγ
    have hae := wp_ae_eq ((hbound γ hγ).1.locallyIntegrable (by norm_num)) (hweak γ hγ)
    have : l2 (weakPartial γ (fun x => χ x * f x)) = l2 (leibnizSum γ χ' f) := by
      unfold l2
      rw [eLpNorm_congr_ae hae]
    rw [this]
    exact (hbound γ hγ).2
  rw [normH_eq]
  have hB : 0 ≤ 2 ^ k * N * normH k f := by
    have := normH_nonneg k f
    positivity
  calc Real.sqrt (∑ γ ∈ multiIdx k, l2 (weakPartial γ (fun x => χ x * f x)) ^ 2)
      ≤ (k + 1) * (2 ^ k * N * normH k f) :=
        sqrt_sum_sq_le hB (fun γ _ => l2_nonneg _) hl2
    _ = (k + 1) * 2 ^ k * N * normH k f := by ring

end LeibnizAux

open LeibnizAux

/-- The weak Leibniz formula for a `C^k` multiplier with bounded derivatives. -/
theorem MemH.weakPartial_mul_ae_eq {k : ℕ} {f χ : ℂ → ℂ} (hf : MemH k f)
    (hχ : MemCk k univ χ) {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx k) :
    weakPartial γ (fun x => χ x * f x) =ᵐ[volume] fun x =>
      ∑ β ∈ leIdx γ, ((γ.1.choose β.1 * γ.2.choose β.2 : ℕ) : ℂ) * partialD β χ x *
        weakPartial (γ.1 - β.1, γ.2 - β.2) f x := by
  obtain ⟨V, -, hUV, hcd⟩ := hχ.near
  have hVu : V = univ := eq_univ_of_univ_subset hUV
  subst hVu
  have hχc : ContDiff ℝ k χ := contDiffOn_univ.1 hcd
  have hL := (hasWeakDerivOn_mul_leibnizSum hf hχc hγ).congr_ae
    ((weakPartial_zero_ae_eq hf).mono fun x hx _ => by rw [hx])
    (Eventually.of_forall fun _ _ => rfl)
  have := weakDerivOn_ae_eq isOpen_univ
    ((locallyIntegrable_leibnizSum hf hχc hγ).locallyIntegrableOn univ) hL
  filter_upwards [this] with x hx
  exact hx (mem_univ x)

/-- `H^k` is stable under multiplication by `χ ∈ C^k(K)` when `f = 0` a.e. outside the closed
set `K`, with `‖χ f‖_{H^k} ≤ (k+1) 2^k ‖χ‖_{C^k(K)} ‖f‖_{H^k}`. (`K = univ` is the global
statement.) -/
theorem MemH.mul_of_memCk {k : ℕ} {f χ : ℂ → ℂ} {K : Set ℂ} (hK : IsClosed K) (hf : MemH k f)
    (hfK : ∀ᵐ x, x ∉ K → f x = 0) (hχ : MemCk k K χ) :
    MemH k (fun x => χ x * f x) ∧
      normH k (fun x => χ x * f x) ≤ (k + 1) * 2 ^ k * normCk k K χ * normH k f := by
  obtain ⟨V, hVo, hKV, hcd⟩ := hχ.near
  exact mul_aux hK hVo hKV hf hfK hcd (normCk_nonneg k K χ)
    (fun β hβ x hx => norm_partialD_le_normCk hχ hβ hx)

/-- Weak derivatives of a function vanishing a.e. outside a closed set vanish a.e. outside
it. -/
theorem MemH.weakPartial_eq_zero_outside {k : ℕ} {f : ℂ → ℂ} {K : Set ℂ} (hK : IsClosed K)
    (hf : MemH k f) (hfK : ∀ᵐ x, x ∉ K → f x = 0) {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx k) :
    ∀ᵐ x, x ∉ K → weakPartial γ f x = 0 :=
  weakPartial_eq_zero_outside_aux hK hf hfK hγ

/-- The transport term `h·∇w` of a vector field `h ∈ C^k(K)` and `w ∈ H^{k+1}` vanishing a.e.
outside the closed set `K`. -/
theorem MemH.dotGrad_of_memCk {k : ℕ} {w h : ℂ → ℂ} {K : Set ℂ} (hK : IsClosed K)
    (hw : MemH (k + 1) w) (hwK : ∀ᵐ x, x ∉ K → w x = 0) (hh : MemCk k K h) :
    MemH k (dotGrad h w) ∧
      normH k (dotGrad h w) ≤ (k + 1) * 2 ^ (k + 1) * normCk k K h * normH (k + 1) w := by
  -- the two derivatives of `w`
  obtain ⟨hw1, hn1⟩ := memH_wp_e1 hw
  obtain ⟨hw2, hn2⟩ := memH_wp_e2 hw
  have hz1 := weakPartial_eq_zero_outside_aux hK hw hwK (γ := (1, 0)) (by simp [mem_multiIdx])
  have hz2 := weakPartial_eq_zero_outside_aux hK hw hwK (γ := (0, 1)) (by simp [mem_multiIdx])
  -- the two components of `h`
  have hLre : ‖Complex.ofRealCLM.comp Complex.reCLM‖ ≤ 1 :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (by simp)
  have hLim : ‖Complex.ofRealCLM.comp Complex.imCLM‖ ≤ 1 :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (by simp)
  obtain ⟨hre, hnre⟩ := LeibnizAux.MemCk.clm_comp hh _ hLre
  obtain ⟨him, hnim⟩ := LeibnizAux.MemCk.clm_comp hh _ hLim
  simp only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply,
    Complex.ofRealCLM_apply] at hre hnre him hnim
  obtain ⟨hm1, hb1⟩ := hw1.mul_of_memCk hK hz1 hre
  obtain ⟨hm2, hb2⟩ := hw2.mul_of_memCk hK hz2 him
  have hsplit : dotGrad h w = (fun x => ((h x).re : ℂ) * weakPartial (1, 0) w x) +
      (fun x => ((h x).im : ℂ) * weakPartial (0, 1) w x) := rfl
  rw [hsplit]
  obtain ⟨hm, hb⟩ := hm1.add hm2
  refine ⟨hm, hb.trans ?_⟩
  have hC := normCk_nonneg k K h
  have hH := normH_nonneg (k + 1) w
  have hA : (0 : ℝ) ≤ (k + 1) * 2 ^ k := by positivity
  calc normH k (fun x => ((h x).re : ℂ) * weakPartial (1, 0) w x) +
        normH k (fun x => ((h x).im : ℂ) * weakPartial (0, 1) w x)
      ≤ (k + 1) * 2 ^ k * normCk k K h * normH (k + 1) w +
          (k + 1) * 2 ^ k * normCk k K h * normH (k + 1) w := by
        gcongr
        · exact hb1.trans (by gcongr; exact normH_nonneg _ _)
        · exact hb2.trans (by gcongr; exact normH_nonneg _ _)
    _ = (k + 1) * 2 ^ (k + 1) * normCk k K h * normH (k + 1) w := by ring

end NonUniqueEuler.Sob
