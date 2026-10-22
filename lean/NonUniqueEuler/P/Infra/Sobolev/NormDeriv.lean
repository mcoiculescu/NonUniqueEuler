import NonUniqueEuler.Defs.Infra.Sobolev
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv

/-!
# Proof: weak derivatives of `H^k` functions and the order of the norm (library I-HK)

Proves `I/Infra/Sobolev/NormDeriv.lean` (same declarations, statements copied verbatim).

Uses `weakDerivOn_ae_eq` and `HasWeakDerivOn.perm` (`I/Infra/Sobolev/WeakDeriv.lean`) as black
boxes, and `weakDerivOn_spec` (`Defs/Infra/Sobolev.lean`).

* `weakPartial_ae_eq`: uniqueness of the weak derivative (an `L²` function is locally
  integrable).
* `memLp_weakPartial`: the chosen weak derivative agrees a.e. with the `L²` one of `MemH`.
* the norm bounds are single terms (or sub-sums) of the defining sum.
* `MemH.weakPartial`: `∂^β (∂^γ f) = ∂^{β+γ} f` weakly. For a test function `φ`, apply the
  definition of `∂^γ f` to the test function `∂^β φ`, and the definition of `∂^{β+γ} f`
  (with the directions reordered as `pdList γ ++ pdList β`, `HasWeakDerivOn.perm`) to `φ`;
  then `β ↦ β + γ` is injective from `multiIdx k` into `multiIdx (k + |γ|)`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace NonUniqueEuler.Sob

/-- An `L²` function on the plane is locally integrable on every set. -/
private theorem locallyIntegrableOn_of_memLp_two {g : ℂ → ℂ} (hg : MemLp g 2 volume)
    (V : Set ℂ) : LocallyIntegrableOn g V :=
  (hg.locallyIntegrable (by norm_num)).locallyIntegrableOn V

set_option linter.unusedVariables false in
/-- The weak derivative of an `H^k` function, `|γ| ≤ k`, agrees a.e. with any `L²` weak
derivative. -/
theorem MemH.weakPartial_ae_eq {k : ℕ} {f g : ℂ → ℂ} (hf : MemH k f) {γ : ℕ × ℕ}
    (hγ : γ ∈ multiIdx k) (hg : MemLp g 2 volume) (h : HasWeakDerivOn univ (pdList γ) f g) :
    weakPartial γ f =ᵐ[volume] g := by
  have := weakDerivOn_ae_eq isOpen_univ (locallyIntegrableOn_of_memLp_two hg univ) h
  exact this.mono fun x hx => hx (mem_univ x)

theorem MemH.memLp_weakPartial {k : ℕ} {f : ℂ → ℂ} (hf : MemH k f) {γ : ℕ × ℕ}
    (hγ : γ ∈ multiIdx k) :
    MemLp (weakPartial γ f) 2 volume ∧ HasWeakDerivOn univ (pdList γ) f (weakPartial γ f) := by
  obtain ⟨g, hg, hfg⟩ := hf.deriv γ hγ
  rw [Measure.restrict_univ] at hg
  have hae : weakPartial γ f =ᵐ[volume] g := hf.weakPartial_ae_eq hγ hg hfg
  refine ⟨hg.ae_eq hae.symm, ?_⟩
  exact (weakDerivOn_spec (locallyIntegrableOn_of_memLp_two hg univ) hfg).2

set_option linter.unusedVariables false in
/-- `‖∂^γ f‖_{L²} ≤ ‖f‖_{H^k}` for `|γ| ≤ k`, and `‖f‖_{L²} ≤ ‖f‖_{H^k}`. -/
theorem MemH.l2_weakPartial_le {k : ℕ} {f : ℂ → ℂ} (hf : MemH k f) {γ : ℕ × ℕ}
    (hγ : γ ∈ multiIdx k) : l2 (weakPartial γ f) ≤ normH k f := by
  rw [normH_eq]
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun β => l2 (weakPartial β f) ^ 2)
    (fun β _ => sq_nonneg _) hγ

theorem MemH.l2_le {k : ℕ} {f : ℂ → ℂ} (hf : MemH k f) : l2 f ≤ normH k f := by
  have h0 := zero_mem_multiIdx k
  have hf2 : MemLp f 2 volume := (memH_iff.1 hf).1
  have hnil : HasWeakDerivOn univ (pdList (0, 0)) f f := by
    intro φ _
    simp [pdList]
  have hae : weakPartial (0, 0) f =ᵐ[volume] f := hf.weakPartial_ae_eq h0 hf2 hnil
  have heq : l2 (weakPartial (0, 0) f) = l2 f := by
    unfold l2
    rw [eLpNorm_congr_ae hae]
  rw [← heq]
  exact hf.l2_weakPartial_le h0

set_option linter.unusedVariables false in
theorem MemH.normH_mono {k k' : ℕ} {f : ℂ → ℂ} (hf : MemH k' f) (hk : k ≤ k') :
    normH k f ≤ normH k' f := by
  rw [normH_eq, normH_eq]
  refine Real.sqrt_le_sqrt ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg (multiIdx_mono hk) fun _ _ _ => sq_nonneg _

/-- The directions of `∂^{β+γ}` are a permutation of those of `∂^γ ∂^β`. -/
private theorem pdList_add_perm (β γ : ℕ × ℕ) :
    (pdList (β + γ)).Perm (pdList γ ++ pdList β) := by
  simp only [pdList, Prod.fst_add, Prod.snd_add, List.replicate_add]
  set A := List.replicate β.1 (1 : ℂ)
  set B := List.replicate β.2 Complex.I
  set C := List.replicate γ.1 (1 : ℂ)
  set D := List.replicate γ.2 Complex.I
  have h1 : (C ++ (B ++ D)).Perm (B ++ (C ++ D)) := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm (l₁ := C) (l₂ := B)).append_right D
  have h2 : (A ++ C ++ (B ++ D)).Perm (A ++ B ++ (C ++ D)) := by
    simpa only [List.append_assoc] using h1.append_left A
  exact h2.trans List.perm_append_comm

/-- `∂^β (∂^γ f) = ∂^{β+γ} f` weakly. -/
private theorem hasWeakDerivOn_weakPartial_comp {β γ : ℕ × ℕ} {f g h : ℂ → ℂ}
    (hg : HasWeakDerivOn univ (pdList γ) f g) (hh : HasWeakDerivOn univ (pdList (β + γ)) f h) :
    HasWeakDerivOn univ (pdList β) g h := by
  intro φ hφ
  have hh' := hh.perm (pdList_add_perm β γ) φ hφ
  have hg' := hg _ (hφ.iterDirDeriv (pdList β))
  rw [iterDirDeriv_append, hg'] at hh'
  simp only [List.length_append, pdList_length] at hh'
  simp only [pdList_length]
  have hs : ((-1 : ℂ) ^ (γ.1 + γ.2)) * (-1 : ℂ) ^ (γ.1 + γ.2) = 1 := by
    rw [← mul_pow]; simp
  calc ∫ x, g x * iterDirDeriv (pdList β) φ x
      = ((-1 : ℂ) ^ (γ.1 + γ.2)) * ((-1 : ℂ) ^ (γ.1 + γ.2) *
          ∫ x, g x * iterDirDeriv (pdList β) φ x) := by rw [← mul_assoc, hs, one_mul]
    _ = ((-1 : ℂ) ^ (γ.1 + γ.2)) * ((-1 : ℂ) ^ (γ.1 + γ.2 + (β.1 + β.2)) * ∫ x, h x * φ x) := by
        rw [hh']
    _ = (-1 : ℂ) ^ (β.1 + β.2) * ∫ x, h x * φ x := by
        rw [pow_add (-1 : ℂ) (γ.1 + γ.2) (β.1 + β.2), ← mul_assoc, ← mul_assoc, hs, one_mul]

/-- Derivatives of `H^{k+|γ|}` functions lie in `H^k`.

`protected`: the elaborator opens the namespace
`MemH` inside every `theorem MemH.foo`, so an unprotected `MemH.weakPartial` would capture the
identifier `weakPartial` in the statements of `MemH.weakPartial_mul_ae_eq`,
`MemH.weakPartial_eq_zero_outside` (`Leibniz.lean`) and `MemH.weakPartial_comp_smul`
(`Symmetry.lean`) whenever this file is in the environment. Use it as `hf.weakPartial` or
`MemH.weakPartial hf`. -/
protected theorem MemH.weakPartial {k : ℕ} {γ : ℕ × ℕ} {f : ℂ → ℂ} (hf : MemH (k + (γ.1 + γ.2)) f) :
    MemH k (weakPartial γ f) ∧ normH k (weakPartial γ f) ≤ normH (k + (γ.1 + γ.2)) f := by
  have hγ : γ ∈ multiIdx (k + (γ.1 + γ.2)) := mem_multiIdx.2 (by omega)
  obtain ⟨hg2, hg⟩ := hf.memLp_weakPartial hγ
  have hβγ : ∀ β ∈ multiIdx k, β + γ ∈ multiIdx (k + (γ.1 + γ.2)) := by
    intro β hβ
    rw [mem_multiIdx] at hβ ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  have hder : ∀ β ∈ multiIdx k, MemLp (Sob.weakPartial (β + γ) f) 2 volume ∧
      HasWeakDerivOn univ (pdList β) (Sob.weakPartial γ f) (Sob.weakPartial (β + γ) f) := by
    intro β hβ
    obtain ⟨h1, h2⟩ := hf.memLp_weakPartial (hβγ β hβ)
    exact ⟨h1, hasWeakDerivOn_weakPartial_comp hg h2⟩
  have hmem : MemH k (Sob.weakPartial γ f) :=
    memH_iff.2 ⟨hg2, fun β hβ => ⟨_, hder β hβ⟩⟩
  refine ⟨hmem, ?_⟩
  have hl2 : ∀ β ∈ multiIdx k, l2 (Sob.weakPartial β (Sob.weakPartial γ f)) ^ 2 =
      l2 (Sob.weakPartial (β + γ) f) ^ 2 := by
    intro β hβ
    have hae := hmem.weakPartial_ae_eq hβ (hder β hβ).1 (hder β hβ).2
    unfold l2
    rw [eLpNorm_congr_ae hae]
  rw [normH_eq, normH_eq]
  refine Real.sqrt_le_sqrt ?_
  rw [Finset.sum_congr rfl hl2]
  have hinj : Set.InjOn (fun β : ℕ × ℕ => β + γ) (multiIdx k) :=
    fun _ _ _ _ h => add_right_cancel h
  rw [← Finset.sum_image (f := fun α => l2 (Sob.weakPartial α f) ^ 2) hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => sq_nonneg _
  intro α hα
  obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hα
  exact hβγ β hβ

end NonUniqueEuler.Sob
