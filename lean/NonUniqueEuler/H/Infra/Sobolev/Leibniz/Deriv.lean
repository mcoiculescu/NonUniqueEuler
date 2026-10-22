import Mathlib.Analysis.SpecialFunctions.Sqrt
import NonUniqueEuler.H.Infra.Sobolev.Leibniz.Product
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv

/-!
# Helper for `P/Infra/Sobolev/Leibniz`: weak derivatives of `H^k` functions

These facts are also stated in `I/Infra/Sobolev/NormDeriv.lean`. They are re-derived here
(from `Defs` and `I/Infra/Sobolev/WeakDeriv.lean`) because importing `NormDeriv` puts the
theorem `NonUniqueEuler.Sob.MemH.weakPartial` in the environment, and then the identifier
`weakPartial` inside the verbatim statements `theorem MemH.weakPartial_mul_ae_eq` and
`theorem MemH.weakPartial_eq_zero_outside` (whose namespace `MemH` is opened during
elaboration) resolves to that theorem instead of the definition `Sob.weakPartial`.

* `memLp_wp`: `∂^γ f ∈ L²` is a weak derivative of `f ∈ H^k`, `|γ| ≤ k`;
* `wp_ae_eq`: it agrees a.e. with any locally integrable weak derivative;
* `l2_wp_le`: `‖∂^γ f‖_{L²} ≤ ‖f‖_{H^k}`;
* `memH_wp_e1`, `memH_wp_e2`: `∂_i w ∈ H^k` with `‖∂_i w‖_{H^k} ≤ ‖w‖_{H^{k+1}}`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace NonUniqueEuler.Sob.LeibnizAux

theorem memLp_wp {k : ℕ} {f : ℂ → ℂ} (hf : MemH k f) {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx k) :
    MemLp (weakPartial γ f) 2 volume ∧ HasWeakDerivOn univ (pdList γ) f (weakPartial γ f) := by
  obtain ⟨g, hg, hfg⟩ := (memH_iff.1 hf).2 γ hγ
  have hloc : LocallyIntegrableOn g univ :=
    (hg.locallyIntegrable (by norm_num)).locallyIntegrableOn _
  have hspec := (weakDerivOn_spec hloc hfg).2
  have hae := weakDerivOn_ae_eq isOpen_univ hloc hfg
  have hae' : g =ᵐ[volume] weakPartial γ f := by
    filter_upwards [hae] with x hx
    exact (hx (mem_univ x)).symm
  exact ⟨hg.ae_eq hae', hspec⟩

theorem wp_ae_eq {γ : ℕ × ℕ} {f g : ℂ → ℂ} (hg : LocallyIntegrable g)
    (h : HasWeakDerivOn univ (pdList γ) f g) : weakPartial γ f =ᵐ[volume] g := by
  have hae := weakDerivOn_ae_eq isOpen_univ (hg.locallyIntegrableOn _) h
  filter_upwards [hae] with x hx
  exact hx (mem_univ x)

theorem l2_wp_le {k : ℕ} {f : ℂ → ℂ} {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx k) :
    l2 (weakPartial γ f) ≤ normH k f := by
  rw [normH_eq]
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun γ => l2 (weakPartial γ f) ^ 2)
    (fun _ _ => sq_nonneg _) hγ

/-- A derivative `∂_e w` of `w ∈ H^{k+1}` lies in `H^k`, given the shift `β ↦ sh β` of
multi-indices and the weak relations `∂^β ∂_e w = ∂^{sh β} w`. -/
theorem memH_wp_of_shift {k : ℕ} {w : ℂ → ℂ} (hw : MemH (k + 1) w) {e : ℕ × ℕ}
    (he : e ∈ multiIdx (k + 1)) (sh : ℕ × ℕ → ℕ × ℕ) (hsh : Set.InjOn sh (multiIdx k))
    (hshk : ∀ β ∈ multiIdx k, sh β ∈ multiIdx (k + 1))
    (hrel : ∀ β ∈ multiIdx k,
      HasWeakDerivOn univ (pdList β) (weakPartial e w) (weakPartial (sh β) w)) :
    MemH k (weakPartial e w) ∧ normH k (weakPartial e w) ≤ normH (k + 1) w := by
  have hm : MemH k (weakPartial e w) := memH_iff.2 ⟨(memLp_wp hw he).1, fun β hβ =>
    ⟨weakPartial (sh β) w, (memLp_wp hw (hshk β hβ)).1, hrel β hβ⟩⟩
  refine ⟨hm, ?_⟩
  have hl2 : ∀ β ∈ multiIdx k,
      l2 (weakPartial β (weakPartial e w)) = l2 (weakPartial (sh β) w) := by
    intro β hβ
    have := wp_ae_eq ((memLp_wp hw (hshk β hβ)).1.locallyIntegrable (by norm_num)) (hrel β hβ)
    unfold l2
    rw [eLpNorm_congr_ae this]
  rw [normH_eq, normH_eq]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ β ∈ multiIdx k, l2 (weakPartial β (weakPartial e w)) ^ 2
      = ∑ β ∈ multiIdx k, l2 (weakPartial (sh β) w) ^ 2 :=
        Finset.sum_congr rfl fun β hβ => by rw [hl2 β hβ]
    _ = ∑ δ ∈ (multiIdx k).image sh, l2 (weakPartial δ w) ^ 2 :=
        (Finset.sum_image (f := fun δ => l2 (weakPartial δ w) ^ 2)
          fun a ha b hb hab => hsh ha hb hab).symm
    _ ≤ ∑ δ ∈ multiIdx (k + 1), l2 (weakPartial δ w) ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => sq_nonneg _
        intro δ hδ
        obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hδ
        exact hshk β hβ

theorem memH_wp_e1 {k : ℕ} {w : ℂ → ℂ} (hw : MemH (k + 1) w) :
    MemH k (weakPartial (1, 0) w) ∧ normH k (weakPartial (1, 0) w) ≤ normH (k + 1) w := by
  have he : ((1 : ℕ), (0 : ℕ)) ∈ multiIdx (k + 1) := mem_multiIdx.2 (by simp)
  refine memH_wp_of_shift hw he (fun β => (β.1 + 1, β.2)) ?_ ?_ ?_
  · intro a _ b _ hab
    simp only [Prod.mk.injEq] at hab
    exact Prod.ext (by omega) hab.2
  · intro β hβ
    have := mem_multiIdx.1 hβ
    exact mem_multiIdx.2 (by simp; omega)
  · intro β hβ
    have hβ' := mem_multiIdx.1 hβ
    have a := (memLp_wp hw he).2
    have b := (memLp_wp hw (mem_multiIdx.2 (by simp; omega) : (β.1 + 1, β.2) ∈ multiIdx (k + 1))).2
    have e : pdList (β.1 + 1, β.2) = pdList (1, 0) ++ pdList β := by
      simp [pdList, List.replicate_succ]
    rw [e] at b
    exact HasWeakDerivOn.of_append a b

theorem memH_wp_e2 {k : ℕ} {w : ℂ → ℂ} (hw : MemH (k + 1) w) :
    MemH k (weakPartial (0, 1) w) ∧ normH k (weakPartial (0, 1) w) ≤ normH (k + 1) w := by
  have he : ((0 : ℕ), (1 : ℕ)) ∈ multiIdx (k + 1) := mem_multiIdx.2 (by simp)
  refine memH_wp_of_shift hw he (fun β => (β.1, β.2 + 1)) ?_ ?_ ?_
  · intro a _ b _ hab
    simp only [Prod.mk.injEq] at hab
    exact Prod.ext hab.1 (by omega)
  · intro β hβ
    have := mem_multiIdx.1 hβ
    exact mem_multiIdx.2 (by simp; omega)
  · intro β hβ
    have hβ' := mem_multiIdx.1 hβ
    have a := (memLp_wp hw he).2
    have b := (memLp_wp hw (mem_multiIdx.2 (by simp; omega) : (β.1, β.2 + 1) ∈ multiIdx (k + 1))).2
    have hp : (pdList (β.1, β.2 + 1)).Perm (pdList (0, 1) ++ pdList β) := by
      simp only [pdList, List.replicate_succ, List.replicate_zero, List.nil_append,
        List.singleton_append]
      exact List.perm_middle
    exact HasWeakDerivOn.of_append a (b.perm hp)

end NonUniqueEuler.Sob.LeibnizAux
