import NonUniqueEuler.I.Infra.Sobolev.NormDeriv
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv
import NonUniqueEuler.I.Infra.Sobolev.Norm

/-!
# Helper for `P/Infra/Sobolev/DotGradSharp`: weak derivatives of `∂_j w` and of sums

* `weakPartial_e1_ae_eq`, `weakPartial_e2_ae_eq`: for `w ∈ H^{k+1}` and `|δ| ≤ k`,
  `∂^δ ∂₁ w = ∂^{δ+(1,0)} w` and `∂^δ ∂₂ w = ∂^{δ+(0,1)} w` a.e. (`04_ring.tex:1564`);
* `weakPartial_add_ae_eq`: `∂^γ (f + g) = ∂^γ f + ∂^γ g` a.e. for `f, g ∈ H^k`, `|γ| ≤ k`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace NonUniqueEuler.Sob.DotGradSharpAux

theorem memH_e1 {k : ℕ} {w : ℂ → ℂ} (hw : MemH (k + 1) w) :
    MemH k (weakPartial (1, 0) w) ∧ normH k (weakPartial (1, 0) w) ≤ normH (k + 1) w :=
  MemH.weakPartial (γ := (1, 0)) hw

theorem memH_e2 {k : ℕ} {w : ℂ → ℂ} (hw : MemH (k + 1) w) :
    MemH k (weakPartial (0, 1) w) ∧ normH k (weakPartial (0, 1) w) ≤ normH (k + 1) w :=
  MemH.weakPartial (γ := (0, 1)) hw

theorem pdList_e1_perm (δ : ℕ × ℕ) :
    (pdList δ ++ pdList (1, 0)).Perm (pdList (δ.1 + 1, δ.2)) := by
  have h1 : pdList (1, 0) = [1] := by simp [pdList]
  have h2 : pdList (δ.1 + 1, δ.2) = 1 :: pdList δ := by
    simp [pdList, List.replicate_succ]
  rw [h1, h2]
  exact List.perm_append_singleton _ _

theorem pdList_e2_eq (δ : ℕ × ℕ) :
    pdList δ ++ pdList (0, 1) = pdList (δ.1, δ.2 + 1) := by
  simp [pdList, List.replicate_succ', List.append_assoc]

/-- `∂^δ ∂₁ w = ∂^{δ+(1,0)} w` a.e. for `w ∈ H^{k+1}`, `|δ| ≤ k`. -/
theorem weakPartial_e1_ae_eq {k : ℕ} {w : ℂ → ℂ} (hw : MemH (k + 1) w) {δ : ℕ × ℕ}
    (hδ : δ ∈ multiIdx k) :
    weakPartial δ (weakPartial (1, 0) w) =ᵐ[volume] weakPartial (δ.1 + 1, δ.2) w := by
  have h1 := (memH_e1 hw).1
  obtain ⟨hm, hd⟩ := MemH.memLp_weakPartial h1 hδ
  have h10 : ((1 : ℕ), (0 : ℕ)) ∈ multiIdx (k + 1) := mem_multiIdx.2 (by simp)
  have h0 := (MemH.memLp_weakPartial hw h10).2
  have ht := (HasWeakDerivOn.trans h0 hd).perm (pdList_e1_perm δ)
  have hδ' : (δ.1 + 1, δ.2) ∈ multiIdx (k + 1) := by
    have := mem_multiIdx.1 hδ
    exact mem_multiIdx.2 (by simp only; omega)
  exact (MemH.weakPartial_ae_eq hw hδ' hm ht).symm

/-- `∂^δ ∂₂ w = ∂^{δ+(0,1)} w` a.e. for `w ∈ H^{k+1}`, `|δ| ≤ k`. -/
theorem weakPartial_e2_ae_eq {k : ℕ} {w : ℂ → ℂ} (hw : MemH (k + 1) w) {δ : ℕ × ℕ}
    (hδ : δ ∈ multiIdx k) :
    weakPartial δ (weakPartial (0, 1) w) =ᵐ[volume] weakPartial (δ.1, δ.2 + 1) w := by
  have h1 := (memH_e2 hw).1
  obtain ⟨hm, hd⟩ := MemH.memLp_weakPartial h1 hδ
  have h01 : ((0 : ℕ), (1 : ℕ)) ∈ multiIdx (k + 1) := mem_multiIdx.2 (by simp)
  have h0 := (MemH.memLp_weakPartial hw h01).2
  have ht := HasWeakDerivOn.trans h0 hd
  rw [pdList_e2_eq] at ht
  have hδ' : (δ.1, δ.2 + 1) ∈ multiIdx (k + 1) := by
    have := mem_multiIdx.1 hδ
    exact mem_multiIdx.2 (by simp only; omega)
  exact (MemH.weakPartial_ae_eq hw hδ' hm ht).symm

/-- Linearity of the chosen weak derivatives of `H^k` functions. -/
theorem weakPartial_add_ae_eq {k : ℕ} {f g : ℂ → ℂ} (hf : MemH k f) (hg : MemH k g)
    {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx k) :
    weakPartial γ (f + g) =ᵐ[volume] weakPartial γ f + weakPartial γ g := by
  obtain ⟨hfm, hfd⟩ := MemH.memLp_weakPartial hf hγ
  obtain ⟨hgm, hgd⟩ := MemH.memLp_weakPartial hg hγ
  have hf0 : MemLp f 2 volume := (memH_iff.1 hf).1
  have hg0 : MemLp g 2 volume := (memH_iff.1 hg).1
  have hli : ∀ {u : ℂ → ℂ}, MemLp u 2 volume → LocallyIntegrableOn u univ := fun hu =>
    (hu.locallyIntegrable (by norm_num)).locallyIntegrableOn univ
  have hs := HasWeakDerivOn.add isOpen_univ (hli hf0) (hli hg0) (hli hfm) (hli hgm) hfd hgd
  exact MemH.weakPartial_ae_eq (hf.add hg).1 hγ (hfm.add hgm) hs

end NonUniqueEuler.Sob.DotGradSharpAux
