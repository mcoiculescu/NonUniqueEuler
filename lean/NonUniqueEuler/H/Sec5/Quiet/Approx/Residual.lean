import NonUniqueEuler.H.Sec5.Quiet.Approx.Induction

/-!
# Helpers for `quiet_approx`: the residual of `w_app = Σ_{j ≤ N_Q} w^{[j]}`

Helper of `P/Sec5/Quiet/Approx.lean` (fully proved). Namespace `NonUniqueEuler.OneRing.QAppH`.
Manuscript `05_single_ring.tex:494-507`: summing the equations of the `w^{[j]}` and using
`Σ_{j=2}^{N_Q} Σ_{i+l=j} B(w^{[i]},w^{[l]}) = B(w_app,w_app) - Σ_{i,l ≤ N_Q, i+l > N_Q} B(w^{[i]},w^{[l]})`,
`Σ_{j=2}^{N_Q} h·∇w^{[j-1]} = h·∇w_app - h·∇w^{[N_Q]}`, the residual of `lem:energy` is
`R_app = -Σ_{i,l ≤ N_Q, i+l > N_Q} B(w^{[i]},w^{[l]}) + h·∇w^{[N_Q]}` (a.e.).

* `Y_fn_sum`, `Lfn_sum_ae`: `L(G)` on functions is additive a.e. on `X^{k+1}` (through the
  bounded operator `Lin.L`);
* `rapp_ae`: the residual identity, with `w_app' = L(G)w_app + Σ_j g^{[j]}`.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace NonUniqueEuler.OneRing.QAppH

open Sect Sob RingData

theorem Y_fn_sum {s : ℕ} {K : Set ℂ} {ι : Type*} (S : Finset ι) (w : ι → Y s K) :
    (∑ i ∈ S, w i).fn =ᵐ[volume] fun x => ∑ i ∈ S, (w i).fn x := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Y_fn_zero s K
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Y_fn_add (w a) (∑ i ∈ S, w i), ih] with x h1 h2
    rw [h1, h2, Finset.sum_insert ha]

/-- `L(G)(Σ f_i) = Σ L(G) f_i` a.e. for `f_i ∈ X^{k+1}`. -/
theorem Lfn_sum_ae (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) {k : ℕ} (G : ℝ) {ι : Type*}
    (S : Finset ι) {f : ι → ℂ → ℂ} (hf : ∀ i ∈ S, Lin.MemXFn (k + 1) (f i)) :
    Lin.Lfn χ G (∑ i ∈ S, f i) =ᵐ[volume] fun x => ∑ i ∈ S, Lin.Lfn χ G (f i) x := by
  have h1 := L_toY_fn_ae χ hχ k G (MemXFn.sum S hf)
  rw [toY_sum S hf, map_sum] at h1
  have h2 := Y_fn_sum S (fun i => Lin.L χ k G (toY (k + 1) annN (f i)))
  have h3 : ∀ᵐ x ∂(volume : Measure ℂ), ∀ i ∈ S,
      (Lin.L χ k G (toY (k + 1) annN (f i))).fn x = Lin.Lfn χ G (f i) x :=
    (Filter.eventually_all_finset S).2 fun i hi => L_toY_fn_ae χ hχ k G (hf i hi)
  filter_upwards [h1, h2, h3] with x e1 e2 e3
  rw [← e1, e2]
  exact Finset.sum_congr rfl e3

/-- **The residual identity** (`05_single_ring.tex:497-506`). -/
theorem rapp_ae (χ : ℝ → ℝ) (K : ℕ) (G : ℝ) (h : ℝ → ℂ → ℂ) {NQ : ℕ} (hQ : 2 ≤ NQ) (τ : ℝ)
    (hX : ∀ j ∈ Finset.Icc 1 NQ, Lin.MemXFn 2 (hw χ K G h j τ)) :
    Rapp χ G h (fun t => ∑ j ∈ Finset.Icc 1 NQ, hw χ K G h j t)
        (fun t => Lin.Lfn χ G (∑ j ∈ Finset.Icc 1 NQ, hw χ K G h j t) +
          ∑ j ∈ Finset.Icc 1 NQ, hg χ K G h j t) τ =ᵐ[volume]
      -(∑ p ∈ (Finset.Icc 1 NQ ×ˢ Finset.Icc 1 NQ : Finset (ℕ × ℕ)).filter
          (fun p : ℕ × ℕ => ¬ p.1 + p.2 ≤ NQ), Bfn (hw χ K G h p.1 τ) (hw χ K G h p.2 τ)) +
        hGrad (h τ) (hw χ K G h NQ τ) := by
  set W : ℕ → ℂ → ℂ := fun j => hw χ K G h j τ with hW
  set S : Finset (ℕ × ℕ) := Finset.Icc 1 NQ ×ˢ Finset.Icc 1 NQ with hS
  have hX1 : ∀ j ∈ Finset.Icc 1 NQ, MemH 1 (W j) := fun j hj => (hX j hj).1.mono_order (by omega)
  have hB := Bfn_sum_sum_ae (Finset.Icc 1 NQ) (Finset.Icc 1 NQ) hX hX1
  have hH := hGrad_sum_right_ae (h τ) (Finset.Icc 1 NQ) hX1
  -- the sum of the `g^{[j]}`
  have hsumg : ∀ x, ∑ j ∈ Finset.Icc 1 NQ, hg χ K G h j τ x =
      -hGrad (h τ) (PhiC χ) x + ∑ p ∈ S.filter (fun p : ℕ × ℕ => p.1 + p.2 ≤ NQ),
        Bfn (W p.1) (W p.2) x - ∑ l ∈ Finset.Ico 1 NQ, hGrad (h τ) (W l) x := by
    intro x
    rw [← Finset.add_sum_Ioc_eq_sum_Icc (by omega : 1 ≤ NQ), hg_one]
    have hj : ∀ j ∈ Finset.Ioc 1 NQ, hg χ K G h j τ x =
        ∑ p ∈ pairs j, Bfn (W p.1) (W p.2) x - hGrad (h τ) (W (j - 1)) x := by
      intro j hjm
      rw [Finset.mem_Ioc] at hjm
      rw [hg_of_two_le χ K G h (by omega) τ]
      simp only [Pi.sub_apply, Finset.sum_apply, hW]
    rw [Finset.sum_congr rfl hj, Finset.sum_sub_distrib,
      sum_pairs_eq NQ (fun p : ℕ × ℕ => Bfn (W p.1) (W p.2) x),
      sum_Ioc_pred NQ (fun l => hGrad (h τ) (W l) x)]
    show -hGrad (h τ) (PhiC χ) x + _ = _
    ring
  have hsumB : ∀ x, ∑ i ∈ Finset.Icc 1 NQ, ∑ l ∈ Finset.Icc 1 NQ, Bfn (W i) (W l) x =
      ∑ p ∈ S.filter (fun p : ℕ × ℕ => p.1 + p.2 ≤ NQ), Bfn (W p.1) (W p.2) x +
        ∑ p ∈ S.filter (fun p : ℕ × ℕ => ¬ p.1 + p.2 ≤ NQ), Bfn (W p.1) (W p.2) x := by
    intro x
    rw [Finset.sum_filter_add_sum_filter_not, hS, Finset.sum_product]
  have hsumH : ∀ x, ∑ l ∈ Finset.Icc 1 NQ, hGrad (h τ) (W l) x =
      ∑ l ∈ Finset.Ico 1 NQ, hGrad (h τ) (W l) x + hGrad (h τ) (W NQ) x := by
    intro x
    rw [Finset.sum_Ico_add_eq_sum_Icc (by omega : 1 ≤ NQ)]
  filter_upwards [hB, hH] with x e1 e2
  simp only [Rapp, ringRHS, Pi.add_apply, Pi.neg_apply, Finset.sum_apply]
  rw [e1, e2, hsumg x, hsumB x, hsumH x]
  ring

end NonUniqueEuler.OneRing.QAppH
