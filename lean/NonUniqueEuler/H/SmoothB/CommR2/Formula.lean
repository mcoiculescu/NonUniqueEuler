import NonUniqueEuler.H.SmoothB.CommR2.Calc
import NonUniqueEuler.Defs.Sec2.Conventions

/-!
# Helper for `lem:comm-R2`: the commutator formula

Helper of `P/SmoothB/CommR2.lean`, step 1 of the proof of `lem:comm-R2`
(`B_global_smooth.tex:162-165`): for smooth `g` and `u`,
`[∂^α, u·∇]g = ∑_{l} ∑_{(w₁,w₂)} ∂_{w₁} u_l ∂_{w₂} ∂_l g`, the inner sum over the splittings
`(w₁, w₂) ∈ splitsPos (pdList α)` of the list of directions of `∂^α` with `w₁ ≠ []`
(`comm_formula`). Here `u_l = comp2 l ∘ u` (as a complex function, `compL l`), and the transport
term is `u·∇g = Dg(u) = ∑_l u_l ∂_l g` (`fderiv_apply_eq_sum`).
-/

noncomputable section

open scoped ContDiff

namespace NonUniqueEuler.Smooth.CommR2Aux

open Sob

/-- The coordinate maps `z ↦ z₁`, `z ↦ z₂`, as real-linear maps. -/
def coordCLM : Fin 2 → (ℂ →L[ℝ] ℝ) := ![Complex.reCLM, Complex.imCLM]

/-- `z ↦ (z_l : ℂ)`, the `l`-th coordinate of `z ∈ ℝ² = ℂ` viewed as a complex number. -/
def compL (l : Fin 2) : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp (coordCLM l)

theorem compL_apply (l : Fin 2) (z : ℂ) : compL l z = ((Prelim.comp2 l z : ℝ) : ℂ) := by
  fin_cases l <;> simp [compL, coordCLM, Prelim.comp2]

theorem norm_compL_le (l : Fin 2) (z : ℂ) : ‖compL l z‖ ≤ ‖z‖ := by
  rw [compL_apply, Complex.norm_real, Real.norm_eq_abs]
  fin_cases l
  · exact Complex.abs_re_le_norm z
  · exact Complex.abs_im_le_norm z

/-- `L z = z₁ L(e₁) + z₂ L(e₂)` for a real-linear `L`. -/
theorem clm_apply_eq_sum (L : ℂ →L[ℝ] ℂ) (z : ℂ) :
    L z = ∑ l : Fin 2, compL l z * L (Prelim.e2 l) := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hz]
  rw [map_add, map_smul, map_smul, Fin.sum_univ_two, compL_apply, compL_apply]
  simp [Complex.real_smul, Prelim.e2]

/-- The transport term `u·∇g = Dg(u) = ∑_l u_l ∂_l g`. -/
theorem fderiv_apply_eq_sum (g : ℂ → ℂ) (u : ℂ → ℂ) (y : ℂ) :
    fderiv ℝ g y (u y) = ∑ l : Fin 2, compL l (u y) * dirDeriv (Prelim.e2 l) g y :=
  clm_apply_eq_sum _ _

/-- The terms of the commutator formula. -/
def commTerm (u g : ℂ → ℂ) (l : Fin 2) (p : List ℂ × List ℂ) (x : ℂ) : ℂ :=
  compL l (iterDirDeriv p.1 u x) * iterDirDeriv p.2 (dirDeriv (Prelim.e2 l) g) x

/-- The commutator formula `[∂^α, u·∇]g = ∑_l ∑_{(w₁,w₂), w₁ ≠ []} ∂_{w₁} u_l ∂_{w₂} ∂_l g`. -/
theorem comm_formula {g u : ℂ → ℂ} (hg : ContDiff ℝ ∞ g) (hu : ContDiff ℝ ∞ u)
    (α : ℕ × ℕ) (x : ℂ) :
    partialD α (fun y => fderiv ℝ g y (u y)) x - fderiv ℝ (partialD α g) x (u x) =
      ∑ l : Fin 2, ((splitsPos (pdList α)).map (fun p => commTerm u g l p x)).sum := by
  have ha : ∀ l : Fin 2, ContDiff ℝ ∞ (fun y => compL l (u y)) :=
    fun l => (compL l).contDiff.comp hu
  have hG : ∀ l : Fin 2, ContDiff ℝ ∞ (dirDeriv (Prelim.e2 l) g) :=
    fun l => contDiff_dirDeriv hg _
  have h1 : (fun y => fderiv ℝ g y (u y)) = fun y =>
      compL 0 (u y) * dirDeriv (Prelim.e2 0) g y + compL 1 (u y) * dirDeriv (Prelim.e2 1) g y := by
    funext y
    rw [fderiv_apply_eq_sum, Fin.sum_univ_two]
  have hL : ∀ l : Fin 2, partialD α (fun y => compL l (u y) * dirDeriv (Prelim.e2 l) g y) x =
      compL l (u x) * dirDeriv (Prelim.e2 l) (partialD α g) x +
        ((splitsPos (pdList α)).map (fun p => commTerm u g l p x)).sum := by
    intro l
    simp only [partialD]
    rw [iterDirDeriv_mul (ha l) (hG l)]
    have e1 : iterDirDeriv (pdList α) (dirDeriv (Prelim.e2 l) g) =
        dirDeriv (Prelim.e2 l) (iterDirDeriv (pdList α) g) := by
      have := iterDirDeriv_append (pdList α) [Prelim.e2 l] g
      simp only [iterDirDeriv_cons, iterDirDeriv_nil] at this
      rw [← this, iterDirDeriv_perm (List.perm_append_singleton _ _) hg]
      rfl
    rw [e1]
    beta_reduce
    congr 1
    refine congrArg (fun L : List ℂ => L.sum) (List.map_congr_left fun p _ => ?_)
    simp only [commTerm]
    rw [iterDirDeriv_clm_comp (compL l) hu]
  rw [h1]
  have hadd := iterDirDeriv_add ((ha 0).mul (hG 0)) ((ha 1).mul (hG 1)) (pdList α)
  simp only [partialD] at hL ⊢
  rw [hadd]
  beta_reduce
  rw [hL 0, hL 1, fderiv_apply_eq_sum (iterDirDeriv (pdList α) g) u x, Fin.sum_univ_two,
    Fin.sum_univ_two]
  ring

/-- The properties of a splitting used for the bounds: `w₁ ≠ []`, `w₁ ++ w₂ ~ pdList α`. -/
theorem splitsPos_pdList {α : ℕ × ℕ} {p : List ℂ × List ℂ} (hp : p ∈ splitsPos (pdList α)) :
    ∃ β δ : ℕ × ℕ, p.1.Perm (pdList β) ∧ p.2.Perm (pdList δ) ∧ 1 ≤ β.1 + β.2 ∧
      (β.1 + β.2) + (δ.1 + δ.2) = α.1 + α.2 := by
  obtain ⟨hne, hperm⟩ := mem_splitsPos hp
  have hmem : ∀ v ∈ p.1 ++ p.2, v = 1 ∨ v = Complex.I :=
    fun v hv => mem_pdList (hperm.subset hv)
  obtain ⟨β, hβ, hβl⟩ := exists_perm_pdList fun v hv => hmem v (List.mem_append_left _ hv)
  obtain ⟨δ, hδ, hδl⟩ := exists_perm_pdList fun v hv => hmem v (List.mem_append_right _ hv)
  refine ⟨β, δ, hβ, hδ, ?_, ?_⟩
  · rw [hβl]
    rcases hp1 : p.1 with _ | ⟨a, w⟩
    · exact absurd hp1 hne
    · simp
  · rw [hβl, hδl, ← List.length_append, hperm.length_eq, pdList_length]

end NonUniqueEuler.Smooth.CommR2Aux
