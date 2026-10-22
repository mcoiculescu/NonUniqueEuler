import NonUniqueEuler.Defs.SmoothB.Iteration
import NonUniqueEuler.H.SmoothB.CommR2.Bounds

/-!
# Proof: `lem:comm-R2` (the commutator estimate on the plane)

Proof of `NonUniqueEuler/I/SmoothB/CommR2.lean` (same declaration, same statement).
Manuscript: `B_global_smooth.tex:149-175`.

1. Leibniz (`H/SmoothB/CommR2/Formula.lean`, `CommR2Aux.comm_formula`):
   `[∂^α, u·∇]g = ∑_l ∑_{(w₁,w₂)} ∂_{w₁} u_l ∂_{w₂} ∂_l g` over the `2^s - 1` splittings of the
   directions of `∂^α` into a nonempty sublist `w₁` and its complement `w₂` (the manuscript's
   `∑_{0<β≤α} C(α,β)`: `C(α,β)` counts the sublists with `w₁ ~ pdList β`).
2. Each term is `∂^β u_l ∂^γ g` with `|β| ≥ 1`, `|γ| ≥ 1`, `|β| + |γ| = s + 1`, and its `L²`
   norm is at most the bracket (`H/SmoothB/CommR2/Bounds.lean`, `CommR2Aux.commTerm_bound`:
   the three cases `|β| = 1`, `|β| = s`, `2 ≤ |β| ≤ s - 1` of the manuscript).
3. Triangle inequality: `‖[∂^α, u·∇]g‖₂ ≤ 2 (2^s - 1) · bracket ≤ 2^{s+1} · bracket`.
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler.Smooth

/-- `lem:comm-R2`: for an integer `s ≥ 2`, `g ∈ C_c^∞(ℝ²)`, and `u ∈ C^∞(ℝ²; ℝ²)` with
`|∇u|_max < ∞` and `∂^β u ∈ L²` for `1 ≤ |β| ≤ s`, every multi-index `α` with `|α| = s` satisfies
`‖[∂^α, u·∇]g‖_{L²} ≤ 2^{s+1}[(|∇u|_max + ‖∇u‖_{H^{s-1}})‖g‖_{H^s} + ‖∇u‖_{H^{s-1}}‖∇g‖_{L^∞}]`. -/
theorem comm_R2 {s : ℕ} (hs : 2 ≤ s) {g : ℂ → ℂ}
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hgc : HasCompactSupport g) {u : ℂ → ℂ}
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    (hbdd : ∃ M : ℝ, ∀ x : ℂ, ∀ i l : Fin 2, |Prelim.gradEntry u i l x| ≤ M)
    (hL2 : ∀ β : ℕ × ℕ, 1 ≤ β.1 + β.2 → β.1 + β.2 ≤ s → MemLp (Sob.partialD β u) 2 volume)
    {α : ℕ × ℕ} (hα : α.1 + α.2 = s) :
    MemLp (fun x => Sob.partialD α (fun y => fderiv ℝ g y (u y)) x -
        fderiv ℝ (Sob.partialD α g) x (u x)) 2 volume ∧
      Sob.l2 (fun x => Sob.partialD α (fun y => fderiv ℝ g y (u y)) x -
          fderiv ℝ (Sob.partialD α g) x (u x)) ≤
        2 ^ (s + 1) * ((gradEntryMax u + Prelim.gradNormH (s - 1) u) * Sob.normH s g +
          Prelim.gradNormH (s - 1) u * gradSupC g) := by
  have hform : (fun x => Sob.partialD α (fun y => fderiv ℝ g y (u y)) x -
      fderiv ℝ (Sob.partialD α g) x (u x)) = fun x =>
        ((CommR2Aux.splitsPos (Sob.pdList α)).map (fun p => CommR2Aux.commTerm u g 0 p x)).sum +
        ((CommR2Aux.splitsPos (Sob.pdList α)).map (fun p => CommR2Aux.commTerm u g 1 p x)).sum := by
    funext x
    rw [CommR2Aux.comm_formula hg hu α x, Fin.sum_univ_two]
  have hterm : ∀ l : Fin 2, ∀ p ∈ CommR2Aux.splitsPos (Sob.pdList α),
      MemLp (CommR2Aux.commTerm u g l p) 2 volume ∧
        Sob.l2 (CommR2Aux.commTerm u g l p) ≤ CommR2Aux.bracket s g u := by
    intro l p hp
    obtain ⟨β, δ, hβ, hδ, hβ1, hsum⟩ := CommR2Aux.splitsPos_pdList hp
    have heq : CommR2Aux.commTerm u g l p = fun x => CommR2Aux.compL l (Sob.partialD β u x) *
        Sob.partialD (δ + CommR2Aux.unitIdx l) g x := by
      funext x
      simp only [CommR2Aux.commTerm]
      rw [CommR2Aux.iterDirDeriv_perm hβ hu, ← CommR2Aux.partialD_unitIdx,
        CommR2Aux.iterDirDeriv_perm hδ (CommR2Aux.contDiff_partialD hg _),
        ← CommR2Aux.partialD_partialD hg]
      rfl
    rw [heq]
    have hl := CommR2Aux.unitIdx_size l
    exact CommR2Aux.commTerm_bound hs hg hgc hu hbdd hL2 hβ1
      (by simp only [Prod.fst_add, Prod.snd_add]; omega)
      (by simp only [Prod.fst_add, Prod.snd_add]; omega) l
  obtain ⟨h0m, h0b⟩ := CommR2Aux.listSum_bound _ _ (hterm 0)
  obtain ⟨h1m, h1b⟩ := CommR2Aux.listSum_bound _ _ (hterm 1)
  rw [hform]
  refine ⟨h0m.add h1m, ?_⟩
  have hlen := CommR2Aux.length_splitsPos (Sob.pdList α)
  rw [Sob.pdList_length, hα] at hlen
  have hB : 0 ≤ CommR2Aux.bracket s g u :=
    add_nonneg (mul_nonneg (add_nonneg (CommR2Aux.gradEntryMax_nonneg hbdd)
      (CommR2Aux.gradNormH_nonneg _ _)) (Sob.normH_nonneg _ _))
      (mul_nonneg (CommR2Aux.gradNormH_nonneg _ _) (CommR2Aux.gradSupC_nonneg hg hgc))
  have hL : ((CommR2Aux.splitsPos (Sob.pdList α)).length : ℝ) + 1 = 2 ^ s := by
    exact_mod_cast hlen
  show _ ≤ 2 ^ (s + 1) * CommR2Aux.bracket s g u
  calc _ ≤ _ := CommR2Aux.l2_add_le h0m h1m
    _ ≤ _ := add_le_add h0b h1b
    _ ≤ 2 ^ (s + 1) * CommR2Aux.bracket s g u := by
      rw [pow_succ, ← hL]
      nlinarith

end NonUniqueEuler.Smooth
