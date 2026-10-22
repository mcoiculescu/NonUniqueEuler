import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.IntermediateValue

/-!
# Helper for `prop:confine`(a): a trajectory with a conditional speed bound

Helper of `P/Sec7/Confine.lean` (`07_several_rings.tex:357-368`). A curve `γ` differentiable on
`ℝ` with `‖γ t₀‖ ≤ ρ₀` and `‖γ' t‖ ≤ V` whenever `t ∈ [t₀, t₁]` and `‖γ t‖ ≤ L`, where `V > 0` and
`ρ₀ + V (t₁ - t₀) ≤ L`, satisfies `‖γ t‖ ≤ ρ₀ + V (t - t₀)` on `[t₀, t₁]`.

This is the continuity argument of the manuscript, carried out for one trajectory at a time (the
speed bound `prop:confine`(b) holds on the whole ball `\bar B_{Λ r_{k+1}}` at every time of the window,
independently of the other trajectories, so the manuscript's uniform continuity in `y` is not
needed). The proof is "real induction" (`IsClosed.Icc_subset_of_forall_exists_gt`) on the closed
set `{t | ‖γ t - γ t₀‖ ≤ V (t - t₀)}`, with the mean value inequality on short intervals.
-/

open Set Filter Topology Metric

namespace NonUniqueEuler.Rings.ConfineH

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The trajectory lemma.** If `γ` has derivative `γ' t` at every `t`, `‖γ t₀‖ ≤ ρ₀`, `V > 0`,
`ρ₀ + V(t₁ - t₀) ≤ L`, and `‖γ' t‖ ≤ V` at every `t ∈ [t₀, t₁]` with `‖γ t‖ ≤ L`, then
`‖γ t‖ ≤ ρ₀ + V(t - t₀)` for `t ∈ [t₀, t₁]`. -/
theorem norm_le_of_cond_deriv_bound {γ γ' : ℝ → E} {t₀ t₁ ρ₀ V L : ℝ}
    (hγ : ∀ t, HasDerivAt γ (γ' t) t) (hV : 0 < V) (h0 : ‖γ t₀‖ ≤ ρ₀)
    (hL : ρ₀ + V * (t₁ - t₀) ≤ L)
    (hbound : ∀ t ∈ Icc t₀ t₁, ‖γ t‖ ≤ L → ‖γ' t‖ ≤ V) :
    ∀ t ∈ Icc t₀ t₁, ‖γ t‖ ≤ ρ₀ + V * (t - t₀) := by
  have hcont : Continuous γ := continuous_iff_continuousAt.mpr fun t => (hγ t).continuousAt
  set s : Set ℝ := {t | ‖γ t - γ t₀‖ ≤ V * (t - t₀)} with hs_def
  have hs_closed : IsClosed s :=
    isClosed_le (continuous_norm.comp (hcont.sub continuous_const))
      (continuous_const.mul (continuous_id.sub continuous_const))
  have hsub : Icc t₀ t₁ ⊆ s := by
    refine (hs_closed.inter isClosed_Icc).Icc_subset_of_forall_exists_gt ?_ ?_
    · simp [hs_def]
    · rintro x ⟨hxs, hx₀, hx₁⟩ y hy
      have hxs' : ‖γ x - γ t₀‖ ≤ V * (x - t₀) := hxs
      -- `‖γ x‖ < L`
      have hγx : ‖γ x‖ < L := by
        have h1 : ‖γ x‖ ≤ ‖γ t₀‖ + ‖γ x - γ t₀‖ := by
          have := norm_add_le (γ t₀) (γ x - γ t₀)
          simpa using this
        have h2 : V * (x - t₀) < V * (t₁ - t₀) := mul_lt_mul_of_pos_left (by linarith) hV
        linarith
      -- a neighbourhood where `‖γ‖ < L`
      have hev : ∀ᶠ z in 𝓝 x, ‖γ z‖ < L :=
        (hcont.continuousAt.norm).eventually (gt_mem_nhds hγx)
      obtain ⟨δ, hδ, hδball⟩ := Metric.eventually_nhds_iff.mp hev
      set z : ℝ := min y (min (x + δ / 2) t₁) with hz_def
      have hxz : x < z := by
        simp only [hz_def, lt_min_iff]
        exact ⟨hy, by linarith, hx₁⟩
      have hzy : z ≤ y := min_le_left _ _
      have hzδ : z ≤ x + δ / 2 := (min_le_right _ _).trans (min_le_left _ _)
      have hzt₁ : z ≤ t₁ := (min_le_right _ _).trans (min_le_right _ _)
      refine ⟨z, ?_, hxz, hzy⟩
      -- the mean value inequality on `[x, z]`
      have hmv := norm_image_sub_le_of_norm_deriv_le_segment' (f := γ) (f' := γ') (C := V)
        (a := x) (b := z) (fun τ _ => (hγ τ).hasDerivWithinAt)
        (fun τ hτ => by
          refine hbound τ ⟨by linarith [hτ.1], by linarith [hτ.2]⟩ ?_
          refine (hδball ?_).le
          rw [Real.dist_eq, abs_lt]
          constructor <;> linarith [hτ.1, hτ.2])
        z ⟨hxz.le, le_rfl⟩
      have htri : ‖γ z - γ t₀‖ ≤ ‖γ z - γ x‖ + ‖γ x - γ t₀‖ := by
        have := norm_add_le (γ z - γ x) (γ x - γ t₀)
        simpa using this
      show ‖γ z - γ t₀‖ ≤ V * (z - t₀)
      have hz' : V * (z - x) + V * (x - t₀) = V * (z - t₀) := by ring
      linarith
  intro t ht
  have hts : ‖γ t - γ t₀‖ ≤ V * (t - t₀) := hsub ht
  have h1 : ‖γ t‖ ≤ ‖γ t₀‖ + ‖γ t - γ t₀‖ := by
    have := norm_add_le (γ t₀) (γ t - γ t₀)
    simpa using this
  linarith

end NonUniqueEuler.Rings.ConfineH
