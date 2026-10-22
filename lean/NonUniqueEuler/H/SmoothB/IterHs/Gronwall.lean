import Mathlib.Analysis.ODE.Gronwall

/-!
# Helper for `lem:iter-Hs`: a two-sided scalar Grönwall inequality

Helper of `P/SmoothB/IterHs.lean` (`B_global_smooth.tex:345-348`: "Gronwall's inequality
gives `𝓗(t) ≤ (‖ω₀‖²_{H^s} + 𝓜² + 1) e^{𝓑_s(T)|t|}`"). If `G ≥ 0` is differentiable with
`|G'| ≤ B G` on `[-T, T]`, then `G(τ) ≤ G(0) e^{B|τ|}` for `|τ| ≤ T`. Both time directions are
needed; the backward one is the forward one for `σ ↦ G(-σ)`. Uses Mathlib's
`norm_le_gronwallBound_of_norm_deriv_right_le`.
-/

noncomputable section

open Set

namespace NonUniqueEuler.Smooth.IterHsH

/-- Forward direction: `G(τ) ≤ G(0) e^{Bτ}` for `0 ≤ τ ≤ T`. -/
theorem le_mul_exp_of_abs_deriv_le_fwd {G G' : ℝ → ℝ} {B T : ℝ}
    (hG : ∀ τ, HasDerivAt G (G' τ) τ) (hpos : ∀ τ, |τ| ≤ T → 0 ≤ G τ)
    (hbd : ∀ τ, |τ| ≤ T → |G' τ| ≤ B * G τ) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ : τ ≤ T) :
    G τ ≤ G 0 * Real.exp (B * τ) := by
  have hcont : ContinuousOn G (Icc 0 τ) := fun x _ => (hG x).continuousAt.continuousWithinAt
  have hder : ∀ x ∈ Ico 0 τ, HasDerivWithinAt G (G' x) (Ici x) x :=
    fun x _ => (hG x).hasDerivWithinAt
  have h0 : 0 ≤ G 0 := hpos 0 (by simp; linarith)
  have ha : ‖G 0‖ ≤ G 0 := by rw [Real.norm_of_nonneg h0]
  have hbound : ∀ x ∈ Ico 0 τ, ‖G' x‖ ≤ B * ‖G x‖ + 0 := by
    intro x hx
    have hxT : |x| ≤ T := by
      rw [abs_of_nonneg hx.1]
      linarith [hx.2]
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (hpos x hxT), add_zero]
    exact hbd x hxT
  have h := norm_le_gronwallBound_of_norm_deriv_right_le hcont hder ha hbound τ
    ⟨hτ0, le_rfl⟩
  rw [gronwallBound_ε0, sub_zero] at h
  exact (Real.le_norm_self _).trans h

/-- `G(τ) ≤ G(0) e^{B|τ|}` for `|τ| ≤ T`, if `G ≥ 0` and `|G'| ≤ B G` on `[-T, T]`. -/
theorem le_mul_exp_of_abs_deriv_le {G G' : ℝ → ℝ} {B T : ℝ}
    (hG : ∀ τ, HasDerivAt G (G' τ) τ) (hpos : ∀ τ, |τ| ≤ T → 0 ≤ G τ)
    (hbd : ∀ τ, |τ| ≤ T → |G' τ| ≤ B * G τ) {τ : ℝ} (hτ : |τ| ≤ T) :
    G τ ≤ G 0 * Real.exp (B * |τ|) := by
  rcases le_total 0 τ with hτ0 | hτ0
  · rw [abs_of_nonneg hτ0]
    exact le_mul_exp_of_abs_deriv_le_fwd hG hpos hbd hτ0 ((le_abs_self τ).trans hτ)
  · -- backward direction: apply the forward one to `σ ↦ G(-σ)`
    set F : ℝ → ℝ := fun σ => G (-σ) with hF
    have hF' : ∀ σ, HasDerivAt F (-G' (-σ)) σ := by
      intro σ
      have h := (hG (-σ)).comp σ (hasDerivAt_neg σ)
      simpa [hF, Function.comp_def] using h
    have hFpos : ∀ σ, |σ| ≤ T → 0 ≤ F σ := fun σ hσ => hpos (-σ) (by rwa [abs_neg])
    have hFbd : ∀ σ, |σ| ≤ T → |-G' (-σ)| ≤ B * F σ := fun σ hσ => by
      rw [abs_neg]
      exact hbd (-σ) (by rwa [abs_neg])
    have h := le_mul_exp_of_abs_deriv_le_fwd hF' hFpos hFbd (τ := -τ) (by linarith)
      (by rw [abs_of_nonpos hτ0] at hτ; exact hτ)
    simp only [hF, neg_neg, neg_zero] at h
    rw [abs_of_nonpos hτ0]
    exact h

end NonUniqueEuler.Smooth.IterHsH
