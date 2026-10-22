import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Proof: the a priori enclosure on one Taylor step (Grönwall)

Proof of the interface `NonUniqueEuler/I/Verify/StepGronwall.lean` (same declarations, same
statements).

**Manuscript.** Proof of Proposition A.3, step (iii) (`A_verification.tex:406-419`).

**Proof.** Put `Z t = (κ • ψ t, ψ' t) : ℂ × ℂ`; the `Prod` norm is the max norm, so
`‖Z t‖ = max(κ|ψ|, |ψ'|)`, and `‖Z'‖ = max(κ|ψ'|, |V||ψ|) ≤ κ‖Z‖` because `|V| ≤ q ≤ κ²`.
Grönwall (`norm_le_gronwallBound_of_norm_deriv_right_le` with `ε = 0`) gives
`‖Z t‖ ≤ ‖Z s‖ e^{κ(t-s)} ≤ M`. The two differences then follow from the mean value
inequality `norm_image_sub_le_of_norm_deriv_le_segment'`, with `|ψ'| ≤ M` and
`|Vψ| ≤ q · M/κ`.
-/

open Set

namespace NonUniqueEuler

namespace AppA

set_option linter.unusedVariables false in
/-- The bound of the a priori step itself: `max(κ|ψ|, |ψ'|) ≤ M` on the step. -/
theorem apriori_step_bound {ψ ψ' V : ℝ → ℂ} {s h κ q M : ℝ} (hh : 0 ≤ h) (hκ : 0 < κ)
    (hψ : ∀ ξ ∈ Icc s (s + h), HasDerivWithinAt ψ (ψ' ξ) (Icc s (s + h)) ξ)
    (hψ' : ∀ ξ ∈ Icc s (s + h), HasDerivWithinAt ψ' (V ξ * ψ ξ) (Icc s (s + h)) ξ)
    (hV : ∀ ξ ∈ Icc s (s + h), ‖V ξ‖ ≤ q) (hq : q ≤ κ ^ 2)
    (hM : max (κ * ‖ψ s‖) ‖ψ' s‖ * Real.exp (κ * h) ≤ M) :
    ∀ ξ ∈ Icc s (s + h), max (κ * ‖ψ ξ‖) ‖ψ' ξ‖ ≤ M := by
  -- the vector `Z t = (κ ψ t, ψ' t)` and its derivative
  set Z : ℝ → ℂ × ℂ := fun t => (κ • ψ t, ψ' t) with hZ
  set Z' : ℝ → ℂ × ℂ := fun t => (κ • ψ' t, V t * ψ t) with hZ'
  have hnormZ : ∀ t, ‖Z t‖ = max (κ * ‖ψ t‖) ‖ψ' t‖ := by
    intro t
    simp only [hZ, Prod.norm_mk, norm_smul, Real.norm_eq_abs, abs_of_pos hκ]
  have hderiv : ∀ ξ ∈ Icc s (s + h), HasDerivWithinAt Z (Z' ξ) (Icc s (s + h)) ξ := by
    intro ξ hξ
    exact ((hψ ξ hξ).const_smul κ).prodMk (hψ' ξ hξ)
  have hcont : ContinuousOn Z (Icc s (s + h)) := fun ξ hξ => (hderiv ξ hξ).continuousWithinAt
  have hderiv' : ∀ ξ ∈ Ico s (s + h), HasDerivWithinAt Z (Z' ξ) (Ici ξ) ξ := by
    intro ξ hξ
    exact (hderiv ξ (Ico_subset_Icc_self hξ)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hξ)
  have hbound : ∀ ξ ∈ Ico s (s + h), ‖Z' ξ‖ ≤ κ * ‖Z ξ‖ + 0 := by
    intro ξ hξ
    have hξ' : ξ ∈ Icc s (s + h) := Ico_subset_Icc_self hξ
    rw [add_zero, hnormZ]
    simp only [hZ', Prod.norm_mk, norm_smul, Real.norm_eq_abs, abs_of_pos hκ, norm_mul]
    refine max_le ?_ ?_
    · exact mul_le_mul_of_nonneg_left (le_max_right _ _) hκ.le
    · calc ‖V ξ‖ * ‖ψ ξ‖ ≤ q * ‖ψ ξ‖ := mul_le_mul_of_nonneg_right (hV ξ hξ') (norm_nonneg _)
        _ ≤ κ ^ 2 * ‖ψ ξ‖ := mul_le_mul_of_nonneg_right hq (norm_nonneg _)
        _ = κ * (κ * ‖ψ ξ‖) := by ring
        _ ≤ κ * max (κ * ‖ψ ξ‖) ‖ψ' ξ‖ :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) hκ.le
  have hG := norm_le_gronwallBound_of_norm_deriv_right_le hcont hderiv' le_rfl hbound
  intro ξ hξ
  have h1 := hG ξ hξ
  rw [gronwallBound_ε0, hnormZ, hnormZ] at h1
  have hδ : 0 ≤ max (κ * ‖ψ s‖) ‖ψ' s‖ :=
    le_max_of_le_right (norm_nonneg _)
  have hexp : Real.exp (κ * (ξ - s)) ≤ Real.exp (κ * h) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (by linarith [hξ.2]) hκ.le
  calc max (κ * ‖ψ ξ‖) ‖ψ' ξ‖ ≤ max (κ * ‖ψ s‖) ‖ψ' s‖ * Real.exp (κ * (ξ - s)) := h1
    _ ≤ max (κ * ‖ψ s‖) ‖ψ' s‖ * Real.exp (κ * h) := mul_le_mul_of_nonneg_left hexp hδ
    _ ≤ M := hM

/-- **A priori step enclosure.** -/
theorem apriori_step {ψ ψ' V : ℝ → ℂ} {s h κ q M : ℝ} (hh : 0 ≤ h) (hκ : 0 < κ)
    (hψ : ∀ ξ ∈ Icc s (s + h), HasDerivWithinAt ψ (ψ' ξ) (Icc s (s + h)) ξ)
    (hψ' : ∀ ξ ∈ Icc s (s + h), HasDerivWithinAt ψ' (V ξ * ψ ξ) (Icc s (s + h)) ξ)
    (hV : ∀ ξ ∈ Icc s (s + h), ‖V ξ‖ ≤ q) (hq : q ≤ κ ^ 2)
    (hM : max (κ * ‖ψ s‖) ‖ψ' s‖ * Real.exp (κ * h) ≤ M) :
    ∀ ξ ∈ Icc s (s + h), ‖ψ ξ - ψ s‖ ≤ h * M ∧ ‖ψ' ξ - ψ' s‖ ≤ h * q * M / κ := by
  have hB := apriori_step_bound hh hκ hψ hψ' hV hq hM
  have hs : s ∈ Icc s (s + h) := ⟨le_rfl, by linarith⟩
  have hM0 : 0 ≤ M := (le_max_right _ _ |>.trans' (norm_nonneg (ψ' s))).trans (hB s hs)
  have hq0 : 0 ≤ q := (norm_nonneg _).trans (hV s hs)
  -- `|ψ'| ≤ M` and `|ψ| ≤ M / κ` on the step
  have hψ'M : ∀ x ∈ Icc s (s + h), ‖ψ' x‖ ≤ M := fun x hx => (le_max_right _ _).trans (hB x hx)
  have hψM : ∀ x ∈ Icc s (s + h), ‖ψ x‖ ≤ M / κ := by
    intro x hx
    rw [le_div_iff₀ hκ, mul_comm]
    exact (le_max_left _ _).trans (hB x hx)
  have hmv1 := norm_image_sub_le_of_norm_deriv_le_segment' hψ
    (fun x hx => hψ'M x (Ico_subset_Icc_self hx))
  have hmv2 := norm_image_sub_le_of_norm_deriv_le_segment' (C := q * (M / κ)) hψ'
    (fun x hx => by
      rw [norm_mul]
      exact mul_le_mul (hV x (Ico_subset_Icc_self hx)) (hψM x (Ico_subset_Icc_self hx))
        (norm_nonneg _) hq0)
  intro ξ hξ
  have hξs : ξ - s ≤ h := by linarith [hξ.2]
  refine ⟨?_, ?_⟩
  · calc ‖ψ ξ - ψ s‖ ≤ M * (ξ - s) := hmv1 ξ hξ
      _ ≤ M * h := mul_le_mul_of_nonneg_left hξs hM0
      _ = h * M := mul_comm _ _
  · have hC : 0 ≤ q * (M / κ) := mul_nonneg hq0 (div_nonneg hM0 hκ.le)
    calc ‖ψ' ξ - ψ' s‖ ≤ q * (M / κ) * (ξ - s) := hmv2 ξ hξ
      _ ≤ q * (M / κ) * h := mul_le_mul_of_nonneg_left hξs hC
      _ = h * q * M / κ := by ring

end AppA

end NonUniqueEuler
