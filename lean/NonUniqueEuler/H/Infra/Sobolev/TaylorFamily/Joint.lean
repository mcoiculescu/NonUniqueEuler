import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.Bounded
import NonUniqueEuler.Defs.Infra.Sobolev

/-!
# Helper for `P/Infra/Sobolev/TaylorFamily`: spatial derivatives of jointly smooth families and
a second-order Taylor bound in time

For a jointly smooth `W : ℝ × ℂ → ℂ`, the spatial iterated directional derivatives
`∂_{v₁} ⋯ ∂_{vₙ} W(s, ·)` are the slices of a jointly smooth function `H`, and the time
derivative commutes with them (symmetry of second derivatives, `ContDiffAt.isSymmSndFDerivAt`).
If `W` vanishes on an open set, so does `H`. (The first group of lemmas is adapted from the
helper `H/Infra/Sobolev/Paths/Joint.lean` of this project, in a separate namespace.)

`exists_bound_sq`: if `H(0, x) = 0` and `∂_t H(0, x) = 0`, then `|H(κ, x)| ≤ B κ²` on
`[0,1] × K` (two applications of the mean value inequality, `B = sup_{[0,1]×K} |∂²_t H|`).
-/

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace NonUniqueEuler.Sob.TaylorFamilyH

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The derivative of a slice `y ↦ H (s, y)` is the derivative of `H` in the direction `(0, v)`. -/
theorem fderiv_slice_apply {H : ℝ × ℂ → G} {s : ℝ} {x : ℂ} (hH : DifferentiableAt ℝ H (s, x))
    (v : ℂ) : fderiv ℝ (fun y => H (s, y)) x v = fderiv ℝ H (s, x) (0, v) := by
  have hp : HasFDerivAt (fun y : ℂ => (s, y))
      ((0 : ℂ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℂ)) x :=
    (hasFDerivAt_const s x).prodMk (hasFDerivAt_id x)
  have h : fderiv ℝ (fun y => H (s, y)) x =
      (fderiv ℝ H (s, x)).comp ((0 : ℂ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℂ)) :=
    (hH.hasFDerivAt.comp x hp).fderiv
  rw [h]
  simp

/-- The time derivative of a slice `τ ↦ H (τ, x)`. -/
theorem hasDerivAt_time_slice {H : ℝ × ℂ → G} {s : ℝ} {x : ℂ}
    (hH : DifferentiableAt ℝ H (s, x)) :
    HasDerivAt (fun τ => H (τ, x)) (fderiv ℝ H (s, x) (1, 0)) s := by
  have hp : HasDerivAt (fun τ : ℝ => (τ, x)) ((1 : ℝ), (0 : ℂ)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
  exact hH.hasFDerivAt.comp_hasDerivAt s hp

/-- A function vanishing on an open set has vanishing derivative there. -/
theorem fderiv_eq_zero_of_eqOn_zero {H : ℝ × ℂ → G} {U : Set (ℝ × ℂ)} (hU : IsOpen U)
    (hHU : ∀ p ∈ U, H p = 0) {p : ℝ × ℂ} (hp : p ∈ U) : fderiv ℝ H p = 0 := by
  have h : H =ᶠ[𝓝 p] fun _ => (0 : G) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact hHU q hq
  rw [h.fderiv_eq]
  simp

/-- The derivative of `p ↦ DH(p) a` in the direction `b` is `D²H(p) b a`. -/
theorem fderiv_fderiv_apply_const {H : ℝ × ℂ → ℂ} (hH : ContDiff ℝ ∞ H) (a b p : ℝ × ℂ) :
    fderiv ℝ (fun q => fderiv ℝ H q a) p b = fderiv ℝ (fderiv ℝ H) p b a := by
  have hd : DifferentiableAt ℝ (fderiv ℝ H) p :=
    ((hH.fderiv_right (m := 1) (by simp)).differentiable (by simp)) p
  rw [fderiv_clm_apply hd (differentiableAt_const a)]
  simp

theorem contDiff_fderiv_apply {H : ℝ × ℂ → G} (hH : ContDiff ℝ ∞ H) (a : ℝ × ℂ) :
    ContDiff ℝ ∞ (fun q => fderiv ℝ H q a) :=
  (hH.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- Spatial iterated derivatives of a jointly smooth family are slices of a jointly smooth
function, which commutes with the time derivative and vanishes where `W` vanishes (on an open
set). -/
theorem exists_joint_iterDirDeriv {W : ℝ × ℂ → ℂ} (hW : ContDiff ℝ ∞ W) {U : Set (ℝ × ℂ)}
    (hU : IsOpen U) (hWU : ∀ p ∈ U, W p = 0) (vs : List ℂ) :
    ∃ H : ℝ × ℂ → ℂ, ContDiff ℝ ∞ H ∧ (∀ p ∈ U, H p = 0) ∧
      (∀ s x, iterDirDeriv vs (fun y => W (s, y)) x = H (s, x)) ∧
      (∀ s x, iterDirDeriv vs (fun y => fderiv ℝ W (s, y) (1, 0)) x =
        fderiv ℝ H (s, x) (1, 0)) := by
  induction vs with
  | nil => exact ⟨W, hW, hWU, fun s x => rfl, fun s x => rfl⟩
  | cons v vs ih =>
    obtain ⟨H, hH, hHU, hsl, htm⟩ := ih
    refine ⟨fun q => fderiv ℝ H q (0, v), contDiff_fderiv_apply hH (0, v), ?_, ?_, ?_⟩
    · intro p hp
      simp [fderiv_eq_zero_of_eqOn_zero hU hHU hp]
    · intro s x
      have hfun : iterDirDeriv vs (fun y => W (s, y)) = fun y => H (s, y) :=
        funext fun y => hsl s y
      rw [iterDirDeriv_cons, dirDeriv, hfun, fderiv_slice_apply ((hH.differentiable (by simp)) _)]
    · intro s x
      have hfun : iterDirDeriv vs (fun y => fderiv ℝ W (s, y) (1, 0)) =
          fun y => fderiv ℝ H (s, y) (1, 0) :=
        funext fun y => htm s y
      have hsymm := (hH.contDiffAt (x := (s, x))).isSymmSndFDerivAt (n := ∞) (by simp)
      rw [iterDirDeriv_cons, dirDeriv, hfun,
        fderiv_slice_apply (((contDiff_fderiv_apply hH (1, 0)).differentiable (by simp)) _),
        fderiv_fderiv_apply_const hH, fderiv_fderiv_apply_const hH, hsymm]

/-- Iterated directional derivatives of the zero function vanish. -/
theorem iterDirDeriv_zero (vs : List ℂ) :
    iterDirDeriv vs (fun _ : ℂ => (0 : ℂ)) = fun _ => 0 := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    rw [iterDirDeriv_cons, ih]
    funext x
    simp [dirDeriv]

/-- **Second-order bound in time.** If `H(0, x) = 0` and `∂_t H(0, x) = 0` for all `x`, then
`‖H(κ, x)‖ ≤ B κ²` for `κ ∈ [0,1]` and `x ∈ K`, with `B ≥ 0` a bound of `|∂²_t H|` on the
compact set `[0,1] × K`. -/
theorem exists_bound_sq {H : ℝ × ℂ → ℂ} (hH : ContDiff ℝ ∞ H) {K : Set ℂ} (hK : IsCompact K)
    (h0 : ∀ x, H (0, x) = 0) (h1 : ∀ x, fderiv ℝ H (0, x) (1, 0) = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ κ ∈ Icc (0 : ℝ) 1, ∀ x ∈ K, ‖H (κ, x)‖ ≤ B * κ ^ 2 := by
  have hH1s : ContDiff ℝ ∞ (fun p => fderiv ℝ H p (1, 0)) := contDiff_fderiv_apply hH (1, 0)
  have hH2c : Continuous (fun p => fderiv ℝ (fun q => fderiv ℝ H q (1, 0)) p (1, 0)) :=
    (contDiff_fderiv_apply hH1s (1, 0)).continuous
  obtain ⟨B0, hB0⟩ :=
    ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod hK).exists_bound_of_continuousOn
      hH2c.continuousOn
  refine ⟨max B0 0, le_max_right _ _, ?_⟩
  intro κ hκ x hx
  have hdH : ∀ p, DifferentiableAt ℝ H p := fun p => (hH.differentiable (by simp)) p
  have hdH1 : ∀ p, DifferentiableAt ℝ (fun p => fderiv ℝ H p (1, 0)) p := fun p =>
    (hH1s.differentiable (by simp)) p
  -- first step: `‖∂_t H(t, x)‖ ≤ B t` on `[0,1]`
  have step1 : ∀ t ∈ Icc (0 : ℝ) 1, ‖fderiv ℝ H (t, x) (1, 0)‖ ≤ max B0 0 * t := by
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment' (a := 0) (b := 1)
      (f := fun t => fderiv ℝ H (t, x) (1, 0))
      (f' := fun t => fderiv ℝ (fun q => fderiv ℝ H q (1, 0)) (t, x) (1, 0)) (C := max B0 0)
      (fun t _ => (hasDerivAt_time_slice (hdH1 (t, x))).hasDerivWithinAt)
      (fun t ht => (hB0 (t, x) ⟨Ico_subset_Icc_self ht, hx⟩).trans (le_max_left _ _))
    intro t ht
    have h := hmv t ht
    simp only [h1 x, sub_zero] at h
    exact h
  -- second step: `‖H(κ, x)‖ ≤ (B κ) κ`
  have step2 := norm_image_sub_le_of_norm_deriv_le_segment' (a := 0) (b := κ)
    (f := fun t => H (t, x)) (f' := fun t => fderiv ℝ H (t, x) (1, 0)) (C := max B0 0 * κ)
    (fun t _ => (hasDerivAt_time_slice (hdH (t, x))).hasDerivWithinAt)
    (fun t ht => (step1 t ⟨ht.1, ht.2.le.trans hκ.2⟩).trans
      (mul_le_mul_of_nonneg_left ht.2.le (le_max_right _ _)))
    κ ⟨hκ.1, le_rfl⟩
  simp only [h0 x, sub_zero] at step2
  calc ‖H (κ, x)‖ ≤ max B0 0 * κ * κ := step2
    _ = max B0 0 * κ ^ 2 := by ring

end NonUniqueEuler.Sob.TaylorFamilyH
