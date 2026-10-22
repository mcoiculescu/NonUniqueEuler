import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Operations
import NonUniqueEuler.Defs.Infra.Sobolev

/-!
# Helper for `P/Infra/Sobolev/Paths`: spatial derivatives of jointly smooth families

For a jointly smooth `W : ℝ × ℂ → ℂ`, the spatial iterated directional derivatives
`∂_{v₁} ⋯ ∂_{vₙ} W(s, ·)` are the slices of a jointly smooth function `H`, and the time
derivative commutes with them (symmetry of second derivatives, `ContDiffAt.isSymmSndFDerivAt`).
If `W` vanishes on an open set, so does `H`.
-/

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace NonUniqueEuler.Sob.PathsH

/-- The derivative of a slice `y ↦ H (s, y)` is the derivative of `H` in the direction `(0, v)`. -/
theorem fderiv_slice_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : ℝ × ℂ → F} {s : ℝ} {x : ℂ} (hH : DifferentiableAt ℝ H (s, x)) (v : ℂ) :
    fderiv ℝ (fun y => H (s, y)) x v = fderiv ℝ H (s, x) (0, v) := by
  have hp : HasFDerivAt (fun y : ℂ => (s, y))
      ((0 : ℂ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℂ)) x :=
    (hasFDerivAt_const s x).prodMk (hasFDerivAt_id x)
  have h : fderiv ℝ (fun y => H (s, y)) x =
      (fderiv ℝ H (s, x)).comp ((0 : ℂ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℂ)) :=
    (hH.hasFDerivAt.comp x hp).fderiv
  rw [h]
  simp

/-- The time derivative of a slice `τ ↦ H (τ, x)`. -/
theorem hasDerivAt_time_slice {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : ℝ × ℂ → F} {s : ℝ} {x : ℂ} (hH : DifferentiableAt ℝ H (s, x)) :
    HasDerivAt (fun τ => H (τ, x)) (fderiv ℝ H (s, x) (1, 0)) s := by
  have hp : HasDerivAt (fun τ : ℝ => (τ, x)) ((1 : ℝ), (0 : ℂ)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
  exact hH.hasFDerivAt.comp_hasDerivAt s hp

/-- A function vanishing on an open set has vanishing derivative there. -/
theorem fderiv_eq_zero_of_eqOn_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : ℝ × ℂ → F} {U : Set (ℝ × ℂ)} (hU : IsOpen U) (hHU : ∀ p ∈ U, H p = 0) {p : ℝ × ℂ}
    (hp : p ∈ U) : fderiv ℝ H p = 0 := by
  have h : H =ᶠ[𝓝 p] fun _ => (0 : F) := by
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

theorem contDiff_fderiv_apply {H : ℝ × ℂ → ℂ} (hH : ContDiff ℝ ∞ H) (a : ℝ × ℂ) :
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

end NonUniqueEuler.Sob.PathsH
