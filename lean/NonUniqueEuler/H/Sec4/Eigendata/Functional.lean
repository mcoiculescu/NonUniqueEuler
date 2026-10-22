import NonUniqueEuler.H.Sec4.Eigendata.Basic

/-!
# Helpers for `def:eigendata`: `L²` pairings as continuous functionals on `Y^s(K)`

Helper of `P/Sec4/Eigendata.lean` (fully proved). Namespace `NonUniqueEuler.Eig.EigendataH`.

* `exists_pairing`: for `e ∈ L²`, `w ↦ ∫ w e` is a continuous functional on `Y^s(K)` with
  `|∫ w e| ≤ ‖e‖_{L²} ‖w‖` (the `L²` inner product with `conj e`, and `‖w.fn‖_{L²} ≤ ‖w‖`);
* `l2_conj`: `‖conj g‖_{L²} = ‖g‖_{L²}`;
* `integral_mul_conj_self`: `∫ g conj g = ‖g‖²_{L²}` for `g ∈ L²`.
-/

noncomputable section

open MeasureTheory Set Real Filter Topology ComplexConjugate
open scoped ENNReal

namespace NonUniqueEuler.Eig.EigendataH

open Sect Sob

/-- `‖conj g‖_{L²} = ‖g‖_{L²}`. -/
theorem l2_conj (g : ℂ → ℂ) : l2 (fun x => conj (g x)) = l2 g := by
  unfold l2
  congr 1
  exact eLpNorm_congr_norm_ae (Eventually.of_forall fun x => by simp)

/-- `∫ g conj g = ‖g‖²_{L²}` for `g ∈ L²`. -/
theorem integral_mul_conj_self {g : ℂ → ℂ} (hg : MemLp g 2 volume) :
    ∫ x, g x * conj (g x) = ((l2 g ^ 2 : ℝ) : ℂ) := by
  have h1 : inner ℂ (hg.toLp g) (hg.toLp g) = ∫ x, g x * conj (g x) := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp hg] with x hx
    rw [hx, RCLike.inner_apply]
  rw [← h1, inner_self_eq_norm_sq_to_K, Lp.norm_toLp]
  push_cast
  rfl

/-- For `e ∈ L²`, `w ↦ ∫ w e` is a continuous functional on `Y^s(K)`, bounded by
`‖e‖_{L²} ‖w‖`. -/
theorem exists_pairing (s : ℕ) (K : Set ℂ) {e : ℂ → ℂ} (he : MemLp e 2 volume) :
    ∃ T : Y s K →L[ℂ] ℂ, (∀ w : Y s K, T w = ∫ x, w.fn x * e x) ∧
      ∀ w : Y s K, ‖T w‖ ≤ l2 e * ‖w‖ := by
  set E : Lp ℂ 2 (volume : Measure ℂ) := he.star.toLp (star e) with hEdef
  refine ⟨(innerSL ℂ E).comp ((proj0 s).comp (YSub s K).subtypeL), fun w => ?_, fun w => ?_⟩
  · rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp he.star] with x hx
    rw [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, coeFn_proj0, hx,
      RCLike.inner_apply]
    simp
  · rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply]
    refine (norm_inner_le_norm (𝕜 := ℂ) _ _).trans ?_
    have hE : ‖E‖ = l2 e := by
      rw [hEdef, Lp.norm_toLp]
      have : (star e) = fun x => conj (e x) := rfl
      rw [this]
      exact l2_conj e
    rw [hE]
    refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
    rw [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
    exact PiLp.norm_apply_le _ _

end NonUniqueEuler.Eig.EigendataH
