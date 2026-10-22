import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import NonUniqueEuler.Defs.Infra.Sobolev
import NonUniqueEuler.Defs.Infra.Polar
import NonUniqueEuler.Statement.Plane
import NonUniqueEuler.I.Infra.Sobolev.NormDeriv
import NonUniqueEuler.I.Infra.Sobolev.Symmetry

/-!
# Proof: first weak derivatives of a rotated function (library I-HK)

Proof of `NonUniqueEuler/I/Infra/Sobolev/RotDeriv.lean` (same declaration, same statement).

Following the docstring of the interface file:
* `RotDerivAux.hasWeakDerivOn_comp_rot`: the chain rule for one weak derivative under the
  rotation `O_θ`: if `g = ∂_{O_θ v} f` weakly then `g ∘ O_θ = ∂_v (f ∘ O_θ)` weakly. For a test
  function `φ`, `ψ = φ ∘ O_{-θ}` is a test function, `∂_v φ = (∂_{O_θ v} ψ) ∘ O_θ`, and the
  integrals are transported by the measure preserving map `O_θ`.
* `RotDerivAux.hasWeakDerivOn_single_add`: weak derivatives are linear in the direction.
* `O_θ 1 = cos θ · 1 + sin θ · i` and `O_θ i = -sin θ · 1 + cos θ · i`.
* The resulting `L²` weak derivatives of `f ∘ O_θ ∈ H^1` (`MemH.comp_rot`) agree a.e. with the
  chosen ones (`MemH.weakPartial_ae_eq`).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace NonUniqueEuler.Sob

namespace RotDerivAux

/-! ### The rotation as a change of variables -/

theorem exists_rot_clm (θ : ℝ) :
    ∃ L : ℂ →L[ℝ] ℂ, (∀ v, L v = rot θ v) ∧ ∀ x, HasFDerivAt (rot θ) L x := by
  refine ⟨((rotation (Circle.exp θ)).toContinuousLinearEquiv : ℂ →L[ℝ] ℂ), fun v => ?_,
    fun x => ?_⟩
  · rw [Polar.rot_eq_rotation]
    rfl
  · rw [Polar.rot_eq_rotation]
    exact (rotation (Circle.exp θ)).toContinuousLinearEquiv.hasFDerivAt

theorem rot_continuous (θ : ℝ) : Continuous (rot θ) := by
  unfold rot
  exact continuous_const.mul continuous_id

theorem rot_contDiff (θ : ℝ) : ContDiff ℝ ∞ (rot θ) := by
  unfold rot
  exact contDiff_const.mul contDiff_id

theorem rot_neg_rot (θ : ℝ) (x : ℂ) : rot (-θ) (rot θ x) = x := by
  rw [← Polar.rot_add, neg_add_cancel, Polar.rot_zero]

theorem rot_measurableEmbedding (θ : ℝ) : MeasurableEmbedding (rot θ) := by
  rw [Polar.rot_eq_rotation]
  exact (rotation (Circle.exp θ)).toHomeomorph.measurableEmbedding

theorem integral_comp_rot (θ : ℝ) (h : ℂ → ℂ) : ∫ x, h (rot θ x) = ∫ y, h y :=
  (Polar.measurePreserving_rot θ).integral_comp (rot_measurableEmbedding θ) h

theorem isTestFn_comp_rot {φ : ℂ → ℂ} (hφ : IsTestFn univ φ) (θ : ℝ) :
    IsTestFn univ (fun y => φ (rot θ y)) := by
  refine ⟨hφ.smooth.comp (rot_contDiff θ), ?_, subset_univ _⟩
  refine HasCompactSupport.intro (hφ.compact.image (rot_continuous (-θ))) (fun y hy => ?_)
  apply image_eq_zero_of_notMem_tsupport
  intro h
  exact hy ⟨rot θ y, h, rot_neg_rot θ y⟩

/-- `∂_v (ψ ∘ O_θ) = (∂_{O_θ v} ψ) ∘ O_θ`. -/
theorem dirDeriv_comp_rot {ψ : ℂ → ℂ} (hψ : Differentiable ℝ ψ) (θ : ℝ) (v x : ℂ) :
    dirDeriv v (fun y => ψ (rot θ y)) x = dirDeriv (rot θ v) ψ (rot θ x) := by
  obtain ⟨L, hLv, hL⟩ := exists_rot_clm θ
  have h2 := (hψ (rot θ x)).hasFDerivAt.comp x (hL x)
  show fderiv ℝ (ψ ∘ rot θ) x v = fderiv ℝ ψ (rot θ x) (rot θ v)
  rw [h2.fderiv, ContinuousLinearMap.comp_apply, hLv]

/-- The chain rule for one weak derivative under a rotation: if `g = ∂_{O_θ v} f` weakly, then
`g ∘ O_θ = ∂_v (f ∘ O_θ)` weakly. -/
theorem hasWeakDerivOn_comp_rot {θ : ℝ} {v : ℂ} {f g : ℂ → ℂ}
    (h : HasWeakDerivOn univ [rot θ v] f g) :
    HasWeakDerivOn univ [v] (fun x => f (rot θ x)) (fun x => g (rot θ x)) := by
  intro φ hφ
  obtain ⟨ψ, hψ, rfl⟩ : ∃ ψ : ℂ → ℂ, IsTestFn univ ψ ∧ φ = fun x => ψ (rot θ x) :=
    ⟨fun y => φ (rot (-θ) y), isTestFn_comp_rot hφ (-θ), by
      funext x
      show φ x = φ (rot (-θ) (rot θ x))
      rw [rot_neg_rot]⟩
  have key := h ψ hψ
  rw [List.length_singleton] at key ⊢
  simp only [iterDirDeriv_cons, iterDirDeriv_nil] at key ⊢
  have hd : Differentiable ℝ ψ := hψ.smooth.differentiable (by simp)
  have e1 : ∫ x, f (rot θ x) * dirDeriv v (fun y => ψ (rot θ y)) x =
      ∫ y, f y * dirDeriv (rot θ v) ψ y := by
    rw [← integral_comp_rot θ (fun y => f y * dirDeriv (rot θ v) ψ y)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [dirDeriv_comp_rot hd]
  have e2 : ∫ x, g (rot θ x) * ψ (rot θ x) = ∫ y, g y * ψ y :=
    integral_comp_rot θ (fun y => g y * ψ y)
  rw [e1, e2, key]

/-! ### Linearity in the direction -/

theorem integrable_mul_testFn {g φ : ℂ → ℂ} (hg : LocallyIntegrableOn g univ)
    (hφ : IsTestFn univ φ) : Integrable (fun x => g x * φ x) := by
  have hK : IsCompact (tsupport φ) := hφ.compact
  have h1 : IntegrableOn g (tsupport φ) := hg.integrableOn_compact_subset hφ.subset hK
  have h2 : IntegrableOn (fun x => g x * φ x) (tsupport φ) :=
    h1.mul_continuousOn hφ.continuous.continuousOn hK
  refine h2.integrable_of_forall_notMem_eq_zero (fun x hx => ?_)
  simp [image_eq_zero_of_notMem_tsupport hx]

theorem dirDeriv_add_smul (φ : ℂ → ℂ) (u w : ℂ) (a b : ℝ) (x : ℂ) :
    dirDeriv (a • u + b • w) φ x = (a : ℂ) * dirDeriv u φ x + (b : ℂ) * dirDeriv w φ x := by
  simp only [dirDeriv]
  rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]

/-- Weak first derivatives are linear in the direction:
`∂_{a u + b w} f = a ∂_u f + b ∂_w f`. -/
theorem hasWeakDerivOn_single_add {u w : ℂ} {f g₁ g₂ : ℂ → ℂ}
    (hf : LocallyIntegrableOn f univ) (hg₁ : LocallyIntegrableOn g₁ univ)
    (hg₂ : LocallyIntegrableOn g₂ univ) (a b : ℝ)
    (h₁ : HasWeakDerivOn univ [u] f g₁) (h₂ : HasWeakDerivOn univ [w] f g₂) :
    HasWeakDerivOn univ [a • u + b • w] f (fun x => (a : ℂ) * g₁ x + (b : ℂ) * g₂ x) := by
  intro φ hφ
  have i1 := integrable_mul_testFn hf (hφ.dirDeriv u)
  have i2 := integrable_mul_testFn hf (hφ.dirDeriv w)
  have j1 := integrable_mul_testFn hg₁ hφ
  have j2 := integrable_mul_testFn hg₂ hφ
  have k1 := h₁ φ hφ
  have k2 := h₂ φ hφ
  rw [List.length_singleton] at k1 k2 ⊢
  simp only [iterDirDeriv_cons, iterDirDeriv_nil] at k1 k2 ⊢
  have e1 : ∫ x, f x * dirDeriv (a • u + b • w) φ x =
      (a : ℂ) * (∫ x, f x * dirDeriv u φ x) + (b : ℂ) * (∫ x, f x * dirDeriv w φ x) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (i1.const_mul _) (i2.const_mul _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [dirDeriv_add_smul]
    ring
  have e2 : ∫ x, ((a : ℂ) * g₁ x + (b : ℂ) * g₂ x) * φ x =
      (a : ℂ) * (∫ x, g₁ x * φ x) + (b : ℂ) * (∫ x, g₂ x * φ x) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (j1.const_mul _) (j2.const_mul _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  rw [e1, e2, k1, k2]
  ring

/-! ### The rotated coordinate directions -/

theorem rot_one (θ : ℝ) : rot θ 1 = (Real.cos θ) • (1 : ℂ) + (Real.sin θ) • Complex.I := by
  apply Complex.ext <;>
    simp [rot, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.cos_ofReal_re,
      Complex.sin_ofReal_re]

theorem rot_I (θ : ℝ) :
    rot θ Complex.I = (-Real.sin θ) • (1 : ℂ) + (Real.cos θ) • Complex.I := by
  apply Complex.ext <;>
    simp [rot, Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

theorem locInt_of_memLp {g : ℂ → ℂ} (hg : MemLp g 2 volume) : LocallyIntegrableOn g univ :=
  (hg.locallyIntegrable (by norm_num)).locallyIntegrableOn univ

theorem pdList_one_zero : pdList (1, 0) = [1] := rfl

theorem pdList_zero_one : pdList (0, 1) = [Complex.I] := rfl

end RotDerivAux

open RotDerivAux

/-- The first weak derivatives of `f ∘ O_θ` for `f ∈ H^1`. -/
theorem MemH.weakPartial_comp_rot {f : ℂ → ℂ} (hf : MemH 1 f) (θ : ℝ) :
    weakPartial (1, 0) (fun x => f (rot θ x)) =ᵐ[volume]
        (fun x => (Real.cos θ : ℂ) * weakPartial (1, 0) f (rot θ x) +
          (Real.sin θ : ℂ) * weakPartial (0, 1) f (rot θ x)) ∧
      weakPartial (0, 1) (fun x => f (rot θ x)) =ᵐ[volume]
        (fun x => -(Real.sin θ : ℂ) * weakPartial (1, 0) f (rot θ x) +
          (Real.cos θ : ℂ) * weakPartial (0, 1) f (rot θ x)) := by
  have h10 : ((1 : ℕ), (0 : ℕ)) ∈ multiIdx 1 := mem_multiIdx.2 (by norm_num)
  have h01 : ((0 : ℕ), (1 : ℕ)) ∈ multiIdx 1 := mem_multiIdx.2 (by norm_num)
  obtain ⟨hA1, hA2⟩ := hf.memLp_weakPartial h10
  obtain ⟨hB1, hB2⟩ := hf.memLp_weakPartial h01
  have hf2 : MemLp f 2 volume := (memH_iff.1 hf).1
  have hrot : MemH 1 (fun x => f (rot θ x)) := (hf.comp_rot θ).1
  set A := weakPartial (1, 0) f
  set B := weakPartial (0, 1) f
  rw [pdList_one_zero] at hA2
  rw [pdList_zero_one] at hB2
  have hmp := Polar.measurePreserving_rot θ
  refine ⟨?_, ?_⟩
  · have d : HasWeakDerivOn univ [rot θ 1] f
        (fun x => (Real.cos θ : ℂ) * A x + (Real.sin θ : ℂ) * B x) := by
      rw [rot_one]
      exact hasWeakDerivOn_single_add (locInt_of_memLp hf2) (locInt_of_memLp hA1)
        (locInt_of_memLp hB1) _ _ hA2 hB2
    have hm : MemLp (fun x => (Real.cos θ : ℂ) * A x + (Real.sin θ : ℂ) * B x) 2 volume :=
      (hA1.const_mul _).add (hB1.const_mul _)
    refine hrot.weakPartial_ae_eq h10 (hm.comp_measurePreserving hmp) ?_
    rw [pdList_one_zero]
    exact hasWeakDerivOn_comp_rot d
  · have d : HasWeakDerivOn univ [rot θ Complex.I] f
        (fun x => -(Real.sin θ : ℂ) * A x + (Real.cos θ : ℂ) * B x) := by
      rw [rot_I]
      have := hasWeakDerivOn_single_add (locInt_of_memLp hf2) (locInt_of_memLp hA1)
        (locInt_of_memLp hB1) (-Real.sin θ) (Real.cos θ) hA2 hB2
      simpa only [Complex.ofReal_neg] using this
    have hm : MemLp (fun x => -(Real.sin θ : ℂ) * A x + (Real.cos θ : ℂ) * B x) 2 volume :=
      (hA1.const_mul _).add (hB1.const_mul _)
    refine hrot.weakPartial_ae_eq h01 (hm.comp_measurePreserving hmp) ?_
    rw [pdList_zero_one]
    exact hasWeakDerivOn_comp_rot d

end NonUniqueEuler.Sob
