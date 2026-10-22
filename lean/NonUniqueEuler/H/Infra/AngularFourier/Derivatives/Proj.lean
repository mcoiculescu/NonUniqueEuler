import NonUniqueEuler.Defs.Infra.AngularFourier
import NonUniqueEuler.I.Infra.Sobolev.Space
import NonUniqueEuler.I.Infra.Sobolev.Symmetry
import NonUniqueEuler.I.Infra.Sobolev.Norm
import NonUniqueEuler.I.Infra.AngularFourier.Derivatives.RotPath
import NonUniqueEuler.I.Infra.AngularFourier.Derivatives.Average

/-!
# Helpers for `P/Infra/AngularFourier/Derivatives`: `P_ℓ` preserves `H^k`

`P_ℓ g` is the function of the `Hk`-valued Bochner integral
`G = (2π)⁻¹ ∫₀^{2π} e^{-iℓθ} toHk k (g ∘ O_θ) dθ` (`Hk_fn_average_ae_eq`,
`I/Infra/AngularFourier/Derivatives/Average.lean`; the integrand is continuous,
`Sob.continuous_toHk_comp_rot`, `I/Infra/AngularFourier/Derivatives/RotPath.lean`), so
`P_ℓ g ∈ H^k` and `‖P_ℓ g‖_{H^k} = ‖G‖ ≤ sup_θ ‖g ∘ O_θ‖_{H^k} ≤ 2^k ‖g‖_{H^k}`
(`Sob.MemH.comp_rot`).
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace NonUniqueEuler.Ang

namespace DerivAux

theorem norm_exp_neg_mul_I' (ℓ : ℤ) (θ : ℝ) :
    ‖Complex.exp (-((ℓ : ℂ) * θ * Complex.I))‖ = 1 := by
  rw [Complex.norm_exp]; simp

theorem memH_sectorProj_aux {k : ℕ} {g : ℂ → ℂ} (hg : Sob.MemH k g) (ℓ : ℤ) :
    Sob.MemH k (sectorProj ℓ g) ∧ Sob.normH k (sectorProj ℓ g) ≤ 2 ^ k * Sob.normH k g := by
  have hFc : Continuous (fun θ : ℝ => Sob.toHk k (fun x => g (rot θ x))) :=
    Sob.continuous_toHk_comp_rot hg
  have hFg : ∀ θ : ℝ, (Sob.toHk k (fun x => g (rot θ x))).fn =ᵐ[volume] fun x => g (rot θ x) :=
    fun θ => Sob.toHk_fn (hg.comp_rot θ).1
  have hG := Hk_fn_average_ae_eq (Sob.memH_iff.1 hg).1 hFc hFg ℓ
  obtain ⟨hGm, hGn⟩ := Sob.Hk.memH_fn ((2 * π : ℂ)⁻¹ • ∫ θ in (0 : ℝ)..2 * π,
    Complex.exp (-((ℓ : ℂ) * θ * Complex.I)) • Sob.toHk k (fun x => g (rot θ x)))
  obtain ⟨hPm, hPn⟩ := hGm.congr_ae hG
  refine ⟨hPm, ?_⟩
  rw [hPn, hGn, norm_smul]
  have hbound : ∀ θ ∈ uIoc (0 : ℝ) (2 * π),
      ‖Complex.exp (-((ℓ : ℂ) * θ * Complex.I)) • Sob.toHk k (fun x => g (rot θ x))‖ ≤
        2 ^ k * Sob.normH k g := by
    intro θ _
    rw [norm_smul, norm_exp_neg_mul_I', one_mul, Sob.norm_toHk (hg.comp_rot θ).1]
    exact (hg.comp_rot θ).2
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have h2π : ‖(2 * π : ℂ)⁻¹‖ = (2 * π)⁻¹ := by
    rw [norm_inv]
    congr 1
    have : (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [h2π]
  calc (2 * π)⁻¹ * ‖∫ θ in (0 : ℝ)..2 * π,
        Complex.exp (-((ℓ : ℂ) * θ * Complex.I)) • Sob.toHk k (fun x => g (rot θ x))‖
      ≤ (2 * π)⁻¹ * (2 ^ k * Sob.normH k g * |2 * π - 0|) := by gcongr
    _ = 2 ^ k * Sob.normH k g := by
      rw [sub_zero, abs_of_pos (by positivity)]
      field_simp

end DerivAux

end NonUniqueEuler.Ang
