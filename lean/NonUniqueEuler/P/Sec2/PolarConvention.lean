import NonUniqueEuler.Defs.Sec2.BiotSavart
import NonUniqueEuler.I.Sec2.BSSmooth
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Proof: the sign conventions of the stream function in polar coordinates

Proof of `I/Sec2/PolarConvention.lean` (manuscript `02_prelim.tex:38-47`, Conventions).

* `Prelim.inner_perpGrad_radial_angular`: by the chain rule, `∂_θψ(x) = Dψ(x)(ix)` (the curve
  `θ ↦ O_θ x` has velocity `ix` at `θ = 0`) and `∂_rψ(x) = Dψ(x)(x/|x|)` (the ray
  `r ↦ r x/|x|` passes through `x` at `r = |x|` with velocity `x/|x|`). With
  `Dψ(x) z = ⟨∇ψ(x), z⟩` (`Prelim.fderiv_apply_eq_inner_grad`) and `∇^⊥ψ = i∇ψ`, both identities
  are the elementary relations `⟨ia, b/|x|⟩ = -|x|⁻¹⟨a, ib⟩`, `⟨ia, ib/|x|⟩ = ⟨a, b/|x|⟩`.
* `BS.inner_velocity_radial_angular_of_smooth`: rewrite `velocity g = ∇^⊥ψ`
  (`BS.velocity_eq_perpGrad_of_smooth`, `lem:BS-basic`(d)); `ψ` is smooth
  (`BS.contDiff_velocity_of_smooth`), hence differentiable at `x`.
-/

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace NonUniqueEuler

/-- The curve `θ ↦ O_θ x` has velocity `ix` at `θ = 0`. -/
private theorem hasDerivAt_rot_zero (x : ℂ) :
    HasDerivAt (fun θ : ℝ => rot θ x) (Complex.I * x) 0 := by
  have h1 : HasDerivAt (fun θ : ℝ => ((θ : ℝ) : ℂ)) 1 (0 : ℝ) :=
    (hasDerivAt_id (0 : ℝ)).ofReal_comp
  have h2 := ((h1.mul_const Complex.I).cexp).mul_const x
  unfold rot
  exact h2.congr_deriv (by simp)

/-- `∂_θψ(x) = Dψ(x)(ix)`. -/
private theorem deriv_angular_eq {ψ : ℂ → ℝ} {x : ℂ} (hψ : DifferentiableAt ℝ ψ x) :
    deriv (fun θ : ℝ => ψ (rot θ x)) 0 = fderiv ℝ ψ x (Complex.I * x) := by
  have hrot0 : rot 0 x = x := by simp [rot]
  have hψ' : HasFDerivAt ψ (fderiv ℝ ψ x) (rot 0 x) := by
    rw [hrot0]; exact hψ.hasFDerivAt
  exact (hψ'.comp_hasDerivAt (0 : ℝ) (hasDerivAt_rot_zero x)).deriv

/-- `∂_rψ(x) = Dψ(x)(x/|x|)`. -/
private theorem deriv_radial_eq {ψ : ℂ → ℝ} {x : ℂ} (hx : x ≠ 0)
    (hψ : DifferentiableAt ℝ ψ x) :
    deriv (fun r : ℝ => ψ ((r : ℂ) * (x / (‖x‖ : ℂ)))) ‖x‖ =
      fderiv ℝ ψ x (x / (‖x‖ : ℂ)) := by
  have hn : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hx
  have hpt : ((‖x‖ : ℝ) : ℂ) * (x / (‖x‖ : ℂ)) = x := by field_simp
  have hray : HasDerivAt (fun r : ℝ => (r : ℂ) * (x / (‖x‖ : ℂ))) (x / (‖x‖ : ℂ)) ‖x‖ := by
    have h1 : HasDerivAt (fun r : ℝ => ((r : ℝ) : ℂ)) 1 ‖x‖ :=
      (hasDerivAt_id ‖x‖).ofReal_comp
    exact (h1.mul_const (x / (‖x‖ : ℂ))).congr_deriv (by simp)
  have hψ' : HasFDerivAt ψ (fderiv ℝ ψ x) (((‖x‖ : ℝ) : ℂ) * (x / (‖x‖ : ℂ))) := by
    rw [hpt]; exact hψ.hasFDerivAt
  exact (hψ'.comp_hasDerivAt ‖x‖ hray).deriv

/-- The polar form of `∇^⊥`: for real `ψ` differentiable at `x ≠ 0`,
`∇^⊥ψ(x)·e_r = -|x|⁻¹ ∂_θψ(x)` and `∇^⊥ψ(x)·e_θ = ∂_rψ(x)`. -/
theorem Prelim.inner_perpGrad_radial_angular {ψ : ℂ → ℝ} {x : ℂ} (hx : x ≠ 0)
    (hψ : DifferentiableAt ℝ ψ x) :
    inner ℝ (Prelim.perpGrad ψ x) (x / (‖x‖ : ℂ)) =
        -(‖x‖⁻¹ * deriv (fun θ : ℝ => ψ (rot θ x)) 0) ∧
      inner ℝ (Prelim.perpGrad ψ x) (Complex.I * x / (‖x‖ : ℂ)) =
        deriv (fun r : ℝ => ψ ((r : ℂ) * (x / (‖x‖ : ℂ)))) ‖x‖ := by
  rw [deriv_angular_eq hψ, deriv_radial_eq hx hψ, Prelim.fderiv_apply_eq_inner_grad,
    Prelim.fderiv_apply_eq_inner_grad]
  have hdiv : ∀ z : ℂ, z / (‖x‖ : ℂ) = ((‖x‖⁻¹ : ℝ) : ℂ) * z := by
    intro z; rw [Complex.ofReal_inv, div_eq_inv_mul]
  simp only [Prelim.perpGrad, Complex.inner, hdiv, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im]
  constructor <;> ring

/-- The sign conventions of `02_prelim.tex:45-47` for `v = K ∗ g`, `g ∈ C_c^∞` real, and its
stream function `ψ = (2π)⁻¹ log|·| ∗ g`: `v·e_r = -r⁻¹ ∂_θψ` and `v·e_θ = ∂_rψ` at every
`x ≠ 0`. -/
theorem BS.inner_velocity_radial_angular_of_smooth {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) {x : ℂ} (hx : x ≠ 0) :
    inner ℝ (velocity g x) (x / (‖x‖ : ℂ)) =
        -(‖x‖⁻¹ * deriv (fun θ : ℝ => Multipole.logPotentialReal g (rot θ x)) 0) ∧
      inner ℝ (velocity g x) (Complex.I * x / (‖x‖ : ℂ)) =
        deriv (fun r : ℝ => Multipole.logPotentialReal g ((r : ℂ) * (x / (‖x‖ : ℂ)))) ‖x‖ := by
  rw [BS.velocity_eq_perpGrad_of_smooth hg hgc]
  have hψ : DifferentiableAt ℝ (Multipole.logPotentialReal g) x :=
    ((BS.contDiff_velocity_of_smooth hg hgc).2.differentiable (by simp)).differentiableAt
  exact Prelim.inner_perpGrad_radial_angular hx hψ

end NonUniqueEuler
