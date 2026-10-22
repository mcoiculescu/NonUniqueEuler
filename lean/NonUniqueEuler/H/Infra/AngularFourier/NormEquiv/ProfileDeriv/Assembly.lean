import NonUniqueEuler.H.Infra.AngularFourier.NormEquiv.ProfileDeriv.Sides

/-!
# Helpers for `P/Infra/AngularFourier/NormEquiv/ProfileDeriv`: the two weak derivatives

`dir_one`, `dir_two`: the weak-derivative identities against a test function `φ`, for
`0 < ρ₋ ≤ ρ₊`. With `C = angCoef (cC ℓ) φ`, `S = angCoef (cS ℓ) φ`,
`Q∓ = angCoef (eA (ℓ ∓ 1)) φ` (so `Q₋ + Q₊ = 2C`, `Q₋ - Q₊ = -2iS`), and `J u g = ∫₀^∞ u g`:
* LHS of `∂₁`: `J h (C + rC') + iℓ J h S` (`lhs_eq`, `key_one`), and `J h (C + rC') = -J h' (rC)`
  (`weak_identity`);
* RHS of `∂₁`: `½(J h' (rQ₋) + ℓ J h Q₋) + ½(J h' (rQ₊) - ℓ J h Q₊)` (`rhs_eq`);
and the same for `∂₂` with `key_two`. The rest is linear algebra.
-/

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff

namespace NonUniqueEuler.Ang.NEProfileDerivAux

variable {ρm ρp : ℝ} {h : ℝ → ℂ} {φ : ℂ → ℂ}

theorem rA_eq {h' : ℝ → ℂ} (ℓ : ℤ) (r : ℝ) (hr : r ∈ Ioi (0 : ℝ)) :
    (r : ℂ) * ((2 : ℂ)⁻¹ * (h' r + (ℓ : ℂ) * h r / (r : ℂ))) =
      (2 : ℂ)⁻¹ * ((r : ℂ) * h' r + (ℓ : ℂ) * h r) := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
  field_simp

theorem rB_eq {h' : ℝ → ℂ} (ℓ : ℤ) (r : ℝ) (hr : r ∈ Ioi (0 : ℝ)) :
    (r : ℂ) * ((2 : ℂ)⁻¹ * (h' r - (ℓ : ℂ) * h r / (r : ℂ))) =
      (2 : ℂ)⁻¹ * ((r : ℂ) * h' r + (-(ℓ : ℂ)) * h r) := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
  field_simp
  ring

/-- `J h' (r X)` and `J h X` for `X = a Q₋ + b Q₊`. -/
theorem J_lin (hρm : 0 < ρm) (hh : Sob.MemH1On 1 (Ioi 0) h)
    (hhI : ∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc ρm ρp → h r = 0)
    {X Qm Qp : ℝ → ℂ} (hQm : Continuous Qm) (hQp : Continuous Qp) (a b : ℂ)
    (hX : ∀ r, X r = a * Qm r + b * Qp r) :
    (∫ r in Ioi (0 : ℝ), Sob.weakDeriv1On (Ioi 0) 1 h r * ((r : ℂ) * X r)) =
        a * (∫ r in Ioi (0 : ℝ), Sob.weakDeriv1On (Ioi 0) 1 h r * ((r : ℂ) * Qm r)) +
          b * ∫ r in Ioi (0 : ℝ), Sob.weakDeriv1On (Ioi 0) 1 h r * ((r : ℂ) * Qp r) ∧
      (∫ r in Ioi (0 : ℝ), h r * X r) =
        a * (∫ r in Ioi (0 : ℝ), h r * Qm r) + b * ∫ r in Ioi (0 : ℝ), h r * Qp r := by
  have i1 := good_deriv hρm hh hhI (g := fun r : ℝ => (r : ℂ) * Qm r)
    (Complex.continuous_ofReal.mul hQm)
  have i2 := good_deriv hρm hh hhI (g := fun r : ℝ => (r : ℂ) * Qp r)
    (Complex.continuous_ofReal.mul hQp)
  have i3 := good_profile hρm hh hhI hQm
  have i4 := good_profile hρm hh hhI hQp
  constructor
  · rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (Integrable.const_mul i1 a) (Integrable.const_mul i2 b)]
    congr 1; funext r; rw [hX r]; ring
  · rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (Integrable.const_mul i3 a) (Integrable.const_mul i4 b)]
    congr 1; funext r; rw [hX r]; ring

/-- The LHS in radial form, for `X = C` (direction `1`) or `X = S` (direction `I`). -/
theorem lhs_lin (hρm : 0 < ρm) (hh : Sob.MemH1On 1 (Ioi 0) h)
    (hhI : ∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc ρm ρp → h r = 0) (ℓ : ℤ)
    (hφ : Sob.IsTestFn univ φ) (v : ℂ) {X Y : ℝ → ℂ} (hXs : ContDiff ℝ ∞ X)
    (hYs : ContDiff ℝ ∞ Y) (κ : ℂ)
    (hkey : ∀ r : ℝ, (r : ℂ) * (∫ θ in (0 : ℝ)..2 * π, eA ℓ θ * fderiv ℝ φ (circleMap 0 r θ) v) =
      (X r + r * deriv X r) + κ * Y r) :
    ∫ x, ofProfile ℓ h x * fderiv ℝ φ x v =
      (∫ r in Ioi (0 : ℝ), h r * (X r + r * deriv X r)) + κ * ∫ r in Ioi (0 : ℝ), h r * Y r := by
  have hXc' : Continuous (deriv X) := hXs.continuous_deriv (by simp)
  have hi1 := good_profile hρm hh hhI (g := fun r : ℝ => X r + r * deriv X r)
    (hXs.continuous.add (Complex.continuous_ofReal.mul hXc'))
  have hi2 := good_profile hρm hh hhI hYs.continuous
  rw [lhs_eq hρm hh hhI ℓ hφ v, ← integral_const_mul,
    ← integral_add hi1 (Integrable.const_mul hi2 κ)]
  congr 1
  funext r
  rw [hkey r]
  ring

theorem dir_one (hρm : 0 < ρm) (hρ : ρm ≤ ρp) (hh : Sob.MemH1On 1 (Ioi 0) h)
    (hhI : ∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc ρm ρp → h r = 0) (ℓ : ℤ)
    (hφ : Sob.IsTestFn univ φ) :
    ∫ x, ofProfile ℓ h x * fderiv ℝ φ x 1 =
      -∫ x, (ofProfile (ℓ - 1)
            (fun r => (2 : ℂ)⁻¹ * (Sob.weakDeriv1On (Ioi 0) 1 h r + (ℓ : ℂ) * h r / (r : ℂ))) x +
          ofProfile (ℓ + 1)
            (fun r => (2 : ℂ)⁻¹ * (Sob.weakDeriv1On (Ioi 0) 1 h r - (ℓ : ℂ) * h r / (r : ℂ))) x) *
          φ x := by
  have hφs := hφ.smooth
  have hCs : ContDiff ℝ ∞ (angCoef (cC ℓ) φ) := contDiff_angCoef (contDiff_cC ℓ) hφs
  have hSs : ContDiff ℝ ∞ (angCoef (cS ℓ) φ) := contDiff_angCoef (contDiff_cS ℓ) hφs
  have hQm : Continuous (angCoef (eA (ℓ - 1)) φ) :=
    (contDiff_angCoef (contDiff_eA _) hφs).continuous
  have hQp : Continuous (angCoef (eA (ℓ + 1)) φ) :=
    (contDiff_angCoef (contDiff_eA _) hφs).continuous
  -- the left side
  have hL := lhs_lin hρm hh hhI ℓ hφ 1 hCs hSs ((ℓ : ℂ) * Complex.I) (fun r => by
    rw [key_one hφs ℓ r, ← (hasDerivAt_angCoef (contDiff_cC ℓ) hφs r).deriv])
  have hW := weak_identity hρm hρ hh hhI hCs
    (fun r => ((hCs.differentiable (by simp)) r).hasDerivAt)
  -- the right side
  have hA := rhs_eq hρm hh hhI hφ (A := fun r =>
    (2 : ℂ)⁻¹ * (Sob.weakDeriv1On (Ioi 0) 1 h r + (ℓ : ℂ) * h r / (r : ℂ))) (ℓ : ℂ)
    (fun r hr => rA_eq ℓ r hr) (ℓ - 1)
  have hB := rhs_eq hρm hh hhI hφ (A := fun r =>
    (2 : ℂ)⁻¹ * (Sob.weakDeriv1On (Ioi 0) 1 h r - (ℓ : ℂ) * h r / (r : ℂ))) (-(ℓ : ℂ))
    (fun r hr => rB_eq ℓ r hr) (ℓ + 1)
  have hR : ∫ x, (ofProfile (ℓ - 1)
            (fun r => (2 : ℂ)⁻¹ * (Sob.weakDeriv1On (Ioi 0) 1 h r + (ℓ : ℂ) * h r / (r : ℂ))) x +
          ofProfile (ℓ + 1)
            (fun r => (2 : ℂ)⁻¹ * (Sob.weakDeriv1On (Ioi 0) 1 h r - (ℓ : ℂ) * h r / (r : ℂ))) x) *
          φ x =
      (∫ x, ofProfile (ℓ - 1)
            (fun r => (2 : ℂ)⁻¹ * (Sob.weakDeriv1On (Ioi 0) 1 h r + (ℓ : ℂ) * h r / (r : ℂ))) x *
          φ x) +
        ∫ x, ofProfile (ℓ + 1)
            (fun r => (2 : ℂ)⁻¹ * (Sob.weakDeriv1On (Ioi 0) 1 h r - (ℓ : ℂ) * h r / (r : ℂ))) x *
          φ x := by
    rw [← integral_add hA.1 hB.1]
    congr 1; funext x; ring
  -- `C = ½(Q₋ + Q₊)`, `S = (i/2)(Q₋ - Q₊)`
  have hCrel := J_lin hρm hh hhI (X := angCoef (cC ℓ) φ) hQm hQp (2 : ℂ)⁻¹ (2 : ℂ)⁻¹ (fun r => by
    have := angCoef_add hφs ℓ r
    linear_combination (-(2 : ℂ)⁻¹) * this)
  have hSrel := J_lin hρm hh hhI (X := angCoef (cS ℓ) φ) hQm hQp (Complex.I / 2)
    (-(Complex.I / 2)) (fun r => by
    have := angCoef_sub hφs ℓ r
    linear_combination (-(Complex.I / 2)) * this +
      (angCoef (cS ℓ) φ r) * Complex.I_sq)
  rw [hL, hW, hR, hA.2, hB.2, hCrel.1, hSrel.2]
  linear_combination ((ℓ : ℂ) / 2 * ((∫ r in Ioi (0 : ℝ), h r * angCoef (eA (ℓ - 1)) φ r) -
    ∫ r in Ioi (0 : ℝ), h r * angCoef (eA (ℓ + 1)) φ r)) * Complex.I_sq

theorem dir_two (hρm : 0 < ρm) (hρ : ρm ≤ ρp) (hh : Sob.MemH1On 1 (Ioi 0) h)
    (hhI : ∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc ρm ρp → h r = 0) (ℓ : ℤ)
    (hφ : Sob.IsTestFn univ φ) :
    ∫ x, ofProfile ℓ h x * fderiv ℝ φ x Complex.I =
      -∫ x, (Complex.I * (ofProfile (ℓ - 1)
            (fun r => (2 : ℂ)⁻¹ * (Sob.weakDeriv1On (Ioi 0) 1 h r + (ℓ : ℂ) * h r / (r : ℂ))) x -
          ofProfile (ℓ + 1)
            (fun r => (2 : ℂ)⁻¹ * (Sob.weakDeriv1On (Ioi 0) 1 h r - (ℓ : ℂ) * h r / (r : ℂ))) x)) *
          φ x := by
  have hφs := hφ.smooth
  have hCs : ContDiff ℝ ∞ (angCoef (cC ℓ) φ) := contDiff_angCoef (contDiff_cC ℓ) hφs
  have hSs : ContDiff ℝ ∞ (angCoef (cS ℓ) φ) := contDiff_angCoef (contDiff_cS ℓ) hφs
  have hQm : Continuous (angCoef (eA (ℓ - 1)) φ) :=
    (contDiff_angCoef (contDiff_eA _) hφs).continuous
  have hQp : Continuous (angCoef (eA (ℓ + 1)) φ) :=
    (contDiff_angCoef (contDiff_eA _) hφs).continuous
  -- the left side
  have hL := lhs_lin hρm hh hhI ℓ hφ Complex.I hSs hCs (-((ℓ : ℂ) * Complex.I)) (fun r => by
    rw [key_two hφs ℓ r, ← (hasDerivAt_angCoef (contDiff_cS ℓ) hφs r).deriv]
    ring)
  have hW := weak_identity hρm hρ hh hhI hSs
    (fun r => ((hSs.differentiable (by simp)) r).hasDerivAt)
  -- the right side
  have hA := rhs_eq hρm hh hhI hφ (A := fun r =>
    (2 : ℂ)⁻¹ * (Sob.weakDeriv1On (Ioi 0) 1 h r + (ℓ : ℂ) * h r / (r : ℂ))) (ℓ : ℂ)
    (fun r hr => rA_eq ℓ r hr) (ℓ - 1)
  have hB := rhs_eq hρm hh hhI hφ (A := fun r =>
    (2 : ℂ)⁻¹ * (Sob.weakDeriv1On (Ioi 0) 1 h r - (ℓ : ℂ) * h r / (r : ℂ))) (-(ℓ : ℂ))
    (fun r hr => rB_eq ℓ r hr) (ℓ + 1)
  have hR : ∫ x, (Complex.I * (ofProfile (ℓ - 1)
            (fun r => (2 : ℂ)⁻¹ * (Sob.weakDeriv1On (Ioi 0) 1 h r + (ℓ : ℂ) * h r / (r : ℂ))) x -
          ofProfile (ℓ + 1)
            (fun r => (2 : ℂ)⁻¹ * (Sob.weakDeriv1On (Ioi 0) 1 h r - (ℓ : ℂ) * h r / (r : ℂ))) x)) *
          φ x =
      Complex.I * ((∫ x, ofProfile (ℓ - 1)
            (fun r => (2 : ℂ)⁻¹ * (Sob.weakDeriv1On (Ioi 0) 1 h r + (ℓ : ℂ) * h r / (r : ℂ))) x *
          φ x) -
        ∫ x, ofProfile (ℓ + 1)
            (fun r => (2 : ℂ)⁻¹ * (Sob.weakDeriv1On (Ioi 0) 1 h r - (ℓ : ℂ) * h r / (r : ℂ))) x *
          φ x) := by
    rw [← integral_sub hA.1 hB.1, ← integral_const_mul]
    congr 1; funext x; ring
  have hCrel := J_lin hρm hh hhI (X := angCoef (cC ℓ) φ) hQm hQp (2 : ℂ)⁻¹ (2 : ℂ)⁻¹ (fun r => by
    have := angCoef_add hφs ℓ r
    linear_combination (-(2 : ℂ)⁻¹) * this)
  have hSrel := J_lin hρm hh hhI (X := angCoef (cS ℓ) φ) hQm hQp (Complex.I / 2)
    (-(Complex.I / 2)) (fun r => by
    have := angCoef_sub hφs ℓ r
    linear_combination (-(Complex.I / 2)) * this +
      (angCoef (cS ℓ) φ r) * Complex.I_sq)
  rw [hL, hW, hR, hA.2, hB.2, hSrel.1, hCrel.2]
  ring

end NonUniqueEuler.Ang.NEProfileDerivAux
