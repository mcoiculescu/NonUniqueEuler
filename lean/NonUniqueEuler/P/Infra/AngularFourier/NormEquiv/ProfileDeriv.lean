import NonUniqueEuler.H.Infra.AngularFourier.NormEquiv.ProfileDeriv.Assembly

/-!
# Proof: first weak derivatives of a sector function `h(r) e^{iℓθ}`

Proof of `I/Infra/AngularFourier/NormEquiv/ProfileDeriv.lean` (manuscript `lem:norm-equiv`,
`04_ring.tex:843-864`, the formulas `∂₁ = cos θ ∂_r - (sin θ / r) ∂_θ`,
`∂₂ = sin θ ∂_r + (cos θ / r) ∂_θ`, `∂_θ = iℓ` on sector `ℓ`).

For a test function `φ` on `ℂ`, both sides of the weak-derivative identity are written in polar
coordinates (`NEProfileDerivAux.lhs_eq`, `NEProfileDerivAux.rhs_eq`). Per radius, the polar form
of `∂₁`, `∂₂` and an integration by parts in `θ` give
`r ∫ e^{iℓθ} ∂₁φ(re^{iθ}) dθ = (rC)' + iℓ S` and `r ∫ e^{iℓθ} ∂₂φ(re^{iθ}) dθ = (rS)' - iℓ C`
with `C(r) = ∫ e^{iℓθ} cos θ φ(re^{iθ}) dθ`, `S(r) = ∫ e^{iℓθ} sin θ φ(re^{iθ}) dθ`
(`NEProfileDerivAux.key_one`, `key_two`); `C`, `S` are smooth (`paramInt_contDiff`). The weak
derivative of `h` on `(0, ∞)` is tested against `χ(r) r C(r)` and `χ(r) r S(r)`, `χ` a smooth
cutoff equal to `1` near `[ρ₋, ρ₊]` (`NEProfileDerivAux.weak_identity`; it uses that `h' = 0`
a.e. off `[ρ₋, ρ₊]`, `weakDeriv_ae_zero`). The case `ρ₊ < ρ₋` reduces to `ρ₊ := max ρ₋ ρ₊`.
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace NonUniqueEuler.Ang

/-- `∂₁ (h(r)e^{iℓθ}) = A(r)e^{i(ℓ-1)θ} + B(r)e^{i(ℓ+1)θ}` and
`∂₂ (h(r)e^{iℓθ}) = i (A(r)e^{i(ℓ-1)θ} - B(r)e^{i(ℓ+1)θ})` weakly on the plane, with
`A = (h' + ℓh/r)/2`, `B = (h' - ℓh/r)/2`, for a profile `h ∈ H^1((0,∞))` vanishing outside
`[ρ₋, ρ₊]`, `ρ₋ > 0`. -/
theorem hasWeakDerivOn_ofProfile {ρm ρp : ℝ} (hρm : 0 < ρm) {h : ℝ → ℂ}
    (hh : Sob.MemH1On 1 (Ioi 0) h)
    (hhI : ∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc ρm ρp → h r = 0) (ℓ : ℤ) :
    Sob.HasWeakDerivOn univ (Sob.pdList (1, 0)) (ofProfile ℓ h)
        (fun x => ofProfile (ℓ - 1)
            (fun r => (2 : ℂ)⁻¹ * (Sob.weakDeriv1On (Ioi 0) 1 h r + (ℓ : ℂ) * h r / (r : ℂ))) x +
          ofProfile (ℓ + 1)
            (fun r => (2 : ℂ)⁻¹ * (Sob.weakDeriv1On (Ioi 0) 1 h r - (ℓ : ℂ) * h r / (r : ℂ))) x) ∧
      Sob.HasWeakDerivOn univ (Sob.pdList (0, 1)) (ofProfile ℓ h)
        (fun x => Complex.I * (ofProfile (ℓ - 1)
            (fun r => (2 : ℂ)⁻¹ * (Sob.weakDeriv1On (Ioi 0) 1 h r + (ℓ : ℂ) * h r / (r : ℂ))) x -
          ofProfile (ℓ + 1)
            (fun r => (2 : ℂ)⁻¹ * (Sob.weakDeriv1On (Ioi 0) 1 h r - (ℓ : ℂ) * h r / (r : ℂ))) x)) := by
  set ρp' := max ρm ρp with hρp'
  have hρ : ρm ≤ ρp' := le_max_left _ _
  have hhI' : ∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc ρm ρp' → h r = 0 := by
    filter_upwards [hhI] with r hr hr'
    exact hr (fun h1 => hr' ⟨h1.1, h1.2.trans (le_max_right _ _)⟩)
  constructor
  · intro φ hφ
    have e1 : Sob.iterDirDeriv (Sob.pdList (1, 0)) φ = fun x => fderiv ℝ φ x 1 := by
      funext x
      simp [Sob.pdList, Sob.dirDeriv]
    rw [e1, Sob.pdList_length, show ((-1 : ℂ)) ^ (1 + 0) = -1 by norm_num, neg_one_mul]
    exact NEProfileDerivAux.dir_one hρm hρ hh hhI' ℓ hφ
  · intro φ hφ
    have e1 : Sob.iterDirDeriv (Sob.pdList (0, 1)) φ = fun x => fderiv ℝ φ x Complex.I := by
      funext x
      simp [Sob.pdList, Sob.dirDeriv]
    rw [e1, Sob.pdList_length, show ((-1 : ℂ)) ^ (0 + 1) = -1 by norm_num, neg_one_mul]
    exact NEProfileDerivAux.dir_two hρm hρ hh hhI' ℓ hφ

end NonUniqueEuler.Ang
