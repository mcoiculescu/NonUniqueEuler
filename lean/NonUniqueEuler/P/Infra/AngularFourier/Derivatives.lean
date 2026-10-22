import NonUniqueEuler.Defs.Infra.AngularFourier
import NonUniqueEuler.I.Infra.AngularFourier.SectorL2
import NonUniqueEuler.H.Infra.AngularFourier.Derivatives.Proj
import NonUniqueEuler.H.Infra.AngularFourier.Derivatives.OfProfile
import NonUniqueEuler.H.Infra.AngularFourier.Derivatives.Profile

/-!
# Proof: sector projections and derivatives (library I-ANG)

Proof of `NonUniqueEuler/I/Infra/AngularFourier/Derivatives.lean` (same declarations, statements
copied verbatim). Manuscript: `04_ring.tex:174-185` (`P_ℓ`), `04_ring.tex:424-425` (profiles in
`H^s((0,∞))`), `04_ring.tex:851-853` (`∂_θ`, `∂_r`).

Structure (helpers in `H/Infra/AngularFourier/Derivatives/*`, steps in
`I/Infra/AngularFourier/Derivatives/*`):
* `Sob.MemH.sectorProj`: `P_ℓ g` is the function of the `Hk`-valued Bochner integral
  `(2π)⁻¹ ∫₀^{2π} e^{-iℓφ} (g ∘ O_φ) dφ` (steps `RotPath`, `Average`; helper `Proj`).
* `sectorProj_eq_zero_outside`: replace `g` by `1_K g` (a.e. equal, `sectorProj_congr_ae`); for
  `x ∉ K` every `O_φ x ∉ K`.
* `sectorProj_thetaDeriv`: duality with test functions (helper `Theta`; step `SmoothSector`).
  Restructured argument: instead of integrating by parts in `φ` and extending by
  density, test against `ψ`, move `P_ℓ` to `ψ` by self-adjointness (with the weight `1 + |x|`,
  since `∂_θ g` is only locally `L²`), and use the classical identity `∂_θ (P_ℓ ψ) = iℓ P_ℓ ψ`.
* `thetaDeriv_ofProfile`: from `sectorProj_thetaDeriv`, `P_m (h(r)e^{iℓθ}) = δ_{mℓ} h(r)e^{iℓθ}`
  and uniqueness of the angular expansion (helper `OfProfile`).
* `memH1On_angularSector`: induction on `k` with `(g_ℓ)' = (∂_r g)_ℓ` (steps `ProfileDeriv`,
  `ProfileL2`; helper `Profile`).
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace NonUniqueEuler.Ang

/-- `P_ℓ` preserves `H^k`, with `‖P_ℓ g‖_{H^k} ≤ 2^k ‖g‖_{H^k}`. -/
theorem _root_.NonUniqueEuler.Sob.MemH.sectorProj {k : ℕ} {g : ℂ → ℂ} (hg : Sob.MemH k g)
    (ℓ : ℤ) : Sob.MemH k (sectorProj ℓ g) ∧ Sob.normH k (sectorProj ℓ g) ≤ 2 ^ k * Sob.normH k g := by
  exact DerivAux.memH_sectorProj_aux hg ℓ

/-- `P_ℓ` preserves vanishing outside a rotation-invariant set. -/
theorem sectorProj_eq_zero_outside {K : Set ℂ} (hK : ∀ θ x, rot θ x ∈ K ↔ x ∈ K)
    {g : ℂ → ℂ} (hgK : ∀ᵐ x, x ∉ K → g x = 0) (ℓ : ℤ) :
    ∀ᵐ x, x ∉ K → sectorProj ℓ g x = 0 := by
  classical
  have hgg : g =ᵐ[volume] fun x => if x ∈ K then g x else 0 := by
    filter_upwards [hgK] with x hx
    by_cases h : x ∈ K
    · simp [h]
    · simp [h, hx h]
  filter_upwards [sectorProj_congr_ae ℓ hgg] with x hx hxK
  rw [hx]
  have h0 : ∀ φ : ℝ, (fun x => if x ∈ K then g x else 0) (rot φ x) = 0 := by
    intro φ
    have : rot φ x ∉ K := fun h => hxK ((hK φ x).1 h)
    simp [this]
  simp [sectorProj, h0]

/-- `∂_θ` acts as `iℓ` on sector `ℓ`: `P_ℓ(∂_θ g) = iℓ P_ℓ g` for `g ∈ H^1`. -/
theorem sectorProj_thetaDeriv {g : ℂ → ℂ} (hg : Sob.MemH 1 g) (ℓ : ℤ) :
    sectorProj ℓ (thetaDeriv g) =ᵐ[volume] fun x => ((ℓ : ℂ) * Complex.I) * sectorProj ℓ g x := by
  exact DerivAux.sectorProj_thetaDeriv_aux hg ℓ

/-- `∂_θ (h(r) e^{iℓθ}) = iℓ h(r) e^{iℓθ}` for sector functions in `H^1`. -/
theorem thetaDeriv_ofProfile {ℓ : ℤ} {h : ℝ → ℂ} (hh : Sob.MemH 1 (ofProfile ℓ h)) :
    thetaDeriv (ofProfile ℓ h) =ᵐ[volume] fun x => ((ℓ : ℂ) * Complex.I) * ofProfile ℓ h x := by
  exact DerivAux.thetaDeriv_ofProfile_aux hh

/-- The radial profile of an `H^k` function supported in the annulus `{ρ₋ ≤ |x| ≤ ρ₊}` is in
`H^k((0, ∞))` and vanishes outside `[ρ₋, ρ₊]`. -/
theorem memH1On_angularSector {k : ℕ} {ρm ρp : ℝ} (hρm : 0 < ρm) {g : ℂ → ℂ} (hg : Sob.MemH k g)
    (hgK : ∀ᵐ x, ¬ (ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp) → g x = 0) (ℓ : ℤ) :
    Sob.MemH1On k (Ioi 0) (Polar.angularSector g ℓ) ∧
      ∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc ρm ρp → Polar.angularSector g ℓ r = 0 := by
  exact ⟨DerivAux.memH1On_angularSector_aux hρm ℓ k hg hgK,
    (memLp_angularSector_of_support hρm (Sob.memH_iff.1 hg).1 hgK ℓ).2⟩

end NonUniqueEuler.Ang
