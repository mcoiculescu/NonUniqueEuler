import NonUniqueEuler.Defs.Sec4.Setting
import NonUniqueEuler.Defs.Sec4.Extra1Sector
import NonUniqueEuler.I.Sec4.Sector.CouplingProj
import NonUniqueEuler.H.Sec4.Sector.CouplingOfProfile.Finite
import NonUniqueEuler.H.Sec4.Sector.CouplingOfProfile.RealAxis

/-!
# Proof: the coupling term on a sector function, `-(K_BS * (g e^{iℓθ}))·∇ω̄ = (k_ℓ𝒢_ℓ g) e^{iℓθ}`

Proof of `I/Sec4/Sector/CouplingOfProfile.lean` (`04_ring.tex:257-263`, proof of
`lem:sector`(2)).

**Deviation (proof only).** As planned in the interface docstring, the formula is computed
directly in polar coordinates with the explicit circle integral of
`I/Infra/Multipole/CircleKernel.lean`, instead of the manuscript's identification of the stream
function via `lem:sector`(1) plus density.

Steps (helpers in `H/Sec4/Sector/CouplingOfProfile/`):
1. `ae_convAbs_lt_top` (`Finite.lean`): `(|K_BS| ⋆ |W|)(r) < ∞` for almost every `r ∈ (0, R)`.
2. `couplingFn_ofReal` (`RealAxis.lean`): at such a radius `r > 0`, `(𝒦W)(r) = k_ℓ(r)𝒢_ℓ g(r)`;
   where `ω̄'(r) = 0` both sides vanish.
3. Rotation: `(𝒦W)(x) = e^{iℓ arg x}(𝒦W)(|x|)` (`couplingFn_rot` of
   `I/Sec4/Sector/CouplingProj.lean` and `W ∘ O_θ = e^{iℓθ} W`).
4. Almost every radius gives almost every point (`ae_of_ae_norm`).
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler

namespace SectorSetting

open CouplingOfProfileH in
/-- `𝒦` commutes with multiplication by a constant. -/
private theorem couplingFn_const_mul' (S : SectorSetting) (c : ℂ) (w : ℂ → ℂ) (x : ℂ) :
    S.couplingFn (fun y => c * w y) x = c * S.couplingFn w x := by
  simp only [couplingFn]
  have e : (fun y => ((fderiv ℝ S.om x (biotSavartKernel (x - y)) : ℝ) : ℂ) * (c * w y)) =
      fun y => c * (((fderiv ℝ S.om x (biotSavartKernel (x - y)) : ℝ) : ℂ) * w y) := by
    funext y
    ring
  rw [e, integral_const_mul, mul_neg]

open CouplingOfProfileH in
/-- The coupling term of the sector function `g(r)e^{iℓθ}` is `(k_ℓ𝒢_ℓ g)(r)e^{iℓθ}`, for every
profile `g ∈ Y^0_ℓ` and every `ℓ` (`04_ring.tex:257-263`). -/
theorem couplingFn_ofProfile (S : SectorSetting) (hS : S.Valid) {g : ℝ → ℂ}
    (hg : S.IsProfileL2 g) (ℓ : ℤ) :
    S.couplingFn (Ang.ofProfile ℓ g) =ᵐ[volume] Ang.ofProfile ℓ (S.KsecFn ℓ g) := by
  have hrad : ∀ᵐ (r : ℝ) ∂(volume.restrict (Ioi (0 : ℝ))),
      0 < r → S.couplingFn (Ang.ofProfile ℓ g) (r : ℂ) = S.KsecFn ℓ g r := by
    filter_upwards [ae_convAbs_lt_top hS hg ℓ (S.r₂ + 1)] with r hr hr0
    by_cases hd : S.dom r = 0
    · have h1 : S.couplingFn (Ang.ofProfile ℓ g) (r : ℂ) = 0 := by
        simp [couplingFn, fderiv_om_ofReal hS hr0, hd]
      have h2 : S.KsecFn ℓ g r = 0 := by
        simp [KsecFn, kcoef, hd]
      rw [h1, h2]
    · have hrR : r < S.r₂ + 1 := by
        by_contra h
        exact hd (hS.dom_eq_zero r hr0 fun h' => by linarith [h'.2])
      exact couplingFn_ofReal hS hg ℓ hr0 (hr hrR)
  have h0 : ∀ᵐ x : ℂ ∂volume, x ≠ 0 := by
    rw [ae_iff]
    simp
  filter_upwards [ae_of_ae_norm hrad, h0] with x hx hx0
  have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
  calc S.couplingFn (Ang.ofProfile ℓ g) x
      = S.couplingFn (Ang.ofProfile ℓ g) (rot (Complex.arg x) (‖x‖ : ℂ)) := by
        rw [rot_arg_norm]
    _ = S.couplingFn (fun y => Ang.ofProfile ℓ g (rot (Complex.arg x) y)) (‖x‖ : ℂ) :=
        couplingFn_rot S hS _ _ _
    _ = Complex.exp ((ℓ : ℂ) * (Complex.arg x : ℝ) * Complex.I) *
          S.couplingFn (Ang.ofProfile ℓ g) (‖x‖ : ℂ) := by
        simp only [ofProfile_rot]
        exact couplingFn_const_mul' S _ _ _
    _ = Ang.ofProfile ℓ (S.KsecFn ℓ g) x := by
        rw [hx hpos, Ang.ofProfile, angPhase_eq_exp_arg ℓ hx0]
        ring

end SectorSetting

end NonUniqueEuler
