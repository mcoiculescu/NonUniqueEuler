import NonUniqueEuler.Defs.Sec4.Evans
import NonUniqueEuler.Defs.Sec4.RingSetting
import NonUniqueEuler.I.Sec4.Dilation
import NonUniqueEuler.I.Sec4.EvansBasic
import NonUniqueEuler.I.Sec4.RingFacts

/-!
# Proof: `eq:evans-units` (the Evans function in ring units)

Proof of `I/Sec4/EvansUnits.lean` (`04_ring.tex:1167-1170`, and `:1426-1427` for the
derivative). `ringPhiSetting χ = (ringRefSetting χ).dilate R_c` (`ringPhiSetting_eq_dilate`),
`lem:dilation`(2) (`SectorSetting.dilate_evans`, with `R = R_c > 0` and the validity
`ringRefSetting_valid`) and `lem:evans-basic`, last assertion (`ringRefSetting_evans`). The
derivative statement follows because the two functions of `λ` agree on the open half-plane
`{Re λ > 0}`, a neighbourhood of `λ` (`Filter.EventuallyEq.deriv_eq`).
-/

noncomputable section

namespace NonUniqueEuler

open RingData

/-- `eq:evans-units`: `E^Φ_ℓ(λ;G) = E_ℓ(λ;R_c²G)`. -/
theorem evans_units {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (z : ℂ)
    (hz : 0 < z.re) (G : ℝ) : (ringPhiSetting χ).evans ℓ z G = evans χ ℓ z (Rc ^ 2 * G) := by
  have hRc : 0 < Rc := Real.exp_pos ξR
  rw [ringPhiSetting_eq_dilate,
    SectorSetting.dilate_evans (ringRefSetting χ) (ringRefSetting_valid hχ) hRc ℓ hℓ z hz G]
  exact ringRefSetting_evans hχ ℓ hℓ z hz (Rc ^ 2 * G)

/-- The `λ`-derivatives agree as well: `∂_λE^Φ_ℓ(λ;G) = ∂_λE_ℓ(λ;R_c²G)` (`04_ring.tex:1426-1427`). -/
theorem evans_units_deriv {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (z : ℂ)
    (hz : 0 < z.re) (G : ℝ) :
    deriv (fun w => (ringPhiSetting χ).evans ℓ w G) z =
      deriv (fun w => evans χ ℓ w (Rc ^ 2 * G)) z := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : (fun w => (ringPhiSetting χ).evans ℓ w G) =ᶠ[nhds z]
      (fun w => evans χ ℓ w (Rc ^ 2 * G)) :=
    Filter.eventually_of_mem (hopen.mem_nhds hz) fun w hw => evans_units hχ ℓ hℓ w hw G
  exact hev.deriv_eq

end NonUniqueEuler
