import NonUniqueEuler.Defs.Sec4.Eigendata
import NonUniqueEuler.I.Sec4.SectorSetting
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.I.Infra.SectorSpace.RadialMul
import NonUniqueEuler.I.Infra.CkNorm.Basic

/-!
# Helpers for `P/Sec4/PropSemigroup`: `G ↦ L_ℓ(G)` is continuous

`L_ℓ(G) = -iℓΩ(·;G) + k_ℓ𝒢_ℓ` with `Ω(r;G) = Ω(r;0) + Gr⁻²` (`Omega_eq_add`), so
`L_ℓ(G) = L_ℓ(0)`-part `+ G • (multiplication by -iℓr⁻²)` is affine in `G` (`radialMul_add`;
`04_ring.tex:1466-1467`: "`L_ℓ(G) = L_ℓ(0) - iℓGr⁻²` is bounded and affine in `G`").
-/

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace NonUniqueEuler

namespace PropSemigroupH

open Sect RingData

/-- A function smooth on `(0, ∞)` is `C^k` on `[ρ₋, ρ₊]` for `0 < ρ₋`. -/
theorem memCk_Icc_of_contDiffOn {k : ℕ} {f : ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f (Ioi 0)) {ρm ρp : ℝ}
    (hρm : 0 < ρm) : MemCk k (Icc ρm ρp) f :=
  IsCkNear.memCk_of_isCompact
    ⟨Ioi 0, isOpen_Ioi, fun _ hr => lt_of_lt_of_le hρm hr.1, contDiffOn_infty.1 hf k⟩
    isCompact_Icc

/-- **`G ↦ L_ℓ(G)` is continuous** (affine) in the operator norm of `Y^s_ℓ(N)`. -/
theorem Lsec_continuous {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (s : ℕ) (ℓ : ℤ) :
    Continuous fun G => Lin.Lsec χ s ℓ G := by
  set S := ringPhiSetting χ with hSdef
  have hS : S.Valid := ringPhiSetting_valid hχ
  have hρm : 0 < S.ρm := hS.ρm_pos
  have hρ : S.ρm < S.ρp := hS.ρm_lt_ρp
  set a : ℝ → ℂ := fun r => -(Complex.I * (ℓ : ℂ) * ((S.Omega 0 r : ℝ) : ℂ)) with ha_def
  set b : ℝ → ℂ := fun r => -(Complex.I * (ℓ : ℂ) * ((((r ^ 2)⁻¹ : ℝ)) : ℂ)) with hb_def
  have ha : MemCk s (Icc S.ρm S.ρp) a := by
    refine memCk_Icc_of_contDiffOn ?_ hρm
    have h0 : ContDiffOn ℝ ∞ (S.Omega 0) (Ioi 0) := SectorSetting.contDiffOn_Omega S hS 0
    have h1 : ContDiffOn ℝ ∞ (fun r => ((S.Omega 0 r : ℝ) : ℂ)) (Ioi 0) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn h0
    exact (contDiffOn_const.mul h1).neg
  have hb : MemCk s (Icc S.ρm S.ρp) b := by
    refine memCk_Icc_of_contDiffOn ?_ hρm
    have h0 : ContDiffOn ℝ ∞ (fun r : ℝ => (r ^ 2)⁻¹) (Ioi 0) :=
      (contDiffOn_id.pow 2).inv fun r hr => pow_ne_zero 2 (ne_of_gt hr)
    have h1 : ContDiffOn ℝ ∞ (fun r : ℝ => (((r ^ 2)⁻¹ : ℝ) : ℂ)) (Ioi 0) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn h0
    exact (contDiffOn_const.mul h1).neg
  have hfun : ∀ G : ℝ, (fun r => -(Complex.I * (ℓ : ℂ) * ((S.Omega G r : ℝ) : ℂ))) =
      fun r => a r + (G : ℂ) * b r := by
    intro G
    funext r
    rw [S.Omega_eq_add G r]
    simp only [ha_def, hb_def]
    push_cast
    ring
  have hadd : ∀ G : ℝ, radialMul s S.Nstar ℓ (fun r => a r + (G : ℂ) * b r) =
      radialMul s S.Nstar ℓ a + (G : ℂ) • radialMul s S.Nstar ℓ b :=
    fun G => radialMul_add hρm hρ ℓ ha hb (G : ℂ)
  have hL : ∀ G : ℝ, Lin.Lsec χ s ℓ G =
      radialMul s S.Nstar ℓ a + (G : ℂ) • radialMul s S.Nstar ℓ b + S.Ksec s ℓ := by
    intro G
    rw [Lin.Lsec_def]
    change radialMul s S.Nstar ℓ
        (fun r => -(Complex.I * (ℓ : ℂ) * ((S.Omega G r : ℝ) : ℂ))) + S.Ksec s ℓ = _
    rw [hfun G, hadd G]
  rw [show (fun G => Lin.Lsec χ s ℓ G) = fun G : ℝ =>
      radialMul s S.Nstar ℓ a + (G : ℂ) • radialMul s S.Nstar ℓ b + S.Ksec s ℓ from funext hL]
  exact (continuous_const.add (Complex.continuous_ofReal.smul continuous_const)).add
    continuous_const

end PropSemigroupH

end NonUniqueEuler
