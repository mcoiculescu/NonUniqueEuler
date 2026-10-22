import NonUniqueEuler.H.Sec4.PropSemigroup.Sectors
import NonUniqueEuler.H.Sec4.PropSemigroup.EllSector

/-!
# Helpers for `P/Sec4/PropSemigroup`: `ℓ_*(G)(e^{tL}w) = e^{λ_* t} ℓ_*(G)(w)`

`04_ring.tex:1497-1500`: `ℓ_*(G)(e^{tL}w) = n_* ℓ_*(exp(tL_3)w_3) = e^{λ_*t} ℓ_*(G)(w)`.
Here the sector identity `ℓ_*(exp(tL_3)g) = e^{λ_*t}ℓ_*(g)` is read off the projection identity
`P(e^{tL_3}g) = e^{tL_3}Pg = e^{λ_*t}Pg` for the rank-one Riesz projection `P = ℓ_*(·)g_*`
(`R_sector`: `R` commutes with `e^{tL}`; `Dunford.exp_mul_proj`; `ℓ_*(g_*) = 1` from `lam_SU`),
and `ℓ_*(G)(w) = n_* ℓ_*((P_3w)_3)` is `ell_eq_ellStarY_secProj`.
-/

noncomputable section

open MeasureTheory Set ComplexConjugate

namespace NonUniqueEuler

namespace PropSemigroupH

open Sect RingData

section Generic

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- For a rank-one projection `P = f(·)g` with `f g = 1` and `A P = z P`: if
`P y = exp(tA)(P x)` then `f y = e^{zt} f x` (multiplied by any constant `c`). -/
theorem rankOne_exp_apply (A : X →L[ℂ] X) (f : X →L[ℂ] ℂ) (g : X) (hfg : f g = 1) (z : ℂ)
    (hAP : A * Dunford.rankOneProj f g = z • Dunford.rankOneProj f g) (t : ℝ) (x y : X)
    (hxy : Dunford.rankOneProj f g y =
      NormedSpace.exp ((t : ℂ) • A) (Dunford.rankOneProj f g x)) (c : ℂ) :
    c * f y = Complex.exp (z * t) * (c * f x) := by
  have h1 : NormedSpace.exp ((t : ℂ) • A) (Dunford.rankOneProj f g x) =
      (NormedSpace.exp ((t : ℂ) • A) * Dunford.rankOneProj f g) x := rfl
  rw [h1, Dunford.exp_mul_proj hAP] at hxy
  have h2 := congrArg f hxy
  simp only [Dunford.rankOneProj_apply, map_smul, hfg, smul_eq_mul, mul_one,
    FunLike.coe_smul, Pi.smul_apply] at h2
  rw [h2]
  ring_nf

end Generic

/-- **`ℓ_*(G)(e^{tL(G)}w) = e^{λ_*(G)t} ℓ_*(G)(w)`** for every `w ∈ Y^s(N)`
(`04_ring.tex:1497-1500`). -/
theorem ell_S (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) {G : ℝ}
    (hG : G ∈ Icc (0 : ℝ) Gbar) (s : ℕ) {t : ℝ} (ht : 0 ≤ t) (w : Y s annN) :
    Eig.ell χ s G (Lin.S χ s G t w) = Complex.exp (Eig.lam χ G * (t : ℂ)) * Eig.ell χ s G w := by
  obtain ⟨-, -, hfg, hsp3, -⟩ := Eig.lam_SU χ hχ hN hG s
  obtain ⟨hR3, -, -, -, hcomm⟩ := Eig.R_sector χ hχ hN hG s
  have hc : Lin.S χ s G t (Eig.R χ s G w) = Eig.R χ s G (Lin.S χ s G t w) :=
    congrArg (fun T : Y s annN →L[ℂ] Y s annN => T w) (hcomm t ht)
  have hxy : (ringPhiSetting χ).rieszSec s 3 (Eig.lam χ G) G
      (secProj s annN 3 (Lin.S χ s G t w)) =
      NormedSpace.exp ((t : ℂ) • Lin.Lsec χ s 3 G)
        ((ringPhiSetting χ).rieszSec s 3 (Eig.lam χ G) G (secProj s annN 3 w)) :=
    (hR3 (Lin.S χ s G t w)).symm.trans
      ((congrArg (secProj s annN 3) hc.symm).trans
        ((secProj_S hχ s G ht 3 (Eig.R χ s G w)).trans
          (congrArg (fun v => NormedSpace.exp ((t : ℂ) • Lin.Lsec χ s 3 G) v) (hR3 w))))
  rw [ell_eq_ellStarY_secProj χ hχ hN hG s, ell_eq_ellStarY_secProj χ hχ hN hG s]
  exact rankOne_exp_apply (Lin.Lsec χ s 3 G) _ _ hfg (Eig.lam χ G) hsp3.mul_proj t _ _ hxy _

end PropSemigroupH

end NonUniqueEuler
