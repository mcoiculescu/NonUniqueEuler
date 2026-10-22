import NonUniqueEuler.Defs.Sec4.Evans
import NonUniqueEuler.Defs.Sec4.Extra1Sector
import NonUniqueEuler.Defs.Sec2.Multipole
import NonUniqueEuler.I.Sec4.EvansSimple
import NonUniqueEuler.H.Sec4.Adjoint.ExpSeries
import NonUniqueEuler.H.Sec4.Adjoint.Eigen
import NonUniqueEuler.H.Sec4.Adjoint.StreamMain
import NonUniqueEuler.H.Sec4.Adjoint.Field

/-!
# Proof of `lem:adjoint` (adjoint eigenfunction, `ℓ_*`, multipole data `pout_*`, `pin_*`, `β`)

Proof of `I/Sec4/Adjoint.lean` (`04_ring.tex:575-651`). Same declarations, statements copied
verbatim. Helpers: `H/Sec4/Adjoint/*.lean`.
* (1) `AdjointAux.weak_eigen` (Fubini on the symmetric kernel of `𝒢_ℓ`, `𝒢_ℓg_* = ψ_*(log r)`),
  `AdjointAux.adjEig_not_ae_zero` (`ψ_*(ξ₁) = 1`, continuity);
* (2) the profile identities from (1); on `Y^s_ℓ` from `thm:evans-simple`(2)
  (`P L = λ_* P` for `P = ℓ_*(·)g_*`, `ℓ_*(g_*) = 1`) and the exponential series
  (`AdjointAux.apply_exp_smul_of_comp_eq`);
* (3) `AdjointAux.adjoint_stream_aux`;
* (4) pointwise algebra `b ψ_* M_* r = -(2ℓ)⁻¹ r^{1-ℓ} g_*`, and
  `AdjointAux.angularSector_forcing`;
* (5) from (3), (4), `thm:evans-simple`(1) (`ψ_*(ξ₂) ≠ 0`) and (2) (`J ≠ 0`).
-/

noncomputable section

open MeasureTheory Set ComplexConjugate

namespace NonUniqueEuler

namespace SectorSetting

open Sect

/-- `lem:adjoint`(1): `conj(ψ_*(log r)M_*(r))` is an eigenfunction of the adjoint `L_ℓ(G)^*` with
eigenvalue `conj λ_*` (weak form: `⟨L_ℓ(G)g, conj X⟩ = λ_* ⟨g, conj X⟩` for every `g ∈ Y^0_ℓ`,
`⟨f, h⟩ = ∫_0^∞ f h̄ r dr`), and it is not zero in `L²([ρ₋,ρ₊])`. -/
theorem adjoint_eigen (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (z : ℂ)
    (hz : 0 < z.re) (G : ℝ) (hE : S.evans ℓ z G = 0)
    (hE' : deriv (fun w => S.evans ℓ w G) z ≠ 0) :
    (∀ g : ℝ → ℂ, S.IsProfileL2 g →
        ∫ r in Ioi (0 : ℝ), S.LsecFn ℓ G g r * conj (S.adjEig ℓ z G r) * (r : ℂ) =
          z * ∫ r in Ioi (0 : ℝ), g r * conj (S.adjEig ℓ z G r) * (r : ℂ)) ∧
      ¬ (∀ᵐ r ∂(volume.restrict (Icc S.ρm S.ρp)), S.adjEig ℓ z G r = 0) := by
  refine ⟨fun g hg => ?_, AdjointAux.adjEig_not_ae_zero S hS ℓ hℓ z hz G⟩
  have hc : ∀ r, conj (S.adjEig ℓ z G r) = S.psi ℓ z G (Real.log r) * S.Mres ℓ z G r :=
    fun r => by simp [adjEig]
  simp_rw [hc]
  exact AdjointAux.weak_eigen S hS ℓ hℓ z hz G hE hg

/-- `lem:adjoint`(2): `ℓ_*(g_*) = 1`, `ℓ_*(L_ℓ(G)g) = λ_*ℓ_*(g)` for `g ∈ Y^0_ℓ` (on profiles),
and, as functionals on every `Y^s_ℓ`: `ℓ_*(g_*) = 1`, `ℓ_*(L_ℓ g) = λ_*ℓ_*(g)` and
`ℓ_*(e^{tL_ℓ}g) = e^{λ_*t}ℓ_*(g)` for `t ≥ 0`, `e^{tL_ℓ}` the exponential series of the bounded
operator `L_ℓ(G)`. -/
theorem adjoint_ellStar (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (z : ℂ)
    (hz : 0 < z.re) (G : ℝ) (hE : S.evans ℓ z G = 0)
    (hE' : deriv (fun w => S.evans ℓ w G) z ≠ 0) :
    S.ellStar ℓ z G (S.gStar ℓ z G) = 1 ∧
      (∀ g : ℝ → ℂ, S.IsProfileL2 g →
        S.ellStar ℓ z G (S.LsecFn ℓ G g) = z * S.ellStar ℓ z G g) ∧
      ∀ s : ℕ,
        S.ellStarY s ℓ z G (S.gStarY s ℓ z G) = 1 ∧
          (∀ g : Ysec s S.Nstar ℓ,
            S.ellStarY s ℓ z G (S.Lsec s ℓ G g) = z * S.ellStarY s ℓ z G g) ∧
          ∀ t : ℝ, 0 ≤ t → ∀ g : Ysec s S.Nstar ℓ,
            S.ellStarY s ℓ z G (NormedSpace.exp ((t : ℂ) • S.Lsec s ℓ G) g) =
              Complex.exp (z * t) * S.ellStarY s ℓ z G g := by
  obtain ⟨hJ, hR⟩ := evansSimple_riesz S hS ℓ hℓ z hz G hE hE'
  refine ⟨ellStar_gStar S ℓ z G hJ, fun g hg => ?_, fun s => ?_⟩
  · have h := (adjoint_eigen S hS ℓ hℓ z hz G hE hE').1 g hg
    have e1 : ∀ f : ℝ → ℂ,
        (fun r : ℝ => f r * S.psi ℓ z G (Real.log r) * S.Mres ℓ z G r * (r : ℂ)) =
          fun r : ℝ => f r * conj (S.adjEig ℓ z G r) * (r : ℂ) := by
      intro f
      funext r
      simp only [adjEig, Complex.conj_conj]
      ring
    simp only [ellStar]
    rw [e1, e1, h]
    ring
  · obtain ⟨-, hone, hproj, -⟩ := hR s
    have hcomp : ∀ g : Ysec s S.Nstar ℓ,
        S.ellStarY s ℓ z G (S.Lsec s ℓ G g) = z * S.ellStarY s ℓ z G g := by
      intro g
      have h1 : S.rieszSec s ℓ z G (S.Lsec s ℓ G g) = z • S.rieszSec s ℓ z G g := by
        have := congrArg (fun T : Ysec s S.Nstar ℓ →L[ℂ] Ysec s S.Nstar ℓ => T g) hproj.proj_mul
        simpa [mul_apply_eq_comp] using this
      rw [rieszSec_apply, rieszSec_apply] at h1
      have h2 := congrArg (S.ellStarY s ℓ z G) h1
      rw [map_smul, map_smul, map_smul, hone, smul_eq_mul, smul_eq_mul, smul_eq_mul] at h2
      simpa using h2
    exact ⟨hone, hcomp, fun t _ g =>
      AdjointAux.apply_exp_smul_of_comp_eq (S.Lsec s ℓ G) (S.ellStarY s ℓ z G) z hcomp (t : ℂ) g⟩

/-- `lem:adjoint`(3): outside `supp ω̄'` the stream function `(2π)⁻¹ log|·| * (g_*e^{iℓθ})` of
`g_*e^{iℓθ}` is `-(pout_*/(2ℓ)) r^{-ℓ} e^{iℓθ}` for `r ≥ r₂` and `-(pin_*/(2ℓ)) r^ℓ e^{iℓθ}` for
`r ≤ r₁`; `pin_* = -2ℓe^{-ℓξ₁}`, `pout_* = -2ℓe^{ℓξ₂}ψ_*(ξ₂)`; and `pout_*`, `pin_*` are the
multipole coefficients `pout_ℓ`, `pin_ℓ` of `g_*e^{iℓθ}` (`def:multipole`). -/
theorem adjoint_stream (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (z : ℂ)
    (hz : 0 < z.re) (G : ℝ) (hE : S.evans ℓ z G = 0)
    (hE' : deriv (fun w => S.evans ℓ w G) z ≠ 0) :
    (∀ x : ℂ, S.r₂ ≤ ‖x‖ →
        Multipole.logPotential (Ang.ofProfile ℓ (S.gStar ℓ z G)) x =
          Ang.ofProfile ℓ
            (fun r => -(S.poutStar ℓ z G / (2 * (ℓ : ℂ))) * (r : ℂ) ^ (-(ℓ : ℤ))) x) ∧
      (∀ x : ℂ, ‖x‖ ≤ S.r₁ →
        Multipole.logPotential (Ang.ofProfile ℓ (S.gStar ℓ z G)) x =
          Ang.ofProfile ℓ (fun r => -(S.pinStar ℓ z G / (2 * (ℓ : ℂ))) * (r : ℂ) ^ ℓ) x) ∧
      S.pinStar ℓ z G = -2 * (ℓ : ℂ) * ((Real.exp (-(ℓ * S.ξ₁)) : ℝ) : ℂ) ∧
      S.poutStar ℓ z G =
        -2 * (ℓ : ℂ) * ((Real.exp (ℓ * S.ξ₂) : ℝ) : ℂ) * S.psi ℓ z G S.ξ₂ ∧
      S.poutStar ℓ z G = BS.pout ℓ (Ang.ofProfile ℓ (S.gStar ℓ z G)) ∧
      S.pinStar ℓ z G = BS.pin ℓ (Ang.ofProfile ℓ (S.gStar ℓ z G)) :=
  AdjointAux.adjoint_stream_aux S hS ℓ hℓ z hz G hE

/-- `lem:adjoint`(4): with `b(r) = -(i/2)r^{-ℓ-1}ω̄'(r)`, `β = ℓ_*(b) = -pin_*/(2ℓJ)`; and for
every `m ∈ ℂ` the real field `h = ∇^⊥(-(m/(2ℓ))r^{-ℓ}e^{iℓθ} + c.c.)` satisfies
`ℓ_*((-h·∇ω̄)_ℓ) = β m`, `(·)_ℓ` the sector-`ℓ` profile. -/
theorem adjoint_beta (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (z : ℂ)
    (hz : 0 < z.re) (G : ℝ) (hE : S.evans ℓ z G = 0)
    (hE' : deriv (fun w => S.evans ℓ w G) z ≠ 0) :
    S.betaStar ℓ z G = -S.pinStar ℓ z G / (2 * (ℓ : ℂ) * S.J ℓ z G) ∧
      ∀ m : ℂ,
        S.ellStar ℓ z G
            (Polar.angularSector
              (fun x => -((fderiv ℝ S.om x (multipoleField ℓ m x) : ℝ) : ℂ)) ℓ) =
          S.betaStar ℓ z G * m := by
  have hℓC : (ℓ : ℂ) ≠ 0 := by exact_mod_cast (show ℓ ≠ 0 by omega)
  refine ⟨?_, fun m => ?_⟩
  · have hpt : ∀ r ∈ Ioi (0 : ℝ),
        S.bfun ℓ r * S.psi ℓ z G (Real.log r) * S.Mres ℓ z G r * (r : ℂ) =
          -((2 * (ℓ : ℂ))⁻¹) * ((r : ℂ) ^ ((1 : ℤ) - ℓ) * S.gStar ℓ z G r) := by
      intro r hr
      have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (mem_Ioi.1 hr))
      simp only [bfun, gStar, kcoef]
      rw [zpow_sub₀ hr0 (-(ℓ : ℤ)) 1, zpow_sub₀ hr0 1 (ℓ : ℤ), zpow_neg, zpow_one,
        zpow_natCast]
      push_cast
      field_simp
    simp only [betaStar, ellStar]
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, ← pinStar,
      div_eq_mul_inv, mul_inv, mul_inv]
    ring
  · have hpt : ∀ r ∈ Ioi (0 : ℝ),
        Polar.angularSector (fun x => -((fderiv ℝ S.om x (multipoleField ℓ m x) : ℝ) : ℂ)) ℓ r *
            S.psi ℓ z G (Real.log r) * S.Mres ℓ z G r * (r : ℂ) =
          m * (S.bfun ℓ r * S.psi ℓ z G (Real.log r) * S.Mres ℓ z G r * (r : ℂ)) := by
      intro r hr
      rw [AdjointAux.angularSector_forcing S hS ℓ hℓ m (mem_Ioi.1 hr)]
      ring
    simp only [betaStar, ellStar]
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
    ring

/-- `lem:adjoint`(5): `pout_* ≠ 0`, `pin_* ≠ 0` and `β ≠ 0`. -/
theorem adjoint_ne_zero (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (z : ℂ)
    (hz : 0 < z.re) (G : ℝ) (hE : S.evans ℓ z G = 0)
    (hE' : deriv (fun w => S.evans ℓ w G) z ≠ 0) :
    S.poutStar ℓ z G ≠ 0 ∧ S.pinStar ℓ z G ≠ 0 ∧ S.betaStar ℓ z G ≠ 0 := by
  have hℓC : (ℓ : ℂ) ≠ 0 := by exact_mod_cast (show ℓ ≠ 0 by omega)
  obtain ⟨-, -, hpin, hpout, -, -⟩ := adjoint_stream S hS ℓ hℓ z hz G hE hE'
  have hJ := (evansSimple_riesz S hS ℓ hℓ z hz G hE hE').1
  have hψ := (evansSimple_deriv S hS ℓ hℓ z hz G hE).1
  have hβ := (adjoint_beta S hS ℓ hℓ z hz G hE hE').1
  have h2 : (-2 : ℂ) ≠ 0 := by norm_num
  have hpin0 : S.pinStar ℓ z G ≠ 0 := by
    rw [hpin]
    exact mul_ne_zero (mul_ne_zero h2 hℓC) (Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne')
  refine ⟨?_, hpin0, ?_⟩
  · rw [hpout]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2 hℓC)
      (Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne')) hψ
  · rw [hβ]
    exact div_ne_zero (neg_ne_zero.2 hpin0) (mul_ne_zero (mul_ne_zero two_ne_zero hℓC) hJ)

end SectorSetting

end NonUniqueEuler
