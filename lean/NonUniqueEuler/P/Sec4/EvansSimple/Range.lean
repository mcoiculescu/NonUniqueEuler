import NonUniqueEuler.Defs.Sec4.Evans
import NonUniqueEuler.H.Sec4.EvansSimple.Range.Basic
import NonUniqueEuler.H.Sec4.EvansSimple.Range.Bvp
import NonUniqueEuler.I.Sec4.Resolvent.Regularity

/-!
# Proof of `I/Sec4/EvansSimple/Range.lean`: solvability of `(L_ℓ(G) - λ_*) x = h` at a zero
`λ_*` of `E_ℓ` (step of `thm:evans-simple`(2), the Fredholm alternative)

Manuscript: the argument of `thm:evans-simple`(3) (`04_ring.tex:536-551`) with a general right
side, plus the regularity part of the proof of `lem:resolvent`(1) (`04_ring.tex:423-440`).

Structure (namespace `NonUniqueEuler.EvansRangeAux` for the helpers):
* the profile `p = h_ℓ` of `h ∈ Y^s_ℓ` lies in `H^s((0,∞))`, supported in `[ρ₋,ρ₊]`
  (`profile_memH1On`, `H/Sec4/EvansSimple/Range/Basic.lean`);
* profile level (`exists_profile_sol`, `H/Sec4/EvansSimple/Range/Bvp.lean`): with
  `F = e^{2ξ}(M_* p)(e^ξ)`, the variation of constants formula with a second solution `φ₂`,
  `W(ψ_*, φ₂) = 1`, solves `eq:bvp` because `∫_ℝ ψ_*F = ∫_0^∞ p ψ_*(log r) M_* r dr = 0`; the
  converse part of the reduction (`green_eq_of_bvp`) gives `q ∈ Y^0_ℓ` with
  `λ_* q - L_ℓ q = p` on `(0,∞)`;
* regularity: `q ∈ H^s((0,∞))` (`memH1On_of_resolvent_eq`, `I/Sec4/Resolvent/Regularity.lean`),
  so `q e^{iℓθ}` is an element `η ∈ Y^s_ℓ` (`exists_Ysec_ofProfile`), and
  `λ_* η - L_ℓ η = h` (compare functions a.e.); `x = -η`.

**Deviation.** The manuscript solves `(L_ℓ - λ_*)g₁ = g_*` with the ξ-ODE regularity
induction; here the right side is a general `h` (so its forcing is only `L¹`), `eq:bvp` is in
integrated form, and the regularity comes from the bootstrap of
`I/Sec4/Resolvent/Regularity.lean` (as in `P/Sec4/Resolvent.lean`).
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler

namespace SectorSetting

open Sect

open EvansRangeAux in
/-- Solvability at a zero of the Evans function (step of `thm:evans-simple`(2); the argument of
`thm:evans-simple`(3), `04_ring.tex:536-551`, with a general right side): if
`∫_0^∞ h_ℓ ψ_*(log r) M_* r dr = 0`, then `L_ℓ(G) x - λ_* x = h` has a solution `x ∈ Y^s_ℓ`. -/
theorem evansSimple_range (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (z : ℂ)
    (hz : 0 < z.re) (G : ℝ) (hE : S.evans ℓ z G = 0) (s : ℕ) (h : Ysec s S.Nstar ℓ)
    (h0 : ∫ r in Ioi (0 : ℝ), Polar.angularSector h.fn ℓ r * S.psi ℓ z G (Real.log r) *
      S.Mres ℓ z G r * (r : ℂ) = 0) :
    ∃ x : Ysec s S.Nstar ℓ, S.Lsec s ℓ G x - z • x = h := by
  set p := Polar.angularSector h.fn (ℓ : ℤ) with hp
  obtain ⟨hpH, hpI⟩ := profile_memH1On S hS h
  have hpL2 := profile_isProfileL2 S hS h
  obtain ⟨q, hq2, hqeq⟩ := exists_profile_sol S hS ℓ hℓ hz G hE hpL2 h0
  have hqeq' : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), z * q r - S.LsecFn ℓ G q r = p r := by
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
      with r hr
    exact hqeq r hr
  have hqH : Sob.MemH1On s (Ioi 0) q :=
    memH1On_of_resolvent_eq S hS ℓ hℓ z hz G s hq2 hpH hpI hqeq'
  obtain ⟨η, hη⟩ : ∃ η : Ysec s S.Nstar ℓ, η.fn =ᵐ[volume] Ang.ofProfile ℓ q :=
    exists_Ysec_ofProfile hS.ρm_pos hS.ρm_lt_ρp (ℓ : ℤ) hqH hq2.2
  have hT : z • η - S.Lsec s ℓ G η = h := by
    refine Ysec_ext_fn ?_
    have hprof : Polar.angularSector η.fn ℓ =ᵐ[volume.restrict (Ioi (0 : ℝ))] q :=
      profile_of_fn hη
    have h1 : (fun r => z * Polar.angularSector η.fn ℓ r -
        S.LsecFn ℓ G (Polar.angularSector η.fn ℓ) r) =ᵐ[volume.restrict (Ioi (0 : ℝ))] p := by
      filter_upwards [hprof, LsecFn_congr_ae S ℓ G hprof, hqeq'] with r h1r h2r h3r
      rw [h1r, h2r, h3r]
    filter_upwards [sub_Lsec_fn S hS z G η, ofProfile_congr_ae (ℓ := ℓ) h1,
      fn_ae_eq_ofProfile S hS h] with x h2 h3 h4
    rw [h2, h3, h4]
  refine ⟨-η, ?_⟩
  rw [map_neg, smul_neg, ← hT]
  abel

end SectorSetting

end NonUniqueEuler
