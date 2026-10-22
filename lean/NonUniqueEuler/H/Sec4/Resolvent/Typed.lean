import NonUniqueEuler.H.Sec4.Resolvent.Conj
import NonUniqueEuler.H.Sec4.Resolvent.Profile
import NonUniqueEuler.I.Sec4.SemigroupConstruct
import NonUniqueEuler.I.Infra.SectorSpace.Decomposition
import NonUniqueEuler.I.Infra.AngularFourier.Derivatives
import NonUniqueEuler.I.Infra.AngularFourier.Symmetry

/-!
# Helpers for `P/Sec4/Resolvent`: the sector operators on `Y^s_ℓ` through profiles

For `g ∈ Y^s_ℓ` with profile `g_ℓ = Polar.angularSector g.fn ℓ`:
* `profile_memH1On`, `profile_isProfileL2`: `g_ℓ ∈ H^s((0,∞))`, supported in `[ρ₋,ρ₊]`, hence
  in `Y^0_ℓ` as a profile;
* `fn_ae_eq_ofProfile`, `Lsec_fn`: `g = g_ℓ(r)e^{iℓθ}` and `L_ℓ g = (L_ℓ g_ℓ)(r)e^{iℓθ}`;
* `sub_Lsec_fn`: `(z g - L_ℓ g) = (z g_ℓ - L_ℓ g_ℓ)(r) e^{iℓθ}`;
* `conjLIE_Lsec`: conjugation intertwines `L_ℓ(G)` and `L_{-ℓ}(G)` (`lem:sector`(2),
  `LsecFn_neg_conj`).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ComplexConjugate

namespace NonUniqueEuler.ResolventAux

open SectorSetting Sect Ang

theorem profile_memH1On (S : SectorSetting) (hS : S.Valid) {s : ℕ} {ℓ : ℤ}
    (g : Ysec s S.Nstar ℓ) :
    Sob.MemH1On s (Ioi 0) (Polar.angularSector g.fn ℓ) ∧
      ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), r ∉ Icc S.ρm S.ρp →
        Polar.angularSector g.fn ℓ r = 0 :=
  memH1On_angularSector hS.ρm_pos (Ysec_memH_fn g) (Ysec_supp g) ℓ

theorem profile_isProfileL2 (S : SectorSetting) (hS : S.Valid) {s : ℕ} {ℓ : ℤ}
    (g : Ysec s S.Nstar ℓ) : S.IsProfileL2 (Polar.angularSector g.fn ℓ) := by
  obtain ⟨hH, hI⟩ := profile_memH1On S hS g
  refine ⟨hH.memLp.mono_measure (Measure.restrict_mono ?_ le_rfl), hI⟩
  exact fun r hr => lt_of_lt_of_le hS.ρm_pos hr.1

theorem fn_ae_eq_ofProfile (S : SectorSetting) (hS : S.Valid) {s : ℕ} {ℓ : ℤ}
    (g : Ysec s S.Nstar ℓ) : g.fn =ᵐ[volume] ofProfile ℓ (Polar.angularSector g.fn ℓ) :=
  Ysec.fn_ae_eq_ofProfile hS.ρm_pos g

theorem Lsec_fn (S : SectorSetting) (hS : S.Valid) {s : ℕ} {ℓ : ℤ} (G : ℝ)
    (g : Ysec s S.Nstar ℓ) :
    (S.Lsec s ℓ G g).fn =ᵐ[volume]
      ofProfile ℓ (S.LsecFn ℓ G (Polar.angularSector g.fn ℓ)) :=
  semigroupConstruct_Lsec S hS s ℓ G g

/-- The profile of a function `a.e.` equal to `p(r)e^{iℓθ}` is `p`. -/
theorem profile_of_fn {ℓ : ℤ} {f : ℂ → ℂ} {p : ℝ → ℂ} (h : f =ᵐ[volume] ofProfile ℓ p) :
    Polar.angularSector f ℓ =ᵐ[volume.restrict (Ioi (0 : ℝ))] p :=
  (angularSector_congr_ae h ℓ).trans (angularSector_ofProfile_ae ℓ p)

theorem algebraMap_sub_apply {s : ℕ} {ℓ : ℤ} {K : Set ℂ} (z : ℂ) (A : Ysec s K ℓ →L[ℂ] Ysec s K ℓ)
    (g : Ysec s K ℓ) : (algebraMap ℂ (Ysec s K ℓ →L[ℂ] Ysec s K ℓ) z - A) g = z • g - A g := by
  rw [Algebra.algebraMap_eq_smul_one]
  simp

/-- `z g - L_ℓ g = (z g_ℓ - L_ℓ g_ℓ)(r)e^{iℓθ}`. -/
theorem sub_Lsec_fn (S : SectorSetting) (hS : S.Valid) {s : ℕ} {ℓ : ℤ} (z : ℂ) (G : ℝ)
    (g : Ysec s S.Nstar ℓ) :
    (z • g - S.Lsec s ℓ G g).fn =ᵐ[volume]
      ofProfile ℓ (fun r => z * Polar.angularSector g.fn ℓ r -
        S.LsecFn ℓ G (Polar.angularSector g.fn ℓ) r) := by
  rw [ofProfile_sub, ofProfile_smul]
  filter_upwards [Ysec_fn_sub (z • g) (S.Lsec s ℓ G g), Ysec_fn_smul z g,
    fn_ae_eq_ofProfile S hS g, Lsec_fn S hS G g] with x h1 h2 h3 h4
  rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, h4]
  rfl

/-- `L_{-ℓ}(G) ḡ = conj(L_ℓ(G) g)` on `Y^s_ℓ` (`lem:sector`(2)). -/
theorem conjLIE_Lsec (S : SectorSetting) (hS : S.Valid) (s : ℕ) (ℓ : ℤ) (G : ℝ)
    (g : Ysec s S.Nstar ℓ) :
    S.Lsec s (-ℓ) G (conjLIE s S.Nstar ℓ g) = conjLIE s S.Nstar ℓ (S.Lsec s ℓ G g) := by
  refine Ysec_ext_fn ?_
  set p := Polar.angularSector g.fn ℓ with hp
  have h1 : Polar.angularSector (conjLIE s S.Nstar ℓ g).fn (-ℓ) =ᵐ[volume.restrict (Ioi 0)]
      fun r => conj (p r) := by
    filter_upwards [angularSector_congr_ae (conjLIE_fn ℓ g) (-ℓ)] with r hr
    rw [hr, angularSector_conj]
  have h2 : S.LsecFn (-ℓ) G (Polar.angularSector (conjLIE s S.Nstar ℓ g).fn (-ℓ))
      =ᵐ[volume.restrict (Ioi 0)] fun r => conj (S.LsecFn ℓ G p r) := by
    filter_upwards [LsecFn_congr_ae S (-ℓ) G h1] with r hr
    rw [hr, LsecFn_neg_conj]
  filter_upwards [Lsec_fn S hS G (conjLIE s S.Nstar ℓ g), ofProfile_congr_ae (ℓ := -ℓ) h2,
    ofProfile_neg_conj_ae ℓ (S.LsecFn ℓ G p), Lsec_fn S hS G g,
    conjLIE_fn ℓ (S.Lsec s ℓ G g)] with x h3 h4 h5 h6 h7
  rw [h3, h4, h5, h7, h6]

end NonUniqueEuler.ResolventAux
