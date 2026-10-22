import NonUniqueEuler.H.Sec4.EvansSimple.Basic
import NonUniqueEuler.H.Sec4.EvansSimple.Profile
import NonUniqueEuler.I.Sec4.SemigroupConstruct

/-!
# Helper for `thm:evans-simple`(2): the functional `ℓ_*` on `Y^s_ℓ`

Helper of `P/Sec4/EvansSimple.lean` (fully proved). Namespace `NonUniqueEuler.EvansSimpleAux`.
Manuscript `04_ring.tex:462-469` (`ℓ_*`), `:529` (`ℓ_*(g_*) = 1`), `lem:adjoint`(2)
(`ℓ_*(L_ℓ g) = λ_* ℓ_*(g)`, `04_ring.tex:602-614`).

* `isProfileL2_angularSector_Ysec`: the profile of `g ∈ Y^s_ℓ` is in `Y^0_ℓ`;
* `exists_ellStarY`, `ellStarY_spec`: `ℓ_*` is a bounded functional on every `Y^s_ℓ`
  (the `L²` pairing `exists_profile_pairing`);
* `ellStar_congr_ae`, `ellStarY_gStarY`: `ℓ_*(g_*) = 1` when `J ≠ 0`;
* `angularSector_Lsec`, `integral_Lsec_eq`, `ellStarY_Lsec`: `ℓ_* ∘ L_ℓ = λ_* ℓ_*` on `Y^s_ℓ`
  (`weak_eigen`, the symmetric Green kernel).
-/

noncomputable section

open MeasureTheory Set Filter Topology ComplexConjugate
open scoped ContDiff

namespace NonUniqueEuler.EvansSimpleAux

open SectorSetting Sect Ang

/-- The profile of `g ∈ Y^s_ℓ` lies in `Y^0_ℓ` (as a profile). -/
theorem isProfileL2_angularSector_Ysec (S : SectorSetting) (hS : S.Valid) (s : ℕ) (ℓ : ℤ)
    (g : Ysec s S.Nstar ℓ) : S.IsProfileL2 (Polar.angularSector g.fn ℓ) := by
  have h := memLp_angularSector_of_support hS.ρm_pos (Ysec_memLp_fn g)
    (by
      filter_upwards [Ysec_supp g] with x hx hx'
      exact hx hx') ℓ
  exact ⟨h.1.mono_measure (Measure.restrict_mono (Icc_subset_Ioi S hS) le_rfl), h.2⟩

/-- `ℓ_*` is a bounded functional on `Y^s_ℓ`. -/
theorem exists_ellStarY (S : SectorSetting) (hS : S.Valid) (s : ℕ) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    {z : ℂ} (hz : 0 < z.re) (G : ℝ) :
    ∃ T : Ysec s S.Nstar ℓ →L[ℂ] ℂ, ∀ g : Ysec s S.Nstar ℓ,
      T g = S.ellStar ℓ z G (Polar.angularSector g.fn ℓ) := by
  obtain ⟨T, hT⟩ : ∃ T : Ysec s S.Nstar ℓ →L[ℂ] ℂ, ∀ g : Ysec s S.Nstar ℓ,
      T g = ∫ r in Ioi (0 : ℝ), Polar.angularSector g.fn ℓ r *
        (S.psi ℓ z G (Real.log r) * S.Mres ℓ z G r) * (r : ℂ) :=
    exists_profile_pairing (ρp := S.ρp) s hS.ρm_pos (ℓ : ℤ) (continuousOn_X S hS ℓ hℓ hz G)
  refine ⟨(S.J ℓ z G)⁻¹ • T, fun g => ?_⟩
  rw [smul_apply, hT g, smul_eq_mul, ellStar]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only
  ring

theorem ellStarY_spec (S : SectorSetting) (hS : S.Valid) (s : ℕ) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    {z : ℂ} (hz : 0 < z.re) (G : ℝ) (g : Ysec s S.Nstar ℓ) :
    S.ellStarY s ℓ z G g = S.ellStar ℓ z G (Polar.angularSector g.fn ℓ) :=
  ellStarY_spec_of_exists S s ℓ z G (exists_ellStarY S hS s ℓ hℓ hz G) g

/-- `ℓ_*` only sees the a.e. class of the profile on `(0,∞)`. -/
theorem ellStar_congr_ae (S : SectorSetting) (ℓ : ℕ) (z : ℂ) (G : ℝ) {h₁ h₂ : ℝ → ℂ}
    (h : h₁ =ᵐ[volume.restrict (Ioi (0 : ℝ))] h₂) :
    S.ellStar ℓ z G h₁ = S.ellStar ℓ z G h₂ := by
  unfold ellStar
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [h] with r hr
  rw [hr]

/-- `ℓ_*(g_*) = 1` on `Y^s_ℓ` when `J ≠ 0` (`04_ring.tex:529`). -/
theorem ellStarY_gStarY (S : SectorSetting) (hS : S.Valid) (s : ℕ) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    {z : ℂ} (hz : 0 < z.re) (G : ℝ) (hE : S.evans ℓ z G = 0) (hJ : S.J ℓ z G ≠ 0) :
    S.ellStarY s ℓ z G (S.gStarY s ℓ z G) = 1 := by
  have hfn := ((eigen_of_evans_eq_zero S hS ℓ hℓ z hz G hE).2.2.2.2 s).1
  rw [ellStarY_spec S hS s ℓ hℓ hz G, ellStar_congr_ae S ℓ z G
    (angularSector_ae_of_ae_ofProfile hfn), ellStar_gStar S ℓ z G hJ]

/-- The profile of `L_ℓ(G) g` is `L_ℓ(G)` applied to the profile of `g`, a.e. on `(0,∞)`. -/
theorem angularSector_Lsec (S : SectorSetting) (hS : S.Valid) (s : ℕ) (ℓ : ℤ) (G : ℝ)
    (g : Ysec s S.Nstar ℓ) :
    Polar.angularSector (S.Lsec s ℓ G g).fn ℓ =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      S.LsecFn ℓ G (Polar.angularSector g.fn ℓ) :=
  angularSector_ae_of_ae_ofProfile (semigroupConstruct_Lsec S hS s ℓ G g)

/-- `∫ (L_ℓ g)_ℓ ψ_* M_* r dr = λ_* ∫ g_ℓ ψ_* M_* r dr` on `Y^s_ℓ` (`lem:adjoint`(1)). -/
theorem integral_Lsec_eq (S : SectorSetting) (hS : S.Valid) (s : ℕ) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    {z : ℂ} (hz : 0 < z.re) (G : ℝ) (hE : S.evans ℓ z G = 0) (g : Ysec s S.Nstar ℓ) :
    ∫ r in Ioi (0 : ℝ), Polar.angularSector (S.Lsec s ℓ G g).fn ℓ r *
        S.psi ℓ z G (Real.log r) * S.Mres ℓ z G r * (r : ℂ) =
      z * ∫ r in Ioi (0 : ℝ), Polar.angularSector g.fn ℓ r *
        S.psi ℓ z G (Real.log r) * S.Mres ℓ z G r * (r : ℂ) := by
  have hw := weak_eigen S hS ℓ hℓ z hz G hE (isProfileL2_angularSector_Ysec S hS s ℓ g)
  have e1 : ∫ r in Ioi (0 : ℝ), Polar.angularSector (S.Lsec s ℓ G g).fn ℓ r *
        S.psi ℓ z G (Real.log r) * S.Mres ℓ z G r * (r : ℂ) =
      ∫ r in Ioi (0 : ℝ), S.LsecFn ℓ G (Polar.angularSector g.fn ℓ) r *
        (S.psi ℓ z G (Real.log r) * S.Mres ℓ z G r) * (r : ℂ) := by
    refine integral_congr_ae ?_
    filter_upwards [angularSector_Lsec S hS s ℓ G g] with r hr
    rw [hr]
    ring
  rw [e1, hw]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only
  ring

/-- `ℓ_*(L_ℓ g) = λ_* ℓ_*(g)` on `Y^s_ℓ` (`lem:adjoint`(2), `04_ring.tex:613-614`). -/
theorem ellStarY_Lsec (S : SectorSetting) (hS : S.Valid) (s : ℕ) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    {z : ℂ} (hz : 0 < z.re) (G : ℝ) (hE : S.evans ℓ z G = 0) (g : Ysec s S.Nstar ℓ) :
    S.ellStarY s ℓ z G (S.Lsec s ℓ G g) = z * S.ellStarY s ℓ z G g := by
  rw [ellStarY_spec S hS s ℓ hℓ hz G, ellStarY_spec S hS s ℓ hℓ hz G, ellStar, ellStar,
    integral_Lsec_eq S hS s ℓ hℓ hz G hE g]
  ring

end NonUniqueEuler.EvansSimpleAux
