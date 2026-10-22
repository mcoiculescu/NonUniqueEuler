import NonUniqueEuler.Defs.Sec4.Evans
import NonUniqueEuler.Defs.Sec4.Extra1Sector
import NonUniqueEuler.H.Sec4.Resolvent.Typed
import NonUniqueEuler.I.Sec4.Resolvent.Regularity
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Algebra.Algebra.Spectrum.Basic

/-!
# Proof of `lem:resolvent` (`I/Sec4/Resolvent.lean`)

Manuscript `04_ring.tex:366-448`. Structure of the proof:
* profile level (`H/Sec4/Resolvent/Profile.lean`), from the reduction to `eq:bvp`
  (`I/Sec4/Resolvent/Reduction.lean`), the Wronskian formula (`I/Sec4/Resolvent/PsiG.lean`) and
  `lem:evans-basic`: the resolvent formula solves the equation, injectivity for `E ≠ 0`,
  `𝒢_ℓ g_λ = ψ_ℓ(log r)` and the kernel for `E = 0`;
* typed level (this file, with `H/Sec4/Resolvent/Typed.lean`): `λ - L_ℓ(G)` is injective on
  `Y^s_ℓ` and surjective (the profile solution lies in `H^s`, `I/Sec4/Resolvent/Regularity.lean`,
  so it is an element of `Y^s_ℓ`, `Sect.exists_Ysec_ofProfile`); the open mapping theorem
  (`ContinuousLinearMap.isUnit_iff_bijective`) gives invertibility. **Deviation:** the manuscript
  proves boundedness of `(λ - L_ℓ)⁻¹` on `Y^s_ℓ` by explicit estimates (`04_ring.tex:423-433`);
  here bijectivity and the open mapping theorem replace them.
* conjugation (`H/Sec4/Resolvent/Conj.lean`): `g ↦ ḡ` is a real-linear isometry
  `Y^s_ℓ ≃ Y^s_{-ℓ}`, conjugate-linear over `ℂ`, intertwining `L_ℓ` and `L_{-ℓ}`; it transports
  the spectrum (`z ∈ σ(L_{-ℓ}) ↔ z̄ ∈ σ(L_ℓ)`) and the eigenvectors.
-/

noncomputable section

open MeasureTheory Set ComplexConjugate
open scoped ContDiff

namespace NonUniqueEuler

namespace SectorSetting

open Sect

open ResolventAux in
/-- `lem:resolvent`(1): if `E_ℓ(λ;G) ≠ 0` (`ℓ ≥ 1`, `Re λ > 0`), then `λ - L_ℓ(G)` is invertible
on every `Y^s_ℓ`, and `(λ - L_ℓ)⁻¹ g = M_λ(g + k_ℓψ_g)`, with
`ψ_g(ξ) = W⁻¹[ψ_R(ξ)∫_{-∞}^ξ ψ_L F + ψ_L(ξ)∫_ξ^∞ ψ_R F]`, `F(ξ) = e^{2ξ}(M_λ g)(e^ξ)`. -/
theorem resolvent_of_evans_ne_zero (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (z : ℂ) (hz : 0 < z.re) (G : ℝ) (hE : S.evans ℓ z G ≠ 0) (s : ℕ) :
    z ∈ resolventSet ℂ (S.Lsec s ℓ G) ∧
      ∀ g : Ysec s S.Nstar ℓ,
        (resolvent (S.Lsec s ℓ G) z g).fn =ᵐ[volume]
          Ang.ofProfile ℓ (S.resolventFn ℓ z G (Polar.angularSector g.fn ℓ)) := by
  set T : Ysec s S.Nstar ℓ →L[ℂ] Ysec s S.Nstar ℓ :=
    algebraMap ℂ (Ysec s S.Nstar ℓ →L[ℂ] Ysec s S.Nstar ℓ) z - S.Lsec s ℓ G with hTdef
  have hT : ∀ η, T η = z • η - S.Lsec s ℓ G η := fun η => algebraMap_sub_apply z _ η
  -- existence of a solution of `T η = g`, with the resolvent formula
  have hex : ∀ g : Ysec s S.Nstar ℓ, ∃ η : Ysec s S.Nstar ℓ, T η = g ∧
      η.fn =ᵐ[volume] Ang.ofProfile ℓ (S.resolventFn ℓ z G (Polar.angularSector g.fn ℓ)) := by
    intro g
    set p := Polar.angularSector g.fn (ℓ : ℤ) with hp
    obtain ⟨hpH, hpI⟩ := profile_memH1On S hS g
    have hpL2 := profile_isProfileL2 S hS g
    obtain ⟨hq2, hqeq⟩ := resolventFn_spec S hS ℓ hℓ hz G hE hpL2
    set q := S.resolventFn ℓ z G p with hq
    have hqeq' : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), z * q r - S.LsecFn ℓ G q r = p r := by
      filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
        with r hr
      exact hqeq r hr
    have hqH : Sob.MemH1On s (Ioi 0) q :=
      memH1On_of_resolvent_eq S hS ℓ hℓ z hz G s hq2 hpH hpI hqeq'
    obtain ⟨η, hη⟩ : ∃ η : Ysec s S.Nstar ℓ, η.fn =ᵐ[volume] Ang.ofProfile ℓ q :=
      exists_Ysec_ofProfile hS.ρm_pos hS.ρm_lt_ρp (ℓ : ℤ) hqH hq2.2
    refine ⟨η, ?_, hη⟩
    rw [hT]
    refine Ysec_ext_fn ?_
    have hprof : Polar.angularSector η.fn ℓ =ᵐ[volume.restrict (Ioi (0 : ℝ))] q :=
      profile_of_fn hη
    have h1 : (fun r => z * Polar.angularSector η.fn ℓ r -
        S.LsecFn ℓ G (Polar.angularSector η.fn ℓ) r) =ᵐ[volume.restrict (Ioi (0 : ℝ))] p := by
      filter_upwards [hprof, LsecFn_congr_ae S ℓ G hprof, hqeq'] with r h1r h2r h3r
      rw [h1r, h2r, h3r]
    filter_upwards [sub_Lsec_fn S hS z G η, ofProfile_congr_ae (ℓ := ℓ) h1,
      fn_ae_eq_ofProfile S hS g] with x h2 h3 h4
    rw [h2, h3, h4]
  -- injectivity
  have hinj0 : ∀ η, T η = 0 → η = 0 := by
    intro η hη
    rw [hT] at hη
    set p := Polar.angularSector η.fn (ℓ : ℤ) with hp
    have h1 : Ang.ofProfile ℓ (fun r => z * p r - S.LsecFn ℓ G p r) =ᵐ[volume]
        Ang.ofProfile ℓ (fun _ => 0) := by
      rw [Ang.ofProfile_zero_profile]
      refine (sub_Lsec_fn S hS z G η).symm.trans ?_
      rw [hη]
      exact Ysec_fn_zero
    have h2 := ae_eq_zero_of_resolvent_eq_zero S hS ℓ hℓ hz G hE (profile_isProfileL2 S hS η)
      (ofProfile_ae_inj h1)
    refine Ysec_ext_fn ?_
    filter_upwards [fn_ae_eq_ofProfile S hS η, ofProfile_congr_ae (ℓ := ℓ) h2,
      (Ysec_fn_zero : (0 : Ysec s S.Nstar ℓ).fn =ᵐ[volume] 0)] with x h3 h4 h5
    rw [h3, h4, h5]
    simp [Ang.ofProfile]
  have hbij : Function.Bijective T := by
    refine ⟨fun a b hab => ?_, fun g => (hex g).imp fun η h => h.1⟩
    have : T (a - b) = 0 := by rw [map_sub, hab, sub_self]
    exact sub_eq_zero.1 (hinj0 _ this)
  have hunit : IsUnit T := ContinuousLinearMap.isUnit_iff_bijective.2 hbij
  refine ⟨hunit, fun g => ?_⟩
  obtain ⟨η, hTη, hηfn⟩ := hex g
  have hres : resolvent (S.Lsec s ℓ G) z g = η := by
    have h1 : Ring.inverse T * T = 1 := Ring.inverse_mul_cancel T hunit
    have h2 : (Ring.inverse T * T) η = η := by rw [h1]; rfl
    rw [resolvent, ← hTdef, ← hTη]
    exact h2
  rw [hres]
  exact hηfn

open ResolventAux in
/-- `lem:resolvent`(2): if `E_ℓ(λ;G) = 0` (`ℓ ≥ 1`, `Re λ > 0`), then
`g_λ = M_λ k_ℓ ψ_ℓ(log r; λ, G)` is smooth on `(0,∞)`, supported in `[r₁, r₂]`, not identically
zero, with `𝒢_ℓ g_λ = ψ_ℓ(log r)`; and on every `Y^s_ℓ`, `g_λ e^{iℓθ}` (`S.gStarY`) is an
eigenvector of `L_ℓ(G)` for the eigenvalue `λ` that spans `ker(L_ℓ(G) - λ)`. -/
theorem eigen_of_evans_eq_zero (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (z : ℂ) (hz : 0 < z.re) (G : ℝ) (hE : S.evans ℓ z G = 0) :
    ContDiffOn ℝ ∞ (S.gStar ℓ z G) (Ioi 0) ∧
      (∀ r : ℝ, 0 < r → r ∉ Icc S.r₁ S.r₂ → S.gStar ℓ z G r = 0) ∧
      (∃ r : ℝ, 0 < r ∧ S.gStar ℓ z G r ≠ 0) ∧
      (∀ r : ℝ, 0 < r → green ℓ (S.gStar ℓ z G) r = S.psi ℓ z G (Real.log r)) ∧
      ∀ s : ℕ,
        (S.gStarY s ℓ z G).fn =ᵐ[volume] Ang.ofProfile ℓ (S.gStar ℓ z G) ∧
          S.gStarY s ℓ z G ≠ 0 ∧
          S.Lsec s ℓ G (S.gStarY s ℓ z G) = z • S.gStarY s ℓ z G ∧
          ∀ η : Ysec s S.Nstar ℓ, S.Lsec s ℓ G η = z • η → ∃ c : ℂ, η = c • S.gStarY s ℓ z G := by
  have hcd := contDiffOn_gStar S hS ℓ hℓ hz G
  have hsupp : ∀ r : ℝ, 0 < r → r ∉ Icc S.r₁ S.r₂ → S.gStar ℓ z G r = 0 :=
    fun r hr hrI => gStar_eq_zero_of_not_mem S hS ℓ z G hr hrI
  have hne := exists_gStar_ne_zero S hS ℓ hℓ hz G hE
  obtain ⟨-, hgreen⟩ := green_gStar S hS ℓ hℓ hz G hE
  refine ⟨hcd, hsupp, hne, hgreen, fun s => ?_⟩
  -- `g_λ e^{iℓθ} ∈ Y^s_ℓ`
  have hsuppAE : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), r ∉ Icc S.ρm S.ρp →
      S.gStar ℓ z G r = 0 := by
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
      with r hr hrI
    exact hsupp r hr fun h => hrI (Icc_subset_Icc hS.ρm_lt_r₁.le hS.r₂_lt_ρp.le h)
  have hex : ∃ g : Ysec s S.Nstar ℓ, g.fn =ᵐ[volume] Ang.ofProfile ℓ (S.gStar ℓ z G) :=
    exists_Ysec_ofProfile hS.ρm_pos hS.ρm_lt_ρp (ℓ : ℤ) (memH1On_gStar S hS ℓ hℓ hz G s) hsuppAE
  have hfn : (S.gStarY s ℓ z G).fn =ᵐ[volume] Ang.ofProfile ℓ (S.gStar ℓ z G) := toYsec_spec hex
  have hprof := profile_of_fn hfn
  -- the eigenvalue equation on profiles: `L_ℓ g_λ = z g_λ` on `(0,∞)`
  have heig : ∀ r : ℝ, 0 < r → S.LsecFn ℓ G (S.gStar ℓ z G) r = z * S.gStar ℓ z G r := by
    intro r hr
    have h := hgreen r hr
    have hM := denom_mul_Mres S hz (ℓ : ℤ) G r
    rw [LsecFn_eq, h]
    simp only [gStar]
    linear_combination (-(S.kcoef ℓ r * S.psi ℓ z G (Real.log r))) * hM
  refine ⟨hfn, ?_, ?_, ?_⟩
  · -- `g_λ e^{iℓθ} ≠ 0`
    intro h0
    have h1 : Ang.ofProfile ℓ (S.gStar ℓ z G) =ᵐ[volume] Ang.ofProfile ℓ (fun _ => 0) := by
      rw [Ang.ofProfile_zero_profile]
      refine hfn.symm.trans ?_
      rw [h0]
      exact Ysec_fn_zero
    have h2 := ofProfile_ae_inj h1
    have h3 := Measure.eqOn_open_of_ae_eq h2 isOpen_Ioi hcd.continuousOn continuousOn_const
    obtain ⟨r, hr, hr0⟩ := hne
    exact hr0 (h3 hr)
  · -- the eigenvalue equation
    refine Ysec_ext_fn ?_
    have h1 : S.LsecFn ℓ G (Polar.angularSector (S.gStarY s ℓ z G).fn ℓ)
        =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun r => z * S.gStar ℓ z G r := by
      filter_upwards [LsecFn_congr_ae S ℓ G hprof,
        self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))] with r hr hr0
      rw [hr, heig r hr0]
    filter_upwards [Lsec_fn S hS G (S.gStarY s ℓ z G), ofProfile_congr_ae (ℓ := ℓ) h1,
      Ysec_fn_smul z (S.gStarY s ℓ z G), hfn] with x h2 h3 h4 h5
    rw [h2, h3, h4, ofProfile_smul, Pi.smul_apply, Pi.smul_apply, h5]
  · -- the kernel
    intro η hη
    set p := Polar.angularSector η.fn (ℓ : ℤ) with hp
    have h1 : Ang.ofProfile ℓ (S.LsecFn ℓ G p) =ᵐ[volume] Ang.ofProfile ℓ (fun r => z * p r) := by
      rw [ofProfile_smul]
      filter_upwards [Lsec_fn S hS G η, Ysec_fn_smul z η, fn_ae_eq_ofProfile S hS η] with x h2 h3 h4
      rw [← h2, hη, h3, Pi.smul_apply, Pi.smul_apply, h4]
    obtain ⟨c, hc⟩ := exists_eq_smul_gStar S hS ℓ hℓ hz G (profile_isProfileL2 S hS η)
      (ofProfile_ae_inj h1)
    refine ⟨c, Ysec_ext_fn ?_⟩
    filter_upwards [fn_ae_eq_ofProfile S hS η, ofProfile_congr_ae (ℓ := ℓ) hc,
      Ysec_fn_smul c (S.gStarY s ℓ z G), hfn] with x h2 h3 h4 h5
    rw [h2, h3, h4, ofProfile_smul, Pi.smul_apply, Pi.smul_apply, h5]

open ResolventAux in
/-- `lem:resolvent`, last assertion: for `ℓ ≥ 1`, the spectrum of `L_ℓ(G)` on `Y^s_ℓ` in
`{Re λ > 0}` is the zero set of `E_ℓ(·;G)` (for every `s`, so it does not depend on `s`); the
spectrum of `L_{-ℓ}(G)` in `{Re λ > 0}` is its complex conjugate. -/
theorem spectrum_re_pos (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (G : ℝ)
    (s : ℕ) :
    (∀ z : ℂ, 0 < z.re → (z ∈ spectrum ℂ (S.Lsec s ℓ G) ↔ S.evans ℓ z G = 0)) ∧
      ∀ z : ℂ, 0 < z.re →
        (z ∈ spectrum ℂ (S.Lsec s (-(ℓ : ℤ)) G) ↔ S.evans ℓ (conj z) G = 0) := by
  have h1 : ∀ z : ℂ, 0 < z.re → (z ∈ spectrum ℂ (S.Lsec s ℓ G) ↔ S.evans ℓ z G = 0) := by
    intro z hz
    by_cases hE : S.evans ℓ z G = 0
    · simp only [hE, iff_true]
      rw [spectrum.mem_iff, ContinuousLinearMap.isUnit_iff_bijective]
      intro hbij
      obtain ⟨-, hne, heig, -⟩ := (eigen_of_evans_eq_zero S hS ℓ hℓ z hz G hE).2.2.2.2 s
      apply hne
      apply hbij.1
      rw [algebraMap_sub_apply, heig, sub_self, map_zero]
    · simp only [hE, iff_false]
      exact spectrum.notMem_iff.2 (resolvent_of_evans_ne_zero S hS ℓ hℓ z hz G hE s).1
  refine ⟨h1, fun z hz => ?_⟩
  rw [← h1 (conj z) (by simpa using hz)]
  -- transport through conjugation
  set C := conjLIE s S.Nstar (ℓ : ℤ) with hC
  have hint := conjLIE_Lsec S hS s (ℓ : ℤ) G
  set Tm : Ysec s S.Nstar (-(ℓ : ℤ)) →L[ℂ] Ysec s S.Nstar (-(ℓ : ℤ)) :=
    algebraMap ℂ _ z - S.Lsec s (-(ℓ : ℤ)) G with hTm
  set Tp : Ysec s S.Nstar (ℓ : ℤ) →L[ℂ] Ysec s S.Nstar (ℓ : ℤ) :=
    algebraMap ℂ _ (conj z) - S.Lsec s (ℓ : ℤ) G with hTp
  have hcomm : ∀ g, Tm (C g) = C (Tp g) := by
    intro g
    rw [hTm, hTp, algebraMap_sub_apply, algebraMap_sub_apply, hint, map_sub, conjLIE_smul,
      Complex.conj_conj]
  have hfun1 : (Tm : Ysec s S.Nstar (-(ℓ : ℤ)) → Ysec s S.Nstar (-(ℓ : ℤ))) =
      C ∘ Tp ∘ C.symm := by
    funext x
    simp only [Function.comp_apply]
    rw [← hcomm, LinearIsometryEquiv.apply_symm_apply]
  have hfun2 : (Tp : Ysec s S.Nstar (ℓ : ℤ) → Ysec s S.Nstar (ℓ : ℤ)) = C.symm ∘ Tm ∘ C := by
    funext x
    simp only [Function.comp_apply]
    rw [hcomm, LinearIsometryEquiv.symm_apply_apply]
  rw [spectrum.mem_iff, spectrum.mem_iff, ← hTm, ← hTp, ContinuousLinearMap.isUnit_iff_bijective,
    ContinuousLinearMap.isUnit_iff_bijective, not_iff_not]
  constructor
  · intro h
    rw [hfun2]
    exact C.symm.bijective.comp (h.comp C.bijective)
  · intro h
    rw [hfun1]
    exact C.bijective.comp (h.comp C.symm.bijective)

open ResolventAux in
/-- `lem:resolvent`, last assertion, in the form used later: for every sector `ℓ ≠ 0` and every
`s`, each point of the spectrum of `L_ℓ(G)` on `Y^s_ℓ` with positive real part is an eigenvalue
of `L_ℓ(G)` on `Y^0_ℓ`. -/
theorem spectrum_re_pos_eigen (S : SectorSetting) (hS : S.Valid) (ℓ : ℤ) (hℓ : ℓ ≠ 0) (G : ℝ)
    (s : ℕ) (z : ℂ) (hz : 0 < z.re) (hzs : z ∈ spectrum ℂ (S.Lsec s ℓ G)) :
    ∃ g : Ysec 0 S.Nstar ℓ, g ≠ 0 ∧ S.Lsec 0 ℓ G g = z • g := by
  rcases lt_or_gt_of_ne hℓ with hneg | hpos
  · -- `ℓ = -n`, `n ≥ 1`
    obtain ⟨n, hn⟩ : ∃ n : ℕ, ℓ = -(n : ℤ) := ⟨ℓ.natAbs, by omega⟩
    subst hn
    have hn1 : 1 ≤ n := by omega
    have hE := ((spectrum_re_pos S hS n hn1 G s).2 z hz).1 hzs
    have hzc : 0 < (conj z).re := by simpa using hz
    obtain ⟨-, hne, heig, -⟩ := (eigen_of_evans_eq_zero S hS n hn1 (conj z) hzc G hE).2.2.2.2 0
    refine ⟨conjLIE 0 S.Nstar (n : ℤ) (S.gStarY 0 n (conj z) G), ?_, ?_⟩
    · intro h0
      apply hne
      have := congrArg (conjLIE 0 S.Nstar (n : ℤ)).symm h0
      rwa [LinearIsometryEquiv.symm_apply_apply, map_zero] at this
    · rw [conjLIE_Lsec S hS 0 (n : ℤ) G, heig, conjLIE_smul, Complex.conj_conj]
  · -- `ℓ = n`, `n ≥ 1`
    obtain ⟨n, hn⟩ : ∃ n : ℕ, ℓ = (n : ℤ) := ⟨ℓ.natAbs, by omega⟩
    subst hn
    have hn1 : 1 ≤ n := by omega
    have hE := ((spectrum_re_pos S hS n hn1 G s).1 z hz).1 hzs
    obtain ⟨-, hne, heig, -⟩ := (eigen_of_evans_eq_zero S hS n hn1 z hz G hE).2.2.2.2 0
    exact ⟨S.gStarY 0 n z G, hne, heig⟩

open ResolventAux in
/-- Proof of `lem:resolvent`, last assertion (`04_ring.tex:446-448`), with `lem:sector`(2)
(`L_{-ℓ}(G) ḡ = conj(L_ℓ(G) g)`): complex conjugation `g ↦ ḡ` is a conjugate-linear isometry of
`Y^s_ℓ` onto `Y^s_{-ℓ}` (for every `s` and every `ℓ ∈ ℤ`) that intertwines `L_ℓ(G)` and
`L_{-ℓ}(G)`. -/
theorem exists_conj_Ysec (S : SectorSetting) (hS : S.Valid) (s : ℕ) (ℓ : ℤ) (G : ℝ) :
    ∃ C : Ysec s S.Nstar ℓ ≃ₗᵢ[ℝ] Ysec s S.Nstar (-ℓ),
      (∀ g : Ysec s S.Nstar ℓ, (C g).fn =ᵐ[volume] fun x => conj (g.fn x)) ∧
        (∀ (c : ℂ) (g : Ysec s S.Nstar ℓ), C (c • g) = conj c • C g) ∧
        ∀ g : Ysec s S.Nstar ℓ, S.Lsec s (-ℓ) G (C g) = C (S.Lsec s ℓ G g) :=
  ⟨conjLIE s S.Nstar ℓ, conjLIE_fn ℓ, conjLIE_smul ℓ, conjLIE_Lsec S hS s ℓ G⟩

end SectorSetting

end NonUniqueEuler
