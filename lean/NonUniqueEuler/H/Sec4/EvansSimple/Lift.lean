import NonUniqueEuler.H.Sec4.EvansSimple.Functional
import NonUniqueEuler.I.Infra.SectorSpace.Decomposition
import NonUniqueEuler.I.Infra.SobolevOneD.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Helper for `thm:evans-simple`(3): lifting a smooth profile to `Y^s_ℓ`; the converse of (3)

Helper of `P/Sec4/EvansSimple.lean` (fully proved). Namespace `NonUniqueEuler.EvansSimpleAux`.
Manuscript `04_ring.tex:536-563`.

* `memLp_Ioi_of_continuousOn_Icc`, `memH1On_of_smooth_supported`: a profile smooth on `(0,∞)`
  and vanishing off `[a, b] ⊂ (0,∞)` lies in `H^s((0,∞))`;
* `exists_Ysec_genEigen`: a smooth profile `g₁` supported in `[r₁,r₂]` with
  `L_ℓ g₁ - λ_* g₁ = g_*` on `(0,∞)` gives `h ∈ Y^s_ℓ` with `h = g₁ e^{iℓθ}` and
  `L_ℓ(G) h - λ_* h = g_*` in `Y^s_ℓ`;
* `J_eq_zero_of_genEigen`: conversely, `(L_ℓ - λ_*) g₁ = g_*` in `Y^0_ℓ` forces `J = 0`: apply
  the (unnormalized) functional `g ↦ ∫ g_ℓ ψ_* M_* r dr`, which annihilates the range of
  `L_ℓ - λ_*` (`integral_Lsec_eq`) and takes the value `J` at `g_*` (restructured: the manuscript
  argues with the growth of the variation-of-constants solution, `04_ring.tex:544-551`).
-/

noncomputable section

open MeasureTheory Set Filter Topology ComplexConjugate
open scoped ContDiff

namespace NonUniqueEuler.EvansSimpleAux

open SectorSetting Sect Sob Ang

/-- A function continuous on `[a,b]` and vanishing on `(0,∞) \ [a,b]` is in `L²((0,∞))`. -/
theorem memLp_Ioi_of_continuousOn_Icc {F : ℝ → ℂ} {a b : ℝ} (hF : ContinuousOn F (Icc a b))
    (hz : ∀ r : ℝ, 0 < r → r ∉ Icc a b → F r = 0) :
    MemLp F 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have h1 : MemLp ((Icc a b).indicator F) 2 volume := by
    rw [memLp_indicator_iff_restrict measurableSet_Icc]
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hF
    exact MemLp.of_bound (hF.aestronglyMeasurable measurableSet_Icc) C
      ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall hC))
  refine h1.restrict (Ioi 0) |>.ae_eq ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  by_cases hrI : r ∈ Icc a b
  · rw [indicator_of_mem hrI]
  · rw [indicator_of_notMem hrI, hz r hr hrI]

/-- A profile smooth on `(0,∞)` and vanishing on `(0,∞) \ [a,b]` lies in `H^s((0,∞))`. -/
theorem memH1On_of_smooth_supported (s : ℕ) {g : ℝ → ℂ} (hg : ContDiffOn ℝ ∞ g (Ioi 0))
    {a b : ℝ} (ha : 0 < a) (hz : ∀ r : ℝ, 0 < r → r ∉ Icc a b → g r = 0) :
    MemH1On s (Ioi 0) g := by
  refine memH1On_of_contDiffOn isOpen_Ioi (hg.of_le (by exact_mod_cast le_top)) ?_
  intro j _
  refine memLp_Ioi_of_continuousOn_Icc (a := a) (b := b) ?_ ?_
  · have h1 : ContinuousOn (iteratedDerivWithin j g (Ioi 0)) (Ioi 0) :=
      hg.continuousOn_iteratedDerivWithin (by exact_mod_cast le_top) (uniqueDiffOn_Ioi 0)
    have h2 : ContinuousOn (iteratedDeriv j g) (Ioi 0) :=
      h1.congr fun r hr => (iteratedDerivWithin_of_isOpen isOpen_Ioi hr).symm
    exact h2.mono fun r hr => lt_of_lt_of_le ha hr.1
  · intro r hr hrI
    have hopen : IsOpen ({r : ℝ | 0 < r} ∩ (Icc a b)ᶜ) :=
      isOpen_Ioi.inter isClosed_Icc.isOpen_compl
    have hev : g =ᶠ[𝓝 r] fun _ => (0 : ℂ) := by
      filter_upwards [hopen.mem_nhds ⟨hr, hrI⟩] with t ht
      exact hz t ht.1 ht.2
    rw [hev.iteratedDeriv_eq j, iteratedDeriv_const]
    split_ifs <;> rfl

/-- Lifting the generalized eigenprofile to `Y^s_ℓ` (`thm:evans-simple`(3)). -/
theorem exists_Ysec_genEigen (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {z : ℂ}
    (hz : 0 < z.re) (G : ℝ) (hE : S.evans ℓ z G = 0) {g₁ : ℝ → ℂ}
    (hg₁ : ContDiffOn ℝ ∞ g₁ (Ioi 0)) (hsupp : ∀ r : ℝ, 0 < r → r ∉ Icc S.r₁ S.r₂ → g₁ r = 0)
    (heq : ∀ r : ℝ, 0 < r → S.LsecFn ℓ G g₁ r - z * g₁ r = S.gStar ℓ z G r) (s : ℕ) :
    ∃ h : Ysec s S.Nstar ℓ, h.fn =ᵐ[volume] Ang.ofProfile ℓ g₁ ∧
      S.Lsec s ℓ G h - z • h = S.gStarY s ℓ z G := by
  have hmem := memH1On_of_smooth_supported s hg₁ hS.r₁_pos hsupp
  have hI : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), r ∉ Icc S.ρm S.ρp → g₁ r = 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr hrI
    exact hsupp r hr fun h => hrI (Icc_r_subset_Icc_ρ S hS h)
  obtain ⟨h, hh⟩ : ∃ h : Ysec s S.Nstar ℓ, h.fn =ᵐ[volume] Ang.ofProfile ℓ g₁ :=
    exists_Ysec_ofProfile (s := s) hS.ρm_pos hS.ρm_lt_ρp (ℓ : ℤ) hmem hI
  refine ⟨h, hh, Ysec_ext_fn ?_⟩
  have hgs := ((eigen_of_evans_eq_zero S hS ℓ hℓ z hz G hE).2.2.2.2 s).1
  have hL := semigroupConstruct_Lsec S hS s (ℓ : ℤ) G h
  have hprof : Polar.angularSector h.fn ℓ =ᵐ[volume.restrict (Ioi (0 : ℝ))] g₁ :=
    angularSector_ae_of_ae_ofProfile hh
  have hL' := ofProfile_congr_ae (ℓ := (ℓ : ℤ)) (LsecFn_congr_ae S (ℓ : ℤ) G hprof)
  have hpt : (fun r => S.LsecFn ℓ G g₁ r - z * g₁ r) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      S.gStar ℓ z G := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact heq r hr
  have hfin := ofProfile_congr_ae (ℓ := (ℓ : ℤ)) hpt
  filter_upwards [Ysec_fn_sub (S.Lsec s ℓ G h) (z • h), Ysec_fn_smul z h, hL, hL', hh, hgs, hfin]
    with x h1 h2 h3 h4 h5 h6 h7
  rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, h4, h5, h6, ← h7, smul_eq_mul]
  simp only [ofProfile]
  ring

/-- `thm:evans-simple`(3), converse: `(L_ℓ - λ_*) g₁ = g_*` in `Y^0_ℓ` forces `J = 0`. -/
theorem J_eq_zero_of_genEigen (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {z : ℂ}
    (hz : 0 < z.re) (G : ℝ) (hE : S.evans ℓ z G = 0) (s : ℕ) (h : Ysec s S.Nstar ℓ)
    (hh : S.Lsec s ℓ G h - z • h = S.gStarY s ℓ z G) : S.J ℓ z G = 0 := by
  obtain ⟨T, hT⟩ : ∃ T : Ysec s S.Nstar ℓ →L[ℂ] ℂ, ∀ g : Ysec s S.Nstar ℓ,
      T g = ∫ r in Ioi (0 : ℝ), Polar.angularSector g.fn ℓ r *
        (S.psi ℓ z G (Real.log r) * S.Mres ℓ z G r) * (r : ℂ) :=
    exists_profile_pairing (ρp := S.ρp) s hS.ρm_pos (ℓ : ℤ) (continuousOn_X S hS ℓ hℓ hz G)
  have hT' : ∀ g : Ysec s S.Nstar ℓ, T g = ∫ r in Ioi (0 : ℝ), Polar.angularSector g.fn ℓ r *
      S.psi ℓ z G (Real.log r) * S.Mres ℓ z G r * (r : ℂ) := by
    intro g
    rw [hT g]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only
    ring
  have hTL : T (S.Lsec s ℓ G h) = z * T h := by
    rw [hT', hT', integral_Lsec_eq S hS s ℓ hℓ hz G hE h]
  have hTg : T (S.gStarY s ℓ z G) = S.J ℓ z G := by
    have hfn := ((eigen_of_evans_eq_zero S hS ℓ hℓ z hz G hE).2.2.2.2 s).1
    rw [hT', J]
    refine integral_congr_ae ?_
    filter_upwards [angularSector_ae_of_ae_ofProfile hfn] with r hr
    rw [hr]
  rw [← hTg, ← hh, map_sub, map_smul, hTL, smul_eq_mul, sub_self]

end NonUniqueEuler.EvansSimpleAux
