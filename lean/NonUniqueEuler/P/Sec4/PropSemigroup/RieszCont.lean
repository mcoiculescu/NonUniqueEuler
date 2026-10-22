import Mathlib.Analysis.Normed.Operator.Bilinear
import NonUniqueEuler.Defs.Sec4.Eigendata
import NonUniqueEuler.I.Sec4.Eigendata
import NonUniqueEuler.I.Sec4.Uniform
import NonUniqueEuler.I.Sec4.PropU
import NonUniqueEuler.I.Infra.SectorSpace.Projection
import NonUniqueEuler.I.Infra.SectorSpace.Lower
import NonUniqueEuler.I.Infra.AngularFourier.Sector
import NonUniqueEuler.I.Infra.AngularFourier.SectorL2
import NonUniqueEuler.I.Infra.AngularFourier.Symmetry
import NonUniqueEuler.H.Sec4.PropSemigroup.RieszCont.Basic

/-!
# Proof: continuity in `G` of the sector Riesz projections at `λ_*(G)` (step of `prop:semigroup`)

Proof of `I/Sec4/PropSemigroup/RieszCont.lean` (`04_ring.tex:1466-1484`, restructuring R2).
With `n = n_*(G)`, `P_ℓ = secProj s N ℓ`, `C` complex conjugation on `Y^s(N)` (`cjY`):
* `n_*(G) = 6e^{-3(ξL-ξR)}/|pin_3[φ_*(G)]|` is continuous (`pinPhi_eq`, `propU_b`);
* `g_* e^{3iθ} = n P_3 φ_*(G)` and `conj(g_*) e^{-3iθ} = n P_{-3}(C φ_*(G))` (`gStarY_eq`,
  `gStarBarY_eq`), continuous since `φ_*` is (`uniform_continuous`);
* with `f(G) = n⁻¹ ℓ_*(G) ∘ (Y^s → Y^0)`, continuous since `ℓ_*(G)` is into `(Y^0)^*`:
  `ellStarY = f(G) ∘ inclSec` and `ellStarBarY h = conj (f(G)(C h))` (`ellStarY_eq`,
  `ellStarBarY_eq`; `angularSector_conj`);
* `rankOneProj` is continuous in both arguments (`smulRightL`).
-/

noncomputable section

open MeasureTheory Set ComplexConjugate

namespace NonUniqueEuler

namespace Sect.RieszContH

open Sob Ang Eig RingData

/-! ### Generic lemmas -/

/-- The rank-one operator `x ↦ f(x) g` depends continuously on `(f, g)`. -/
theorem continuousOn_rankOneProj {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {f : ℝ → X →L[ℂ] ℂ} {g : ℝ → X} {t : Set ℝ} (hf : ContinuousOn f t)
    (hg : ContinuousOn g t) : ContinuousOn (fun G => Dunford.rankOneProj (f G) (g G)) t := by
  have h1 : ContinuousOn (fun G => ContinuousLinearMap.smulRightL ℂ X X (f G)) t :=
    (ContinuousLinearMap.smulRightL ℂ X X).continuous.comp_continuousOn hf
  exact h1.clm_apply hg

/-- `ℓ_*` only sees its argument a.e. on `(0, ∞)`. -/
theorem ellStar_congr (S : SectorSetting) (ℓ : ℕ) (z : ℂ) (G : ℝ) {g₁ g₂ : ℝ → ℂ}
    (h : g₁ =ᵐ[volume.restrict (Ioi (0 : ℝ))] g₂) : S.ellStar ℓ z G g₁ = S.ellStar ℓ z G g₂ := by
  unfold SectorSetting.ellStar
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [h] with r hr
  rw [hr]

/-- The functional `h ↦ conj (f (conj h))` on `Y^s_ℓ(K)`, for `f` on `Y^s(K)`. -/
def cjDual (s : ℕ) (K : Set ℂ) (ℓ : ℤ) (f : Y s K →L[ℂ] ℂ) : Ysec s K ℓ →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun h => conj (f (cjY s K (inclSec s K ℓ h)))
      map_add' := fun h₁ h₂ => by
        simp only [map_add, cjY_add]
      map_smul' := fun c h => by
        simp only [map_smul, cjY_smul, smul_eq_mul, map_mul, Complex.conj_conj,
          RingHom.id_apply] }
    (‖f‖ * ‖inclSec s K ℓ‖) fun h => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Complex.norm_conj]
      calc ‖f (cjY s K (inclSec s K ℓ h))‖ ≤ ‖f‖ * ‖cjY s K (inclSec s K ℓ h)‖ :=
            f.le_opNorm _
        _ = ‖f‖ * ‖inclSec s K ℓ h‖ := by rw [norm_cjY]
        _ ≤ ‖f‖ * (‖inclSec s K ℓ‖ * ‖h‖) := by
            gcongr
            exact (inclSec s K ℓ).le_opNorm h
        _ = ‖f‖ * ‖inclSec s K ℓ‖ * ‖h‖ := by ring

theorem cjDual_apply {s : ℕ} {K : Set ℂ} {ℓ : ℤ} (f : Y s K →L[ℂ] ℂ) (h : Ysec s K ℓ) :
    cjDual s K ℓ f h = conj (f (cjY s K (inclSec s K ℓ h))) := rfl

theorem cjDual_add {s : ℕ} {K : Set ℂ} {ℓ : ℤ} (f f' : Y s K →L[ℂ] ℂ) :
    cjDual s K ℓ (f + f') = cjDual s K ℓ f + cjDual s K ℓ f' := by
  ext h
  simp only [cjDual_apply, add_apply, map_add]

theorem norm_cjDual_le {s : ℕ} {K : Set ℂ} {ℓ : ℤ} (f : Y s K →L[ℂ] ℂ) :
    ‖cjDual s K ℓ f‖ ≤ ‖inclSec s K ℓ‖ * ‖f‖ := by
  rw [mul_comm]
  exact LinearMap.mkContinuous_norm_le _ (by positivity) _

theorem continuous_cjDual (s : ℕ) (K : Set ℂ) (ℓ : ℤ) : Continuous (cjDual s K ℓ) :=
  AddMonoidHomClass.continuous_of_bound (AddMonoidHom.mk' (cjDual s K ℓ) cjDual_add)
    ‖inclSec s K ℓ‖ fun f => norm_cjDual_le f

/-! ### The eigendata -/

variable {χ : ℝ → ℝ}

/-- `n_*(G) = 6e^{-3(ξL-ξR)}/|pin_3[φ_*(G)]|` is continuous on `[0,G₁]`. -/
theorem nstar_continuousOn (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) :
    ContinuousOn (fun G => nstar χ G) (Icc 0 Gbar) := by
  obtain ⟨-, hpin, -, -, -, -, hpos⟩ := propU_b χ hχ hN
  have heq : ∀ G ∈ Icc (0 : ℝ) Gbar,
      6 * Real.exp (-3 * (ξL - ξR)) / ‖pinPhi χ G‖ = nstar χ G := by
    intro G hG
    have hn := (eigendata_phi χ hχ hN hG).1
    have he : 0 < 6 * Real.exp (-3 * (ξL - ξR)) := by positivity
    rw [pinPhi_eq χ hχ hN hG, Complex.norm_real, Real.norm_eq_abs, abs_neg,
      abs_of_pos (div_pos he hn)]
    field_simp
  exact (continuousOn_const.div hpin fun G hG => (hpos G hG).2.1.ne').congr
    fun G hG => (heq G hG).symm

theorem nstarC_continuousOn (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) :
    ContinuousOn (fun G => ((nstar χ G : ℝ) : ℂ)) (Icc 0 Gbar) :=
  Complex.continuous_ofReal.comp_continuousOn (nstar_continuousOn hχ hN)

theorem nstarC_ne_zero (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) {G : ℝ}
    (hG : G ∈ Icc (0 : ℝ) Gbar) : ((nstar χ G : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (eigendata_phi χ hχ hN hG).1.ne'

/-- `P_3 φ_* = n_*⁻¹ g_* e^{3iθ}` (pointwise). -/
theorem sectorProj_phi (G : ℝ) :
    sectorProj 3 (phi χ G) = fun x => ((nstar χ G : ℝ) : ℂ)⁻¹ * ofProfile 3 (gstar χ G) x := by
  have h := sectorProj_radial_mul 3 (fun _ => ((nstar χ G : ℝ) : ℂ)⁻¹) (ofProfile 3 (gstar χ G))
  beta_reduce at h
  change sectorProj 3 (fun x => ((nstar χ G : ℝ) : ℂ)⁻¹ * ofProfile 3 (gstar χ G) x) = _
  rw [h]
  simp only [sectorProj_ofProfile, ↓reduceIte]

theorem secProj_phiY_fn (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) {G : ℝ}
    (hG : G ∈ Icc (0 : ℝ) Gbar) (s : ℕ) :
    (secProj s annN 3 (phiY χ s G)).fn =ᵐ[volume]
      fun x => ((nstar χ G : ℝ) : ℂ)⁻¹ * ofProfile 3 (gstar χ G) x := by
  have h1 := (secProj_spec (s := s) isRotInvariant_annN 3).1 (phiY χ s G)
  have h2 := sectorProj_congr_ae 3 ((eigendata_phi χ hχ hN hG).2.2.1 s).1
  filter_upwards [h1, h2] with x hx1 hx2
  rw [hx1, hx2, sectorProj_phi]

/-- `g_* e^{3iθ} = n_* P_3 φ_*` in `Y^s_3(N)`. -/
theorem gStarY_eq (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) {G : ℝ}
    (hG : G ∈ Icc (0 : ℝ) Gbar) (s : ℕ) :
    (ringPhiSetting χ).gStarY s 3 (lam χ G) G =
      ((nstar χ G : ℝ) : ℂ) • secProj s annN 3 (phiY χ s G) := by
  have hn := nstarC_ne_zero hχ hN hG
  have hfn : (((nstar χ G : ℝ) : ℂ) • secProj s annN 3 (phiY χ s G)).fn =ᵐ[volume]
      ofProfile ((3 : ℕ) : ℤ) ((ringPhiSetting χ).gStar 3 (lam χ G) G) := by
    filter_upwards [Ysec_fn_smul ((nstar χ G : ℝ) : ℂ) (secProj s annN 3 (phiY χ s G)),
      secProj_phiY_fn hχ hN hG s] with x h1 h2
    rw [h1, Pi.smul_apply, h2, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]
    rfl
  have hspec := toYsec_spec (s := s) (K := (ringPhiSetting χ).Nstar) (ℓ := ((3 : ℕ) : ℤ)) ⟨_, hfn⟩
  exact Ysec_ext_fn (hspec.trans hfn.symm)

/-- `conj(g_*) e^{-3iθ} = n_* P_{-3}(conj φ_*)` in `Y^s_{-3}(N)`. -/
theorem gStarBarY_eq (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) {G : ℝ}
    (hG : G ∈ Icc (0 : ℝ) Gbar) (s : ℕ) :
    (ringPhiSetting χ).gStarBarY s 3 (lam χ G) G =
      ((nstar χ G : ℝ) : ℂ) • secProj s annN (-3) (cjY s annN (phiY χ s G)) := by
  have hn := nstarC_ne_zero hχ hN hG
  have hc : (fun x => conj ((phiY χ s G).fn x)) =ᵐ[volume] fun x => conj (phi χ G x) := by
    filter_upwards [((eigendata_phi χ hχ hN hG).2.2.1 s).1] with x hx
    rw [hx]
  have h1 := (secProj_spec (s := s) isRotInvariant_annN (-3)).1 (cjY s annN (phiY χ s G))
  have h2 := sectorProj_congr_ae (-3) ((cjY_fn (phiY χ s G)).trans hc)
  have hfn : (((nstar χ G : ℝ) : ℂ) • secProj s annN (-3) (cjY s annN (phiY χ s G))).fn
      =ᵐ[volume] ofProfile (-((3 : ℕ) : ℤ))
        (fun r => conj ((ringPhiSetting χ).gStar 3 (lam χ G) G r)) := by
    filter_upwards [Ysec_fn_smul ((nstar χ G : ℝ) : ℂ)
      (secProj s annN (-3) (cjY s annN (phiY χ s G))), h1, h2] with x hx1 hx2 hx3
    rw [hx1, Pi.smul_apply, hx2, hx3, sectorProj_conj, sectorProj_phi, smul_eq_mul, map_mul,
      map_inv₀, Complex.conj_ofReal, ← mul_assoc, mul_inv_cancel₀ hn, one_mul, conj_ofProfile]
    rfl
  have hspec := toYsec_spec (s := s) (K := (ringPhiSetting χ).Nstar)
    (ℓ := -((3 : ℕ) : ℤ)) ⟨_, hfn⟩
  exact Ysec_ext_fn (hspec.trans hfn.symm)

/-- `f(G) = n_*⁻¹ ℓ_*(G) ∘ (Y^s(N) → Y^0(N))`. -/
def fStar (χ : ℝ → ℝ) (s : ℕ) (G : ℝ) : Y s annN →L[ℂ] ℂ :=
  ((nstar χ G : ℝ) : ℂ)⁻¹ • (ell χ 0 G).comp (lowerY 0 s annN)

theorem fStar_apply (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) {G : ℝ}
    (hG : G ∈ Icc (0 : ℝ) Gbar) (s : ℕ) (w : Y s annN) :
    fStar χ s G w = (ringPhiSetting χ).ellStar 3 (lam χ G) G (Polar.angularSector w.fn 3) := by
  have hn := nstarC_ne_zero hχ hN hG
  have hell := ell_spec_of_exists (exists_ell χ hχ hN hG 0)
  have hlow := (lowerY_spec (Nat.zero_le s) annN).1 w
  change ((nstar χ G : ℝ) : ℂ)⁻¹ * ell χ 0 G (lowerY 0 s annN w) = _
  rw [hell]
  unfold ellFn
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  exact ellStar_congr _ _ _ _ (angularSector_congr_ae hlow 3)

theorem fStar_continuousOn (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) (s : ℕ) :
    ContinuousOn (fun G => fStar χ s G) (Icc 0 Gbar) := by
  have hnC : ContinuousOn (fun G => ((nstar χ G : ℝ) : ℂ)⁻¹) (Icc 0 Gbar) :=
    (nstarC_continuousOn hχ hN).inv₀ fun G hG => nstarC_ne_zero hχ hN hG
  have hell := (uniform_continuous χ hχ hN).2.2.1
  exact hnC.smul (hell.clm_comp continuousOn_const)

/-- `ℓ_*` on `Y^s_3(N)` is `f(G) ∘ inclSec`. -/
theorem ellStarY_eq (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) {G : ℝ}
    (hG : G ∈ Icc (0 : ℝ) Gbar) (s : ℕ) :
    (ringPhiSetting χ).ellStarY s 3 (lam χ G) G = (fStar χ s G).comp (inclSec s annN 3) := by
  have hT : ∃ T : Ysec s (ringPhiSetting χ).Nstar ((3 : ℕ) : ℤ) →L[ℂ] ℂ,
      ∀ g : Ysec s (ringPhiSetting χ).Nstar ((3 : ℕ) : ℤ),
      T g = (ringPhiSetting χ).ellStar 3 (lam χ G) G (Polar.angularSector g.fn ((3 : ℕ) : ℤ)) :=
    ⟨(fStar χ s G).comp (inclSec s annN 3), fun g => fStar_apply hχ hN hG s (inclSec s annN 3 g)⟩
  refine ContinuousLinearMap.ext fun g => ?_
  rw [SectorSetting.ellStarY_spec_of_exists _ s 3 _ G hT g]
  exact (fStar_apply hχ hN hG s (inclSec s annN 3 g)).symm

theorem cjDual_fStar_apply (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) {G : ℝ}
    (hG : G ∈ Icc (0 : ℝ) Gbar) (s : ℕ) (h : Ysec s annN (-((3 : ℕ) : ℤ))) :
    cjDual s annN (-((3 : ℕ) : ℤ)) (fStar χ s G) h =
      (ringPhiSetting χ).ellStarBar 3 (lam χ G) G
        (Polar.angularSector h.fn (-((3 : ℕ) : ℤ))) := by
  rw [cjDual_apply, fStar_apply hχ hN hG s]
  unfold SectorSetting.ellStarBar
  congr 1
  apply ellStar_congr
  have hc : (cjY s annN (inclSec s annN _ h)).fn =ᵐ[volume] fun x => conj (h.fn x) :=
    cjY_fn (inclSec s annN _ h)
  filter_upwards [angularSector_congr_ae hc 3] with r hr
  rw [hr]
  have := angularSector_conj h.fn (-((3 : ℕ) : ℤ)) r
  rw [neg_neg] at this
  exact this

/-- `h ↦ conj(ℓ_*(conj h_{-3}))` on `Y^s_{-3}(N)` is `cjDual (f(G))`. -/
theorem ellStarBarY_eq (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) {G : ℝ}
    (hG : G ∈ Icc (0 : ℝ) Gbar) (s : ℕ) :
    (ringPhiSetting χ).ellStarBarY s 3 (lam χ G) G =
      cjDual s annN (-((3 : ℕ) : ℤ)) (fStar χ s G) := by
  have hT : ∃ T : Ysec s (ringPhiSetting χ).Nstar (-((3 : ℕ) : ℤ)) →L[ℂ] ℂ,
      ∀ g : Ysec s (ringPhiSetting χ).Nstar (-((3 : ℕ) : ℤ)),
      T g = (ringPhiSetting χ).ellStarBar 3 (lam χ G) G
        (Polar.angularSector g.fn (-((3 : ℕ) : ℤ))) :=
    ⟨cjDual s annN (-((3 : ℕ) : ℤ)) (fStar χ s G), fun g => cjDual_fStar_apply hχ hN hG s g⟩
  refine ContinuousLinearMap.ext fun h => ?_
  rw [SectorSetting.ellStarBarY_spec_of_exists _ s 3 _ G hT h]
  exact (cjDual_fStar_apply hχ hN hG s h).symm

end Sect.RieszContH

namespace Eig

open RingData Sect Sect.RieszContH

/-- **Continuity of the sector Riesz projections** (step of `prop:semigroup`,
`04_ring.tex:1466-1484`, R2): for every `s`, `G ↦ rieszSec s 3 λ_*(G) G` on `Y^s_3(N)` and
`G ↦ rieszSecBar s 3 λ_*(G) G` on `Y^s_{-3}(N)` are continuous on `[0,G₁]` in the operator norm. -/
theorem rieszSec_continuousOn (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ)
    (hN : NumericalHypothesis χ) (s : ℕ) :
    ContinuousOn (fun G => (ringPhiSetting χ).rieszSec s 3 (lam χ G) G) (Icc 0 Gbar) ∧
      ContinuousOn (fun G => (ringPhiSetting χ).rieszSecBar s 3 (lam χ G) G) (Icc 0 Gbar) := by
  have hphi := ((uniform_continuous χ hχ hN).2.1 s).1
  have hnc := nstarC_continuousOn hχ hN
  have hgS : ContinuousOn (fun G => (ringPhiSetting χ).gStarY s 3 (lam χ G) G) (Icc 0 Gbar) :=
    (hnc.smul ((secProj s annN 3).continuous.comp_continuousOn hphi)).congr
      fun G hG => gStarY_eq hχ hN hG s
  have heS : ContinuousOn (fun G => (ringPhiSetting χ).ellStarY s 3 (lam χ G) G) (Icc 0 Gbar) :=
    ((fStar_continuousOn hχ hN s).clm_comp continuousOn_const).congr
      fun G hG => ellStarY_eq hχ hN hG s
  have hgB : ContinuousOn (fun G => (ringPhiSetting χ).gStarBarY s 3 (lam χ G) G)
      (Icc 0 Gbar) :=
    (hnc.smul ((secProj s annN (-3)).continuous.comp_continuousOn
      (continuous_cjY.comp_continuousOn hphi))).congr fun G hG => gStarBarY_eq hχ hN hG s
  have heB : ContinuousOn (fun G => (ringPhiSetting χ).ellStarBarY s 3 (lam χ G) G)
      (Icc 0 Gbar) :=
    ((continuous_cjDual s annN _).comp_continuousOn (fStar_continuousOn hχ hN s)).congr
      fun G hG => ellStarBarY_eq hχ hN hG s
  exact ⟨continuousOn_rankOneProj heS hgS, continuousOn_rankOneProj heB hgB⟩

end Eig

end NonUniqueEuler
