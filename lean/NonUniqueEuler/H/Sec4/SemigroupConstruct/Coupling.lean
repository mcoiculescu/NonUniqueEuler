import NonUniqueEuler.H.Sec4.SemigroupConstruct.SectorOps
import NonUniqueEuler.I.Sec2.BSBasic
import NonUniqueEuler.I.Infra.ConvMinkowski.Young
import NonUniqueEuler.I.Sec4.Sector
import NonUniqueEuler.I.Infra.SectorSpace.DirectSum
import NonUniqueEuler.I.Infra.SectorSpace.Projection
import NonUniqueEuler.I.Infra.SectorSpace.Lower
import NonUniqueEuler.I.Infra.AngularFourier.SectorL2
import NonUniqueEuler.I.Infra.AngularFourier.Parseval
import NonUniqueEuler.I.Infra.AngularFourier.Sector

/-!
# Helpers for `lem:semigroup-construct`(1): the coupling operator `𝒦` on `Y^s`

Helper file of `P/Sec4/SemigroupConstruct.lean` (fully proved). Manuscript `04_ring.tex:996-1000`
(end of the proof of (1)).

* `memLp_couplingFn`: `𝒦w = -(K_BS * w)·∇ω̄ ∈ L²` for `w ∈ L²` supported in `N_*`
  (`|𝒦w| ≤ ‖∇ω̄‖_∞ 1_{B_R} (|K_BS| * |w|)`, Young on a ball, `Conv.eLpNorm_convAbs_ball_le`, and
  `∫_{B_ρ}|K_BS| = ρ`, `BS.integral_norm_biotSavartKernel_ball`).
* `ae_eq_of_sectorProj`: two `L²` functions with a.e. equal sector projections are a.e. equal
  (`Ang.ae_eq_zero_of_sectorProj`).
* `exists_KY`: `𝒦 = ⊕_ℓ k_ℓ𝒢_ℓ` (`sectorSum` of the uniformly bounded `S.Ksec s ℓ`); its function
  is `𝒦 w` because both have the same sector projections (`lem:sector`(2), `couplingFn_sector`).
-/

noncomputable section

open MeasureTheory Set Real Filter Metric
open scoped ContDiff

namespace NonUniqueEuler.SGC

open Sob Sect Ang SectorSetting

/-! ### `𝒦w ∈ L²` -/

theorem measurable_bsKernel : Measurable biotSavartKernel := by
  unfold biotSavartKernel
  fun_prop

theorem couplingFn_congr_ae (S : SectorSetting) {f g : ℂ → ℂ} (hfg : f =ᵐ[volume] g) :
    S.couplingFn f = S.couplingFn g := by
  funext x
  simp only [couplingFn]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hfg] with y hy
  rw [hy]

theorem memLp_couplingFn {S : SectorSetting} (hS : S.Valid) {f : ℂ → ℂ}
    (hf : MemLp f 2 volume) (hfs : ∀ᵐ y ∂volume, y ∉ S.Nstar → f y = 0) :
    MemLp (S.couplingFn f) 2 volume := by
  have hcont : Continuous (fderiv ℝ S.om) := hS.contDiff.continuous_fderiv (by simp)
  have hcomp : HasCompactSupport (fderiv ℝ S.om) := hS.hasCompactSupport.fderiv (𝕜 := ℝ)
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hcomp
  obtain ⟨R, hR⟩ := hcomp.isCompact.isBounded.subset_closedBall 0
  set R' := max R 0 + 1 with hR'
  have hR'pos : 0 < R' := by positivity
  have hzero : ∀ x : ℂ, x ∉ ball (0 : ℂ) R' → fderiv ℝ S.om x = 0 := by
    intro x hx
    refine image_eq_zero_of_notMem_tsupport fun hxt => hx ?_
    have := hR hxt
    rw [mem_closedBall, dist_zero_right] at this
    rw [mem_ball, dist_zero_right]
    linarith [le_max_left R 0]
  set ρ := S.ρp + 1 with hρ
  have hsupp : ∀ᵐ y ∂volume, ρ ≤ ‖y‖ → f y = 0 := by
    filter_upwards [hfs] with y hy hyρ
    exact hy fun h => by linarith [h.2]
  -- measurability
  have hfm : AEStronglyMeasurable f volume := hf.aestronglyMeasurable
  obtain ⟨f', hf'm, hff'⟩ := hfm
  have hcf : S.couplingFn f = S.couplingFn f' := couplingFn_congr_ae S hff'
  have hmeas : AEStronglyMeasurable (S.couplingFn f) volume := by
    rw [hcf]
    have h1 : StronglyMeasurable fun p : ℂ × ℂ =>
        ((fderiv ℝ S.om p.1 (biotSavartKernel (p.1 - p.2)) : ℝ) : ℂ) * f' p.2 := by
      have ha : Continuous fun p : (ℂ →L[ℝ] ℝ) × ℂ => p.1 p.2 :=
        isBoundedBilinearMap_apply.continuous
      have hb : Measurable fun p : ℂ × ℂ => (fderiv ℝ S.om p.1, biotSavartKernel (p.1 - p.2)) :=
        (hcont.measurable.comp measurable_fst).prodMk
          (measurable_bsKernel.comp (measurable_fst.sub measurable_snd))
      have hc : Measurable fun p : ℂ × ℂ =>
          ((fderiv ℝ S.om p.1 (biotSavartKernel (p.1 - p.2)) : ℝ) : ℂ) :=
        Complex.measurable_ofReal.comp (ha.measurable.comp hb)
      exact hc.stronglyMeasurable.mul (hf'm.comp_measurable measurable_snd)
    exact (h1.integral_prod_right' (ν := volume)).aestronglyMeasurable.neg
  refine ⟨hmeas, ?_⟩
  -- the bound
  have hpt : ∀ x : ℂ, ‖S.couplingFn f x‖ₑ ≤
      ENNReal.ofReal C * (ball (0 : ℂ) R').indicator (Conv.convAbs biotSavartKernel f) x := by
    intro x
    have h1 : ‖S.couplingFn f x‖ₑ ≤ ‖fderiv ℝ S.om x‖ₑ * Conv.convAbs biotSavartKernel f x := by
      simp only [couplingFn, enorm_neg, Conv.convAbs]
      refine (enorm_integral_le_lintegral_enorm _).trans ?_
      rw [← lintegral_const_mul' _ _ enorm_ne_top]
      refine lintegral_mono fun y => ?_
      rw [enorm_mul, ← mul_assoc]
      gcongr
      rw [← ofReal_norm_eq_enorm, Complex.norm_real, ofReal_norm_eq_enorm]
      exact (fderiv ℝ S.om x).le_opENorm _
    by_cases hx : x ∈ ball (0 : ℂ) R'
    · rw [indicator_of_mem hx]
      refine h1.trans ?_
      gcongr
      rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hC x)
    · rw [indicator_of_notMem hx, mul_zero]
      refine h1.trans ?_
      rw [hzero x hx]
      refine le_of_eq ?_
      rw [← ofReal_norm_eq_enorm, norm_zero, ENNReal.ofReal_zero, zero_mul]
  have hK : AEStronglyMeasurable biotSavartKernel volume :=
    measurable_bsKernel.aestronglyMeasurable
  have hY := Conv.eLpNorm_convAbs_ball_le hK hf.aestronglyMeasurable (p := 2) (by norm_num) (R := R') hsupp
  have hball := (BS.integral_norm_biotSavartKernel_ball (ρ := R' + ρ) (by
    have := hS.ρm_pos; have := hS.ρm_lt_ρp; have := le_max_right R 0; linarith)).2.2
  calc eLpNorm (S.couplingFn f) 2 volume
      ≤ ENNReal.ofReal C * eLpNorm ((ball (0 : ℂ) R').indicator
          (Conv.convAbs biotSavartKernel f)) 2 volume := by
        have := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' (μ := volume) (c := C.toNNReal)
          (f := S.couplingFn f) (g := (ball (0 : ℂ) R').indicator (Conv.convAbs biotSavartKernel f))
          (Eventually.of_forall fun x => by rw [enorm_eq_self]; exact hpt x) 2
        exact this
    _ = ENNReal.ofReal C * eLpNorm (Conv.convAbs biotSavartKernel f) 2
          (volume.restrict (ball (0 : ℂ) R')) := by
        rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball]
    _ ≤ ENNReal.ofReal C * ((∫⁻ z in ball (0 : ℂ) (R' + ρ), ‖biotSavartKernel z‖ₑ) *
          eLpNorm f 2 volume) := by gcongr
    _ < ⊤ := by
        rw [hball]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.2)

/-! ### Uniqueness from the sector projections -/

theorem sectorProj_sub_ae {f g : ℂ → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (ℓ : ℤ) : sectorProj ℓ (f - g) =ᵐ[volume] sectorProj ℓ f - sectorProj ℓ g := by
  have h1 := sectorProjL_spec ℓ (hf.toLp f - hg.toLp g)
  have h2 := sectorProjL_spec ℓ (hf.toLp f)
  have h3 := sectorProjL_spec ℓ (hg.toLp g)
  have h4 : sectorProj ℓ ((hf.toLp f - hg.toLp g : Lp ℂ 2 volume) : ℂ → ℂ) =ᵐ[volume]
      sectorProj ℓ (f - g) :=
    sectorProj_congr_ae ℓ ((Lp.coeFn_sub _ _).trans (hf.coeFn_toLp.sub hg.coeFn_toLp))
  have h5 := sectorProj_congr_ae ℓ hf.coeFn_toLp
  have h6 := sectorProj_congr_ae ℓ hg.coeFn_toLp
  have h7 := Lp.coeFn_sub (sectorProjL ℓ (hf.toLp f)) (sectorProjL ℓ (hg.toLp g))
  rw [map_sub] at h1
  filter_upwards [h1, h2, h3, h4, h5, h6, h7] with x hx1 hx2 hx3 hx4 hx5 hx6 hx7
  rw [← hx4, ← hx1, hx7, Pi.sub_apply, hx2, hx3, hx5, hx6, Pi.sub_apply]

theorem ae_eq_of_sectorProj {f g : ℂ → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (h : ∀ ℓ : ℤ, sectorProj ℓ f =ᵐ[volume] sectorProj ℓ g) : f =ᵐ[volume] g := by
  have h0 := ae_eq_zero_of_sectorProj (hf.sub hg) fun ℓ => by
    filter_upwards [sectorProj_sub_ae hf hg ℓ, h ℓ] with x hx1 hx2
    rw [hx1, Pi.sub_apply, hx2, sub_self, Pi.zero_apply]
  filter_upwards [h0] with x hx
  exact sub_eq_zero.1 hx

/-! ### Angular sectors of sector projections -/

theorem angularSector_sectorProj (ℓ : ℤ) (f : ℂ → ℂ) {r : ℝ} (hr : 0 < r) :
    Polar.angularSector (sectorProj ℓ f) ℓ r = Polar.angularSector f ℓ r := by
  have h : Polar.angularSector (sectorProj ℓ f) ℓ r =
      Polar.angularSector (ofProfile ℓ (Polar.angularSector f ℓ)) ℓ r := by
    simp only [Polar.angularSector]
    congr 1
    refine intervalIntegral.integral_congr fun θ _ => ?_
    have hx : (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hr.ne') (Complex.exp_ne_zero _)
    rw [sectorProj_eq_angularSector ℓ f hx, ofProfile]
  rw [h, angularSector_ofProfile ℓ _ hr]

theorem KsecFn_congr_ae (S : SectorSetting) (ℓ : ℤ) {h h' : ℝ → ℂ}
    (hh : h =ᵐ[volume.restrict (Ioi 0)] h') : S.KsecFn ℓ h = S.KsecFn ℓ h' := by
  funext r
  simp only [KsecFn, green_congr_ae hh r]

/-- The profile of `P_ℓ w` is the `ℓ`-th angular sector of `w`. -/
theorem angularSector_secProj {S : SectorSetting} {s : ℕ} (ℓ : ℤ) (w : Y s S.Nstar) :
    Polar.angularSector (secProj s S.Nstar ℓ w).fn ℓ =ᵐ[volume.restrict (Ioi 0)]
      Polar.angularSector w.fn ℓ := by
  filter_upwards [angularSector_congr_ae ((secProj_spec S.isRotInvariant_Nstar ℓ).1 w) ℓ,
    ae_restrict_mem measurableSet_Ioi] with r hr hr0
  rw [hr, angularSector_sectorProj ℓ _ hr0]

/-! ### The coupling operator `𝒦` on `Y^s` -/

theorem exists_KY (S : SectorSetting) (hS : S.Valid) (s : ℕ) :
    ∃ T : Y s S.Nstar →L[ℂ] Y s S.Nstar, ∀ w : Y s S.Nstar,
      (T w).fn =ᵐ[volume] S.couplingFn w.fn := by
  obtain ⟨C, -, hK⟩ := exists_norm_Ksec_le S hS s
  refine ⟨sectorSum s S.Nstar (fun ℓ => S.Ksec s ℓ), fun w => ?_⟩
  have hc : MemLp (S.couplingFn w.fn) 2 volume := memLp_couplingFn hS (y_memLp w) (y_supp w)
  refine ae_eq_of_sectorProj (y_memLp _) hc fun ℓ => ?_
  have hP : secProj s S.Nstar ℓ (sectorSum s S.Nstar (fun ℓ => S.Ksec s ℓ) w) =
      S.Ksec s ℓ (secProj s S.Nstar ℓ w) :=
    secProj_sectorSum (A := fun ℓ => S.Ksec s ℓ) hS.ρm_pos hS.ρm_lt_ρp hK ℓ w
  -- the coupling side
  set w0 := lowerY 0 s S.Nstar w with hw0
  have hw0fn : w0.fn =ᵐ[volume] w.fn := (lowerY_spec (Nat.zero_le s) S.Nstar).1 w
  have hcs := couplingFn_sector S hS w0 ℓ
  rw [couplingFn_congr_ae S hw0fn,
    KsecFn_congr_ae S ℓ (angularSector_congr_ae hw0fn ℓ)] at hcs
  have h1 := (secProj_spec (s := s) S.isRotInvariant_Nstar ℓ).1
    (sectorSum s S.Nstar (fun ℓ => S.Ksec s ℓ) w)
  rw [hP] at h1
  have h2 := Ksec_spec S hS s ℓ (secProj s S.Nstar ℓ w)
  rw [KsecFn_congr_ae S ℓ (angularSector_secProj ℓ w)] at h2
  filter_upwards [h1, h2, hcs] with x hx1 hx2 hx3
  rw [← hx1, hx2, hx3]

theorem KY_spec (S : SectorSetting) (hS : S.Valid) (s : ℕ) (w : Y s S.Nstar) :
    (S.KY s w).fn =ᵐ[volume] S.couplingFn w.fn :=
  KY_spec_of_exists S s (exists_KY S hS s) w

end NonUniqueEuler.SGC
