import NonUniqueEuler.H.Sec4.Sector.SecBasic
import NonUniqueEuler.H.Sec4.Sector.Transport
import NonUniqueEuler.I.Sec2.BSBasic
import NonUniqueEuler.I.Infra.ConvMinkowski.Young
import NonUniqueEuler.I.Infra.AngularFourier.Sector
import NonUniqueEuler.I.Infra.AngularFourier.Derivatives
import NonUniqueEuler.I.Sec4.Sector.CouplingProj
import NonUniqueEuler.I.Sec4.Sector.CouplingOfProfile

/-!
# Helper for `lem:sector`(2): the coupling term `𝒦w = -(K_BS * w)·∇ω̄`

Helper file of `P/Sec4/Sector.lean` (fully proved, modulo the interface files
`I/Sec4/Sector/CouplingProj.lean` and `I/Sec4/Sector/CouplingOfProfile.lean`).

* `memLp_couplingFn`: `𝒦w ∈ L²` for `w ∈ L²` supported in `N_*` (copied from
  `H/Sec4/SemigroupConstruct/Coupling.lean`, which no other proof may import).
* `couplingFn_im_eq_zero`: `𝒦` maps real functions to real functions (`ω̄`, `K_BS` real).
* `couplingFn_sector_fn`: `P_ℓ(𝒦w) = (k_ℓ𝒢_ℓ w_ℓ)(r)e^{iℓθ}` for `w ∈ H^k` supported in `N_*`
  (`sectorProj_couplingFn`, then `P_ℓ w = w_ℓ(r)e^{iℓθ}` off the origin, then
  `couplingFn_ofProfile`).
-/

noncomputable section

open MeasureTheory Set Real Filter Metric
open scoped ContDiff ENNReal

namespace NonUniqueEuler.SectorH

open Sob Sect Ang SectorSetting

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
      rw [← ofReal_norm, Complex.norm_real, ofReal_norm]
      exact (fderiv ℝ S.om x).le_opENorm _
    by_cases hx : x ∈ ball (0 : ℂ) R'
    · rw [indicator_of_mem hx]
      refine h1.trans ?_
      gcongr
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hC x)
    · rw [indicator_of_notMem hx, mul_zero]
      refine h1.trans ?_
      rw [hzero x hx]
      refine le_of_eq ?_
      rw [← ofReal_norm, norm_zero, ENNReal.ofReal_zero, zero_mul]
  have hK : AEStronglyMeasurable biotSavartKernel volume :=
    measurable_bsKernel.aestronglyMeasurable
  have hY := Conv.eLpNorm_convAbs_ball_le hK hf.aestronglyMeasurable (p := 2) (by norm_num)
    (R := R') hsupp
  have hball := (BS.integral_norm_biotSavartKernel_ball (ρ := R' + ρ) (by
    have := hS.ρm_pos; have := hS.ρm_lt_ρp; have := le_max_right R 0; linarith)).2.2
  calc eLpNorm (S.couplingFn f) 2 volume
      ≤ ENNReal.ofReal C * eLpNorm ((ball (0 : ℂ) R').indicator
          (Conv.convAbs biotSavartKernel f)) 2 volume := by
        have := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' (μ := volume) (c := C.toNNReal)
          (f := S.couplingFn f)
          (g := (ball (0 : ℂ) R').indicator (Conv.convAbs biotSavartKernel f))
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

/-- `𝒦` maps real functions to real functions (pointwise in `x`). -/
theorem couplingFn_im_eq_zero (S : SectorSetting) {f : ℂ → ℂ}
    (hre : ∀ᵐ y ∂volume, (f y).im = 0) (x : ℂ) : (S.couplingFn f x).im = 0 := by
  have h : (fun y => ((fderiv ℝ S.om x (biotSavartKernel (x - y)) : ℝ) : ℂ) * f y) =ᵐ[volume]
      fun y => ((fderiv ℝ S.om x (biotSavartKernel (x - y)) * (f y).re : ℝ) : ℂ) := by
    filter_upwards [hre] with y hy
    have : f y = ((f y).re : ℂ) := Complex.ext (by simp) (by simp [hy])
    rw [this]
    push_cast
    simp
  simp only [couplingFn]
  rw [integral_congr_ae h, integral_complex_ofReal]
  simp

/-- The profile of an `H^k` function supported in `N_*` lies in `Y^0_ℓ`. -/
theorem isProfileL2_angularSector_of_memH {S : SectorSetting} (hS : S.Valid) {k : ℕ}
    {f : ℂ → ℂ} (hf : MemH k f) (hfs : ∀ᵐ y ∂volume, y ∉ S.Nstar → f y = 0) (ℓ : ℤ) :
    S.IsProfileL2 (Polar.angularSector f ℓ) := by
  have hfs' : ∀ᵐ x ∂volume, ¬ (S.ρm ≤ ‖x‖ ∧ ‖x‖ ≤ S.ρp) → f x = 0 := hfs
  obtain ⟨h1, h2⟩ := memH1On_angularSector hS.ρm_pos hf hfs' ℓ
  refine ⟨h1.memLp.mono_measure (Measure.restrict_mono (fun r hr => hS.ρm_pos.trans_le hr.1)
    le_rfl), h2⟩

theorem memLp_of_memH {k : ℕ} {f : ℂ → ℂ} (hf : MemH k f) : MemLp f 2 volume := by
  have := hf.memLp
  rwa [Measure.restrict_univ] at this

/-- `P_ℓ(𝒦w) = (k_ℓ𝒢_ℓ w_ℓ)(r)e^{iℓθ}` for `w ∈ H^k` supported in `N_*`. -/
theorem couplingFn_sector_fn (S : SectorSetting) (hS : S.Valid) {k : ℕ} {f : ℂ → ℂ}
    (hf : MemH k f) (hfs : ∀ᵐ y ∂volume, y ∉ S.Nstar → f y = 0) (ℓ : ℤ) :
    sectorProj ℓ (S.couplingFn f) =ᵐ[volume]
      ofProfile ℓ (S.KsecFn ℓ (Polar.angularSector f ℓ)) := by
  have h1 := sectorProj_couplingFn S hS (memLp_of_memH hf) hfs ℓ
  have h0 : ∀ᵐ x : ℂ ∂volume, x ≠ 0 := by
    rw [ae_iff]
    simp
  have h2 : S.couplingFn (sectorProj ℓ f) =
      S.couplingFn (ofProfile ℓ (Polar.angularSector f ℓ)) := by
    refine couplingFn_congr_ae S ?_
    filter_upwards [h0] with x hx
    rw [sectorProj_eq_angularSector ℓ f hx, ofProfile]
  have h3 := couplingFn_ofProfile S hS (isProfileL2_angularSector_of_memH hS hf hfs ℓ) ℓ
  rw [h2] at h1
  exact h1.trans h3

end NonUniqueEuler.SectorH
