import NonUniqueEuler.Defs.Sec4.Setting
import NonUniqueEuler.I.Sec2.BSBasic
import NonUniqueEuler.I.Infra.ConvMinkowski.Young
import NonUniqueEuler.I.Infra.AngularFourier.SectorL2

/-!
# Proof: the coupling term `𝒦w = -(K_BS * w)·∇ω̄` commutes with rotations and with `P_ℓ`

Proof of `I/Sec4/Sector/CouplingProj.lean` (manuscript `04_ring.tex:263-266`, proof of
`lem:sector`(2)).

* `couplingFn_rot`: substitute `y = O_φ y'` (`O_φ` is measure preserving), and use
  `K_BS(O_φ z) = O_φ K_BS(z)` and `Dω̄(O_φ x)(O_φ v) = Dω̄(x)(v)` (`ω̄` radial).
* `sectorProj_couplingFn`: replace `w` by a measurable representative vanishing outside `N_*`
  (so `w ∈ L¹`). By `couplingFn_rot`, both sides at `x` are `-(2π)⁻¹` times the two iterated
  integrals of `F(φ, y) = e^{-iℓφ} Dω̄(x)(K_BS(x - y)) w(O_φ y)` on `(0, 2π] × ℂ`; Fubini
  (`integral_integral_swap`) applies as soon as
  `H(x) = ∫₀^{2π} (|K_BS| ⋆ |w|)(O_φ x) dφ < ∞` (substitution `y = O_{-φ} y'` in the inner
  integral). `H < ∞` a.e.: by Tonelli and rotation invariance, `∫_{B_R} H = 2π ∫_{B_R} |K_BS| ⋆ |w|`,
  finite by Young on balls (`Conv.eLpNorm_convAbs_ball_le` with `p = 1`) and
  `∫_{B_ρ} |K_BS| = ρ` (`BS.integral_norm_biotSavartKernel_ball`).

**Deviation.** The manuscript's integrability argument goes through `L²_loc` and polar
coordinates (a.e. circle); here the bound is integrated over balls in `x` instead (Tonelli), which
avoids polar coordinates. The statement is unchanged.
-/

noncomputable section

open MeasureTheory Set Metric Filter Real
open scoped ENNReal

namespace NonUniqueEuler

namespace CouplingProjH

/-! ### Rotations -/

theorem measurableEmbedding_rot (θ : ℝ) : MeasurableEmbedding (rot θ) := by
  rw [Polar.rot_eq_rotation]
  exact (rotation (Circle.exp θ)).toHomeomorph.measurableEmbedding

theorem biotSavartKernel_rot (θ : ℝ) (z : ℂ) :
    biotSavartKernel (rot θ z) = rot θ (biotSavartKernel z) := by
  rw [biotSavartKernel, biotSavartKernel, Polar.norm_rot, rot, rot]
  ring

theorem rot_sub (θ : ℝ) (x y : ℂ) : rot θ x - rot θ y = rot θ (x - y) := by
  simp only [rot]
  ring

theorem enorm_rot (θ : ℝ) (z : ℂ) : ‖rot θ z‖ₑ = ‖z‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, Polar.norm_rot]

theorem continuous_rot_prod : Continuous fun p : ℝ × ℂ => rot p.1 p.2 := by
  unfold rot
  fun_prop

theorem measurable_bsKernel : Measurable biotSavartKernel := by
  unfold biotSavartKernel
  fun_prop

/-- If `ψ ∘ O_θ = ψ`, then `Dψ(O_θ y)(O_θ v) = Dψ(y)(v)`. -/
theorem fderiv_rot_apply {ψ : ℂ → ℝ} (hψ : Differentiable ℝ ψ) {θ : ℝ}
    (hrot : ∀ x, ψ (rot θ x) = ψ x) (y v : ℂ) :
    fderiv ℝ ψ (rot θ y) (rot θ v) = fderiv ℝ ψ y v := by
  set u : ℂ := Complex.exp ((θ : ℂ) * Complex.I)
  have hL : HasFDerivAt (fun z : ℂ => rot θ z) (ContinuousLinearMap.mul ℝ ℂ u) y := by
    have := (ContinuousLinearMap.mul ℝ ℂ u).hasFDerivAt (x := y)
    have hfun : (fun z : ℂ => rot θ z) = ⇑(ContinuousLinearMap.mul ℝ ℂ u) := by
      funext z
      simp [rot, u]
    rw [hfun]
    exact this
  have hc := (hψ (rot θ y)).hasFDerivAt.comp y hL
  have heq : (ψ ∘ fun z => rot θ z) = ψ := funext hrot
  rw [heq] at hc
  rw [hc.fderiv]
  simp [rot, u]

/-! ### The convolution majorant along circles -/

/-- `|K_BS| ⋆ |w|` for measurable `w` is measurable. -/
theorem measurable_convAbs {w : ℂ → ℂ} (hw : Measurable w) :
    Measurable (Conv.convAbs biotSavartKernel w) := by
  have h : Measurable fun p : ℂ × ℂ => ‖biotSavartKernel (p.1 - p.2)‖ₑ * ‖w p.2‖ₑ :=
    (measurable_bsKernel.comp (measurable_fst.sub measurable_snd)).enorm.mul
      (hw.comp measurable_snd).enorm
  exact h.lintegral_prod_right'

/-- `∫ |K_BS(x - y)| |w(O_φ y)| dy = (|K_BS| ⋆ |w|)(O_φ x)`. -/
theorem lintegral_bs_rot (w : ℂ → ℂ) (x : ℂ) (φ : ℝ) :
    ∫⁻ y, ‖biotSavartKernel (x - y)‖ₑ * ‖w (rot φ y)‖ₑ =
      Conv.convAbs biotSavartKernel w (rot φ x) := by
  rw [Conv.convAbs, ← (Polar.measurePreserving_rot φ).lintegral_comp_emb
    (measurableEmbedding_rot φ) (fun y => ‖biotSavartKernel (rot φ x - y)‖ₑ * ‖w y‖ₑ)]
  refine lintegral_congr fun y => ?_
  rw [rot_sub, biotSavartKernel_rot, enorm_rot]

/-- The function `(x, φ) ↦ (|K_BS| ⋆ |w|)(O_φ x)` is measurable. -/
theorem measurable_convAbs_rot {w : ℂ → ℂ} (hw : Measurable w) :
    Measurable fun p : ℂ × ℝ => Conv.convAbs biotSavartKernel w (rot p.2 p.1) :=
  (measurable_convAbs hw).comp (continuous_rot_prod.comp continuous_swap).measurable

/-- `∫_{B_R} ∫₀^{2π} (|K_BS| ⋆ |w|)(O_φ x) dφ dx < ∞` for integrable `w` vanishing outside
`B_ρ`. -/
theorem lintegral_ball_lt_top {w : ℂ → ℂ} (hw : Measurable w) (hwi : Integrable w) {ρ R : ℝ}
    (hρR : 0 < R + ρ) (hsupp : ∀ y, ρ ≤ ‖y‖ → w y = 0) :
    ∫⁻ x in ball (0 : ℂ) R, ∫⁻ φ in Ioc (0 : ℝ) (2 * π),
      Conv.convAbs biotSavartKernel w (rot φ x) < ⊤ := by
  set g := Conv.convAbs biotSavartKernel w with hg
  have hm := measurable_convAbs_rot hw
  rw [lintegral_lintegral_swap (f := fun x φ => g (rot φ x)) hm.aemeasurable]
  have h1 : ∀ φ : ℝ, ∫⁻ x in ball (0 : ℂ) R, g (rot φ x) = ∫⁻ x in ball (0 : ℂ) R, g x := by
    intro φ
    have hpre : rot φ ⁻¹' ball (0 : ℂ) R = ball (0 : ℂ) R := by
      ext x
      simp only [mem_preimage, mem_ball_zero_iff, Polar.norm_rot]
    have h := (Polar.measurePreserving_rot φ).setLIntegral_comp_preimage_emb
      (measurableEmbedding_rot φ) g (ball (0 : ℂ) R)
    rwa [hpre] at h
  simp_rw [h1]
  rw [setLIntegral_const]
  have hY := Conv.eLpNorm_convAbs_ball_le (K := biotSavartKernel) (g := w)
    measurable_bsKernel.aestronglyMeasurable hw.aestronglyMeasurable (p := 1) le_rfl
    (ρ := ρ) (R := R) (ae_of_all _ hsupp)
  rw [eLpNorm_one_eq_lintegral_enorm] at hY
  simp only [enorm_eq_self] at hY
  rw [(BS.integral_norm_biotSavartKernel_ball hρR).2.2] at hY
  have hfin : ∫⁻ x in ball (0 : ℂ) R, g x < ⊤ := by
    refine hY.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
    rw [eLpNorm_one_eq_lintegral_enorm] at *
    exact hwi.2
  exact ENNReal.mul_lt_top hfin (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)

/-- For almost every `x`, `∫₀^{2π} (|K_BS| ⋆ |w|)(O_φ x) dφ < ∞`. -/
theorem ae_lintegral_lt_top {w : ℂ → ℂ} (hw : Measurable w) (hwi : Integrable w) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hsupp : ∀ y, ρ ≤ ‖y‖ → w y = 0) :
    ∀ᵐ x ∂volume, ∫⁻ φ in Ioc (0 : ℝ) (2 * π),
      Conv.convAbs biotSavartKernel w (rot φ x) < ⊤ := by
  have hHm : Measurable fun x : ℂ => ∫⁻ φ in Ioc (0 : ℝ) (2 * π),
      Conv.convAbs biotSavartKernel w (rot φ x) :=
    (measurable_convAbs_rot hw).lintegral_prod_right'
  have hn : ∀ n : ℕ, ∀ᵐ x ∂volume, x ∈ ball (0 : ℂ) ((n : ℝ) + 1) →
      ∫⁻ φ in Ioc (0 : ℝ) (2 * π), Conv.convAbs biotSavartKernel w (rot φ x) < ⊤ := by
    intro n
    rw [← ae_restrict_iff' measurableSet_ball]
    refine ae_lt_top hHm (lintegral_ball_lt_top hw hwi ?_ hsupp).ne
    positivity
  filter_upwards [ae_all_iff.2 hn] with x hx
  obtain ⟨n, hn'⟩ := exists_nat_gt ‖x‖
  exact hx n (by rw [mem_ball_zero_iff]; linarith)

/-! ### Fubini for fixed `x` -/

/-- The integrand `F(φ, y) = e^{-iℓφ} Dω̄(x)(K_BS(x - y)) w(O_φ y)`. -/
def integrand (om : ℂ → ℝ) (w : ℂ → ℂ) (ℓ : ℤ) (x : ℂ) (p : ℝ × ℂ) : ℂ :=
  Complex.exp (-((ℓ : ℂ) * p.1 * Complex.I)) *
    (((fderiv ℝ om x (biotSavartKernel (x - p.2)) : ℝ) : ℂ) * w (rot p.1 p.2))

theorem norm_exp_neg_mul_I (ℓ : ℤ) (φ : ℝ) :
    ‖Complex.exp (-((ℓ : ℂ) * φ * Complex.I))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem integrable_integrand (om : ℂ → ℝ) {w : ℂ → ℂ}
    (hw : Measurable w) (ℓ : ℤ) (x : ℂ)
    (hx : ∫⁻ φ in Ioc (0 : ℝ) (2 * π), Conv.convAbs biotSavartKernel w (rot φ x) < ⊤) :
    Integrable (integrand om w ℓ x) ((volume.restrict (Ioc (0 : ℝ) (2 * π))).prod volume) := by
  have hmeas : Measurable (integrand om w ℓ x) := by
    unfold integrand
    have h1 : Measurable fun p : ℝ × ℂ => Complex.exp (-((ℓ : ℂ) * p.1 * Complex.I)) := by
      fun_prop
    have h2 : Measurable fun p : ℝ × ℂ =>
        ((fderiv ℝ om x (biotSavartKernel (x - p.2)) : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp ((fderiv ℝ om x).continuous.measurable.comp
        (measurable_bsKernel.comp (measurable_const.sub measurable_snd)))
    have h3 : Measurable fun p : ℝ × ℂ => w (rot p.1 p.2) := hw.comp continuous_rot_prod.measurable
    exact h1.mul (h2.mul h3)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  have hG : Measurable fun p : ℝ × ℂ =>
      ‖biotSavartKernel (x - p.2)‖ₑ * ‖w (rot p.1 p.2)‖ₑ :=
    (measurable_bsKernel.comp (measurable_const.sub measurable_snd)).enorm.mul
      (hw.comp continuous_rot_prod.measurable).enorm
  have hpt : ∀ p : ℝ × ℂ, ‖integrand om w ℓ x p‖ₑ ≤
      ‖fderiv ℝ om x‖ₑ * (‖biotSavartKernel (x - p.2)‖ₑ * ‖w (rot p.1 p.2)‖ₑ) := by
    intro p
    unfold integrand
    rw [enorm_mul, enorm_mul, ← ofReal_norm (Complex.exp _), norm_exp_neg_mul_I,
      ENNReal.ofReal_one, one_mul, ← mul_assoc]
    gcongr
    rw [← ofReal_norm, Complex.norm_real, ofReal_norm]
    exact (fderiv ℝ om x).le_opENorm _
  have hcomp : ∀ φ : ℝ, ∫⁻ y, ‖biotSavartKernel (x - y)‖ₑ * ‖w (rot φ y)‖ₑ =
      Conv.convAbs biotSavartKernel w (rot φ x) := lintegral_bs_rot w x
  calc ∫⁻ p, ‖integrand om w ℓ x p‖ₑ ∂((volume.restrict (Ioc (0 : ℝ) (2 * π))).prod volume)
      ≤ ∫⁻ p, ‖fderiv ℝ om x‖ₑ * (‖biotSavartKernel (x - p.2)‖ₑ * ‖w (rot p.1 p.2)‖ₑ)
          ∂((volume.restrict (Ioc (0 : ℝ) (2 * π))).prod volume) := lintegral_mono hpt
    _ = ‖fderiv ℝ om x‖ₑ * ∫⁻ p, ‖biotSavartKernel (x - p.2)‖ₑ * ‖w (rot p.1 p.2)‖ₑ
          ∂((volume.restrict (Ioc (0 : ℝ) (2 * π))).prod volume) := lintegral_const_mul _ hG
    _ = ‖fderiv ℝ om x‖ₑ * ∫⁻ φ in Ioc (0 : ℝ) (2 * π),
          Conv.convAbs biotSavartKernel w (rot φ x) := by
        rw [lintegral_prod _ hG.aemeasurable]
        simp only [hcomp]
    _ < ⊤ := ENNReal.mul_lt_top enorm_lt_top hx

theorem couplingFn_congr_ae (S : SectorSetting) {f g : ℂ → ℂ} (hfg : f =ᵐ[volume] g) :
    S.couplingFn f = S.couplingFn g := by
  funext x
  simp only [SectorSetting.couplingFn]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hfg] with y hy
  rw [hy]

end CouplingProjH

namespace SectorSetting

open CouplingProjH

/-- `𝒦` commutes with rotations (pointwise): `(𝒦w)(O_φ x) = 𝒦(w ∘ O_φ)(x)`. -/
theorem couplingFn_rot (S : SectorSetting) (hS : S.Valid) (w : ℂ → ℂ) (φ : ℝ) (x : ℂ) :
    S.couplingFn w (rot φ x) = S.couplingFn (fun y => w (rot φ y)) x := by
  have hdiff : Differentiable ℝ S.om := hS.contDiff.differentiable (by simp)
  simp only [couplingFn]
  congr 1
  rw [← (Polar.measurePreserving_rot φ).integral_comp (measurableEmbedding_rot φ)]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only
  rw [rot_sub, biotSavartKernel_rot, fderiv_rot_apply hdiff (hS.radial φ)]

/-- The pointwise identity `P_ℓ(𝒦w)(x) = 𝒦(P_ℓ w)(x)` when Fubini applies at `x`. -/
private theorem sectorProj_couplingFn_apply (S : SectorSetting) (hS : S.Valid) {w : ℂ → ℂ}
    (ℓ : ℤ) (x : ℂ) (hint : Integrable (integrand S.om w ℓ x)
      ((volume.restrict (Ioc (0 : ℝ) (2 * π))).prod volume)) :
    Ang.sectorProj ℓ (S.couplingFn w) x = S.couplingFn (Ang.sectorProj ℓ w) x := by
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  simp only [Ang.sectorProj, couplingFn_rot S hS w]
  simp only [couplingFn, Ang.sectorProj]
  simp only [intervalIntegral.integral_of_le h2π]
  have hL : ∀ φ : ℝ, Complex.exp (-((ℓ : ℂ) * φ * Complex.I)) *
      -∫ y, ((fderiv ℝ S.om x (biotSavartKernel (x - y)) : ℝ) : ℂ) * w (rot φ y) =
      -∫ y, integrand S.om w ℓ x (φ, y) := by
    intro φ
    rw [mul_neg, ← integral_const_mul]
    rfl
  have hR : ∀ y : ℂ, ((fderiv ℝ S.om x (biotSavartKernel (x - y)) : ℝ) : ℂ) *
      ((2 * π : ℂ)⁻¹ * ∫ φ in Ioc (0 : ℝ) (2 * π),
        Complex.exp (-((ℓ : ℂ) * φ * Complex.I)) * w (rot φ y)) =
      (2 * π : ℂ)⁻¹ * ∫ φ in Ioc (0 : ℝ) (2 * π), integrand S.om w ℓ x (φ, y) := by
    intro y
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
    congr 1
    funext φ
    simp only [integrand]
    ring
  simp only [hL, hR, integral_neg, integral_const_mul]
  rw [integral_integral_swap (f := fun φ y => integrand S.om w ℓ x (φ, y)) hint]
  ring

/-- `𝒦` commutes with the sector projection `P_ℓ` on `L²` functions supported in `N_*`. -/
theorem sectorProj_couplingFn (S : SectorSetting) (hS : S.Valid) {w : ℂ → ℂ}
    (hw : MemLp w 2 volume) (hws : ∀ᵐ y ∂volume, y ∉ S.Nstar → w y = 0) (ℓ : ℤ) :
    Ang.sectorProj ℓ (S.couplingFn w) =ᵐ[volume] S.couplingFn (Ang.sectorProj ℓ w) := by
  obtain ⟨w', hw'm, hww'⟩ := hw.aestronglyMeasurable
  set v : ℂ → ℂ := S.Nstar.indicator w' with hv
  have hNm : MeasurableSet S.Nstar := S.isCompact_Nstar.isClosed.measurableSet
  have hwv : w =ᵐ[volume] v := by
    filter_upwards [hww', hws] with y h1 h2
    by_cases hy : y ∈ S.Nstar
    · rw [hv, indicator_of_mem hy, h1]
    · rw [hv, indicator_of_notMem hy, h2 hy]
  have hvm : Measurable v := hw'm.measurable.indicator hNm
  have hvi : Integrable v := by
    have hw'2 : MemLp w' 2 volume := MemLp.ae_eq hww' hw
    have : IsFiniteMeasure (volume.restrict S.Nstar) :=
      isFiniteMeasure_restrict.2 S.isCompact_Nstar.measure_lt_top.ne
    have h : IntegrableOn w' S.Nstar := (hw'2.restrict S.Nstar).integrable one_le_two
    exact h.integrable_indicator hNm
  have hρ : 0 ≤ S.ρp + 1 := by linarith [hS.ρm_pos, hS.ρm_lt_ρp]
  have hvs : ∀ y, S.ρp + 1 ≤ ‖y‖ → v y = 0 := by
    intro y hy
    have h : y ∉ S.Nstar := fun h => by linarith [(mem_Nstar.1 h).2]
    rw [hv, indicator_of_notMem h]
  rw [couplingFn_congr_ae S hwv, couplingFn_congr_ae S (Ang.sectorProj_congr_ae ℓ hwv)]
  filter_upwards [ae_lintegral_lt_top hvm hvi hρ hvs] with x hx
  exact sectorProj_couplingFn_apply S hS ℓ x (integrable_integrand S.om hvm ℓ x hx)

end SectorSetting

end NonUniqueEuler
