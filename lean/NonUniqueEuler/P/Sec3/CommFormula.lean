import NonUniqueEuler.Defs.Sec3.Commutator
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Proof: `eq:comm-formula` (the commutator `C_ε[u,w]` as a single integral)

Proof of `NonUniqueEuler/I/Sec3/CommFormula.lean` (`03_compactness.tex:342-363`).

The rescaled kernel `ρ_ε = scaled ρ ε` is `C^∞` with compact support, so
`y ↦ Dρ_ε(x - y)` is continuous with compact support; this gives the integrability of both
integrands of `commEps` (Mathlib's `HasCompactSupport.convolutionExists_right`). The first line of
eq:comm-formula is `integral_sub`; the second is the substitution `y = x - εz`
(`Measure.integral_comp_smul`, `integral_sub_left_eq_self`, `finrank ℝ ℂ = 2`) together with
`Dρ_ε(εz)v = ε⁻² Dρ(z)(ε⁻¹v)` and `Dρ = 0` off `tsupport ρ ⊆ B₁`. The derivative of the
mollification is Mathlib's `HasCompactSupport.hasFDerivAt_convolution_right`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped Convolution

namespace NonUniqueEuler.Weak

/-! ### The rescaled kernel

Helper lemmas live in the sub-namespace `CommFormula` to avoid clashes. -/

namespace CommFormula

theorem scaled_eq_smul (ρ : ℂ → ℝ) (ε : ℝ) :
    scaled ρ ε = fun x => (ε ^ 2)⁻¹ * ρ (ε⁻¹ • x) := by
  funext x
  simp [scaled, Complex.real_smul, Complex.ofReal_inv]

theorem contDiff_scaled {ρ : ℂ → ℝ} (hρ : IsMollifier ρ) (ε : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (scaled ρ ε) := by
  rw [scaled_eq_smul]
  exact contDiff_const.mul (hρ.contDiff.comp (contDiff_id.const_smul _))

theorem hasCompactSupport_scaled {ρ : ℂ → ℝ} (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (scaled ρ ε) := by
  rw [scaled_eq_smul]
  refine (hρ.hasCompactSupport.comp_smul (inv_ne_zero hε.ne')).mono fun x hx => ?_
  rw [Function.mem_support] at hx ⊢
  intro h
  exact hx (by rw [h, mul_zero])

/-- `Dρ_ε(x) v = ε⁻² Dρ(ε⁻¹x)(ε⁻¹v)`. -/
theorem fderiv_scaled_apply {ρ : ℂ → ℝ} (hρ : IsMollifier ρ) (ε : ℝ) (x v : ℂ) :
    fderiv ℝ (scaled ρ ε) x v = (ε ^ 2)⁻¹ * fderiv ℝ ρ (ε⁻¹ • x) (ε⁻¹ • v) := by
  have hd : Differentiable ℝ ρ := hρ.contDiff.differentiable (by simp)
  rw [scaled_eq_smul]
  have hd' : DifferentiableAt ℝ (fun y : ℂ => ρ (ε⁻¹ • y)) x :=
    (hd.comp (differentiable_id.const_smul ε⁻¹)) x
  rw [fderiv_const_mul hd', fderiv_comp_smul (f := ρ) ε⁻¹]
  simp only [FunLike.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul]

/-- `Dρ_ε` is continuous. -/
theorem continuous_fderiv_scaled {ρ : ℂ → ℝ} (hρ : IsMollifier ρ) (ε : ℝ) :
    Continuous (fderiv ℝ (scaled ρ ε)) :=
  (contDiff_scaled hρ ε).continuous_fderiv (by simp)

/-- `Dρ_ε` has compact support. -/
theorem hasCompactSupport_fderiv_scaled {ρ : ℂ → ℝ} (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (fderiv ℝ (scaled ρ ε)) :=
  (hasCompactSupport_scaled hρ hε).fderiv ℝ

/-- `Dρ = 0` off `B₁`. -/
theorem fderiv_eq_zero_of_notMem_ball {ρ : ℂ → ℝ} (hρ : IsMollifier ρ) {z : ℂ}
    (hz : z ∉ ball (0 : ℂ) 1) : fderiv ℝ ρ z = 0 := by
  by_contra h
  exact hz (hρ.tsupport_subset (support_fderiv_subset ℝ h))

/-! ### Integrability of the two integrands -/

/-- The integrand of `dotGradMollify` is integrable (for any fixed direction `v`). -/
theorem integrable_dotGrad_integrand {ρ : ℂ → ℝ} (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    {g : ℂ → ℝ} (hg : LocallyIntegrable g volume) (x v : ℂ) :
    Integrable (fun y => g y * fderiv ℝ (scaled ρ ε) (x - y) v) := by
  have hc : Continuous fun z => fderiv ℝ (scaled ρ ε) z v :=
    (continuous_fderiv_scaled hρ ε).clm_apply continuous_const
  have hcs : HasCompactSupport fun z => fderiv ℝ (scaled ρ ε) z v :=
    (hasCompactSupport_scaled hρ hε).fderiv_apply ℝ v
  have := hcs.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ) hg hc x
  simpa [ConvolutionExistsAt] using this

/-- The integrand of `mollifyDiv` is integrable. -/
theorem integrable_mollifyDiv_integrand {ρ : ℂ → ℝ} (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    {g : ℂ → ℝ} {W : ℂ → ℂ} (hgW : LocallyIntegrable (fun y => g y • W y) volume) (x : ℂ) :
    Integrable (fun y => g y * fderiv ℝ (scaled ρ ε) (x - y) (W y)) := by
  have := (hasCompactSupport_fderiv_scaled hρ hε).convolutionExists_right
    (ContinuousLinearMap.apply ℝ ℝ : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ) →L[ℝ] ℝ) hgW
    (continuous_fderiv_scaled hρ ε) x
  refine (this.congr ?_)
  refine Filter.Eventually.of_forall fun y => ?_
  simp only [map_smul, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.apply_apply, smul_eq_mul]

end CommFormula

open CommFormula

/-! ### The statements -/

theorem commEps_eq_integral {ρ : ℂ → ℝ} (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    {u : ℝ → ℂ → ℝ} {w : ℝ → ℂ → ℂ} {t : ℝ} (hu : LocallyIntegrable (u t) volume)
    (huw : LocallyIntegrable (fun y => u t y • w t y) volume) (x : ℂ) :
    commEps ρ ε u w t x = ∫ y, u t y * fderiv ℝ (scaled ρ ε) (x - y) (w t x - w t y) := by
  rw [commEps, dotGradMollify, mollifyDiv,
    ← integral_sub (integrable_dotGrad_integrand hρ hε hu x (w t x))
      (integrable_mollifyDiv_integrand hρ hε huw x)]
  congr 1
  funext y
  rw [map_sub, mul_sub]

theorem commEps_eq_integral_ball {ρ : ℂ → ℝ} (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    {u : ℝ → ℂ → ℝ} {w : ℝ → ℂ → ℂ} {t : ℝ} (hu : LocallyIntegrable (u t) volume)
    (huw : LocallyIntegrable (fun y => u t y • w t y) volume) (x : ℂ) :
    commEps ρ ε u w t x =
      ∫ z in ball (0 : ℂ) 1,
        u t (x - ε • z) * fderiv ℝ ρ z (ε⁻¹ • (w t x - w t (x - ε • z))) := by
  rw [commEps_eq_integral hρ hε hu huw x]
  set F : ℂ → ℝ := fun y => u t y * fderiv ℝ (scaled ρ ε) (x - y) (w t x - w t y) with hF
  have hε0 : ε ≠ 0 := hε.ne'
  -- the integrand on the right is `ε² F(x - εz)`
  have hG : ∀ z : ℂ, u t (x - ε • z) * fderiv ℝ ρ z (ε⁻¹ • (w t x - w t (x - ε • z))) =
      ε ^ 2 * F (x - ε • z) := by
    intro z
    simp only [hF, sub_sub_cancel, fderiv_scaled_apply hρ ε, inv_smul_smul₀ hε0]
    field_simp
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
    rw [fderiv_eq_zero_of_notMem_ball hρ hz]; simp)]
  simp_rw [hG]
  rw [integral_const_mul,
    Measure.integral_comp_smul volume (fun v => F (x - v)) ε,
    integral_sub_left_eq_self F volume x, Complex.finrank_real_complex, smul_eq_mul,
    abs_of_pos (inv_pos.2 (pow_pos hε 2))]
  field_simp

theorem dotGradMollify_eq_fderiv {ρ : ℂ → ℝ} (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    {u : ℝ → ℂ → ℝ} {w : ℝ → ℂ → ℂ} {t : ℝ} (hu : LocallyIntegrable (u t) volume) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (mollify ρ ε (u t)) ∧
      ∀ x, dotGradMollify ρ ε u w t x = fderiv ℝ (mollify ρ ε (u t)) x (w t x) := by
  have hconv : mollify ρ ε (u t) = (u t) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] scaled ρ ε := by
    funext x
    rw [convolution_mul]
    rfl
  have hcs := hasCompactSupport_scaled hρ hε
  have hcd := contDiff_scaled hρ ε
  refine ⟨?_, fun x => ?_⟩
  · rw [hconv]
    exact hcs.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hu hcd
  · have hint : Integrable (fun y => ((ContinuousLinearMap.mul ℝ ℝ).precompR ℂ (u t y))
        (fderiv ℝ (scaled ρ ε) (x - y))) volume :=
      (hasCompactSupport_fderiv_scaled hρ hε).convolutionExists_right
        ((ContinuousLinearMap.mul ℝ ℝ).precompR ℂ) hu (continuous_fderiv_scaled hρ ε) x
    rw [hconv, (hcs.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hu
      (hcd.of_le (by exact_mod_cast le_top)) x).fderiv, convolution_def,
      ContinuousLinearMap.integral_apply hint]
    rfl

theorem commEps_sub {ρ : ℂ → ℝ} (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    {u : ℝ → ℂ → ℝ} {w₁ w₂ : ℝ → ℂ → ℂ} {t : ℝ} (hu : LocallyIntegrable (u t) volume)
    (huw₁ : LocallyIntegrable (fun y => u t y • w₁ t y) volume)
    (huw₂ : LocallyIntegrable (fun y => u t y • w₂ t y) volume) (x : ℂ) :
    commEps ρ ε u (fun s y => w₁ s y - w₂ s y) t x =
      commEps ρ ε u w₁ t x - commEps ρ ε u w₂ t x := by
  have h1 : dotGradMollify ρ ε u (fun s y => w₁ s y - w₂ s y) t x =
      dotGradMollify ρ ε u w₁ t x - dotGradMollify ρ ε u w₂ t x := by
    rw [dotGradMollify, dotGradMollify, dotGradMollify,
      ← integral_sub (integrable_dotGrad_integrand hρ hε hu x (w₁ t x))
        (integrable_dotGrad_integrand hρ hε hu x (w₂ t x))]
    congr 1
    funext y
    rw [map_sub, mul_sub]
  have h2 : mollifyDiv ρ ε u (fun s y => w₁ s y - w₂ s y) t x =
      mollifyDiv ρ ε u w₁ t x - mollifyDiv ρ ε u w₂ t x := by
    rw [mollifyDiv, mollifyDiv, mollifyDiv,
      ← integral_sub (integrable_mollifyDiv_integrand hρ hε huw₁ x)
        (integrable_mollifyDiv_integrand hρ hε huw₂ x)]
    congr 1
    funext y
    rw [map_sub, mul_sub]
  rw [commEps, commEps, commEps, h1, h2]
  ring

end NonUniqueEuler.Weak
