import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Normed.Group.Pointwise
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import NonUniqueEuler.Defs.Infra.Sobolev

/-!
# Helper for `P/Infra/Sobolev/Density`: mollification and weak derivatives

The mollification `conv ρ f = ρ ⋆ f` of a complex function `f` by a real kernel `ρ`
(Mathlib's `convolution` with `lsmul ℝ ℝ`).

* `integral_conv_mul`: Fubini, `∫ (ρ ⋆ h) u = ∫ ρ(t) ∫ h(y) u(y + t) dy dt` for `h` locally
  integrable and `ρ`, `u` continuous with compact support;
* `hasWeakDerivOn_conv`: weak derivatives commute with mollification,
  `∂_{vs}(ρ ⋆ f) = ρ ⋆ ∂_{vs} f` weakly (test with `φ(· + t)` and use Fubini twice);
* `contDiff_conv`, `tsupport_conv_subset`: `ρ ⋆ f` is smooth for smooth compactly supported `ρ`,
  and supported in `cthickening r K` if `support ρ ⊆ ball 0 r` and `f = 0` a.e. outside `K`.

This is step 2 of the proof sketch of `I/Infra/Sobolev/Density.lean` (standard mollification).
-/

noncomputable section

open MeasureTheory Set Filter Metric Function
open scoped ENNReal ContDiff Topology Convolution Pointwise

namespace NonUniqueEuler.Sob.DensityAux

/-- Mollification `ρ ⋆ f` of a complex function by a real kernel. -/
def conv (ρ : ℂ → ℝ) (f : ℂ → ℂ) : ℂ → ℂ :=
  ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f

theorem conv_eq_integral (ρ : ℂ → ℝ) (f : ℂ → ℂ) (x : ℂ) :
    conv ρ f x = ∫ t, ρ t • f (x - t) := by
  simp only [conv, convolution_def, ContinuousLinearMap.lsmul_apply]

theorem conv_apply (ρ : ℂ → ℝ) (f : ℂ → ℂ) (x : ℂ) :
    conv ρ f x = ∫ t, (ρ t : ℂ) * f (x - t) := by
  rw [conv_eq_integral]
  simp only [Complex.real_smul]

/-- The integrand of `∫ (ρ ⋆ h) u` is integrable on the product. -/
theorem integrable_conv_integrand {ρ : ℂ → ℝ} (hρc : Continuous ρ) (hρ : HasCompactSupport ρ)
    {h : ℂ → ℂ} (hh : LocallyIntegrable h volume) {u : ℂ → ℂ} (huc : Continuous u)
    (hu : HasCompactSupport u) :
    Integrable (fun p : ℂ × ℂ => (ρ p.2 : ℂ) * h (p.1 - p.2) * u p.1)
      ((volume : Measure ℂ).prod volume) := by
  set S : Set ℂ := (fun p : ℂ × ℂ => p.1 - p.2) '' (tsupport u ×ˢ tsupport ρ) with hSdef
  have hS : IsCompact S := (IsCompact.prod hu hρ).image continuous_sub
  set h' : ℂ → ℂ := S.indicator h with hh'def
  have hh' : Integrable h' volume :=
    (integrable_indicator_iff hS.measurableSet).2 (hh.integrableOn_isCompact hS)
  have hρi : Integrable ρ volume := hρc.integrable_of_hasCompactSupport hρ
  have h1 := hρi.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hh'
  obtain ⟨C, hC⟩ := huc.norm.bddAbove_range_of_hasCompactSupport hu.norm
  have h2 : Integrable (fun p : ℂ × ℂ => ((ρ p.2 : ℂ) * h' (p.1 - p.2)) * u p.1)
      ((volume : Measure ℂ).prod volume) := by
    refine Integrable.mul_bdd (c := C) ?_ (huc.comp continuous_fst).aestronglyMeasurable
      (Eventually.of_forall fun p => hC ⟨p.1, rfl⟩)
    simpa only [ContinuousLinearMap.lsmul_apply, Complex.real_smul] using h1
  refine h2.congr (Eventually.of_forall fun p => ?_)
  by_cases hu0 : u p.1 = 0
  · simp [hu0]
  by_cases hρ0 : ρ p.2 = 0
  · simp [hρ0]
  have hmem : p.1 - p.2 ∈ S :=
    ⟨(p.1, p.2), ⟨subset_tsupport _ hu0, subset_tsupport _ hρ0⟩, rfl⟩
  simp only [hh'def, indicator_of_mem hmem]

/-- Fubini for the mollification: `∫ (ρ ⋆ h) u = ∫ ρ(t) ∫ h(y) u(y + t) dy dt`. -/
theorem integral_conv_mul {ρ : ℂ → ℝ} (hρc : Continuous ρ) (hρ : HasCompactSupport ρ)
    {h : ℂ → ℂ} (hh : LocallyIntegrable h volume) {u : ℂ → ℂ} (huc : Continuous u)
    (hu : HasCompactSupport u) :
    ∫ x, conv ρ h x * u x = ∫ t, (ρ t : ℂ) * ∫ y, h y * u (y + t) := by
  have hI := integrable_conv_integrand hρc hρ hh huc hu
  calc ∫ x, conv ρ h x * u x = ∫ x, ∫ t, (ρ t : ℂ) * h (x - t) * u x := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [conv_apply]
        rw [← integral_mul_const]
    _ = ∫ t, ∫ x, (ρ t : ℂ) * h (x - t) * u x :=
        integral_integral_swap (f := fun x t => (ρ t : ℂ) * h (x - t) * u x) hI
    _ = ∫ t, (ρ t : ℂ) * ∫ y, h y * u (y + t) := by
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        simp only
        rw [← integral_const_mul,
          ← integral_sub_right_eq_self (fun y => (ρ t : ℂ) * (h y * u (y + t))) t]
        simp only [sub_add_cancel, mul_assoc]

/-- Directional derivatives commute with translations. -/
theorem iterDirDeriv_comp_add_right (vs : List ℂ) (φ : ℂ → ℂ) (t : ℂ) :
    iterDirDeriv vs (fun y => φ (y + t)) = fun y => iterDirDeriv vs φ (y + t) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    funext y
    simp only [iterDirDeriv_cons, ih, dirDeriv]
    rw [fderiv_comp_add_right]

theorem isTestFn_comp_add_right {φ : ℂ → ℂ} (hφ : IsTestFn univ φ) (t : ℂ) :
    IsTestFn univ (fun y => φ (y + t)) :=
  ⟨hφ.smooth.comp (contDiff_id.add contDiff_const),
    hφ.compact.comp_homeomorph (Homeomorph.addRight t), subset_univ _⟩

/-- Weak derivatives commute with mollification. -/
theorem hasWeakDerivOn_conv {ρ : ℂ → ℝ} (hρc : Continuous ρ) (hρ : HasCompactSupport ρ)
    {vs : List ℂ} {f g : ℂ → ℂ} (hf : LocallyIntegrable f volume)
    (hg : LocallyIntegrable g volume) (hfg : HasWeakDerivOn univ vs f g) :
    HasWeakDerivOn univ vs (conv ρ f) (conv ρ g) := by
  intro φ hφ
  rw [integral_conv_mul hρc hρ hf (hφ.iterDirDeriv vs).continuous (hφ.iterDirDeriv vs).compact,
    integral_conv_mul hρc hρ hg hφ.continuous hφ.compact, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  have key := hfg _ (isTestFn_comp_add_right hφ t)
  rw [iterDirDeriv_comp_add_right] at key
  simp only at key ⊢
  rw [key]
  ring

/-- Smoothness of the mollification. -/
theorem contDiff_conv {ρ : ℂ → ℝ} (hρs : ContDiff ℝ ∞ ρ) (hρ : HasCompactSupport ρ)
    {f : ℂ → ℂ} (hf : LocallyIntegrable f volume) : ContDiff ℝ ∞ (conv ρ f) :=
  hρ.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hρs hf

theorem continuous_conv {ρ : ℂ → ℝ} (hρc : Continuous ρ) (hρ : HasCompactSupport ρ)
    {f : ℂ → ℂ} (hf : LocallyIntegrable f volume) : Continuous (conv ρ f) :=
  hρ.continuous_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hρc hf

/-- Support of the mollification. -/
theorem tsupport_conv_subset {ρ : ℂ → ℝ} {r : ℝ} (hρr : support ρ ⊆ ball 0 r) {f : ℂ → ℂ}
    {K : Set ℂ} (hfK : ∀ᵐ x, x ∉ K → f x = 0) : tsupport (conv ρ f) ⊆ cthickening r K := by
  have hae : f =ᵐ[volume] K.indicator f := by
    filter_upwards [hfK] with x hx
    by_cases hxK : x ∈ K
    · simp [hxK]
    · simp [hxK, hx hxK]
  have heq : conv ρ f = conv ρ (K.indicator f) :=
    convolution_congr _ (EventuallyEq.refl _ _) hae
  rw [heq]
  refine closure_minimal ?_ isClosed_cthickening
  refine (support_convolution_subset _).trans ?_
  calc support ρ + support (K.indicator f) ⊆ ball 0 r + K :=
        Set.add_subset_add hρr (support_indicator_subset)
    _ = thickening r K := ball_add_zero r K
    _ ⊆ cthickening r K := thickening_subset_cthickening _ _

theorem hasCompactSupport_conv {ρ : ℂ → ℝ} {r : ℝ} (hρr : support ρ ⊆ ball 0 r) {f : ℂ → ℂ}
    {K : Set ℂ} (hK : IsCompact K) (hfK : ∀ᵐ x, x ∉ K → f x = 0) :
    HasCompactSupport (conv ρ f) :=
  hK.cthickening.of_isClosed_subset (isClosed_tsupport _) (tsupport_conv_subset hρr hfK)

end NonUniqueEuler.Sob.DensityAux
