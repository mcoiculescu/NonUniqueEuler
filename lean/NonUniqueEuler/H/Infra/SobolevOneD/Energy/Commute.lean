import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import NonUniqueEuler.H.Infra.SobolevOneD.Energy.Yukawa

/-!
# Helper for `P/Infra/SobolevOneD/Energy`: `yukawa` commutes with weak derivatives

If `g, g'` are integrable, vanish a.e. outside `[a, b]` and `g' = ∂g` weakly on `ℝ`, then
`yukawa ℓ g' = ∂(yukawa ℓ g)` weakly on `ℝ` (`hasWeakDerivOn_yukawa_of_weak`).

Proof. For a test function `φ`, Fubini gives `∫ (k0 ⋆ g) φ' = ∫ g Φ[φ']` with
`Φ[θ](y) = ∫ k0(x - y) θ(x) dx = (k0 ⋆ θ)(y)`. `Φ[φ]` is smooth with `Φ[φ]' = Φ[φ']`
(convolution of the locally integrable `k0` with a test function,
`HasCompactSupport.contDiff_convolution_right`, `HasCompactSupport.hasDerivAt_convolution_right`).
With a bump function `χ = 1` near `[a, b]`, `χ Φ[φ]` is a test function, and on `[a, b]` it
coincides with `Φ[φ]` together with its derivative; so the weak derivative identity for `g`
against `χ Φ[φ]` gives `∫ g Φ[φ'] = -∫ g' Φ[φ]`, and Fubini again gives the claim.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology ContDiff Convolution

namespace NonUniqueEuler.Sob.EnergyAux

/-- `Φ[θ](y) = ∫ k0(x - y) θ(x) dx`. -/
def Phi (L : ℝ) (θ : ℝ → ℂ) (y : ℝ) : ℂ := ∫ x, (k0 L (x - y) : ℂ) * θ x

/-- `Φ[θ] = k0 ⋆ θ` (Mathlib's convolution with the scalar multiplication). -/
theorem Phi_eq_conv (L : ℝ) (θ : ℝ → ℂ) :
    Phi L θ = (k0 L) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] θ := by
  funext y
  rw [convolution_def, Phi]
  rw [← integral_sub_left_eq_self (fun x => (k0 L (x - y) : ℂ) * θ x) volume y]
  congr 1
  funext t
  rw [ContinuousLinearMap.lsmul_apply, Complex.real_smul,
    show y - t - y = -t by ring, k0_neg]

theorem contDiff_Phi {L : ℝ} (hL : 0 < L) {φ : ℝ → ℂ} (hφ : IsTestFn univ φ) :
    ContDiff ℝ ∞ (Phi L φ) := by
  rw [Phi_eq_conv]
  exact hφ.compact.contDiff_convolution_right _ (integrable_k0 hL).locallyIntegrable hφ.smooth

theorem hasDerivAt_Phi {L : ℝ} (hL : 0 < L) {φ : ℝ → ℂ} (hφ : IsTestFn univ φ) (y : ℝ) :
    HasDerivAt (Phi L φ) (Phi L (deriv φ) y) y := by
  rw [Phi_eq_conv, Phi_eq_conv]
  exact hφ.compact.hasDerivAt_convolution_right _ (integrable_k0 hL).locallyIntegrable
    (hφ.smooth.of_le (by simp)) y

/-- A smooth bump function `χ` equal to `1` on `ball 0 R`, `R = |a| + |b| + 1`. -/
def cutoff (a b : ℝ) : ContDiffBump (0 : ℝ) where
  rIn := |a| + |b| + 1
  rOut := |a| + |b| + 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

theorem Icc_subset_ball_cutoff (a b : ℝ) : Icc a b ⊆ ball (0 : ℝ) (cutoff a b).rIn := by
  intro y hy
  rw [mem_ball, dist_zero_right, Real.norm_eq_abs]
  show |y| < |a| + |b| + 1
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    linarith [hy.2, le_abs_self b, abs_nonneg a]
  · rw [abs_of_neg h]
    linarith [hy.1, neg_abs_le a, abs_nonneg b]

/-- `χ Φ[φ]`, a test function. -/
def cutPhi (L a b : ℝ) (φ : ℝ → ℂ) (y : ℝ) : ℂ := ((cutoff a b y : ℝ) : ℂ) * Phi L φ y

theorem isTestFn_cutPhi {L : ℝ} (hL : 0 < L) (a b : ℝ) {φ : ℝ → ℂ} (hφ : IsTestFn univ φ) :
    IsTestFn univ (cutPhi L a b φ) := by
  refine ⟨?_, ?_, subset_univ _⟩
  · exact (Complex.ofRealCLM.contDiff.comp (cutoff a b).contDiff).mul (contDiff_Phi hL hφ)
  · have h1 : HasCompactSupport fun y => ((cutoff a b y : ℝ) : ℂ) :=
      (cutoff a b).hasCompactSupport.comp_left Complex.ofReal_zero
    exact h1.mul_right

theorem cutPhi_eq {L a b : ℝ} {φ : ℝ → ℂ} {y : ℝ} (hy : y ∈ Icc a b) :
    cutPhi L a b φ y = Phi L φ y := by
  rw [cutPhi, (cutoff a b).one_of_mem_closedBall
    (ball_subset_closedBall (Icc_subset_ball_cutoff a b hy))]
  simp

theorem deriv_cutPhi_eq {L : ℝ} (hL : 0 < L) {a b : ℝ} {φ : ℝ → ℂ} (hφ : IsTestFn univ φ)
    {y : ℝ} (hy : y ∈ Icc a b) : deriv (cutPhi L a b φ) y = Phi L (deriv φ) y := by
  have hev : cutPhi L a b φ =ᶠ[𝓝 y] Phi L φ := by
    filter_upwards [(cutoff a b).eventuallyEq_one_of_mem_ball (Icc_subset_ball_cutoff a b hy)]
      with z hz
    rw [cutPhi, hz]
    simp
  rw [hev.deriv_eq, (hasDerivAt_Phi hL hφ y).deriv]

/-- `yukawa` commutes with weak derivatives of compactly supported integrable functions. -/
theorem hasWeakDerivOn_yukawa_of_weak {ℓ : ℤ} (hℓ : ℓ ≠ 0) {g g' : ℝ → ℂ} (hg : Integrable g)
    (hg' : Integrable g') {a b : ℝ} (hga : ∀ᵐ x, x ∉ Icc a b → g x = 0)
    (hga' : ∀ᵐ x, x ∉ Icc a b → g' x = 0) (hw : HasWeakDerivOn univ (derivList 1) g g') :
    HasWeakDerivOn univ (derivList 1) (yukawa ℓ g) (yukawa ℓ g') := by
  intro φ hφ
  set L := |(ℓ : ℝ)| with hLdef
  have hL : 0 < L := abs_pos_of_ne hℓ
  have hk0b : ∀ z, |k0 L z| ≤ 1 := fun z => by
    rw [abs_of_pos (k0_pos _ _)]; exact k0_le_one hL.le z
  have hφl := testLike_of_isTestFn hφ
  rw [iterDirDeriv_derivList_one]
  -- the weak derivative identity against `χ Φ[φ]`
  have hζ := hw _ (isTestFn_cutPhi hL a b hφ)
  rw [iterDirDeriv_derivList_one] at hζ
  have e1 : ∫ y, g y * deriv (cutPhi L a b φ) y = ∫ y, g y * Phi L (deriv φ) y := by
    refine integral_congr_ae ?_
    filter_upwards [hga] with y hy
    by_cases hmem : y ∈ Icc a b
    · rw [deriv_cutPhi_eq hL hφ hmem]
    · rw [hy hmem, zero_mul, zero_mul]
  have e2 : ∫ y, g' y * cutPhi L a b φ y = ∫ y, g' y * Phi L φ y := by
    refine integral_congr_ae ?_
    filter_upwards [hga'] with y hy
    by_cases hmem : y ∈ Icc a b
    · rw [cutPhi_eq hmem]
    · rw [hy hmem, zero_mul, zero_mul]
  rw [e1, e2] at hζ
  -- Fubini on both sides
  have f1 : ∫ x, yukawa ℓ g x * deriv φ x =
      -(((2 * L)⁻¹ : ℝ) : ℂ) * ∫ y, g y * Phi L (deriv φ) y := by
    simp_rw [yukawa_eq, mul_assoc]
    rw [integral_const_mul]
    congr 1
    exact integral_conv_mul (continuous_k0 L).measurable hk0b hg hφl.int'
  have f2 : ∫ x, yukawa ℓ g' x * φ x = -(((2 * L)⁻¹ : ℝ) : ℂ) * ∫ y, g' y * Phi L φ y := by
    simp_rw [yukawa_eq, mul_assoc]
    rw [integral_const_mul]
    congr 1
    exact integral_conv_mul (continuous_k0 L).measurable hk0b hg' hφl.int
  rw [f1, f2, hζ]
  simp

end NonUniqueEuler.Sob.EnergyAux
