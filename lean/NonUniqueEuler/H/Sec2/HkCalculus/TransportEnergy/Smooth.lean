import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import NonUniqueEuler.I.Infra.Sobolev.Smooth
import NonUniqueEuler.I.Infra.Sobolev.NormDeriv
import NonUniqueEuler.H.Sec2.HkCalculus.TransportEnergy.Bounds

/-!
# Helper for `P/Sec2/HkCalculus/TransportEnergy`: the smooth case

Step 1 of the proof of `lem:Hk-calculus`(1), second claim (`02_prelim.tex:735-745`): for a test
function `φ` and a real vector field `U ∈ W^{1,∞}` with weak derivatives `G₁ = ∂₁U`,
`G₂ = ∂₂U`,
`Re ∫ (U·∇φ) φ̄ = ½ ∫ U·∇|φ|² = -½ ∫ (Re G₁ + Im G₂) |φ|² = -½ ∫ (div U) |φ|²`.
The integration by parts is the definition of the weak derivatives of `U`, tested against the
test function `|φ|²`.

All fully proved.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal ComplexConjugate ContDiff

namespace NonUniqueEuler.Sob.TransportEnergyAux

/-- `|φ|²` (as a complex function) is a test function. -/
theorem isTestFn_normSq {φ : ℂ → ℂ} (hφ : IsTestFn univ φ) :
    IsTestFn univ (fun x => ((‖φ x‖ ^ 2 : ℝ) : ℂ)) := by
  refine ⟨?_, ?_, subset_univ _⟩
  · exact Complex.ofRealCLM.contDiff.comp (hφ.smooth.norm_sq ℝ)
  · exact hφ.compact.comp_left (g := fun z : ℂ => ((‖z‖ ^ 2 : ℝ) : ℂ)) (by simp)

/-- `∂_v |φ|² = 2 Re (∂_v φ · φ̄)`. -/
theorem dirDeriv_normSq {φ : ℂ → ℂ} (hφ : IsTestFn univ φ) (v x : ℂ) :
    dirDeriv v (fun x => ((‖φ x‖ ^ 2 : ℝ) : ℂ)) x =
      ((2 * (dirDeriv v φ x * conj (φ x)).re : ℝ) : ℂ) := by
  have hφd : HasFDerivAt φ (fderiv ℝ φ x) x :=
    ((hφ.smooth.differentiable (by simp)) x).hasFDerivAt
  have h2 := (Complex.ofRealCLM.hasFDerivAt (x := ‖φ x‖ ^ 2)).comp x hφd.norm_sq
  show fderiv ℝ (Complex.ofRealCLM ∘ fun y => ‖φ y‖ ^ 2) x v = _
  rw [h2.fderiv]
  simp [dirDeriv, Complex.inner]
  ring

/-- The smooth case: `Re ∫ (U·∇φ) φ̄ = -½ ∫ (Re ∂₁U + Im ∂₂U) |φ|²`. -/
theorem re_integral_dotGrad_testFn {U G₁ G₂ φ : ℂ → ℂ} (hφ : IsTestFn univ φ)
    (hU : MemLp U ⊤ volume) (hG₁ : MemLp G₁ ⊤ volume) (hG₂ : MemLp G₂ ⊤ volume)
    (hd₁ : HasWeakDerivOn univ (pdList (1, 0)) U G₁)
    (hd₂ : HasWeakDerivOn univ (pdList (0, 1)) U G₂) :
    (∫ x, dotGrad U φ x * conj (φ x)).re =
      -(1 / 2) * ∫ x, ((G₁ x).re + (G₂ x).im) * ‖φ x‖ ^ 2 := by
  set ψ : ℂ → ℂ := fun x => ((‖φ x‖ ^ 2 : ℝ) : ℂ) with hψdef
  have hψ : IsTestFn univ ψ := isTestFn_normSq hφ
  have hdψ : ∀ v x, dirDeriv v ψ x = ((2 * (dirDeriv v φ x * conj (φ x)).re : ℝ) : ℂ) :=
    dirDeriv_normSq hφ
  -- weak derivatives of `φ` are the classical ones
  obtain ⟨hφH, hwp, -⟩ := memH_of_contDiff_hasCompactSupport hφ.smooth hφ.compact 1
  have hm1 : ((1 : ℕ), (0 : ℕ)) ∈ multiIdx 1 := by simp [mem_multiIdx]
  have hm2 : ((0 : ℕ), (1 : ℕ)) ∈ multiIdx 1 := by simp [mem_multiIdx]
  have hw1 : weakPartial (1, 0) φ =ᵐ[volume] dirDeriv 1 φ := hwp (1, 0) hm1
  have hw2 : weakPartial (0, 1) φ =ᵐ[volume] dirDeriv Complex.I φ := hwp (0, 1) hm2
  -- integrability of the left side
  have hUb := ae_norm_le_toReal_eLpNorm_top hU
  have hint := (dotGrad_mul_conj_bound ENNReal.toReal_nonneg hU.1 hUb
    (hφH.memLp_weakPartial hm1).1 (hφH.memLp_weakPartial hm2).1 (hφ.memLp 2 volume)).1
  -- the weak-derivative identities tested against `ψ = |φ|²`
  have E1 : ∫ x, U x * dirDeriv 1 ψ x = -∫ x, G₁ x * ψ x := by
    have := hd₁ ψ hψ
    simpa [pdList] using this
  have E2 : ∫ x, U x * dirDeriv Complex.I ψ x = -∫ x, G₂ x * ψ x := by
    have := hd₂ ψ hψ
    simpa [pdList] using this
  have hψi : Integrable ψ volume := memLp_one_iff_integrable.1 (hψ.memLp 1 volume)
  have hI1 : Integrable (fun x => U x * dirDeriv 1 ψ x) volume :=
    (memLp_one_iff_integrable.1 ((hψ.dirDeriv 1).memLp 1 volume)).mul_of_top_right hU
  have hI2 : Integrable (fun x => U x * dirDeriv Complex.I ψ x) volume :=
    (memLp_one_iff_integrable.1 ((hψ.dirDeriv Complex.I).memLp 1 volume)).mul_of_top_right hU
  have hJ1 : Integrable (fun x => G₁ x * ψ x) volume := hψi.mul_of_top_right hG₁
  have hJ2 : Integrable (fun x => G₂ x * ψ x) volume := hψi.mul_of_top_right hG₂
  -- real forms
  set a1 : ℂ → ℝ := fun x => 2 * (dirDeriv 1 φ x * conj (φ x)).re with ha1
  set a2 : ℂ → ℝ := fun x => 2 * (dirDeriv Complex.I φ x * conj (φ x)).re with ha2
  have f1 : (fun x => (U x).re * a1 x) = fun x => (U x * dirDeriv 1 ψ x).re := by
    funext x
    rw [hdψ]
    simp [Complex.mul_re, a1]
  have f2 : (fun x => (U x).im * a2 x) = fun x => (U x * dirDeriv Complex.I ψ x).im := by
    funext x
    rw [hdψ]
    simp [Complex.mul_im, a2]
  have g1 : (fun x => (G₁ x).re * ‖φ x‖ ^ 2) = fun x => (G₁ x * ψ x).re := by
    funext x
    rw [hψdef, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have g2 : (fun x => (G₂ x).im * ‖φ x‖ ^ 2) = fun x => (G₂ x * ψ x).im := by
    funext x
    rw [hψdef, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hf1i : Integrable (fun x => (U x).re * a1 x) volume := f1 ▸ hI1.re
  have hf2i : Integrable (fun x => (U x).im * a2 x) volume := f2 ▸ hI2.im
  have hg1i : Integrable (fun x => (G₁ x).re * ‖φ x‖ ^ 2) volume := g1 ▸ hJ1.re
  have hg2i : Integrable (fun x => (G₂ x).im * ‖φ x‖ ^ 2) volume := g2 ▸ hJ2.im
  have R1 : ∫ x, (U x).re * a1 x = -∫ x, (G₁ x).re * ‖φ x‖ ^ 2 := by
    rw [f1, g1]
    have h1 := integral_re hI1
    have h2 := integral_re hJ1
    simp only [RCLike.re_to_complex] at h1 h2
    rw [h1, h2, E1, Complex.neg_re]
  have R2 : ∫ x, (U x).im * a2 x = -∫ x, (G₂ x).im * ‖φ x‖ ^ 2 := by
    rw [f2, g2]
    have h1 := integral_im hI2
    have h2 := integral_im hJ2
    simp only [RCLike.im_to_complex] at h1 h2
    rw [h1, h2, E2, Complex.neg_im]
  -- the left side
  have L : (∫ x, dotGrad U φ x * conj (φ x)).re =
      ∫ x, ((U x).re * a1 x + (U x).im * a2 x) / 2 := by
    have h1 := integral_re hint
    simp only [RCLike.re_to_complex] at h1
    rw [← h1]
    refine integral_congr_ae ?_
    filter_upwards [hw1, hw2] with x e1 e2
    simp only [dotGrad, e1, e2, a1, a2]
    rw [add_mul, mul_assoc, mul_assoc, Complex.add_re, Complex.re_ofReal_mul,
      Complex.re_ofReal_mul]
    ring
  rw [L, integral_div, integral_add hf1i hf2i, R1, R2]
  have hsum : (fun x => ((G₁ x).re + (G₂ x).im) * ‖φ x‖ ^ 2) =
      fun x => (G₁ x).re * ‖φ x‖ ^ 2 + (G₂ x).im * ‖φ x‖ ^ 2 := by
    funext x
    ring
  rw [hsum, integral_add hg1i hg2i]
  ring

end NonUniqueEuler.Sob.TransportEnergyAux
