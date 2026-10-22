import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import NonUniqueEuler.Defs.Infra.AngularFourier

/-!
# Proof of `I/Infra/AngularFourier/Derivatives/SmoothSector`: `P_m` preserves `C^∞`

`contDiff_sectorProj`: for `ψ : ℂ → ℂ` of class `C^∞`, the sector projection
`P_m ψ (x) = (2π)⁻¹ ∫₀^{2π} e^{-imφ} ψ(O_φ x) dφ` is `C^∞`.

Proof: differentiation under the integral sign over a compact interval
(`contDiff_intervalIntegral_of_contDiff_uncurry`, by induction on the order, with the
derivative `x ↦ ∫ ∂ₓF(x, t) dt` bounded on `closedBall x 1 × [a, b]` by compactness).
-/

noncomputable section

open MeasureTheory Set Real Filter
open scoped ENNReal ContDiff Topology Interval

namespace NonUniqueEuler.Ang

universe u

/-- Differentiation under the integral sign, one step: for `F` jointly `C^1`, the parametric
interval integral has derivative `∫ ∂ₓF(x, t) dt` at every point. -/
theorem hasFDerivAt_intervalIntegral_of_contDiff_uncurry {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : E → ℝ → G} (hF : ContDiff ℝ 1 (Function.uncurry F)) (a b : ℝ) (x₀ : E) :
    HasFDerivAt (fun x => ∫ t in a..b, F x t)
      (∫ t in a..b, fderiv ℝ (fun y => F y t) x₀) x₀ := by
  -- joint continuity of the derivative
  have hF' : Continuous (Function.uncurry fun x t => fderiv ℝ (fun y => F y t) x) := by
    have h1 : ContDiff ℝ 1 (Function.uncurry fun (p : E × ℝ) (y : E) => F y p.2) := by
      have : (Function.uncurry fun (p : E × ℝ) (y : E) => F y p.2) =
          Function.uncurry F ∘ fun q : (E × ℝ) × E => (q.2, q.1.2) := by
        ext q; rfl
      rw [this]
      exact hF.comp (by fun_prop)
    have h2 := h1.fderiv (g := fun p : E × ℝ => p.1) (n := 0) contDiff_fst (by simp)
    exact h2.continuous
  have hdiff : ∀ (t : ℝ) (x : E), HasFDerivAt (fun y => F y t)
      (fderiv ℝ (fun y => F y t) x) x := by
    intro t x
    have : ContDiff ℝ 1 (fun y => F y t) :=
      hF.comp (contDiff_id.prodMk contDiff_const)
    exact (this.differentiable (by simp) x).hasFDerivAt
  -- bound on the compact set `closedBall x₀ 1 × [[a, b]]`
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x₀ 1).prod isCompact_uIcc).exists_bound_of_continuousOn
    hF'.continuousOn
  have hFc : Continuous (Function.uncurry F) := hF.continuous
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (E := G) (H := E) (F := F) (F' := fun x t => fderiv ℝ (fun y => F y t) x) (a := a) (b := b)
    (bound := fun _ => C) (μ := volume) (𝕜 := ℝ)
    (s := Metric.closedBall x₀ 1) (Metric.closedBall_mem_nhds x₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · refine Filter.Eventually.of_forall fun x => ?_
    exact (hFc.comp (continuous_const.prodMk continuous_id :
      Continuous fun t : ℝ => (x, t))).aestronglyMeasurable
  · exact (hFc.comp (continuous_const.prodMk continuous_id :
      Continuous fun t : ℝ => (x₀, t))).intervalIntegrable a b
  · exact (hF'.comp (continuous_const.prodMk continuous_id :
      Continuous fun t : ℝ => (x₀, t))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun t ht x hx => ?_
    exact hC (x, t) ⟨hx, uIoc_subset_uIcc ht⟩
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun t _ x _ => hdiff t x

/-- Smoothness of parametric interval integrals of jointly smooth integrands (finite order,
by induction; the target space varies along the induction). -/
theorem contDiff_intervalIntegral_of_contDiff_uncurry_nat {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E] (a b : ℝ) (n : ℕ) :
    ∀ {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
      {F : E → ℝ → G}, ContDiff ℝ ∞ (Function.uncurry F) →
        ContDiff ℝ n (fun x => ∫ t in a..b, F x t) := by
  induction n with
  | zero =>
    intro G _ _ _ F hF
    exact contDiff_zero.2 (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hF.continuous a b)
  | succ n ih =>
    intro G _ _ _ F hF
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by norm_cast,
      contDiff_succ_iff_hasFDerivAt]
    refine ⟨fun x => ∫ t in a..b, fderiv ℝ (fun y => F y t) x, ?_, fun x =>
      hasFDerivAt_intervalIntegral_of_contDiff_uncurry (hF.of_le (by simp)) a b x⟩
    apply ih (G := E →L[ℝ] G)
    have h1 : ContDiff ℝ ∞ (Function.uncurry fun (p : E × ℝ) (y : E) => F y p.2) := by
      have : (Function.uncurry fun (p : E × ℝ) (y : E) => F y p.2) =
          Function.uncurry F ∘ fun q : (E × ℝ) × E => (q.2, q.1.2) := by
        ext q; rfl
      rw [this]
      exact hF.comp (by fun_prop)
    have h2 := h1.fderiv (g := fun p : E × ℝ => p.1) (n := ∞) contDiff_fst (by simp)
    exact h2

/-- Smoothness of parametric interval integrals of jointly smooth integrands. -/
theorem contDiff_intervalIntegral_of_contDiff_uncurry {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E] {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] {F : E → ℝ → G} (hF : ContDiff ℝ ∞ (Function.uncurry F)) (a b : ℝ) :
    ContDiff ℝ ∞ (fun x => ∫ t in a..b, F x t) :=
  contDiff_infty.2 fun n => contDiff_intervalIntegral_of_contDiff_uncurry_nat a b n hF

/-- `P_m ψ` is smooth when `ψ` is. -/
theorem contDiff_sectorProj {ψ : ℂ → ℂ} (hψ : ContDiff ℝ ∞ ψ) (m : ℤ) :
    ContDiff ℝ ∞ (sectorProj m ψ) := by
  have hF : ContDiff ℝ ∞ (Function.uncurry fun (x : ℂ) (φ : ℝ) =>
      Complex.exp (-((m : ℂ) * φ * Complex.I)) * ψ (rot φ x)) := by
    have hexp : ∀ c : ℂ, ContDiff ℝ ∞ fun φ : ℝ => Complex.exp (c * φ * Complex.I) := by
      intro c
      exact (Complex.contDiff_exp (𝕜 := ℝ)).comp
        ((contDiff_const.mul Complex.ofRealCLM.contDiff).mul contDiff_const)
    have hrot : ContDiff ℝ ∞ fun p : ℂ × ℝ => rot p.2 p.1 := by
      have e : (fun p : ℂ × ℝ => rot p.2 p.1) =
          fun p => Complex.exp (1 * (p.2 : ℂ) * Complex.I) * p.1 := by
        funext p; simp [rot]
      rw [e]
      exact ((hexp 1).comp contDiff_snd).mul contDiff_fst
    have hneg : ContDiff ℝ ∞ fun p : ℂ × ℝ => Complex.exp (-((m : ℂ) * p.2 * Complex.I)) := by
      have e : (fun p : ℂ × ℝ => Complex.exp (-((m : ℂ) * p.2 * Complex.I))) =
          fun p => Complex.exp (-(m : ℂ) * (p.2 : ℂ) * Complex.I) := by
        funext p; simp [neg_mul]
      rw [e]
      exact (hexp (-(m : ℂ))).comp contDiff_snd
    exact hneg.mul (hψ.comp hrot)
  have := contDiff_intervalIntegral_of_contDiff_uncurry hF 0 (2 * π)
  exact contDiff_const.mul this

end NonUniqueEuler.Ang
