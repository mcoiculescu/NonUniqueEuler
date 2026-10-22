import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Helpers for `P/Infra/AngularFourier/NormEquiv/ProfileDeriv`: parametric interval integrals

For `F : ℝ × ℝ → ℂ` smooth, `r ↦ ∫_a^b F(r, θ) dθ` is smooth, and its derivative is the
integral of the partial derivative `∂_r F = DF(·)(1, 0)` (`paramInt_hasDerivAt`,
`paramInt_contDiff`). Mathlib has the derivative under the integral sign
(`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`) but not the `C^∞`
statement; we iterate it.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace NonUniqueEuler.Ang.NEProfileDerivAux

/-- The partial derivative in the first variable, `∂_r F (r, θ) = DF(r, θ)(1, 0)`. -/
def d1 (F : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  fderiv ℝ F p (1, 0)

theorem contDiff_d1 {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (d1 F) :=
  (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem hasDerivAt_d1 {F : ℝ × ℝ → ℂ} (hF : Differentiable ℝ F) (r θ : ℝ) :
    HasDerivAt (fun s => F (s, θ)) (d1 F (r, θ)) r := by
  have h1 : HasDerivAt (fun s : ℝ => (s, θ)) ((1 : ℝ), (0 : ℝ)) r :=
    (hasDerivAt_id r).prodMk (hasDerivAt_const r θ)
  have h2 := (hF (r, θ)).hasFDerivAt.comp_hasDerivAt r h1
  simpa [d1, Function.comp_def] using h2

/-- Derivative under the integral sign for a `C¹` integrand. -/
theorem paramInt_hasDerivAt {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ 1 F) (a b r : ℝ) :
    HasDerivAt (fun s => ∫ θ in a..b, F (s, θ)) (∫ θ in a..b, d1 F (r, θ)) r := by
  have hFd : Differentiable ℝ F := hF.differentiable one_ne_zero
  have hd1c : Continuous (d1 F) :=
    ((hF.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have hK : IsCompact (Icc (r - 1) (r + 1) ×ˢ uIcc a b) := isCompact_Icc.prod isCompact_uIcc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hd1c.continuousOn
  have hs : Icc (r - 1) (r + 1) ∈ 𝓝 r := Icc_mem_nhds (by linarith) (by linarith)
  have hFc : Continuous F := hF.continuous
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s θ => F (s, θ)) (F' := fun s θ => d1 F (s, θ)) (bound := fun _ => M) hs
    (Eventually.of_forall fun s => ?_) ?_ ?_ ?_ intervalIntegrable_const ?_).2
  · exact (hFc.comp (Continuous.prodMk_right s)).aestronglyMeasurable
  · exact (hFc.comp (Continuous.prodMk_right r)).intervalIntegrable a b
  · exact (hd1c.comp (Continuous.prodMk_right r)).aestronglyMeasurable
  · refine Eventually.of_forall fun t ht x hx => hM (x, t) ⟨hx, ?_⟩
    exact uIoc_subset_uIcc ht
  · exact Eventually.of_forall fun t _ x _ => hasDerivAt_d1 hFd x t

theorem paramInt_deriv {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ 1 F) (a b : ℝ) :
    deriv (fun s => ∫ θ in a..b, F (s, θ)) = fun r => ∫ θ in a..b, d1 F (r, θ) := by
  funext r
  exact (paramInt_hasDerivAt hF a b r).deriv

/-- `r ↦ ∫_a^b F(r, θ) dθ` is `C^∞` for `F` smooth. -/
theorem paramInt_contDiff {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (a b : ℝ) :
    ContDiff ℝ ∞ (fun s => ∫ θ in a..b, F (s, θ)) := by
  rw [contDiff_infty]
  intro n
  induction n generalizing F with
  | zero =>
    rw [Nat.cast_zero, contDiff_zero]
    have h1 : ContDiff ℝ 1 F := hF.of_le (by simp)
    exact continuous_iff_continuousAt.2 fun r =>
      (paramInt_hasDerivAt h1 a b r).continuousAt
  | succ n ih =>
    have h1 : ContDiff ℝ 1 F := hF.of_le (by simp)
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
    refine ⟨fun r => (paramInt_hasDerivAt h1 a b r).differentiableAt, by simp, ?_⟩
    rw [paramInt_deriv h1 a b]
    exact ih (contDiff_d1 hF)

end NonUniqueEuler.Ang.NEProfileDerivAux
