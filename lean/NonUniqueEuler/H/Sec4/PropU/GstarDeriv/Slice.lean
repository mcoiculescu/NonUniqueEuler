import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.Basic

/-!
# Helpers for `P/Sec4/PropU/GstarDeriv`: derivatives in one variable of parametric families

* `continuousOn_iteratedDeriv_slice`: if `F : ℝ × P → ℂ` is `C^∞` on `ℝ × W` (`W` open), then
  every `ξ`-derivative `∂_ξ^k F(ξ, p)` is jointly continuous on `ℝ × W` (step 2 of the proof
  sketch of `I/Sec4/PropU/GstarDeriv.lean`, for the Riccati coefficient);
* `derivs_deriv`, `derivs_add_mul`: the hypotheses "smooth in `ξ` for each parameter, with
  jointly continuous `ξ`-derivatives" are stable under `∂_ξ` and linear combinations;
* `continuousOn_iteratedDeriv_zpow_log`: under these hypotheses on `Φ`, every `r`-derivative of
  `r^m Φ(log r; p)` is jointly continuous on `(0,∞) × T` (step 3 of the sketch:
  `∂_r[r^m Φ(log r)] = r^{m-1}(Φ' + mΦ)(log r)`).

All results are fully proved.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace NonUniqueEuler

namespace GstarDerivH

section Slice

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The derivative of a slice `ξ ↦ F(ξ, p)` is the partial derivative `DF(ξ,p)(1,0)`. -/
theorem deriv_slice {F : ℝ × P → ℂ} {ξ : ℝ} {p : P} (hF : DifferentiableAt ℝ F (ξ, p)) :
    deriv (fun η => F (η, p)) ξ = fderiv ℝ F (ξ, p) ((1 : ℝ), (0 : P)) := by
  have h1 : HasDerivAt (fun η : ℝ => (η, p)) ((1 : ℝ), (0 : P)) ξ :=
    (hasDerivAt_id ξ).prodMk (hasDerivAt_const ξ p)
  exact (hF.hasFDerivAt.comp_hasDerivAt ξ h1).deriv

/-- **`ξ`-derivatives of a jointly smooth family are jointly continuous.** -/
theorem continuousOn_iteratedDeriv_slice {W : Set P} (hW : IsOpen W) :
    ∀ (k : ℕ) {F : ℝ × P → ℂ}, ContDiffOn ℝ ∞ F (univ ×ˢ W) →
      ContinuousOn (fun q : ℝ × P => iteratedDeriv k (fun ξ => F (ξ, q.2)) q.1) (univ ×ˢ W)
  | 0, F, hF => by
      simp only [iteratedDeriv_zero]
      exact hF.continuousOn
  | k + 1, F, hF => by
      have hU : IsOpen ((univ : Set ℝ) ×ˢ W) := isOpen_univ.prod hW
      have hF' : ContDiffOn ℝ ∞ (fun q : ℝ × P => fderiv ℝ F q ((1 : ℝ), (0 : P)))
          (univ ×ˢ W) :=
        (hF.fderiv_of_isOpen hU le_rfl).clm_apply
          (contDiffOn_const (c := ((1 : ℝ), (0 : P))))
      refine (continuousOn_iteratedDeriv_slice hW k hF').congr fun q hq => ?_
      simp only
      rw [iteratedDeriv_succ']
      congr 1
      funext ξ
      have hmem : (ξ, q.2) ∈ univ ×ˢ W := ⟨mem_univ _, hq.2⟩
      exact deriv_slice ((hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hmem))

end Slice

section Family

variable {P : Type*} [TopologicalSpace P] {T : Set P}

/-- The `ξ`-derivative of a family that is smooth in `ξ` with jointly continuous
`ξ`-derivatives has the same properties. -/
theorem derivs_deriv {Φ : ℝ → P → ℂ} (hΦ : ∀ p ∈ T, ContDiff ℝ ∞ (fun ξ => Φ ξ p))
    (hΦd : ∀ k : ℕ, ContinuousOn (fun q : ℝ × P => iteratedDeriv k (fun ξ => Φ ξ q.2) q.1)
      (univ ×ˢ T)) :
    (∀ p ∈ T, ContDiff ℝ ∞ (fun ξ => deriv (fun η => Φ η p) ξ)) ∧
      ∀ k : ℕ, ContinuousOn
        (fun q : ℝ × P => iteratedDeriv k (fun ξ => deriv (fun η => Φ η q.2) ξ) q.1)
        (univ ×ˢ T) := by
  refine ⟨fun p hp => (contDiff_infty_iff_deriv.mp (hΦ p hp)).2, fun k => ?_⟩
  refine (hΦd (k + 1)).congr fun q _ => ?_
  simp only
  rw [iteratedDeriv_succ']

/-- Linear combinations `Φ₁ + c Φ₂` of such families are such families. -/
theorem derivs_add_mul {Φ₁ Φ₂ : ℝ → P → ℂ} (c : ℂ)
    (h₁ : ∀ p ∈ T, ContDiff ℝ ∞ (fun ξ => Φ₁ ξ p))
    (h₁d : ∀ k : ℕ, ContinuousOn (fun q : ℝ × P => iteratedDeriv k (fun ξ => Φ₁ ξ q.2) q.1)
      (univ ×ˢ T))
    (h₂ : ∀ p ∈ T, ContDiff ℝ ∞ (fun ξ => Φ₂ ξ p))
    (h₂d : ∀ k : ℕ, ContinuousOn (fun q : ℝ × P => iteratedDeriv k (fun ξ => Φ₂ ξ q.2) q.1)
      (univ ×ˢ T)) :
    (∀ p ∈ T, ContDiff ℝ ∞ (fun ξ => Φ₁ ξ p + c * Φ₂ ξ p)) ∧
      ∀ k : ℕ, ContinuousOn
        (fun q : ℝ × P => iteratedDeriv k (fun ξ => Φ₁ ξ q.2 + c * Φ₂ ξ q.2) q.1)
        (univ ×ˢ T) := by
  refine ⟨fun p hp => (h₁ p hp).add (contDiff_const.mul (h₂ p hp)), fun k => ?_⟩
  refine ((h₁d k).add ((continuousOn_const (c := c)).mul (h₂d k))).congr fun q hq => ?_
  have hc₁ : ContDiffAt ℝ k (fun ξ => Φ₁ ξ q.2) q.1 :=
    ((h₁ q.2 hq.2).of_le (by exact_mod_cast le_top)).contDiffAt
  have hc₂ : ContDiffAt ℝ k (fun ξ => c * Φ₂ ξ q.2) q.1 :=
    ((contDiff_const.mul (h₂ q.2 hq.2)).of_le (by exact_mod_cast le_top)).contDiffAt
  rw [iteratedDeriv_fun_add hc₁ hc₂, iteratedDeriv_const_mul_field]
  rfl

/-- `∂_r[r^m Φ(log r)] = r^{m-1}(Φ'(log r) + mΦ(log r))` for `r ≠ 0`. -/
theorem deriv_zpow_smul_log {φ : ℝ → ℂ} (hφ : Differentiable ℝ φ) (m : ℤ) {r : ℝ}
    (hr : r ≠ 0) :
    deriv (fun x : ℝ => x ^ m • φ (Real.log x)) r =
      r ^ (m - 1) • (deriv φ (Real.log r) + (m : ℂ) * φ (Real.log r)) := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ m) ((m : ℝ) * r ^ (m - 1)) r :=
    hasDerivAt_zpow m r (Or.inl hr)
  have h2 : HasDerivAt (fun x : ℝ => φ (Real.log x)) (r⁻¹ • deriv φ (Real.log r)) r :=
    (hφ (Real.log r)).hasDerivAt.scomp r (Real.hasDerivAt_log hr)
  rw [(h1.fun_smul h2).deriv, zpow_sub_one₀ hr m]
  simp only [Complex.real_smul]
  push_cast
  ring

/-- **`r`-derivatives of `r^m Φ(log r; p)` are jointly continuous on `(0,∞) × T`.** -/
theorem continuousOn_iteratedDeriv_zpow_log :
    ∀ (j : ℕ) (m : ℤ) {Φ : ℝ → P → ℂ}, (∀ p ∈ T, ContDiff ℝ ∞ (fun ξ => Φ ξ p)) →
      (∀ k : ℕ, ContinuousOn (fun q : ℝ × P => iteratedDeriv k (fun ξ => Φ ξ q.2) q.1)
        (univ ×ˢ T)) →
      ContinuousOn
        (fun q : ℝ × P => iteratedDeriv j (fun r : ℝ => r ^ m • Φ (Real.log r) q.2) q.1)
        (Ioi 0 ×ˢ T)
  | 0, m, Φ, _, hΦd => by
      simp only [iteratedDeriv_zero]
      have h0 := hΦd 0
      simp only [iteratedDeriv_zero] at h0
      have hA : ContinuousOn (fun q : ℝ × P => q.1 ^ m) (Ioi 0 ×ˢ T) :=
        continuousOn_fst.zpow₀ m fun q hq => Or.inl (ne_of_gt hq.1)
      have hlog : ContinuousOn (fun q : ℝ × P => (Real.log q.1, q.2)) (Ioi 0 ×ˢ T) :=
        (continuousOn_fst.log fun q hq => ne_of_gt hq.1).prodMk continuousOn_snd
      have hB : ContinuousOn (fun q : ℝ × P => Φ (Real.log q.1) q.2) (Ioi 0 ×ˢ T) :=
        h0.comp hlog fun q hq => ⟨mem_univ _, hq.2⟩
      exact hA.smul hB
  | j + 1, m, Φ, hΦ, hΦd => by
      obtain ⟨hD, hDd⟩ := derivs_deriv hΦ hΦd
      obtain ⟨hΨ, hΨd⟩ := derivs_add_mul (m : ℂ) hD hDd hΦ hΦd
      refine (continuousOn_iteratedDeriv_zpow_log j (m - 1) hΨ hΨd).congr fun q hq => ?_
      simp only
      rw [iteratedDeriv_succ']
      apply Filter.EventuallyEq.iteratedDeriv_eq
      filter_upwards [Ioi_mem_nhds hq.1] with r hr
      exact deriv_zpow_smul_log ((hΦ q.2 hq.2).differentiable (by simp)) m (ne_of_gt hr)

end Family

end GstarDerivH

end NonUniqueEuler
