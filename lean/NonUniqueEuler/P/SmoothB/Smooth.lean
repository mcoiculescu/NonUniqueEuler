import NonUniqueEuler.I.SmoothB.IterLimit
import NonUniqueEuler.I.SmoothB.SmoothUnique
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Proof: thm:smooth (1)–(3) and (5) for `Smooth.sol` (the global smooth solution)

Proof of `I/SmoothB/Smooth.lean` (`thm:smooth`, `02_prelim.tex:561-595`; proof
`B_global_smooth.tex:493-521`).

* Existence: `ω₀ = 0` gives `ω ≡ 0` (`isSmoothSolAll_zero`, `B_global_smooth.tex:517-518`);
  otherwise `iter_limit` (`prop:iter-limit`) gives a function with `IsSmoothSolAll ω₀`, so
  `sol_spec` applies.
* Uniqueness in (1)–(3): a function with (1)–(3) for `R₀` is a `C¹` solution on `ℝ`
  (`IsSmoothSol.isC1SolOn_univ`: `C^∞ ⇒ C¹`, the chain rule splits the derivative in the
  direction `(1, v)` into `∂_t ω + v·∇ω`, supports in `B_{R(max(|a|,|b|))}` on `[a, b]`), so (5)
  in the form `isC1SolOn_eq_of_isSmoothSol` (`B_global_smooth.tex:494-513`) identifies it with
  `sol ω₀`.
* (5) for `sol ω₀`: `isC1SolOn_eq_of_isSmoothSol` with `sol_isSmoothSol`.
-/

noncomputable section

open Set Metric

namespace NonUniqueEuler.Smooth

variable {ω₀ : ℂ → ℝ} {R₀ : ℝ}

/-- The derivative of a differentiable space–time function `(t, x) ↦ ω(t, x)` in the direction
`(1, w)` is `∂_t ω(t, x) + ∇ω(t, x)·w`. -/
theorem fderiv_uncurry_one_apply {ω : ℝ → ℂ → ℝ} {t : ℝ} {x : ℂ}
    (hd : DifferentiableAt ℝ (Function.uncurry ω) (t, x)) (w : ℂ) :
    fderiv ℝ (Function.uncurry ω) (t, x) (1, w) =
      deriv (fun s => ω s x) t + fderiv ℝ (ω t) x w := by
  set D := fderiv ℝ (Function.uncurry ω) (t, x) with hD
  have hf : HasFDerivAt (Function.uncurry ω) D (t, x) := hd.hasFDerivAt
  -- time derivative
  have ht : HasDerivAt (fun s => ω s x) (D (1, 0)) t := by
    have h1 : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : ℂ)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
    exact HasFDerivAt.comp_hasDerivAt (x := t) hf h1
  -- space derivative
  have hx : HasFDerivAt (ω t) (D.comp (ContinuousLinearMap.inr ℝ ℝ ℂ)) x := by
    exact HasFDerivAt.comp (x := x) hf (hasFDerivAt_prodMk_right (𝕜 := ℝ) t x)
  rw [ht.deriv, hx.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    ← map_add, Prod.mk_add_mk, add_zero, zero_add]

/-- A function with properties (1)–(3) of thm:smooth for `R₀` is a `C¹` solution on `ℝ` in the
sense of thm:smooth(5) (`B_global_smooth.tex:514-516`). -/
theorem IsSmoothSol.isC1SolOn_univ {ω : ℝ → ℂ → ℝ} (hω : IsSmoothSol ω₀ R₀ ω) :
    IsC1SolOn univ ω₀ ω := by
  have hC1 : ContDiff ℝ 1 (Function.uncurry ω) :=
    hω.contDiff.of_le (by exact_mod_cast le_top)
  refine ⟨hC1.contDiffOn, hω.init, ?_, ?_⟩
  · intro t _ x
    rw [univ_prod_univ, fderivWithin_univ,
      fderiv_uncurry_one_apply (hC1.differentiable one_ne_zero _)]
    exact hω.transport t x
  · intro a b _
    refine ⟨suppRadius ω₀ R₀ (max |a| |b|), fun t ht => ?_⟩
    refine (hω.tsupport_subset t).trans (ball_subset_ball (suppRadius_mono_abs ω₀ R₀ ?_))
    rw [abs_of_nonneg (le_max_of_le_left (abs_nonneg a))]
    rcases le_total 0 t with h0 | h0
    · rw [abs_of_nonneg h0]
      exact (ht.2.trans (le_abs_self b)).trans (le_max_right _ _)
    · rw [abs_of_nonpos h0]
      have : -t ≤ -a := neg_le_neg ht.1
      exact (this.trans (neg_le_abs a)).trans (le_max_left _ _)

/-- Existence of a function with (1)–(3) for every admissible radius
(`B_global_smooth.tex:517-521`). -/
theorem exists_isSmoothSolAll (h : IsSmoothDatum ω₀ R₀) :
    ∃ ω : ℝ → ℂ → ℝ, IsSmoothSolAll ω₀ ω := by
  by_cases hne : ω₀ = 0
  · subst hne
    exact ⟨fun _ _ => 0, isSmoothSolAll_zero⟩
  · obtain ⟨ω, -, -, hω, -⟩ := iter_limit h hne
    exact ⟨ω, hω⟩

/-- thm:smooth (1)–(3) for the chosen solution `Smooth.sol ω₀`, for every admissible radius. -/
theorem sol_isSmoothSolAll (h : IsSmoothDatum ω₀ R₀) : IsSmoothSolAll ω₀ (sol ω₀) :=
  sol_spec (exists_isSmoothSolAll h)

/-- thm:smooth (1)–(3) for `Smooth.sol ω₀` and the radius `R₀`. -/
theorem sol_isSmoothSol (h : IsSmoothDatum ω₀ R₀) : IsSmoothSol ω₀ R₀ (sol ω₀) :=
  (sol_isSmoothSolAll h).isSmoothSol h.tsupport_subset

/-- thm:smooth (1)–(3): for real `ω₀ ∈ C_c^∞(ℝ²)` with `supp ω₀ ⊂ B_{R₀}` there is a unique
`ω ∈ C^∞(ℝ × ℝ²)` with properties (1)–(3). -/
theorem smooth_existsUnique (h : IsSmoothDatum ω₀ R₀) :
    ∃! ω : ℝ → ℂ → ℝ, IsSmoothSol ω₀ R₀ ω := by
  refine ⟨sol ω₀, sol_isSmoothSol h, fun ω' hω' => ?_⟩
  funext t
  exact isC1SolOn_eq_of_isSmoothSol h (sol_isSmoothSol h) ordConnected_univ (mem_univ 0)
    hω'.isC1SolOn_univ t (mem_univ t)

/-- thm:smooth (5) for `Smooth.sol ω₀`: if `I ∋ 0` is an interval and `ω̃ ∈ C¹(I × ℝ²)` satisfies
`ω̃(0) = ω₀`, `∂_t ω̃ + (K_BS ∗ ω̃)·∇ω̃ = 0` on `I × ℝ²`, and for each compact subinterval
`I' ⊂ I`, `supp ω̃(t) ⊂ B_{R̃}` for `t ∈ I'` with `R̃` depending on `I'`, then `ω̃ = ω` on
`I × ℝ²`. -/
theorem smooth_unique (h : IsSmoothDatum ω₀ R₀) {I : Set ℝ} (hI : I.OrdConnected) (h0 : 0 ∈ I)
    {ω' : ℝ → ℂ → ℝ} (hω' : IsC1SolOn I ω₀ ω') :
    ∀ t ∈ I, ω' t = sol ω₀ t :=
  isC1SolOn_eq_of_isSmoothSol h (sol_isSmoothSol h) hI h0 hω'

end NonUniqueEuler.Smooth
