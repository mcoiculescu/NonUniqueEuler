import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Helper for `lem:iter-cauchy`: the comparison argument of the proof

`B_global_smooth.tex:374-379`: from `|d/dt e²| ≤ 2 e g'` and `e(0) = 0` one gets
`e(t) ≤ g(t) - g(0)` (the manuscript writes `|d/dt (e² + ε)^{1/2}| ≤ 2RΨ e_j` and lets
`ε → 0`). Here `f = e²`; the argument is the one of the manuscript: for `ε > 0` the function
`(f + ε)^{1/2} - g` has nonpositive derivative, hence is antitone, and `ε → 0`.

Pure real analysis; fully proved.
-/

noncomputable section

open Set

namespace NonUniqueEuler.Smooth.IterCauchyAux

/-- **Comparison.** Let `f ≥ 0` with `f(0) = 0`, `g` with `g' ≥ 0`, both differentiable on
`[0, T]`, and `|f'| ≤ 2 √f g'` there. Then `√(f t) ≤ g t - g 0` on `[0, T]`. -/
theorem sqrt_le_sub_of_hasDerivAt {f f' g g' : ℝ → ℝ} {T : ℝ}
    (hf : ∀ t ∈ Icc 0 T, HasDerivAt f (f' t) t) (hf0 : f 0 = 0)
    (hfnn : ∀ t ∈ Icc 0 T, 0 ≤ f t)
    (hg : ∀ t ∈ Icc 0 T, HasDerivAt g (g' t) t) (hg'nn : ∀ t ∈ Icc 0 T, 0 ≤ g' t)
    (hbound : ∀ t ∈ Icc 0 T, |f' t| ≤ 2 * Real.sqrt (f t) * g' t) :
    ∀ t ∈ Icc 0 T, Real.sqrt (f t) ≤ g t - g 0 := by
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  refine le_of_forall_pos_le_add fun η hη => ?_
  set ε := η ^ 2 with hε_def
  have hε : 0 < ε := by positivity
  -- `h = (f + ε)^{1/2} - g` is antitone on `[0, T]`
  set h : ℝ → ℝ := fun s => Real.sqrt (f s + ε) - g s with hh
  have hpos : ∀ s ∈ Icc 0 T, f s + ε ≠ 0 := fun s hs => (by linarith [hfnn s hs] : 0 < f s + ε).ne'
  have hderiv : ∀ s ∈ Icc 0 T,
      HasDerivAt h (f' s / (2 * Real.sqrt (f s + ε)) - g' s) s := by
    intro s hs
    exact (((hf s hs).add_const ε).sqrt (hpos s hs)).sub (hg s hs)
  have hcont : ContinuousOn h (Icc 0 T) := fun s hs =>
    (hderiv s hs).continuousAt.continuousWithinAt
  have hint : interior (Icc (0 : ℝ) T) = Ioo 0 T := interior_Icc
  have hanti : AntitoneOn h (Icc 0 T) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T) hcont
      (fun s hs => (hderiv s (interior_subset hs)).hasDerivWithinAt) fun s hs => ?_
    have hs' : s ∈ Icc 0 T := interior_subset hs
    have hsq : 0 < Real.sqrt (f s + ε) := Real.sqrt_pos.2 (by linarith [hfnn s hs'])
    have hle : Real.sqrt (f s) ≤ Real.sqrt (f s + ε) := Real.sqrt_le_sqrt (by linarith)
    have h1 : f' s ≤ 2 * Real.sqrt (f s) * g' s := (le_abs_self _).trans (hbound s hs')
    have h2 : 2 * Real.sqrt (f s) * g' s ≤ 2 * Real.sqrt (f s + ε) * g' s := by
      have := hg'nn s hs'
      nlinarith
    have h3 : f' s / (2 * Real.sqrt (f s + ε)) ≤ g' s := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hle := hanti h0 ht ht.1
  simp only [hh, hf0, zero_add] at hle
  have hsqrtε : Real.sqrt ε = η := by
    rw [hε_def, Real.sqrt_sq hη.le]
  have hmono : Real.sqrt (f t) ≤ Real.sqrt (f t + ε) := Real.sqrt_le_sqrt (by linarith)
  linarith

end NonUniqueEuler.Smooth.IterCauchyAux
