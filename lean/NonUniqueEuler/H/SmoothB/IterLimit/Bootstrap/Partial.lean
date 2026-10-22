import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Helper for `prop:iter-limit`, step 5: `C^{n+1}` from the partial derivatives

Helper of `P/SmoothB/IterLimit/Bootstrap.lean` (`B_global_smooth.tex:449-472`). This replaces the
manuscript's appeal to Schwarz's theorem and the classes `𝒞^l(T)`: a function `F(t, x)` on
`ℝ × ℝ²` whose time derivative `∂_t F` exists everywhere, whose slices `F(t, ·)` are
differentiable, and whose partial derivatives `∂_t F`, `∂_1 F = DF(t)(x)·1`, `∂_2 F = DF(t)(x)·i`
are `C^n` in `(t, x)`, is `C^{n+1}` (`contDiff_succ_of_partials`). The proof uses Mathlib's
`hasStrictFDerivAt_uncurry_coprod` (continuous partial derivatives give a total derivative) and
`contDiff_succ_iff_fderiv_apply`.
-/

noncomputable section

open Filter Topology

namespace NonUniqueEuler.Smooth.BootstrapAux

/-- A real-linear map on `ℂ` is determined by its values at `1` and `i` (local copy). -/
theorem clm_apply_eq_re_im' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : ℂ →L[ℝ] E) (v : ℂ) : L v = v.re • L 1 + v.im • L Complex.I := by
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul]

/-- `C^{n+1}` from the partial derivatives: if `∂_t F` exists everywhere, the slices `F(t, ·)` are
differentiable, and `∂_t F`, `DF(t)(x)·1`, `DF(t)(x)·i` are `C^n` in `(t, x)`, then `F` is
`C^{n+1}` on `ℝ × ℂ`. -/
theorem contDiff_succ_of_partials {n : ℕ} {F : ℝ → ℂ → ℂ} {Ft : ℝ × ℂ → ℂ}
    (ht : ∀ p : ℝ × ℂ, HasDerivAt (fun s => F s p.2) (Ft p) p.1)
    (hx : ∀ t, Differentiable ℝ (F t))
    (hFt : ContDiff ℝ n Ft)
    (hF1 : ContDiff ℝ n (fun p : ℝ × ℂ => fderiv ℝ (F p.1) p.2 1))
    (hFI : ContDiff ℝ n (fun p : ℝ × ℂ => fderiv ℝ (F p.1) p.2 Complex.I)) :
    ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (fun p : ℝ × ℂ => F p.1 p.2) := by
  set f₁ : ℝ → ℂ → ℝ →L[ℝ] ℂ := fun t x => (1 : ℝ →L[ℝ] ℝ).smulRight (Ft (t, x)) with hf₁
  set f₂ : ℝ → ℂ → ℂ →L[ℝ] ℂ := fun t x => fderiv ℝ (F t) x with hf₂
  -- the space derivative applied to a vector
  have happ : ∀ (y : ℂ) (p : ℝ × ℂ), fderiv ℝ (F p.1) p.2 y =
      y.re • fderiv ℝ (F p.1) p.2 1 + y.im • fderiv ℝ (F p.1) p.2 Complex.I :=
    fun y p => clm_apply_eq_re_im' _ y
  have hcy : ∀ y : ℂ, ContDiff ℝ n (fun p : ℝ × ℂ => fderiv ℝ (F p.1) p.2 y) := by
    intro y
    have : ContDiff ℝ n (fun p : ℝ × ℂ =>
        y.re • fderiv ℝ (F p.1) p.2 1 + y.im • fderiv ℝ (F p.1) p.2 Complex.I) :=
      (hF1.const_smul y.re).add (hFI.const_smul y.im)
    have he : (fun p : ℝ × ℂ =>
        y.re • fderiv ℝ (F p.1) p.2 1 + y.im • fderiv ℝ (F p.1) p.2 Complex.I) =
        fun p : ℝ × ℂ => fderiv ℝ (F p.1) p.2 y := funext fun p => (happ y p).symm
    rwa [he] at this
  have cf₁ : Continuous (Function.uncurry f₁) := by
    have : ContDiff ℝ n (fun p : ℝ × ℂ => (1 : ℝ →L[ℝ] ℝ).smulRight (Ft p)) :=
      contDiff_const.smulRight hFt
    exact this.continuous
  have cf₂ : Continuous (Function.uncurry f₂) :=
    continuous_clm_apply.2 fun y => (hcy y).continuous
  have hD : ∀ p : ℝ × ℂ, HasFDerivAt (fun q : ℝ × ℂ => F q.1 q.2)
      ((f₁ p.1 p.2).coprod (f₂ p.1 p.2)) p := by
    intro p
    have := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := p) (f := F) (f₁ := f₁) (f₂ := f₂)
      (Eventually.of_forall fun v => (ht v).hasFDerivAt)
      (Eventually.of_forall fun v => (hx v.1 v.2).hasFDerivAt)
      cf₁.continuousAt cf₂.continuousAt
    exact this.hasFDerivAt
  have hfd : ∀ p : ℝ × ℂ, fderiv ℝ (fun q : ℝ × ℂ => F q.1 q.2) p =
      (f₁ p.1 p.2).coprod (f₂ p.1 p.2) := fun p => (hD p).fderiv
  rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv_apply]
  refine ⟨fun p => (hD p).differentiableAt, fun h => absurd h (WithTop.natCast_ne_top n), ?_⟩
  intro y
  have hy : ∀ p : ℝ × ℂ, fderiv ℝ (fun q : ℝ × ℂ => F q.1 q.2) p y =
      y.1 • Ft p + fderiv ℝ (F p.1) p.2 y.2 := by
    intro p
    rw [hfd p]
    simp [hf₁, hf₂]
  have he : (fun p : ℝ × ℂ => fderiv ℝ (fun q : ℝ × ℂ => F q.1 q.2) p y) =
      fun p : ℝ × ℂ => y.1 • Ft p + fderiv ℝ (F p.1) p.2 y.2 := funext hy
  rw [he]
  exact (hFt.const_smul y.1).add (hcy y.2)

end NonUniqueEuler.Smooth.BootstrapAux
