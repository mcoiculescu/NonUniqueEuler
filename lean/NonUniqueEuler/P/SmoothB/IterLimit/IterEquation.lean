import NonUniqueEuler.Defs.SmoothB.Iteration
import NonUniqueEuler.I.SmoothB.Iterates
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Proof: `prop:iter-limit`, step 4a — the differentiated transport equation of the iterates

Proof of `I/SmoothB/IterLimit/IterEquation.lean` (`B_global_smooth.tex:432-436`).

For a `C^∞` space–time function `Φ : ℝ × ℂ → E` write `∂_w Φ (p) = DΦ(p) w`. The steps:
1. slices: `D_y Φ(t, y) v = DΦ(t, y)(0, v)` and `∂_t Φ(t, x) = DΦ(t, x)(1, 0)`
   (`fderiv_slice_snd`, `hasDerivAt_slice_fst`);
2. `∂_u ∂_w Φ = ∂_w ∂_u Φ` for `C^∞` `Φ` (symmetry of the second derivative,
   `fderiv_partial_comm`);
3. `∂_t ∂_x^{vs} f = ∂_x^{vs} ∂_t f` for every list of directions (`fderiv_time_iterDirDeriv`,
   induction on `vs`);
4. `∂_t ω^{[j+1]} = -v^{[j]} · ∇ω^{[j+1]}` (`iterates_flow`), and `∂_x^γ` commutes with `-`.
-/

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace NonUniqueEuler.Smooth

namespace IterEquationAux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A spatial slice derivative is the full derivative in the direction `(0, v)`. -/
theorem fderiv_slice_snd {Φ : ℝ × ℂ → E} {t : ℝ} {x : ℂ} (hΦ : DifferentiableAt ℝ Φ (t, x))
    (v : ℂ) : fderiv ℝ (fun y => Φ (t, y)) x v = fderiv ℝ Φ (t, x) (0, v) := by
  have hd : HasFDerivAt (fun y => Φ (t, y))
      ((fderiv ℝ Φ (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ ℂ)) x :=
    hΦ.hasFDerivAt.comp x (hasFDerivAt_prodMk_right (𝕜 := ℝ) t x)
  rw [hd.fderiv]
  rfl

/-- The time slice has derivative `DΦ(t, x)(1, 0)`. -/
theorem hasDerivAt_slice_fst {Φ : ℝ × ℂ → E} {t : ℝ} {x : ℂ} (hΦ : DifferentiableAt ℝ Φ (t, x)) :
    HasDerivAt (fun s => Φ (s, x)) (fderiv ℝ Φ (t, x) (1, 0)) t := by
  have hd := hΦ.hasFDerivAt.comp t (hasFDerivAt_prodMk_left (𝕜 := ℝ) t x)
  exact hd.hasDerivAt

/-- A directional derivative of a `C^∞` function is `C^∞`. -/
theorem contDiff_partial {Φ : ℝ × ℂ → E} (hΦ : ContDiff ℝ ∞ Φ) (w : ℝ × ℂ) :
    ContDiff ℝ ∞ (fun p => fderiv ℝ Φ p w) :=
  (hΦ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- The derivative of `p ↦ DΦ(p) u` in the direction `w` is `D²Φ(q) w u`. -/
theorem fderiv_partial_apply {Φ : ℝ × ℂ → E} (hΦ : ContDiff ℝ ∞ Φ) (u q w : ℝ × ℂ) :
    fderiv ℝ (fun p => fderiv ℝ Φ p u) q w = fderiv ℝ (fderiv ℝ Φ) q w u := by
  have hc : DifferentiableAt ℝ (fderiv ℝ Φ) q :=
    ((hΦ.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) q
  rw [fderiv_clm_apply hc (differentiableAt_const u)]
  simp

/-- Directional derivatives of a `C^∞` function commute. -/
theorem fderiv_partial_comm {Φ : ℝ × ℂ → E} (hΦ : ContDiff ℝ ∞ Φ) (u q w : ℝ × ℂ) :
    fderiv ℝ (fun p => fderiv ℝ Φ p u) q w = fderiv ℝ (fun p => fderiv ℝ Φ p w) q u := by
  rw [fderiv_partial_apply hΦ, fderiv_partial_apply hΦ]
  exact (hΦ.contDiffAt (x := q)).isSymmSndFDerivAt (by simp) w u

/-- Spatial derivatives of a `C^∞` space–time function are `C^∞` in `(t, x)`. -/
theorem contDiff_iterDirDeriv {f : ℝ → ℂ → ℂ} (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (vs : List ℂ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℂ => Sob.iterDirDeriv vs (f p.1) p.2) := by
  induction vs with
  | nil => exact hf
  | cons v vs ih =>
    have h1 : ContDiff ℝ ∞
        (Function.uncurry fun (p : ℝ × ℂ) (y : ℂ) => Sob.iterDirDeriv vs (f p.1) y) :=
      ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
    exact h1.fderiv_apply contDiff_snd contDiff_const (by simp)

/-- `∂^{v :: vs} f(t) = D_y (∂^{vs} f)(t, ·) v`, rewritten with the joint derivative. -/
theorem iterDirDeriv_cons_eq {f : ℝ → ℂ → ℂ} (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (v : ℂ) (vs : List ℂ) :
    (fun p : ℝ × ℂ => Sob.iterDirDeriv (v :: vs) (f p.1) p.2) =
      fun p => fderiv ℝ (fun q : ℝ × ℂ => Sob.iterDirDeriv vs (f q.1) q.2) p (0, v) := by
  funext p
  have hd : DifferentiableAt ℝ (fun q : ℝ × ℂ => Sob.iterDirDeriv vs (f q.1) q.2) (p.1, p.2) :=
    ((contDiff_iterDirDeriv hf vs).differentiable (by simp)) _
  exact fderiv_slice_snd hd v

/-- The time derivative commutes with the spatial derivatives: `∂_t ∂^{vs} f = ∂^{vs} ∂_t f`,
with `∂_t f(t, y) = Df(t, y)(1, 0)`. -/
theorem fderiv_time_iterDirDeriv {f : ℝ → ℂ → ℂ} (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (vs : List ℂ) (t : ℝ) (x : ℂ) :
    fderiv ℝ (fun p : ℝ × ℂ => Sob.iterDirDeriv vs (f p.1) p.2) (t, x) (1, 0) =
      Sob.iterDirDeriv vs (fun y => fderiv ℝ (Function.uncurry f) (t, y) (1, 0)) x := by
  induction vs generalizing t x with
  | nil => rfl
  | cons v vs ih =>
    set g : ℝ → ℂ → ℂ := fun s y => fderiv ℝ (Function.uncurry f) (s, y) (1, 0) with hg_def
    have hg : ContDiff ℝ ∞ (Function.uncurry g) := contDiff_partial hf (1, 0)
    have hΨ := contDiff_iterDirDeriv hf vs
    rw [iterDirDeriv_cons_eq hf, fderiv_partial_comm hΨ]
    have hfun : (fun p : ℝ × ℂ =>
        fderiv ℝ (fun q : ℝ × ℂ => Sob.iterDirDeriv vs (f q.1) q.2) p (1, 0)) =
        fun p : ℝ × ℂ => Sob.iterDirDeriv vs (g p.1) p.2 := by
      funext p
      exact ih p.1 p.2
    rw [hfun]
    have hd : DifferentiableAt ℝ (fun q : ℝ × ℂ => Sob.iterDirDeriv vs (g q.1) q.2) (t, x) :=
      ((contDiff_iterDirDeriv hg vs).differentiable (by simp)) _
    rw [← fderiv_slice_snd hd v]
    rfl

/-- `∂^{vs}(-φ) = -∂^{vs} φ`. -/
theorem iterDirDeriv_neg (vs : List ℂ) (φ : ℂ → ℂ) :
    Sob.iterDirDeriv vs (fun y => -φ y) = fun y => -Sob.iterDirDeriv vs φ y := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    funext y
    change fderiv ℝ (Sob.iterDirDeriv vs (fun y => -φ y)) y v =
      -(fderiv ℝ (Sob.iterDirDeriv vs φ) y v)
    rw [ih, fderiv_fun_neg]
    rfl

end IterEquationAux

open IterEquationAux

variable {ω₀ : ℂ → ℝ} {R₀ : ℝ}

/-- `prop:iter-limit`, step 4a (`B_global_smooth.tex:432-436`): `∂_t ∂_x^γ ω^{[j+1]} =
-∂_x^γ(v^{[j]} · ∇ω^{[j+1]})` on `ℝ × ℝ²`. -/
theorem iter_hasDerivAt_spaceD (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (j : ℕ) (γ : ℕ × ℕ)
    (t : ℝ) (x : ℂ) :
    HasDerivAt (fun s => spaceD γ (ofRealST (iter ω₀ (j + 1))) s x)
      (-(spaceD γ (fun s y => ((fderiv ℝ (iter ω₀ (j + 1) s) y (iterVel ω₀ j s y) : ℝ) : ℂ))
        t x)) t := by
  set F := iter ω₀ (j + 1) with hF_def
  have hF : ContDiff ℝ ∞ (Function.uncurry F) := (iterates_smooth_support h hne (j + 1)).1
  have htr := (iterates_flow h hne j).2.2.2.2
  set f : ℝ → ℂ → ℂ := ofRealST F with hf_def
  have hf : ContDiff ℝ ∞ (Function.uncurry f) := Complex.ofRealCLM.contDiff.comp hF
  set Ψ := fun p : ℝ × ℂ => Sob.iterDirDeriv (Sob.pdList γ) (f p.1) p.2 with hΨ_def
  have hΨ : ContDiff ℝ ∞ Ψ := contDiff_iterDirDeriv hf _
  have h1 : HasDerivAt (fun s => Ψ (s, x)) (fderiv ℝ Ψ (t, x) (1, 0)) t :=
    hasDerivAt_slice_fst ((hΨ.differentiable (by simp)) _)
  have h2 := fderiv_time_iterDirDeriv hf (Sob.pdList γ) t x
  -- the time derivative of `f`
  have h3 : (fun y => fderiv ℝ (Function.uncurry f) (t, y) (1, 0)) =
      fun y => -(((fderiv ℝ (F t) y (iterVel ω₀ j t y) : ℝ) : ℂ)) := by
    funext y
    have hc : HasDerivAt (fun s => f s y) (fderiv ℝ (Function.uncurry f) (t, y) (1, 0)) t :=
      hasDerivAt_slice_fst ((hf.differentiable (by simp)) _)
    have hr : HasDerivAt (fun s => F s y) (fderiv ℝ (Function.uncurry F) (t, y) (1, 0)) t :=
      hasDerivAt_slice_fst ((hF.differentiable (by simp)) _)
    have hrc : HasDerivAt (fun s => f s y)
        ((fderiv ℝ (Function.uncurry F) (t, y) (1, 0) : ℝ) : ℂ) t := hr.ofReal_comp
    have hval : fderiv ℝ (Function.uncurry F) (t, y) (1, 0) =
        -(fderiv ℝ (F t) y (iterVel ω₀ j t y)) := by
      rw [← hr.deriv]
      exact eq_neg_of_add_eq_zero_left (htr t y)
    rw [hc.unique hrc, hval]
    push_cast
    rfl
  rw [h3, iterDirDeriv_neg] at h2
  rw [h2] at h1
  exact h1

end NonUniqueEuler.Smooth
