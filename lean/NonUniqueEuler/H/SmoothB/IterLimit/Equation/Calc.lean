import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.Basic
import NonUniqueEuler.Defs.Infra.Sobolev

/-!
# Helper for `prop:iter-limit`, step 4: calculus of iterated directional derivatives

Helper of `P/SmoothB/IterLimit/Equation.lean` (`B_global_smooth.tex:432-448`). For smooth
functions on the plane:
* smoothness of directional derivatives, also jointly in a time parameter
  (`contDiff_iterDirDeriv`, `contDiff_iterDirDeriv_uncurry`);
* directional derivatives commute, so `iterDirDeriv vs f` depends only on `vs` up to
  permutation (`iterDirDeriv_perm`), and every list of directions in `{1, i}` is a permutation of
  some `pdList β` (`exists_perm_pdList`);
* linearity, the product rule and real-linear maps (`iterDirDeriv_add`, `dirDeriv_mul`,
  `iterDirDeriv_clm_comp`);
* the derivative of a real function viewed as complex valued, and `L v = Re v L 1 + Im v L i`.

The lemmas of the first three items are copied from `H/SmoothB/CommR2/Calc.lean` (helper of the
proof `SmoothB/CommR2`, itself copied from `P/Infra/Sobolev/WeakDeriv.lean`); those of the last
item and `contDiff_iterDirDeriv_uncurry` from `H/SmoothB/IterLimit/Basic.lean` (helper of the
proof `SmoothB/IterLimit`). Helper files of other proofs cannot be imported (import rules,
`README.md`).
-/

noncomputable section

open scoped ContDiff

namespace NonUniqueEuler.Smooth.IterLimitEqAux

open Sob

/-! ### Smoothness and commutation -/

theorem contDiff_dirDeriv {φ : ℂ → ℂ} (h : ContDiff ℝ ∞ φ) (v : ℂ) :
    ContDiff ℝ ∞ (dirDeriv v φ) :=
  (ContDiff.fderiv_right (m := ∞) h (by simp)).clm_apply contDiff_const

theorem contDiff_iterDirDeriv {φ : ℂ → ℂ} (h : ContDiff ℝ ∞ φ) (vs : List ℂ) :
    ContDiff ℝ ∞ (iterDirDeriv vs φ) := by
  induction vs with
  | nil => simpa using h
  | cons v vs ih => simpa using contDiff_dirDeriv ih v

theorem differentiable_iterDirDeriv {φ : ℂ → ℂ} (h : ContDiff ℝ ∞ φ) (vs : List ℂ) :
    Differentiable ℝ (iterDirDeriv vs φ) :=
  (contDiff_iterDirDeriv h vs).differentiable (by simp)

/-- Spatial directional derivatives of a `C^∞` space–time function are `C^∞` in `(t, x)`. -/
theorem contDiff_iterDirDeriv_uncurry {F : ℝ → ℂ → ℂ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (vs : List ℂ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℂ => iterDirDeriv vs (F p.1) p.2) := by
  induction vs with
  | nil => exact hF
  | cons v vs ih =>
    have h1 : ContDiff ℝ ∞
        (Function.uncurry fun (p : ℝ × ℂ) (y : ℂ) => iterDirDeriv vs (F p.1) y) :=
      ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
    exact h1.fderiv_apply contDiff_snd contDiff_const (by simp)

/-- A slice `x ↦ f(t, x)` of a `C^∞` space–time function is `C^∞`. -/
theorem contDiff_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → ℂ → E}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (t : ℝ) : ContDiff ℝ ∞ (f t) :=
  hf.comp (contDiff_const.prodMk contDiff_id)

theorem dirDeriv_dirDeriv_eq {φ : ℂ → ℂ} (h : ContDiff ℝ ∞ φ) (v w x : ℂ) :
    dirDeriv v (dirDeriv w φ) x = fderiv ℝ (fderiv ℝ φ) x v w := by
  have hd : Differentiable ℝ (fderiv ℝ φ) :=
    (ContDiff.fderiv_right (m := ∞) h (by simp)).differentiable (by simp)
  have hx : HasFDerivAt (fun y => fderiv ℝ φ y w) ((fderiv ℝ (fderiv ℝ φ) x).flip w) x := by
    have := (hd x).hasFDerivAt.clm_apply (hasFDerivAt_const w x)
    simpa using this
  show fderiv ℝ (fun y => fderiv ℝ φ y w) x v = _
  rw [hx.fderiv]
  rfl

theorem dirDeriv_comm {φ : ℂ → ℂ} (h : ContDiff ℝ ∞ φ) (v w : ℂ) :
    dirDeriv v (dirDeriv w φ) = dirDeriv w (dirDeriv v φ) := by
  funext x
  rw [dirDeriv_dirDeriv_eq h, dirDeriv_dirDeriv_eq h]
  exact (h.contDiffAt.isSymmSndFDerivAt (by simp)).eq v w

/-- For smooth `φ`, `iterDirDeriv vs φ` only depends on `vs` up to permutation. -/
theorem iterDirDeriv_perm {vs ws : List ℂ} (hp : vs.Perm ws) {φ : ℂ → ℂ}
    (h : ContDiff ℝ ∞ φ) : iterDirDeriv vs φ = iterDirDeriv ws φ := by
  induction hp with
  | nil => rfl
  | cons x _ ih => simp only [iterDirDeriv_cons, ih]
  | swap x y l =>
    simp only [iterDirDeriv_cons]
    exact dirDeriv_comm (contDiff_iterDirDeriv h l) y x
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ### Lists of directions -/

theorem mem_pdList {γ : ℕ × ℕ} {v : ℂ} (hv : v ∈ pdList γ) : v = 1 ∨ v = Complex.I := by
  simp only [pdList, List.mem_append, List.mem_replicate] at hv
  rcases hv with h | h
  · exact Or.inl h.2
  · exact Or.inr h.2

/-- A list of directions in `{1, i}` is a permutation of `pdList β`, `|β| = |w|`. -/
theorem exists_perm_pdList {w : List ℂ} (hw : ∀ v ∈ w, v = 1 ∨ v = Complex.I) :
    ∃ β : ℕ × ℕ, w.Perm (pdList β) ∧ β.1 + β.2 = w.length := by
  induction w with
  | nil => exact ⟨(0, 0), by simp [pdList], rfl⟩
  | cons v w ih =>
    obtain ⟨β, hβ, hl⟩ := ih (fun x hx => hw x (by simp [hx]))
    rcases hw v (by simp) with rfl | rfl
    · refine ⟨(β.1 + 1, β.2), ?_, by simp; omega⟩
      simp only [pdList, List.replicate_succ, List.cons_append]
      exact hβ.cons 1
    · refine ⟨(β.1, β.2 + 1), ?_, by simp; omega⟩
      simp only [pdList, List.replicate_succ]
      exact (hβ.cons _).trans List.perm_middle.symm

/-! ### Linearity, products and real-linear maps -/

theorem dirDeriv_add {f₁ f₂ : ℂ → ℂ} (h₁ : Differentiable ℝ f₁) (h₂ : Differentiable ℝ f₂)
    (v : ℂ) : dirDeriv v (fun x => f₁ x + f₂ x) = fun x => dirDeriv v f₁ x + dirDeriv v f₂ x := by
  funext x
  simp only [dirDeriv]
  rw [fderiv_fun_add (h₁ x) (h₂ x)]
  rfl

theorem dirDeriv_mul {a h : ℂ → ℂ} (ha : Differentiable ℝ a) (hh : Differentiable ℝ h)
    (v : ℂ) : dirDeriv v (fun x => a x * h x) =
      fun x => dirDeriv v a x * h x + a x * dirDeriv v h x := by
  funext x
  simp only [dirDeriv]
  rw [fderiv_fun_mul (ha x) (hh x)]
  simp only [FunLike.coe_add, Pi.add_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem iterDirDeriv_add {f₁ f₂ : ℂ → ℂ} (h₁ : ContDiff ℝ ∞ f₁) (h₂ : ContDiff ℝ ∞ f₂)
    (vs : List ℂ) : iterDirDeriv vs (fun x => f₁ x + f₂ x) =
      fun x => iterDirDeriv vs f₁ x + iterDirDeriv vs f₂ x := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    rw [iterDirDeriv_cons, ih, dirDeriv_add (differentiable_iterDirDeriv h₁ vs)
      (differentiable_iterDirDeriv h₂ vs)]
    rfl

/-- `∂_{vs}(L ∘ f) = L ∘ ∂_{vs} f` for a real-linear map `L`. -/
theorem iterDirDeriv_clm_comp (L : ℂ →L[ℝ] ℂ) {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
    (vs : List ℂ) : iterDirDeriv vs (fun x => L (f x)) = fun x => L (iterDirDeriv vs f x) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    rw [iterDirDeriv_cons, iterDirDeriv_cons, ih]
    funext x
    have hd : DifferentiableAt ℝ (iterDirDeriv vs f) x := differentiable_iterDirDeriv hf vs x
    have h1 : HasFDerivAt (fun y => L (iterDirDeriv vs f y))
        (L.comp (fderiv ℝ (iterDirDeriv vs f) x)) x :=
      L.hasFDerivAt.comp x hd.hasFDerivAt
    simp only [dirDeriv]
    rw [h1.fderiv]
    rfl

/-- `∂_{vs ++ [v]}(a h) = ∂_{vs}((∂_v a) h) + ∂_{vs}(a ∂_v h)` for smooth `a`, `h`. -/
theorem iterDirDeriv_append_mul {a h : ℂ → ℂ} (ha : ContDiff ℝ ∞ a) (hh : ContDiff ℝ ∞ h)
    (vs : List ℂ) (v : ℂ) :
    iterDirDeriv (vs ++ [v]) (fun y => a y * h y) = fun x =>
      iterDirDeriv vs (fun y => dirDeriv v a y * h y) x +
        iterDirDeriv vs (fun y => a y * dirDeriv v h y) x := by
  rw [iterDirDeriv_append]
  have e : iterDirDeriv [v] (fun y => a y * h y) =
      fun y => dirDeriv v a y * h y + a y * dirDeriv v h y := by
    simp only [iterDirDeriv_cons, iterDirDeriv_nil]
    exact dirDeriv_mul (ha.differentiable (by simp)) (hh.differentiable (by simp)) v
  rw [e]
  exact iterDirDeriv_add ((contDiff_dirDeriv ha v).mul hh) (ha.mul (contDiff_dirDeriv hh v)) vs

/-! ### Real functions and the basis `1, i` -/

/-- The derivative of a real function viewed as complex valued. -/
theorem fderiv_ofReal_apply {g : ℂ → ℝ} {x : ℂ} (hg : DifferentiableAt ℝ g x) (v : ℂ) :
    fderiv ℝ (fun y => (g y : ℂ)) x v = ((fderiv ℝ g x v : ℝ) : ℂ) := by
  have hd : HasFDerivAt (fun y => (g y : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ g x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x hg.hasFDerivAt
  rw [hd.fderiv]
  rfl

theorem clm_apply_eq_re_im {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : ℂ →L[ℝ] E) (v : ℂ) : L v = v.re • L 1 + v.im • L Complex.I := by
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul]

/-- `x ↦ Re z` as a real-linear map `ℂ → ℂ`. -/
def reL : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.reCLM

/-- `x ↦ Im z` as a real-linear map `ℂ → ℂ`. -/
def imL : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.imCLM

theorem reL_apply (z : ℂ) : reL z = (z.re : ℂ) := rfl

theorem imL_apply (z : ℂ) : imL z = (z.im : ℂ) := rfl

/-- `Dg(y)(u(y)) = ∂₁g(y) Re u(y) + ∂₂g(y) Im u(y)` for a differentiable real `g`, written with the
complex-valued directional derivatives of `g`. -/
theorem ofReal_fderiv_apply_eq {g : ℂ → ℝ} (hg : Differentiable ℝ g) (u : ℂ → ℂ) :
    (fun y => ((fderiv ℝ g y (u y) : ℝ) : ℂ)) = fun y =>
      dirDeriv 1 (fun z => (g z : ℂ)) y * reL (u y) +
        dirDeriv Complex.I (fun z => (g z : ℂ)) y * imL (u y) := by
  funext y
  simp only [dirDeriv]
  rw [fderiv_ofReal_apply (hg y), fderiv_ofReal_apply (hg y), clm_apply_eq_re_im (fderiv ℝ g y),
    reL_apply, imL_apply]
  simp only [smul_eq_mul, Complex.ofReal_add, Complex.ofReal_mul]
  ring

end NonUniqueEuler.Smooth.IterLimitEqAux
