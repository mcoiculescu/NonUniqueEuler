import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.Basic
import NonUniqueEuler.Defs.Infra.Sobolev

/-!
# Helper for `prop:iter-limit`, step 5: classical calculus of iterated directional derivatives

Helper of `P/SmoothB/IterLimit/Bootstrap.lean` (`B_global_smooth.tex:449-472`). For smooth
functions on the plane:
* directional derivatives commute, so `∂^γ ∂^δ f = ∂^{γ+δ} f` (`partialD_partialD`);
* linearity, the product rule and real-linear maps (`iterDirDeriv_add`, `dirDeriv_mul`,
  `iterDirDeriv_clm_comp`);
* derivatives of a function vanishing on an open set vanish there
  (`iterDirDeriv_eq_zero_of_isOpen`).

The smoothness, commutation, linearity and composition lemmas are copied (verbatim up to the
namespace) from `H/SmoothB/CommR2/Calc.lean`, a helper of another proof, which may not be imported.
-/

noncomputable section

open scoped ContDiff Topology

namespace NonUniqueEuler.Smooth.BootstrapAux

open Sob

/-! ### Smoothness and commutation (copied from `H/SmoothB/CommR2/Calc.lean`) -/

theorem contDiff_dirDeriv {φ : ℂ → ℂ} (h : ContDiff ℝ ∞ φ) (v : ℂ) :
    ContDiff ℝ ∞ (dirDeriv v φ) :=
  (ContDiff.fderiv_right (m := ∞) h (by simp)).clm_apply contDiff_const

theorem contDiff_iterDirDeriv {φ : ℂ → ℂ} (h : ContDiff ℝ ∞ φ) (vs : List ℂ) :
    ContDiff ℝ ∞ (iterDirDeriv vs φ) := by
  induction vs with
  | nil => simpa using h
  | cons v vs ih => simpa using contDiff_dirDeriv ih v

theorem contDiff_partialD {φ : ℂ → ℂ} (h : ContDiff ℝ ∞ φ) (γ : ℕ × ℕ) :
    ContDiff ℝ ∞ (partialD γ φ) :=
  contDiff_iterDirDeriv h _

theorem differentiable_iterDirDeriv {φ : ℂ → ℂ} (h : ContDiff ℝ ∞ φ) (vs : List ℂ) :
    Differentiable ℝ (iterDirDeriv vs φ) :=
  (contDiff_iterDirDeriv h vs).differentiable (by simp)

theorem differentiable_partialD {φ : ℂ → ℂ} (h : ContDiff ℝ ∞ φ) (γ : ℕ × ℕ) :
    Differentiable ℝ (partialD γ φ) :=
  differentiable_iterDirDeriv h _

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

theorem pdList_add_perm (γ δ : ℕ × ℕ) : (pdList γ ++ pdList δ).Perm (pdList (γ + δ)) := by
  simp only [pdList, Prod.fst_add, Prod.snd_add, List.replicate_add, List.append_assoc]
  refine List.Perm.append_left _ ?_
  have h := (List.perm_append_comm (l₁ := List.replicate γ.2 Complex.I)
    (l₂ := List.replicate δ.1 (1 : ℂ))).append_right (List.replicate δ.2 Complex.I)
  simpa only [List.append_assoc] using h

/-- `∂^γ ∂^δ f = ∂^{γ+δ} f` for smooth `f`. -/
theorem partialD_partialD {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (γ δ : ℕ × ℕ) :
    partialD γ (partialD δ f) = partialD (γ + δ) f := by
  simp only [partialD]
  rw [← iterDirDeriv_append]
  exact iterDirDeriv_perm (pdList_add_perm γ δ) hf

/-! ### Linearity and the product rule (copied from `H/SmoothB/CommR2/Calc.lean`) -/

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

/-! ### New lemmas -/

/-- The first-order partial derivatives `∂^{(1,0)} = ∂_1`, `∂^{(0,1)} = ∂_2` obey the product
rule. -/
theorem partialD_unit_mul {δ : ℕ × ℕ} (hδ : δ = (1, 0) ∨ δ = (0, 1)) {a h : ℂ → ℂ}
    (ha : Differentiable ℝ a) (hh : Differentiable ℝ h) :
    partialD δ (fun x => a x * h x) =
      fun x => partialD δ a x * h x + a x * partialD δ h x := by
  rcases hδ with rfl | rfl
  · exact dirDeriv_mul ha hh 1
  · exact dirDeriv_mul ha hh Complex.I

/-- If `φ` vanishes on an open set `U`, so do all its iterated directional derivatives. -/
theorem iterDirDeriv_eq_zero_of_isOpen {φ : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (h : ∀ x ∈ U, φ x = 0) (vs : List ℂ) : ∀ x ∈ U, iterDirDeriv vs φ x = 0 := by
  induction vs with
  | nil => exact h
  | cons v vs ih =>
    intro x hx
    have hev : iterDirDeriv vs φ =ᶠ[𝓝 x] fun _ => (0 : ℂ) :=
      Filter.eventually_of_mem (hU.mem_nhds hx) ih
    rw [iterDirDeriv_cons]
    show fderiv ℝ (iterDirDeriv vs φ) x v = 0
    rw [hev.fderiv_eq]
    simp

/-- The derivative of a real function viewed as complex valued. -/
theorem fderiv_ofReal_apply {g : ℂ → ℝ} {x : ℂ} (hg : DifferentiableAt ℝ g x) (v : ℂ) :
    fderiv ℝ (fun y => (g y : ℂ)) x v = ((fderiv ℝ g x v : ℝ) : ℂ) := by
  have hd : HasFDerivAt (fun y => (g y : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ g x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x hg.hasFDerivAt
  rw [hd.fderiv]
  rfl

end NonUniqueEuler.Smooth.BootstrapAux
