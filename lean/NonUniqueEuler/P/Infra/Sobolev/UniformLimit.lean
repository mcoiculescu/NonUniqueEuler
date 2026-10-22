import NonUniqueEuler.Defs.Infra.Sobolev
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Proof: uniform limits of smooth functions whose classical partial derivatives converge
(library I-HK)

Proof of `I/Infra/Sobolev/UniformLimit.lean` (`B_global_smooth.tex:411-416`).

Let `G γ x = lim_j ∂^γ f_j (x)`. Completeness of `ℂ` gives `∂^γ f_j → G γ` uniformly. For a
smooth `φ`, `D(∂^γ φ)(x) = Λ(∂^{γ+(1,0)} φ x, ∂^{γ+(0,1)} φ x)` with
`Λ(a, b) z = z.re • a + z.im • b` (commutation of directional derivatives for the second slot), so
`hasFDerivAt_of_tendstoUniformly` gives `DG γ (x) = Λ(G (γ+(1,0)) x, G (γ+(0,1)) x)`. Induction on
`γ` gives `∂^γ g = G γ`, and induction on the order gives `G γ ∈ C^n` for every `n`.

The helpers in `UniformLimitAux` on smoothness and commutation of directional derivatives are
copied from `H/SmoothB/CommR2/Calc.lean` (helpers of another proof, which cannot be imported).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace NonUniqueEuler.Sob

namespace UniformLimitAux

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

/-! ### The partial derivatives `∂^γ` -/

/-- `∂^{(a+1,b)} φ = ∂₁ ∂^{(a,b)} φ` (definitional). -/
theorem partialD_succ_fst (a b : ℕ) (φ : ℂ → ℂ) :
    partialD (a + 1, b) φ = dirDeriv 1 (partialD (a, b) φ) := rfl

/-- `∂^{(0,b+1)} φ = ∂₂ ∂^{(0,b)} φ` (definitional). -/
theorem partialD_zero_succ (b : ℕ) (φ : ℂ → ℂ) :
    partialD (0, b + 1) φ = dirDeriv Complex.I (partialD (0, b) φ) := rfl

/-- For smooth `φ`, `∂₂ ∂^{(a,b)} φ = ∂^{(a,b+1)} φ`. -/
theorem dirDeriv_I_partialD {φ : ℂ → ℂ} (hφ : ContDiff ℝ ∞ φ) (a b : ℕ) :
    dirDeriv Complex.I (partialD (a, b) φ) = partialD (a, b + 1) φ := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [partialD_succ_fst, partialD_succ_fst, dirDeriv_comm (contDiff_partialD hφ (a, b)), ih]

/-! ### The map `Λ(a, b) z = z.re • a + z.im • b` -/

/-- `Λ(a, b)` is the real-linear map `ℂ → ℂ` with `Λ(a, b) 1 = a` and `Λ(a, b) i = b`. -/
def lam : ℂ × ℂ →L[ℝ] (ℂ →L[ℝ] ℂ) :=
  (ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.reCLM).comp (ContinuousLinearMap.fst ℝ ℂ ℂ) +
    (ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.imCLM).comp (ContinuousLinearMap.snd ℝ ℂ ℂ)

theorem lam_apply (p : ℂ × ℂ) (z : ℂ) : lam p z = z.re • p.1 + z.im • p.2 := by
  simp [lam]

theorem lam_apply_one (p : ℂ × ℂ) : lam p 1 = p.1 := by
  simp [lam_apply]

theorem lam_apply_I (p : ℂ × ℂ) : lam p Complex.I = p.2 := by
  simp [lam_apply]

/-- Every real-linear `L : ℂ → ℂ` is `Λ(L 1, L i)`. -/
theorem clm_eq_lam (L : ℂ →L[ℝ] ℂ) : L = lam (L 1, L Complex.I) := by
  ext z
  rw [lam_apply]
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hz]
  rw [map_add, map_smul, map_smul]

/-- For smooth `φ`, `D(∂^γ φ)(x) = Λ(∂^{γ+(1,0)} φ x, ∂^{γ+(0,1)} φ x)`. -/
theorem fderiv_partialD {φ : ℂ → ℂ} (hφ : ContDiff ℝ ∞ φ) (γ : ℕ × ℕ) (x : ℂ) :
    fderiv ℝ (partialD γ φ) x =
      lam (partialD (γ.1 + 1, γ.2) φ x, partialD (γ.1, γ.2 + 1) φ x) := by
  rw [clm_eq_lam (fderiv ℝ (partialD γ φ) x)]
  congr 2
  show dirDeriv Complex.I (partialD (γ.1, γ.2) φ) x = _
  rw [dirDeriv_I_partialD hφ]

/-- Uniform convergence of a pair of sequences (diagonal index). -/
theorem tendstoUniformly_pair {F₁ F₂ : ℕ → ℂ → ℂ} {f₁ f₂ : ℂ → ℂ}
    (h₁ : TendstoUniformly F₁ f₁ atTop) (h₂ : TendstoUniformly F₂ f₂ atTop) :
    TendstoUniformly (fun n x => (F₁ n x, F₂ n x)) (fun x => (f₁ x, f₂ x)) atTop :=
  fun u hu => tendsto_diag.eventually ((h₁.prodMk h₂) u hu)

end UniformLimitAux

open UniformLimitAux in
/-- If smooth `f_j → g` pointwise and every `∂^γ f_j` is uniformly Cauchy on `ℝ²`, then `g` is
smooth and `∂^γ f_j → ∂^γ g` uniformly for every multi-index `γ`
(`B_global_smooth.tex:411-416`). -/
theorem contDiff_and_tendstoUniformly_partialD {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hf : ∀ j, ContDiff ℝ ∞ (f j))
    (hc : ∀ γ : ℕ × ℕ, UniformCauchySeqOn (fun j => partialD γ (f j)) atTop univ)
    (hg : ∀ x, Tendsto (fun j => f j x) atTop (𝓝 (g x))) :
    ContDiff ℝ ∞ g ∧
      ∀ γ : ℕ × ℕ, TendstoUniformly (fun j => partialD γ (f j)) (partialD γ g) atTop := by
  -- the pointwise limits `G γ` of `∂^γ f_j`
  set G : ℕ × ℕ → ℂ → ℂ := fun γ x => limUnder atTop (fun j => partialD γ (f j) x) with hGdef
  have hGpt : ∀ γ x, Tendsto (fun j => partialD γ (f j) x) atTop (𝓝 (G γ x)) := fun γ x =>
    ((hc γ).cauchySeq (mem_univ x)).tendsto_limUnder
  have hGu : ∀ γ, TendstoUniformly (fun j => partialD γ (f j)) (G γ) atTop := fun γ =>
    tendstoUniformlyOn_univ.1 ((hc γ).tendstoUniformlyOn_of_tendsto fun x _ => hGpt γ x)
  have hG0 : G (0, 0) = g := funext fun x => tendsto_nhds_unique (hGpt (0, 0) x) (hg x)
  -- the derivative of `G γ`
  have hGd : ∀ γ x, HasFDerivAt (G γ) (lam (G (γ.1 + 1, γ.2) x, G (γ.1, γ.2 + 1) x)) x := by
    intro γ
    refine hasFDerivAt_of_tendstoUniformly
      (f' := fun n x => lam (partialD (γ.1 + 1, γ.2) (f n) x, partialD (γ.1, γ.2 + 1) (f n) x))
      ?_ ?_ (hGpt γ)
    · exact lam.uniformContinuous.comp_tendstoUniformly
        (tendstoUniformly_pair (hGu (γ.1 + 1, γ.2)) (hGu (γ.1, γ.2 + 1)))
    · intro n x
      have := ((contDiff_partialD (hf n) γ).differentiable (by simp) x).hasFDerivAt
      rwa [fderiv_partialD (hf n) γ x] at this
  -- `∂^γ g = G γ`
  have h0b : ∀ b : ℕ, partialD (0, b) g = G (0, b) := by
    intro b
    induction b with
    | zero => exact hG0.symm
    | succ b ih =>
      funext x
      rw [partialD_zero_succ, ih]
      show fderiv ℝ (G (0, b)) x Complex.I = _
      rw [(hGd (0, b) x).fderiv, lam_apply_I]
  have hpart : ∀ γ : ℕ × ℕ, partialD γ g = G γ := by
    rintro ⟨a, b⟩
    induction a with
    | zero => exact h0b b
    | succ a ih =>
      funext x
      rw [partialD_succ_fst, ih]
      show fderiv ℝ (G (a, b)) x 1 = _
      rw [(hGd (a, b) x).fderiv, lam_apply_one]
  -- every `G γ` is `C^n`
  have hsmooth : ∀ (n : ℕ) (γ : ℕ × ℕ), ContDiff ℝ n (G γ) := by
    intro n
    induction n with
    | zero =>
      intro γ
      rw [Nat.cast_zero, contDiff_zero]
      exact (hGu γ).continuous (Frequently.of_forall fun n => (contDiff_partialD (hf n) γ).continuous)
    | succ n ih =>
      intro γ
      rw [Nat.cast_succ]
      exact contDiff_succ_iff_hasFDerivAt.2
        ⟨fun x => lam (G (γ.1 + 1, γ.2) x, G (γ.1, γ.2 + 1) x),
          lam.contDiff.comp ((ih _).prodMk (ih _)), hGd γ⟩
  refine ⟨?_, fun γ => ?_⟩
  · rw [← hG0]
    exact contDiff_infty.2 fun n => hsmooth n (0, 0)
  · rw [hpart γ]
    exact hGu γ

end NonUniqueEuler.Sob
