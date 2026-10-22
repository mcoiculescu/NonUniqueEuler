import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Helper for `P/Infra/AngularFourier/Parseval`: projections with a Parseval identity

Abstract Hilbert-space facts. Let `P : ℤ → E →L[ℂ] E` satisfy `P_ℓ P_m = δ_{ℓm} P_m` and the
Parseval identity `‖f‖² = ∑_ℓ ‖P_ℓ f‖²` for every `f`. Then:
* the range of `P_ℓ` is orthogonal to its kernel (`inner_eq_zero_of_parseval`): with `x = P_ℓ x`
  and `P_ℓ y = 0`, the sectors of `x + c y` are `x` (at `ℓ`) and `c P_k y` (at `k ≠ ℓ`), so
  Parseval gives `‖x + c y‖² = ‖x‖² + |c|² ‖y‖²` for all `c ∈ ℂ`, hence `⟪x, y⟫ = 0`;
* each `P_ℓ` is self-adjoint and different sectors are orthogonal;
* `f = ∑_ℓ P_ℓ f` in `E`: the sectors of `f - ∑_{ℓ ∈ F} P_ℓ f` are `P_k f` for `k ∉ F` and `0`
  for `k ∈ F`, so `‖f - ∑_{ℓ∈F} P_ℓ f‖² = ‖f‖² - ∑_{ℓ∈F} ‖P_ℓ f‖² → 0`.
-/

noncomputable section

open Filter Topology

namespace NonUniqueEuler.Ang.ParsevalH

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

section

variable (P : ℤ → E →L[ℂ] E)
  (hcomp : ∀ ℓ m : ℤ, (P ℓ).comp (P m) = if ℓ = m then P m else 0)
  (hpars : ∀ f : E, HasSum (fun ℓ : ℤ => ‖P ℓ f‖ ^ 2) (‖f‖ ^ 2))

include hcomp in
theorem apply_apply_of_parseval (k ℓ : ℤ) (f : E) :
    P k (P ℓ f) = if k = ℓ then P ℓ f else 0 := by
  have h := congrArg (fun T : E →L[ℂ] E => T f) (hcomp k ℓ)
  simp only [ContinuousLinearMap.comp_apply] at h
  rw [h]
  split_ifs <;> rfl

include hcomp hpars in
/-- The range of `P_ℓ` is orthogonal to its kernel. -/
theorem inner_eq_zero_of_parseval {ℓ : ℤ} {x y : E} (hx : P ℓ x = x) (hy : P ℓ y = 0) :
    inner ℂ x y = 0 := by
  have key : ∀ c : ℂ, ‖x + c • y‖ ^ 2 = ‖x‖ ^ 2 + ‖c‖ ^ 2 * ‖y‖ ^ 2 := by
    intro c
    have h1 := hpars (x + c • y)
    have h2 : HasSum (fun k : ℤ => (if k = ℓ then ‖x‖ ^ 2 else 0) + ‖c‖ ^ 2 * ‖P k y‖ ^ 2)
        (‖x‖ ^ 2 + ‖c‖ ^ 2 * ‖y‖ ^ 2) :=
      (hasSum_ite_eq ℓ (‖x‖ ^ 2)).add ((hpars y).mul_left (‖c‖ ^ 2))
    have h3 : (fun k : ℤ => ‖P k (x + c • y)‖ ^ 2) =
        fun k : ℤ => (if k = ℓ then ‖x‖ ^ 2 else 0) + ‖c‖ ^ 2 * ‖P k y‖ ^ 2 := by
      funext k
      have hxk : P k x = if k = ℓ then x else 0 := by
        rw [← hx, apply_apply_of_parseval P hcomp k ℓ x, hx]
      rw [map_add, map_smul, hxk]
      by_cases hk : k = ℓ
      · subst hk
        simp [hy]
      · simp [hk, norm_smul, mul_pow]
    rw [h3] at h1
    exact h1.unique h2
  have hre : ∀ c : ℂ, (c * inner ℂ x y).re = 0 := by
    intro c
    have h := key c
    rw [@norm_add_sq ℂ, inner_smul_right, norm_smul, mul_pow, RCLike.re_to_complex] at h
    linarith
  apply Complex.ext
  · simpa using hre 1
  · have := hre Complex.I
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub] at this
    simpa using this

include hcomp hpars in
/-- Each `P_ℓ` is self-adjoint. -/
theorem inner_apply_eq_of_parseval (ℓ : ℤ) (f g : E) :
    inner ℂ (P ℓ f) g = inner ℂ f (P ℓ g) := by
  have hPP : ∀ h : E, P ℓ (P ℓ h) = P ℓ h := fun h => by
    rw [apply_apply_of_parseval P hcomp ℓ ℓ h, ite_eq_left rfl]
  have hker : ∀ h : E, P ℓ (h - P ℓ h) = 0 := fun h => by
    rw [map_sub, hPP, sub_self]
  have h1 : inner ℂ (P ℓ f) g = inner ℂ (P ℓ f) (P ℓ g) := by
    have := inner_eq_zero_of_parseval P hcomp hpars (hPP f) (hker g)
    rw [inner_sub_right] at this
    exact (sub_eq_zero.1 this)
  have h2 : inner ℂ f (P ℓ g) = inner ℂ (P ℓ f) (P ℓ g) := by
    have := inner_eq_zero_symm.1 (inner_eq_zero_of_parseval P hcomp hpars (hPP g) (hker f))
    rw [inner_sub_left] at this
    exact (sub_eq_zero.1 this)
  rw [h1, h2]

include hcomp hpars in
/-- Different sectors are orthogonal. -/
theorem inner_apply_apply_of_ne_of_parseval {ℓ m : ℤ} (h : ℓ ≠ m) (f g : E) :
    inner ℂ (P ℓ f) (P m g) = 0 := by
  refine inner_eq_zero_of_parseval P hcomp hpars (ℓ := ℓ) ?_ ?_
  · rw [apply_apply_of_parseval P hcomp ℓ ℓ f, ite_eq_left rfl]
  · rw [apply_apply_of_parseval P hcomp ℓ m g, ite_eq_right h]

include hcomp hpars in
/-- `f = ∑_ℓ P_ℓ f`. -/
theorem hasSum_apply_of_parseval (f : E) : HasSum (fun ℓ : ℤ => P ℓ f) f := by
  classical
  -- the norm of the remainder of a partial sum
  have hrem : ∀ F : Finset ℤ,
      ‖f - ∑ ℓ ∈ F, P ℓ f‖ ^ 2 = ‖f‖ ^ 2 - ∑ ℓ ∈ F, ‖P ℓ f‖ ^ 2 := by
    intro F
    have hsec : ∀ k : ℤ, P k (f - ∑ ℓ ∈ F, P ℓ f) = if k ∈ F then 0 else P k f := by
      intro k
      rw [map_sub, map_sum]
      simp_rw [apply_apply_of_parseval P hcomp k _ f]
      rw [Finset.sum_ite_eq]
      split_ifs <;> simp
    have h1 := hpars (f - ∑ ℓ ∈ F, P ℓ f)
    simp_rw [hsec] at h1
    have h1' : HasSum (fun k : ℤ => if k ∈ F then 0 else ‖P k f‖ ^ 2)
        (‖f - ∑ ℓ ∈ F, P ℓ f‖ ^ 2) := by
      convert h1 using 2 with k
      split_ifs <;> simp
    have h2 : HasSum (fun k : ℤ => if k ∈ F then ‖P k f‖ ^ 2 else 0)
        (∑ ℓ ∈ F, if ℓ ∈ F then ‖P ℓ f‖ ^ 2 else 0) :=
      hasSum_sum_of_ne_finset_zero (fun b hb => ite_eq_right hb)
    have h2' : (∑ ℓ ∈ F, if ℓ ∈ F then ‖P ℓ f‖ ^ 2 else 0) = ∑ ℓ ∈ F, ‖P ℓ f‖ ^ 2 :=
      Finset.sum_congr rfl fun k hk => ite_eq_left hk
    rw [h2'] at h2
    have h3 := h1'.add h2
    have h4 : (fun k : ℤ => (if k ∈ F then 0 else ‖P k f‖ ^ 2) +
        (if k ∈ F then ‖P k f‖ ^ 2 else 0)) = fun k => ‖P k f‖ ^ 2 := by
      funext k
      split_ifs <;> simp
    rw [h4] at h3
    have := h3.unique (hpars f)
    linarith
  have hT := hpars f
  unfold HasSum at hT ⊢
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun F : Finset ℤ => Real.sqrt (‖f‖ ^ 2 - ∑ ℓ ∈ F, ‖P ℓ f‖ ^ 2))
      (SummationFilter.unconditional ℤ).filter (𝓝 0) := by
    have := (hT.const_sub (‖f‖ ^ 2)).sqrt
    simpa using this
  refine hlim.congr fun F => ?_
  rw [← hrem F, Real.sqrt_sq (norm_nonneg _), norm_sub_rev]

end

end NonUniqueEuler.Ang.ParsevalH
