import NonUniqueEuler.Defs.Verify.Winding
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Proof: winding numbers of products, powers, and of curves with a logarithm

Proof of `NonUniqueEuler/I/Verify/WindingAlgebra.lean` (same declarations, statements copied
verbatim).

**Manuscript.** The argument principle step of Proposition A.4 (`A_verification.tex:512`) and
Lemma A.6 (`:536-560`).

* `HasArgChange.mul`: the sum of the two lifts is a lift of the product.
* `HasWinding.pow`, `HasWinding.finset_prod`: induction, from `mul` and the constant curve `1`.
* `HasWinding.const_mul`: `mul` with the constant curve `w` (winding `0`, lift `arg w`).
* `hasWinding_zero_of_exp`: the lift is `Im ∘ F ∘ γ`.
-/

open Set Real

namespace NonUniqueEuler

/-- Polar form of a product of two polar forms. -/
private lemma polar_mul (z₁ z₂ : ℂ) (θ₁ θ₂ : ℝ)
    (h₁ : z₁ = ((‖z₁‖ : ℝ) : ℂ) * Complex.exp ((θ₁ : ℂ) * Complex.I))
    (h₂ : z₂ = ((‖z₂‖ : ℝ) : ℂ) * Complex.exp ((θ₂ : ℂ) * Complex.I)) :
    z₁ * z₂ = ((‖z₁ * z₂‖ : ℝ) : ℂ) * Complex.exp (((θ₁ + θ₂ : ℝ) : ℂ) * Complex.I) := by
  rw [norm_mul, Complex.ofReal_mul, Complex.ofReal_add, add_mul, Complex.exp_add]
  calc z₁ * z₂ = (((‖z₁‖ : ℝ) : ℂ) * Complex.exp ((θ₁ : ℂ) * Complex.I)) *
        (((‖z₂‖ : ℝ) : ℂ) * Complex.exp ((θ₂ : ℂ) * Complex.I)) := by
          rw [← h₁, ← h₂]
    _ = _ := by ring

theorem HasArgChange.mul {c₁ c₂ : ℝ → ℂ} {a b Δ₁ Δ₂ : ℝ} (h₁ : HasArgChange c₁ a b Δ₁)
    (h₂ : HasArgChange c₂ a b Δ₂) : HasArgChange (fun t => c₁ t * c₂ t) a b (Δ₁ + Δ₂) := by
  obtain ⟨θ₁, hl₁, hd₁⟩ := h₁.exists_lift
  obtain ⟨θ₂, hl₂, hd₂⟩ := h₂.exists_lift
  refine ⟨h₁.le, h₁.continuousOn.mul h₂.continuousOn,
    fun t ht => mul_ne_zero (h₁.ne_zero t ht) (h₂.ne_zero t ht),
    ⟨fun t => θ₁ t + θ₂ t, ⟨hl₁.continuousOn.add hl₂.continuousOn, fun t ht => ?_⟩, ?_⟩⟩
  · exact polar_mul _ _ _ _ (hl₁.eq t ht) (hl₂.eq t ht)
  · rw [← hd₁, ← hd₂]; ring

theorem HasWinding.mul {c₁ c₂ : ℝ → ℂ} {a b : ℝ} {n₁ n₂ : ℤ} (h₁ : HasWinding c₁ a b n₁)
    (h₂ : HasWinding c₂ a b n₂) : HasWinding (fun t => c₁ t * c₂ t) a b (n₁ + n₂) := by
  refine ⟨by simp only [h₁.closed, h₂.closed], ?_⟩
  have h := h₁.argChange.mul h₂.argChange
  convert h using 1
  push_cast; ring

/-- A nonzero constant curve has winding number `0` (lift `arg w`). -/
private lemma hasWinding_const {w : ℂ} (hw : w ≠ 0) {a b : ℝ} (hab : a ≤ b) :
    HasWinding (fun _ => w) a b 0 := by
  refine ⟨rfl, hab, continuousOn_const, fun _ _ => hw,
    ⟨fun _ => Complex.arg w, ⟨continuousOn_const, fun _ _ => ?_⟩, ?_⟩⟩
  · exact (Complex.norm_mul_exp_arg_mul_I w).symm
  · simp

theorem HasWinding.pow {c : ℝ → ℂ} {a b : ℝ} {n : ℤ} (h : HasWinding c a b n) (k : ℕ) :
    HasWinding (fun t => c t ^ k) a b (k * n) := by
  induction k with
  | zero =>
    simpa only [pow_zero, Nat.cast_zero, zero_mul] using
      hasWinding_const (one_ne_zero (α := ℂ)) h.le
  | succ k ih =>
    have h' := ih.mul h
    simp only [← pow_succ] at h'
    convert h' using 1
    push_cast; ring

theorem HasWinding.finset_prod {ι : Type*} (s : Finset ι) {c : ι → ℝ → ℂ} {n : ι → ℤ}
    {a b : ℝ} (hab : a ≤ b) (h : ∀ i ∈ s, HasWinding (c i) a b (n i)) :
    HasWinding (fun t => ∏ i ∈ s, c i t) a b (∑ i ∈ s, n i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.prod_empty, Finset.sum_empty] using
      hasWinding_const (one_ne_zero (α := ℂ)) hab
  | insert j s hj ih =>
    have hs : ∀ i ∈ s, HasWinding (c i) a b (n i) := fun i hi =>
      h i (Finset.mem_insert_of_mem hi)
    have h' := (h j (Finset.mem_insert_self j s)).mul (ih hs)
    simpa only [Finset.prod_insert hj, Finset.sum_insert hj] using h'

/-- Multiplying by a nonzero constant does not change the winding number. -/
theorem HasWinding.const_mul {c : ℝ → ℂ} {a b : ℝ} {n : ℤ} (h : HasWinding c a b n) {w : ℂ}
    (hw : w ≠ 0) : HasWinding (fun t => w * c t) a b n := by
  simpa only [zero_add] using (hasWinding_const hw h.le).mul h

/-- **A function with a continuous logarithm on a set has winding number `0`** along every
closed curve in that set. -/
theorem hasWinding_zero_of_exp {U : Set ℂ} {g F : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn F U) (hgF : ∀ z ∈ U, g z = Complex.exp (F z))
    (hγ : ContinuousOn γ (Icc a b)) (hγU : ∀ t ∈ Icc a b, γ t ∈ U) (hcl : γ a = γ b) :
    HasWinding (fun t => g (γ t)) a b 0 := by
  have hFγ : ContinuousOn (fun t => F (γ t)) (Icc a b) := hF.comp hγ hγU
  refine ⟨by simp only [hcl], hab, ?_, ?_, ⟨fun t => (F (γ t)).im, ⟨?_, fun t ht => ?_⟩, ?_⟩⟩
  · exact (Complex.continuous_exp.comp_continuousOn hFγ).congr fun t ht => hgF _ (hγU t ht)
  · intro t ht
    rw [hgF _ (hγU t ht)]
    exact Complex.exp_ne_zero _
  · exact Complex.continuous_im.comp_continuousOn hFγ
  · rw [hgF _ (hγU t ht), Complex.norm_exp, Complex.ofReal_exp, ← Complex.exp_add,
      Complex.re_add_im]
  · simp [hcl]

end NonUniqueEuler
