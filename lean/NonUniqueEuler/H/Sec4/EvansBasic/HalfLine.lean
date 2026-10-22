import NonUniqueEuler.Defs.Infra.ODE
import NonUniqueEuler.I.Infra.ODE.Existence
import NonUniqueEuler.I.Infra.ODE.Uniqueness
import NonUniqueEuler.I.Infra.ODE.Explicit
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Helpers for `lem:evans-basic`: solutions of `ψ'' = V ψ` where `V = ℓ²` on half-lines

Helper file of `P/Sec4/EvansBasic.lean` (`04_ring.tex:304-344`). Everything is stated for a
continuous coefficient `V : ℝ → ℂ` and an integer `ℓ ≥ 1`:

* `eq_of_le_of_lt`, `eq_of_ge_of_gt`: a continuous `V` equal to a constant on `(-∞, a)`
  (resp. `(b, ∞)`) equals it on `(-∞, a]` (resp. `[b, ∞)`);
* `isSolOn_ofReal_exp`: `e^{f(ξ)}` with `f' = c` solves `ψ'' = c² ψ`;
* `sol_left`: on a left half-line where `V = ℓ²`, the solution normalized by `(1, ℓ)` at `ξ₀`
  is `e^{ℓ(ξ-ξ₀)}` (`04_ring.tex:305-306`);
* `right_coef`: on a right half-line where `V = ℓ²`, `ψ = A e^{ℓξ} + B e^{-ℓξ}` and
  `e^{-ℓξ}(ψ' + ℓψ) = 2ℓA` (`04_ring.tex:325-333`);
* `evans_val_indep`: the number `e^{-ℓ(ξ₂-ξ₁)}(ψ'(ξ₂) + ℓψ(ξ₂))` of `def:evans` does not depend
  on the pair `(ξ₁, ξ₂)` as long as `V = ℓ²` on `(-∞, ξ₁]` and on `[ξ₂, ∞)`
  (`lem:evans-basic`(2), `04_ring.tex:321-344`).

All lemmas are fully proved.
-/

noncomputable section

open Set

namespace NonUniqueEuler

namespace EvansBasicH

open LinODE

variable {V : ℝ → ℂ}

/-- A continuous function constant on `(-∞, a)` takes the same value on `(-∞, a]`. -/
theorem eq_of_le_of_lt (hV : Continuous V) {a : ℝ} {w : ℂ} (h : ∀ ξ, ξ < a → V ξ = w) :
    ∀ ξ, ξ ≤ a → V ξ = w := by
  intro ξ hξ
  have h' : EqOn V (fun _ => w) (Iio a) := fun η hη => h η hη
  have h'' := h'.closure hV continuous_const
  rw [closure_Iio] at h''
  exact h'' hξ

/-- A continuous function constant on `(b, ∞)` takes the same value on `[b, ∞)`. -/
theorem eq_of_ge_of_gt (hV : Continuous V) {b : ℝ} {w : ℂ} (h : ∀ ξ, b < ξ → V ξ = w) :
    ∀ ξ, b ≤ ξ → V ξ = w := by
  intro ξ hξ
  have h' : EqOn V (fun _ => w) (Ioi b) := fun η hη => h η hη
  have h'' := h'.closure hV continuous_const
  rw [closure_Ioi] at h''
  exact h'' hξ

/-- Where `V = c²`, `e^{f(ξ)}` with `f' = c` is a solution of `ψ'' = V ψ`. -/
theorem isSolOn_ofReal_exp {s : Set ℝ} {f : ℝ → ℝ} {c : ℝ} (hf : ∀ ξ, HasDerivAt f c ξ)
    (hV : ∀ ξ ∈ s, V ξ = (c : ℂ) ^ 2) :
    IsSolOn V s (fun ξ => ((Real.exp (f ξ) : ℝ) : ℂ))
      (fun ξ => (c : ℂ) * ((Real.exp (f ξ) : ℝ) : ℂ)) := by
  have hd : ∀ ξ, HasDerivAt (fun ξ => ((Real.exp (f ξ) : ℝ) : ℂ))
      ((c : ℂ) * ((Real.exp (f ξ) : ℝ) : ℂ)) ξ := by
    intro ξ
    have := ((hf ξ).exp).ofReal_comp
    exact this.congr_deriv (by push_cast; ring)
  refine ⟨fun ξ _ => (hd ξ).hasDerivWithinAt, fun ξ hξ => ?_⟩
  have := ((hd ξ).const_mul (c : ℂ)).hasDerivWithinAt (s := s)
  exact this.congr_deriv (by rw [hV ξ hξ]; ring)

/-- `ξ ↦ ℓ(ξ - ξ₀)` has derivative `ℓ`. -/
theorem hasDerivAt_mul_sub (ℓ ξ₀ ξ : ℝ) : HasDerivAt (fun ξ : ℝ => ℓ * (ξ - ξ₀)) ℓ ξ := by
  simpa using ((hasDerivAt_id ξ).sub_const ξ₀).const_mul ℓ

/-- `ξ ↦ -(ℓξ)` has derivative `-ℓ`. -/
theorem hasDerivAt_neg_mul (ℓ ξ : ℝ) : HasDerivAt (fun ξ : ℝ => -(ℓ * ξ)) (-ℓ) ξ := by
  have h := (hasDerivAt_id ξ).const_mul (-ℓ)
  simp only [id, mul_one, neg_mul] at h
  exact h

/-- On a left half-line `(-∞, a]` where `V = ℓ²`, the global solution normalized by `(1, ℓ)` at
`ξ₀ ≤ a` is `e^{ℓ(ξ-ξ₀)}` (`04_ring.tex:305-306`). -/
theorem sol_left (hV : Continuous V) (ℓ : ℕ) {a ξ₀ : ℝ} (hξ₀ : ξ₀ ≤ a)
    (hVa : ∀ ξ, ξ ≤ a → V ξ = (ℓ : ℂ) ^ 2) :
    ∀ ξ, ξ ≤ a → (sol V ξ₀ (1, (ℓ : ℂ)) ξ).1 = ((Real.exp (ℓ * (ξ - ξ₀)) : ℝ) : ℂ) ∧
      (sol V ξ₀ (1, (ℓ : ℂ)) ξ).2 = (ℓ : ℂ) * ((Real.exp (ℓ * (ξ - ξ₀)) : ℝ) : ℂ) := by
  obtain ⟨hsol, h0⟩ := sol_spec hV ξ₀ (1, (ℓ : ℂ))
  have hexp := isSolOn_ofReal_exp (V := V) (s := Iic a) (hasDerivAt_mul_sub (ℓ : ℝ) ξ₀)
    (fun ξ hξ => by rw [hVa ξ hξ]; push_cast; rfl)
  have key := IsSolOn.eqOn ordConnected_Iic hV.continuousOn (hsol.mono (subset_univ _)) hexp
    (show ξ₀ ∈ Iic a from hξ₀) (by simp [h0]) (by simp [h0])
  intro ξ hξ
  refine ⟨key.1 (show ξ ∈ Iic a from hξ), ?_⟩
  have := key.2 (show ξ ∈ Iic a from hξ)
  simpa using this

/-- On a right half-line `[b, ∞)` where `V = ℓ²` (`ℓ ≠ 0`), every solution is
`A e^{ℓξ} + B e^{-ℓξ}`, and `e^{-ℓξ}(ψ' + ℓψ) = 2ℓA` there (`04_ring.tex:325-333`). -/
theorem right_coef {ℓ : ℕ} (hℓ : ℓ ≠ 0) {b : ℝ} (hVb : ∀ ξ, b ≤ ξ → V ξ = (ℓ : ℂ) ^ 2)
    {ψ ψ' : ℝ → ℂ} (h : IsSolOn V (Ici b) ψ ψ') :
    ∃ A B : ℂ, ∀ ξ, b ≤ ξ →
      ψ ξ = A * ((Real.exp (ℓ * ξ) : ℝ) : ℂ) + B * ((Real.exp (-(ℓ * ξ)) : ℝ) : ℂ) ∧
        ψ' ξ = (ℓ : ℂ) * (A * ((Real.exp (ℓ * ξ) : ℝ) : ℂ) -
          B * ((Real.exp (-(ℓ * ξ)) : ℝ) : ℂ)) ∧
        ((Real.exp (-(ℓ * ξ)) : ℝ) : ℂ) * (ψ' ξ + (ℓ : ℂ) * ψ ξ) = 2 * (ℓ : ℂ) * A := by
  have hc : (ℓ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hℓ
  obtain ⟨A, B, hAB⟩ := exists_eq_exp_add_exp ordConnected_Ici hc
    (fun ξ hξ => hVb ξ hξ) h
  refine ⟨A, B, fun ξ hξ => ?_⟩
  obtain ⟨h1, h2⟩ := hAB ξ hξ
  have e1 : Complex.exp ((ℓ : ℂ) * (ξ : ℂ)) = ((Real.exp (ℓ * ξ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]; push_cast; rfl
  have e2 : Complex.exp (-((ℓ : ℂ) * (ξ : ℂ))) = ((Real.exp (-(ℓ * ξ)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]; push_cast; rfl
  rw [e1, e2] at h1 h2
  refine ⟨h1, h2, ?_⟩
  have e3 : ((Real.exp (-(ℓ * ξ)) : ℝ) : ℂ) * ((Real.exp (ℓ * ξ) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one]
  rw [h1, h2]
  linear_combination (2 * (ℓ : ℂ) * A) * e3

/-- **Independence of the normalization points** (`lem:evans-basic`(2), `04_ring.tex:321-344`):
if `V = ℓ²` on `(-∞, a₁]`, `(-∞, a₂]`, `[b₁, ∞)` and `[b₂, ∞)`, the numbers
`e^{-ℓ(b_i-a_i)}(ψ'(b_i) + ℓψ(b_i))`, `ψ` the solution normalized by `(1, ℓ)` at `a_i`, agree. -/
theorem evans_val_indep (hV : Continuous V) {ℓ : ℕ} (hℓ : ℓ ≠ 0) {a₁ a₂ b₁ b₂ : ℝ}
    (hVa₁ : ∀ ξ, ξ ≤ a₁ → V ξ = (ℓ : ℂ) ^ 2) (hVa₂ : ∀ ξ, ξ ≤ a₂ → V ξ = (ℓ : ℂ) ^ 2)
    (hVb₁ : ∀ ξ, b₁ ≤ ξ → V ξ = (ℓ : ℂ) ^ 2) (hVb₂ : ∀ ξ, b₂ ≤ ξ → V ξ = (ℓ : ℂ) ^ 2) :
    ((Real.exp (-(ℓ : ℝ) * (b₁ - a₁)) : ℝ) : ℂ) *
        ((sol V a₁ (1, (ℓ : ℂ)) b₁).2 + (ℓ : ℂ) * (sol V a₁ (1, (ℓ : ℂ)) b₁).1) =
      ((Real.exp (-(ℓ : ℝ) * (b₂ - a₂)) : ℝ) : ℂ) *
        ((sol V a₂ (1, (ℓ : ℂ)) b₂).2 + (ℓ : ℂ) * (sol V a₂ (1, (ℓ : ℂ)) b₂).1) := by
  -- the two normalized solutions and their rescalings `ψ_L = e^{ℓ a_i} ψ`
  obtain ⟨hs₁, -⟩ := sol_spec hV a₁ (1, (ℓ : ℂ))
  obtain ⟨hs₂, -⟩ := sol_spec hV a₂ (1, (ℓ : ℂ))
  have hL₁ := hs₁.const_mul ((Real.exp (ℓ * a₁) : ℝ) : ℂ)
  have hL₂ := hs₂.const_mul ((Real.exp (ℓ * a₂) : ℝ) : ℂ)
  -- they agree at `m = min a₁ a₂`, hence everywhere
  have hm₁ : min a₁ a₂ ≤ a₁ := min_le_left _ _
  have hm₂ : min a₁ a₂ ≤ a₂ := min_le_right _ _
  obtain ⟨hY₁m, hY₁m'⟩ := sol_left hV ℓ le_rfl hVa₁ (min a₁ a₂) hm₁
  obtain ⟨hY₂m, hY₂m'⟩ := sol_left hV ℓ le_rfl hVa₂ (min a₁ a₂) hm₂
  have hexp : ∀ a : ℝ, ((Real.exp (ℓ * a) : ℝ) : ℂ) *
      ((Real.exp (ℓ * (min a₁ a₂ - a)) : ℝ) : ℂ) = ((Real.exp (ℓ * min a₁ a₂) : ℝ) : ℂ) := by
    intro a
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  have hEq := IsSolOn.eqOn ordConnected_univ hV.continuousOn hL₁ hL₂ (mem_univ (min a₁ a₂))
    (by rw [hY₁m, hY₂m, hexp, hexp])
    (by rw [hY₁m', hY₂m', mul_left_comm, hexp, mul_left_comm, hexp])
  -- the quantity `e^{-ℓξ}(ψ_L' + ℓψ_L)` is constant on `[min b₁ b₂, ∞)`
  have hVb : ∀ ξ, min b₁ b₂ ≤ ξ → V ξ = (ℓ : ℂ) ^ 2 := by
    intro ξ hξ
    rcases min_le_iff.1 hξ with h | h
    · exact hVb₁ ξ h
    · exact hVb₂ ξ h
  obtain ⟨A, B, hA⟩ := right_coef hℓ hVb (hL₁.mono (subset_univ _))
  have k₁ := (hA b₁ (min_le_left _ _)).2.2
  have k₂ := (hA b₂ (min_le_right _ _)).2.2
  have e1 : ((Real.exp (ℓ * a₁) : ℝ) : ℂ) * (sol V a₁ (1, (ℓ : ℂ)) b₂).1 =
      ((Real.exp (ℓ * a₂) : ℝ) : ℂ) * (sol V a₂ (1, (ℓ : ℂ)) b₂).1 := hEq.1 (mem_univ b₂)
  have e2 : ((Real.exp (ℓ * a₁) : ℝ) : ℂ) * (sol V a₁ (1, (ℓ : ℂ)) b₂).2 =
      ((Real.exp (ℓ * a₂) : ℝ) : ℂ) * (sol V a₂ (1, (ℓ : ℂ)) b₂).2 := hEq.2 (mem_univ b₂)
  have hsplit : ∀ a b' : ℝ, ((Real.exp (-(ℓ : ℝ) * (b' - a)) : ℝ) : ℂ) =
      ((Real.exp (-(ℓ * b')) : ℝ) : ℂ) * ((Real.exp (ℓ * a) : ℝ) : ℂ) := by
    intro a b'
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  rw [hsplit a₁ b₁, hsplit a₂ b₂]
  linear_combination k₁ - k₂ + ((Real.exp (-(ℓ * b₂)) : ℝ) : ℂ) * e2 +
    ((Real.exp (-(ℓ * b₂)) : ℝ) : ℂ) * (ℓ : ℂ) * e1

end EvansBasicH

end NonUniqueEuler
