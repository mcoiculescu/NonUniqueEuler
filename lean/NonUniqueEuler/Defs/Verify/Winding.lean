import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Winding numbers of curves avoiding `0` (definitions)

Manuscript: the definition of `wind(c, 0)` at the start of Appendix A
(`A_verification.tex:42-46`): for a continuous closed curve `c` avoiding `0`,
`wind(c, 0) = (θ(1) - θ(0)) / 2π` for any continuous `θ` with `c = |c| e^{iθ}`.
Mathlib has no winding number, so we define it through continuous argument lifts.

* `IsArgLift c a b θ`: `θ` is a continuous argument of `c` on `[a, b]`.
* `HasArgChange c a b Δ`: `a ≤ b`, `c` is continuous and nonvanishing on `[a, b]`, and some
  continuous argument of `c` increases by `Δ` from `a` to `b`.
* `HasWinding c a b n`: `c` is closed (`c a = c b`) and `HasArgChange c a b (2πn)`.
  So `HasWinding` contains the facts "continuous" and "does not vanish on `[a, b]`".
* `windingNumber c a b`: the integer `n`, if it exists (uniqueness is an interface lemma).

Proposition A.4 (`prop:winding`, `A_verification.tex:470-512`): the segment types and the
indicator sum.
* `SegKind.P.Admits z ↔ z ∈ slitPlane` (misses `(-∞, 0]`), `SegKind.N.Admits z ↔ -z ∈ slitPlane`
  (misses `[0, ∞)`); `SegKind.AdmitsSet κ B` for a set `B` ("`B` is of type `κ`").
* `negImInd z = 1[Im z < 0]`, and `argN z = arg z + 2π·1[Im z < 0]` (the continuous argument on
  `ℂ \ [0, ∞)` of the proof of Proposition A.4).
* `segIndicatorSum n κ x = Σ_{i < n, κ i = N} (x (i+1) - x i)`: the formula of Proposition A.4
  (with `x i = 1[Im E(p_i) < 0]`).
* `junctionSum n κ x`: the same sum as the package evaluates it (`ringcert.winding.certify_cell`):
  only the values at *junctions* (indices where a type-N segment meets a non-type-N segment,
  cyclically) are read. Its equality with `segIndicatorSum` is an interface lemma.

Indices of segments are natural numbers `i < n`; segment `i` is `[t i, t (i+1)]`; the cyclic
neighbours are `cycPrev n i` and `cycNext n i`.
-/

noncomputable section

open Set Real

namespace NonUniqueEuler

/-! ### Argument lifts and winding numbers -/

/-- `θ` is a continuous argument of `c` on `[a, b]`: `θ` is continuous on `[a, b]` and
`c t = |c t| e^{i θ t}` there. -/
structure IsArgLift (c : ℝ → ℂ) (a b : ℝ) (θ : ℝ → ℝ) : Prop where
  continuousOn : ContinuousOn θ (Icc a b)
  eq : ∀ t ∈ Icc a b, c t = ((‖c t‖ : ℝ) : ℂ) * Complex.exp ((θ t : ℂ) * Complex.I)

/-- The argument of `c` changes by `Δ` along `[a, b]`: `a ≤ b`, `c` is continuous and
nonvanishing on `[a, b]`, and some continuous argument `θ` of `c` has `θ b - θ a = Δ`. -/
structure HasArgChange (c : ℝ → ℂ) (a b : ℝ) (Δ : ℝ) : Prop where
  le : a ≤ b
  continuousOn : ContinuousOn c (Icc a b)
  ne_zero : ∀ t ∈ Icc a b, c t ≠ 0
  exists_lift : ∃ θ : ℝ → ℝ, IsArgLift c a b θ ∧ θ b - θ a = Δ

/-- **Winding number.** The closed curve `c : [a, b] → ℂ \ {0}` winds `n` times around `0`:
`c a = c b`, and the argument of `c` changes by `2πn` (`A_verification.tex:42-46`). This
includes continuity of `c` on `[a, b]` and `c ≠ 0` there. -/
structure HasWinding (c : ℝ → ℂ) (a b : ℝ) (n : ℤ) : Prop where
  closed : c a = c b
  argChange : HasArgChange c a b (2 * π * n)

/-- The winding number of `c` along `[a, b]` around `0`, when `HasWinding c a b n` for some `n`
(it is then unique), and `0` otherwise. -/
def windingNumber (c : ℝ → ℂ) (a b : ℝ) : ℤ :=
  open Classical in
  if h : ∃ n : ℤ, HasWinding c a b n then h.choose else 0

theorem HasWinding.le {c : ℝ → ℂ} {a b : ℝ} {n : ℤ} (h : HasWinding c a b n) : a ≤ b :=
  h.argChange.le

theorem HasWinding.continuousOn {c : ℝ → ℂ} {a b : ℝ} {n : ℤ} (h : HasWinding c a b n) :
    ContinuousOn c (Icc a b) :=
  h.argChange.continuousOn

theorem HasWinding.ne_zero {c : ℝ → ℂ} {a b : ℝ} {n : ℤ} (h : HasWinding c a b n) :
    ∀ t ∈ Icc a b, c t ≠ 0 :=
  h.argChange.ne_zero

/-! ### Segment types and indicators (Proposition A.4) -/

/-- The two segment types of Proposition A.4. -/
inductive SegKind
  | P
  | N
  deriving DecidableEq, Repr, Inhabited

/-- A point allowed on a segment of the given type: type `P` points avoid `(-∞, 0]`
(`z ∈ slitPlane`), type `N` points avoid `[0, ∞)` (`-z ∈ slitPlane`). -/
def SegKind.Admits : SegKind → ℂ → Prop
  | .P, z => z ∈ Complex.slitPlane
  | .N, z => -z ∈ Complex.slitPlane

/-- A set `B ⊆ ℂ` is of type `κ` (`A_verification.tex:468-469`): every point of `B` is allowed
for `κ`. -/
def SegKind.AdmitsSet (κ : SegKind) (B : Set ℂ) : Prop :=
  ∀ z ∈ B, κ.Admits z

/-- `true` for type `N`. -/
def SegKind.isN : SegKind → Bool
  | .P => false
  | .N => true

/-- The indicator `1[Im z < 0]`. -/
def negImInd (z : ℂ) : ℤ := if z.im < 0 then 1 else 0

/-- The continuous argument on `ℂ \ [0, ∞)` used for type-N segments:
`θ_N(z) = Arg z + 2π·1[Im z < 0]`, with values in `(0, 2π)` there. -/
def argN (z : ℂ) : ℝ := Complex.arg z + 2 * π * (negImInd z : ℝ)

/-- The cyclic predecessor of the segment index `i` among `n` segments. -/
def cycPrev (n i : ℕ) : ℕ := if i = 0 then n - 1 else i - 1

/-- The cyclic successor of the segment index `i` among `n` segments. -/
def cycNext (n i : ℕ) : ℕ := if i + 1 = n then 0 else i + 1

/-- The point with index `i` (the start of segment `i`) is a junction: exactly one of the
segments `cycPrev n i` and `i` is of type N. -/
def IsJunction (n : ℕ) (κ : ℕ → SegKind) (i : ℕ) : Prop :=
  (κ (cycPrev n i)).isN ≠ (κ i).isN

instance (n : ℕ) (κ : ℕ → SegKind) (i : ℕ) : Decidable (IsJunction n κ i) := by
  unfold IsJunction; infer_instance

/-- The indicator sum of Proposition A.4: `Σ_{i < n, κ i = N} (x (i+1) - x i)`. With
`x i = 1[Im E(p_i) < 0]` and `p_n = p_0` this is the winding number. -/
def segIndicatorSum (n : ℕ) (κ : ℕ → SegKind) (x : ℕ → ℤ) : ℤ :=
  ∑ i ∈ Finset.range n, if (κ i).isN then x (i + 1) - x i else 0

/-- The indicator sum as `certify_cell` evaluates it: for each type-N segment `i`, add the value
at its end point if that point is a junction (the next segment is not of type N), and subtract
the value at its start point if that point is a junction (the previous segment is not of type
N). Only values at junction indices `< n` are read. -/
def junctionSum (n : ℕ) (κ : ℕ → SegKind) (x : ℕ → ℤ) : ℤ :=
  ∑ i ∈ Finset.range n,
    if (κ i).isN then
      (if (κ (cycNext n i)).isN then 0 else x (cycNext n i)) -
        (if (κ (cycPrev n i)).isN then 0 else x i)
    else 0

/-! ### Basic facts (proved) -/

theorem SegKind.Admits.ne_zero {κ : SegKind} {z : ℂ} (h : κ.Admits z) : z ≠ 0 := by
  rintro rfl
  cases κ <;> simp [SegKind.Admits, Complex.slitPlane] at h

/-- At a point shared by a type-N and a type-P segment the value is not real
(`A_verification.tex:483-485`). -/
theorem SegKind.im_ne_zero_of_admits_P_N {z : ℂ} (hP : SegKind.P.Admits z)
    (hN : SegKind.N.Admits z) : z.im ≠ 0 := by
  intro h
  simp only [SegKind.Admits, Complex.mem_slitPlane_iff, Complex.neg_re, Complex.neg_im,
    h, neg_zero, ne_eq, not_true_eq_false, or_false] at hP hN
  linarith

end NonUniqueEuler
