import NonUniqueEuler.Statement.Certificate
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Order.Lattice
import Mathlib.Data.Rat.Cast.Order

/-!
# Rectangles, their boundary curve, and boundary chains (definitions)

Manuscript: the rectangles `R_A = [9/200, 3] × [-5, 3]` and `R_i` of Definition A.5
(`A_verification.tex:518-534`), the counterclockwise contour "from `(x₀, y₀)`" of the
certification (`A_verification.tex:569-575`), and Proposition A.4 (`prop:winding`).
Checker design decision D8 (see `FORMALIZATION_NOTES.md`).

Rectangles are the statement-layer `QRect` (rational vertices `x₀ x₁ y₀ y₁`, JSON order
`[x0, x1, y0, y1]`).

* `R.closedSet = [x₀, x₁] × [y₀, y₁]`, `R.openSet = (x₀, x₁) × (y₀, y₁)` (as subsets of `ℂ`,
  with Mathlib's `×ℂ`), `R.boundary = closedSet \ openSet`, and `R.Nondeg : x₀ < x₁ ∧ y₀ < y₁`.
* `R.bdryPath : ℝ → ℂ`, the boundary traversed once counterclockwise on `t ∈ [0, 4]`, from
  `(x₀, y₀)` through `(x₁, y₀)`, `(x₁, y₁)`, `(x₀, y₁)` back to `(x₀, y₀)`; edge `e` is the
  parameter interval `[e, e+1]`, on which the curve is affine. It is a closed form built from
  `clamp01 u = max 0 (min u 1)`, so it is one continuous closed curve without gluing.
  It is constant `(x₀, y₀)` for `t ≤ 0` and for `t ≥ 4`.
* `R.bdryPtQ t` computes `R.bdryPath t` exactly in `ℚ` for rational `t` (`bdryPath_ratCast`).
  The contour points of `rect_points` are `R.bdryPtQ (e + j/k)` for `0 ≤ j < k`,
  `k = max 2 ⌈ν L_e⌉`; the midpoint of two parameters on one edge gives the midpoint point.
* `R.segHullQ t₀ t₁`: the exact rational box spanned by the two end points `bdryPtQ t₀`,
  `bdryPtQ t₁` of a segment. If `[t₀, t₁]` lies in one edge, the box contains the image of the
  segment (interface `I/Verify/ContourGeom.lean`), so any box containing it encloses the
  segment (this is `seg_box` of the package).
* `IsBoundaryChain n t`: rational parameters `0 = t 0 < t 1 < ... < t n = 4`, each segment
  `[t i, t (i+1)]` inside one edge. The accepted segments of a certification form such a chain.
-/

noncomputable section

open Set

namespace NonUniqueEuler

/-- `clamp01 u = max 0 (min u 1)`, the clamp of `u` to `[0, 1]`. -/
def clamp01 (u : ℝ) : ℝ := max 0 (min u 1)

/-- The same clamp in `ℚ`. -/
def clamp01Q (u : ℚ) : ℚ := max 0 (min u 1)

/-- The closed interval `[lo, hi] ⊆ ℝ` of a `QInterval`. -/
def QInterval.toSet (J : QInterval) : Set ℝ := Icc (J.lo : ℝ) J.hi

namespace QRect

/-- The closed rectangle `[x₀, x₁] × [y₀, y₁] ⊆ ℂ`. -/
def closedSet (R : QRect) : Set ℂ := Icc (R.x₀ : ℝ) R.x₁ ×ℂ Icc (R.y₀ : ℝ) R.y₁

/-- The open rectangle `(x₀, x₁) × (y₀, y₁) ⊆ ℂ` (the interior of `closedSet`). -/
def openSet (R : QRect) : Set ℂ := Ioo (R.x₀ : ℝ) R.x₁ ×ℂ Ioo (R.y₀ : ℝ) R.y₁

/-- The boundary `∂R = closedSet \ openSet`. -/
def boundary (R : QRect) : Set ℂ := R.closedSet \ R.openSet

/-- The rectangle is nondegenerate: `x₀ < x₁` and `y₀ < y₁`. -/
def Nondeg (R : QRect) : Prop := R.x₀ < R.x₁ ∧ R.y₀ < R.y₁

/-- The boundary of `R`, traversed once counterclockwise for `t ∈ [0, 4]`, starting at
`(x₀, y₀)`; edge `e ∈ {0, 1, 2, 3}` is `t ∈ [e, e+1]` (bottom, right, top, left). -/
def bdryPath (R : QRect) (t : ℝ) : ℂ :=
  ⟨(R.x₀ : ℝ) + ((R.x₁ : ℝ) - R.x₀) * (clamp01 t - clamp01 (t - 2)),
    (R.y₀ : ℝ) + ((R.y₁ : ℝ) - R.y₀) * (clamp01 (t - 1) - clamp01 (t - 3))⟩

/-- `bdryPath` at a rational parameter, computed in `ℚ` (real part, imaginary part). -/
def bdryPtQ (R : QRect) (t : ℚ) : ℚ × ℚ :=
  (R.x₀ + (R.x₁ - R.x₀) * (clamp01Q t - clamp01Q (t - 2)),
    R.y₀ + (R.y₁ - R.y₀) * (clamp01Q (t - 1) - clamp01Q (t - 3)))

/-- The rational box spanned by the end points of the parameter segment `[t₀, t₁]`. -/
def segHullQ (R : QRect) (t₀ t₁ : ℚ) : QRect :=
  ⟨min (R.bdryPtQ t₀).1 (R.bdryPtQ t₁).1, max (R.bdryPtQ t₀).1 (R.bdryPtQ t₁).1,
    min (R.bdryPtQ t₀).2 (R.bdryPtQ t₁).2, max (R.bdryPtQ t₀).2 (R.bdryPtQ t₁).2⟩

theorem mem_closedSet {R : QRect} {z : ℂ} :
    z ∈ R.closedSet ↔ (R.x₀ : ℝ) ≤ z.re ∧ z.re ≤ R.x₁ ∧ (R.y₀ : ℝ) ≤ z.im ∧ z.im ≤ R.y₁ := by
  simp [closedSet, Complex.mem_reProdIm, and_assoc]

theorem mem_openSet {R : QRect} {z : ℂ} :
    z ∈ R.openSet ↔ (R.x₀ : ℝ) < z.re ∧ z.re < R.x₁ ∧ (R.y₀ : ℝ) < z.im ∧ z.im < R.y₁ := by
  simp [openSet, Complex.mem_reProdIm, and_assoc]

theorem openSet_subset_closedSet (R : QRect) : R.openSet ⊆ R.closedSet := by
  intro z hz
  rw [mem_openSet] at hz
  rw [mem_closedSet]
  exact ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩

/-- Inclusion of closed rectangles from the rational comparisons of the vertices. -/
theorem closedSet_subset_closedSet {R S : QRect} (h₀ : S.x₀ ≤ R.x₀) (h₁ : R.x₁ ≤ S.x₁)
    (h₂ : S.y₀ ≤ R.y₀) (h₃ : R.y₁ ≤ S.y₁) : R.closedSet ⊆ S.closedSet := by
  intro z hz
  rw [mem_closedSet] at hz ⊢
  have h₀' : (S.x₀ : ℝ) ≤ R.x₀ := by exact_mod_cast h₀
  have h₁' : (R.x₁ : ℝ) ≤ S.x₁ := by exact_mod_cast h₁
  have h₂' : (S.y₀ : ℝ) ≤ R.y₀ := by exact_mod_cast h₂
  have h₃' : (R.y₁ : ℝ) ≤ S.y₁ := by exact_mod_cast h₃
  exact ⟨h₀'.trans hz.1, hz.2.1.trans h₁', h₂'.trans hz.2.2.1, hz.2.2.2.trans h₃'⟩

/-- A rectangle with positive left edge lies in the open right half-plane. -/
theorem closedSet_subset_re_pos {R : QRect} (hx : 0 < R.x₀) :
    R.closedSet ⊆ {z : ℂ | 0 < z.re} := by
  intro z hz
  rw [mem_closedSet] at hz
  have : (0 : ℝ) < R.x₀ := by exact_mod_cast hx
  exact lt_of_lt_of_le this hz.1

theorem continuous_bdryPath (R : QRect) : Continuous R.bdryPath := by
  have hc : Continuous clamp01 := by
    unfold clamp01; fun_prop
  have h1 : Continuous fun t : ℝ =>
      (R.x₀ : ℝ) + ((R.x₁ : ℝ) - R.x₀) * (clamp01 t - clamp01 (t - 2)) := by
    fun_prop
  have h2 : Continuous fun t : ℝ =>
      (R.y₀ : ℝ) + ((R.y₁ : ℝ) - R.y₀) * (clamp01 (t - 1) - clamp01 (t - 3)) := by
    fun_prop
  have : R.bdryPath = fun t => (Complex.equivRealProdCLM.symm
      ((R.x₀ : ℝ) + ((R.x₁ : ℝ) - R.x₀) * (clamp01 t - clamp01 (t - 2)),
        (R.y₀ : ℝ) + ((R.y₁ : ℝ) - R.y₀) * (clamp01 (t - 1) - clamp01 (t - 3)))) := by
    funext t; rfl
  rw [this]
  exact Complex.equivRealProdCLM.symm.continuous.comp (h1.prodMk h2)

theorem bdryPath_zero (R : QRect) : R.bdryPath 0 = ⟨(R.x₀ : ℝ), (R.y₀ : ℝ)⟩ := by
  simp [bdryPath, clamp01]

/-- The curve is closed. -/
theorem bdryPath_four (R : QRect) : R.bdryPath 4 = R.bdryPath 0 := by
  simp only [bdryPath, clamp01]
  norm_num

theorem clamp01_ratCast (u : ℚ) : clamp01 (u : ℝ) = ((clamp01Q u : ℚ) : ℝ) := by
  simp [clamp01, clamp01Q, Rat.cast_max, Rat.cast_min]

/-- At a rational parameter, `bdryPath` is the exact rational point `bdryPtQ`. -/
theorem bdryPath_ratCast (R : QRect) (t : ℚ) :
    R.bdryPath (t : ℝ) = ⟨((R.bdryPtQ t).1 : ℝ), ((R.bdryPtQ t).2 : ℝ)⟩ := by
  have e2 : ((t : ℝ) - 2) = ((t - 2 : ℚ) : ℝ) := by push_cast; ring
  have e1 : ((t : ℝ) - 1) = ((t - 1 : ℚ) : ℝ) := by push_cast; ring
  have e3 : ((t : ℝ) - 3) = ((t - 3 : ℚ) : ℝ) := by push_cast; ring
  simp only [bdryPath, bdryPtQ, e1, e2, e3, clamp01_ratCast]
  push_cast
  rfl

end QRect

/-- A boundary chain: rational parameters `0 = t 0 < t 1 < ... < t n = 4`, each segment
`[t i, t (i+1)]` inside one edge `[e, e+1]` of the parametrization `QRect.bdryPath`. -/
structure IsBoundaryChain (n : ℕ) (t : ℕ → ℚ) : Prop where
  pos : 0 < n
  start : t 0 = 0
  stop : t n = 4
  lt : ∀ i < n, t i < t (i + 1)
  edge : ∀ i < n, ∃ e : ℤ, (e : ℚ) ≤ t i ∧ t (i + 1) ≤ e + 1

end NonUniqueEuler
