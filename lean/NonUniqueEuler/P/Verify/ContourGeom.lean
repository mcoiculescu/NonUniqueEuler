import NonUniqueEuler.Defs.Verify.Contour
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Order.Compact

/-!
# Proof: geometry of rectangles and of the boundary curve `QRect.bdryPath`

Proof of the interface `NonUniqueEuler/I/Verify/ContourGeom.lean` (same declarations, same
statements). Manuscript: Proposition A.4 (`A_verification.tex:470-475`) and the certification
(`:569-581`).

The proofs follow the sketch of the interface file: elementary facts about `clamp01`
(values in `[0, 1]`, monotone, piecewise affine with integer breakpoints), then the affine form
of `bdryPath` on each parameter edge `[e, e+1]`, then the topological facts from
`Mathlib/Analysis/Complex/ReImTopology.lean`.
-/

open Set

namespace NonUniqueEuler

/-! ### Elementary facts about `clamp01` -/

namespace ContourGeomAux

theorem clamp01_nonneg (u : ℝ) : 0 ≤ clamp01 u := le_max_left _ _

theorem clamp01_le_one (u : ℝ) : clamp01 u ≤ 1 :=
  max_le zero_le_one (min_le_right _ _)

theorem clamp01_mono {u v : ℝ} (h : u ≤ v) : clamp01 u ≤ clamp01 v :=
  max_le_max le_rfl (min_le_min h le_rfl)

theorem clamp01_of_nonpos {u : ℝ} (h : u ≤ 0) : clamp01 u = 0 := by
  unfold clamp01
  exact max_eq_left ((min_le_left _ _).trans h)

theorem clamp01_of_one_le {u : ℝ} (h : 1 ≤ u) : clamp01 u = 1 := by
  unfold clamp01
  rw [min_eq_right h]
  exact max_eq_right zero_le_one

theorem clamp01_of_mem {u : ℝ} (h₀ : 0 ≤ u) (h₁ : u ≤ 1) : clamp01 u = u := by
  unfold clamp01
  rw [min_eq_left h₁]
  exact max_eq_right h₀

/-- `clamp01 t - clamp01 (t - 2) ∈ [0, 1]`. -/
theorem clamp01_sub_nonneg (t : ℝ) : 0 ≤ clamp01 t - clamp01 (t - 2) := by
  have := clamp01_mono (show t - 2 ≤ t by linarith)
  linarith

theorem clamp01_sub_le_one (t : ℝ) : clamp01 t - clamp01 (t - 2) ≤ 1 := by
  rcases le_total t 2 with h | h
  · rw [clamp01_of_nonpos (show t - 2 ≤ 0 by linarith)]
    linarith [clamp01_le_one t]
  · rw [clamp01_of_one_le (show (1 : ℝ) ≤ t by linarith)]
    linarith [clamp01_nonneg (t - 2)]

/-- `clamp01` is affine on each interval `[m, m+1]`, `m ∈ ℤ`. -/
theorem clamp01_affine (m : ℤ) {s : ℝ} (h₀ : (m : ℝ) ≤ s) (h₁ : s ≤ m + 1) :
    clamp01 s = clamp01 m + (s - m) * (clamp01 (m + 1) - clamp01 m) := by
  rcases lt_trichotomy m 0 with hm | hm | hm
  · have hm' : (m : ℝ) ≤ -1 := by
      have : m ≤ -1 := by omega
      exact_mod_cast this
    rw [clamp01_of_nonpos (show s ≤ 0 by linarith), clamp01_of_nonpos (show (m : ℝ) ≤ 0 by linarith),
      clamp01_of_nonpos (show (m : ℝ) + 1 ≤ 0 by linarith)]
    ring
  · subst hm
    simp only [Int.cast_zero] at h₀ h₁ ⊢
    rw [clamp01_of_mem h₀ (by linarith), clamp01_of_nonpos le_rfl,
      clamp01_of_one_le (show (1 : ℝ) ≤ 0 + 1 by norm_num)]
    ring
  · have hm' : (1 : ℝ) ≤ m := by
      have : 1 ≤ m := by omega
      exact_mod_cast this
    rw [clamp01_of_one_le (show 1 ≤ s by linarith), clamp01_of_one_le hm',
      clamp01_of_one_le (show (1 : ℝ) ≤ m + 1 by linarith)]
    ring

/-- The shifted clamp `clamp01 (t - k)` (`k ∈ ℤ`) is affine on each edge `[e, e+1]`. -/
theorem clamp01_shift_affine (e k : ℤ) {t : ℝ} (h₀ : (e : ℝ) ≤ t) (h₁ : t ≤ e + 1) :
    clamp01 (t - k) =
      clamp01 ((e : ℝ) - k) + (t - e) * (clamp01 ((e : ℝ) + 1 - k) - clamp01 ((e : ℝ) - k)) := by
  have h := clamp01_affine (e - k) (s := t - k) (by push_cast; linarith) (by push_cast; linarith)
  have e1 : (((e - k : ℤ) : ℝ) + 1) = (e : ℝ) + 1 - k := by push_cast; ring
  have e2 : ((e - k : ℤ) : ℝ) = (e : ℝ) - k := by push_cast; ring
  rw [e1, e2] at h
  rw [h]
  ring

/-- An affine function `a + s d` on `[t₀, t₁]` takes values between its end values. -/
theorem affine_between (a d : ℝ) {t₀ t t₁ : ℝ} (h₁ : t₀ ≤ t) (h₂ : t ≤ t₁) :
    min (a + t₀ * d) (a + t₁ * d) ≤ a + t * d ∧ a + t * d ≤ max (a + t₀ * d) (a + t₁ * d) := by
  rcases le_total 0 d with hd | hd
  · have h3 : t₀ * d ≤ t * d := mul_le_mul_of_nonneg_right h₁ hd
    have h4 : t * d ≤ t₁ * d := mul_le_mul_of_nonneg_right h₂ hd
    exact ⟨min_le_of_left_le (by linarith), le_max_of_le_right (by linarith)⟩
  · have h3 : t * d ≤ t₀ * d := mul_le_mul_of_nonpos_right h₁ hd
    have h4 : t₁ * d ≤ t * d := mul_le_mul_of_nonpos_right h₂ hd
    exact ⟨min_le_of_right_le (by linarith), le_max_of_le_left (by linarith)⟩

end ContourGeomAux

open ContourGeomAux

namespace QRect

private theorem bdryPath_re (R : QRect) (t : ℝ) :
    (R.bdryPath t).re = (R.x₀ : ℝ) + ((R.x₁ : ℝ) - R.x₀) * (clamp01 t - clamp01 (t - 2)) := rfl

private theorem bdryPath_im (R : QRect) (t : ℝ) :
    (R.bdryPath t).im = (R.y₀ : ℝ) + ((R.y₁ : ℝ) - R.y₀) * (clamp01 (t - 1) - clamp01 (t - 3)) :=
  rfl

theorem bdryPath_mem_closedSet {R : QRect} (h₀ : R.x₀ ≤ R.x₁) (h₁ : R.y₀ ≤ R.y₁) (t : ℝ) :
    R.bdryPath t ∈ R.closedSet := by
  have h₀' : (0 : ℝ) ≤ (R.x₁ : ℝ) - R.x₀ := by
    have : (R.x₀ : ℝ) ≤ R.x₁ := by exact_mod_cast h₀
    linarith
  have h₁' : (0 : ℝ) ≤ (R.y₁ : ℝ) - R.y₀ := by
    have : (R.y₀ : ℝ) ≤ R.y₁ := by exact_mod_cast h₁
    linarith
  have a0 := clamp01_sub_nonneg t
  have a1 := clamp01_sub_le_one t
  have b0 := clamp01_sub_nonneg (t - 1)
  have b1 := clamp01_sub_le_one (t - 1)
  have e : t - 1 - 2 = t - 3 := by ring
  rw [e] at b0 b1
  rw [mem_closedSet, bdryPath_re, bdryPath_im]
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith

theorem x₀_le_re_bdryPath {R : QRect} (h₀ : R.x₀ ≤ R.x₁) (t : ℝ) :
    (R.x₀ : ℝ) ≤ (R.bdryPath t).re := by
  have h₀' : (0 : ℝ) ≤ (R.x₁ : ℝ) - R.x₀ := by
    have : (R.x₀ : ℝ) ≤ R.x₁ := by exact_mod_cast h₀
    linarith
  rw [bdryPath_re]
  have := mul_nonneg h₀' (clamp01_sub_nonneg t)
  linarith

/-- On the parameter interval `[e, e+1]` (`e ∈ ℤ`) the curve is affine. -/
theorem bdryPath_eq_affine (R : QRect) (e : ℤ) {t : ℝ} (ht : t ∈ Icc (e : ℝ) (e + 1)) :
    R.bdryPath t = R.bdryPath e + ((t - e : ℝ) : ℂ) * (R.bdryPath (e + 1) - R.bdryPath e) := by
  obtain ⟨h₀, h₁⟩ := ht
  have c0 := clamp01_shift_affine e 0 h₀ h₁
  have c1 := clamp01_shift_affine e 1 h₀ h₁
  have c2 := clamp01_shift_affine e 2 h₀ h₁
  have c3 := clamp01_shift_affine e 3 h₀ h₁
  simp only [Int.cast_zero, sub_zero, Int.cast_one, Int.cast_ofNat] at c0 c1 c2 c3
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.sub_im, bdryPath_re, zero_mul, sub_zero]
    rw [c0, c2]
    ring
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.sub_im, bdryPath_im, zero_mul, add_zero]
    rw [c1, c3]
    ring

/-- Bisection at the midpoint parameter is bisection at the midpoint point. -/
theorem bdryPath_midpoint (R : QRect) {e : ℤ} {t₀ t₁ : ℝ} (h₀ : (e : ℝ) ≤ t₀) (h₁ : t₀ ≤ t₁)
    (h₂ : t₁ ≤ e + 1) :
    R.bdryPath ((t₀ + t₁) / 2) = (R.bdryPath t₀ + R.bdryPath t₁) / 2 := by
  have hm := R.bdryPath_eq_affine e (t := (t₀ + t₁) / 2) ⟨by linarith, by linarith⟩
  have ha := R.bdryPath_eq_affine e (t := t₀) ⟨h₀, by linarith⟩
  have hb := R.bdryPath_eq_affine e (t := t₁) ⟨by linarith, h₂⟩
  rw [hm, ha, hb]
  push_cast
  ring

theorem bdryPtQ_midpoint (R : QRect) {e : ℤ} {t₀ t₁ : ℚ} (h₀ : (e : ℚ) ≤ t₀) (h₁ : t₀ ≤ t₁)
    (h₂ : t₁ ≤ e + 1) :
    R.bdryPtQ ((t₀ + t₁) / 2) =
      (((R.bdryPtQ t₀).1 + (R.bdryPtQ t₁).1) / 2, ((R.bdryPtQ t₀).2 + (R.bdryPtQ t₁).2) / 2) := by
  have h₀' : (e : ℝ) ≤ (t₀ : ℝ) := by exact_mod_cast h₀
  have h₁' : (t₀ : ℝ) ≤ (t₁ : ℝ) := by exact_mod_cast h₁
  have h₂' : (t₁ : ℝ) ≤ (e : ℝ) + 1 := by exact_mod_cast h₂
  have hm := R.bdryPath_midpoint h₀' h₁' h₂'
  have hc : (((t₀ + t₁) / 2 : ℚ) : ℝ) = ((t₀ : ℝ) + t₁) / 2 := by push_cast; ring
  rw [← hc, bdryPath_ratCast, bdryPath_ratCast, bdryPath_ratCast] at hm
  have hre := congrArg Complex.re hm
  have him := congrArg Complex.im hm
  simp only [Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.add_re,
    Complex.add_im] at hre him
  refine Prod.ext ?_ ?_
  · show (R.bdryPtQ ((t₀ + t₁) / 2)).1 = ((R.bdryPtQ t₀).1 + (R.bdryPtQ t₁).1) / 2
    apply Rat.cast_injective (α := ℝ)
    rw [hre]
    push_cast
    ring
  · show (R.bdryPtQ ((t₀ + t₁) / 2)).2 = ((R.bdryPtQ t₀).2 + (R.bdryPtQ t₁).2) / 2
    apply Rat.cast_injective (α := ℝ)
    rw [him]
    push_cast
    ring

/-- The segment box. If `[t₀, t₁]` lies in one edge `[e, e+1]`, the image of the segment
lies in the rational box spanned by its end points. -/
theorem bdryPath_mem_segHullQ (R : QRect) {e : ℤ} {t₀ t₁ : ℚ} {t : ℝ} (h₀ : (e : ℝ) ≤ t₀)
    (h₁ : (t₀ : ℝ) ≤ t) (h₂ : t ≤ t₁) (h₃ : (t₁ : ℝ) ≤ e + 1) :
    R.bdryPath t ∈ (R.segHullQ t₀ t₁).closedSet := by
  have hA := R.bdryPath_eq_affine e (t := t₀) ⟨h₀, by linarith⟩
  have hT := R.bdryPath_eq_affine e (t := t) ⟨by linarith, by linarith⟩
  have hB := R.bdryPath_eq_affine e (t := t₁) ⟨by linarith, h₃⟩
  set P := R.bdryPath e
  set D := R.bdryPath (e + 1) - R.bdryPath e
  have re_of : ∀ s : ℝ, (P + ((s - e : ℝ) : ℂ) * D).re = (P.re - e * D.re) + s * D.re := by
    intro s
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
    ring
  have im_of : ∀ s : ℝ, (P + ((s - e : ℝ) : ℂ) * D).im = (P.im - e * D.im) + s * D.im := by
    intro s
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero]
    ring
  have hre := affine_between (P.re - e * D.re) D.re h₁ h₂
  have him := affine_between (P.im - e * D.im) D.im h₁ h₂
  rw [← re_of, ← re_of, ← re_of, ← hA, ← hT, ← hB] at hre
  rw [← im_of, ← im_of, ← im_of, ← hA, ← hT, ← hB] at him
  rw [bdryPath_ratCast, bdryPath_ratCast] at hre him
  rw [mem_closedSet]
  simp only [segHullQ, Rat.cast_min, Rat.cast_max]
  exact ⟨hre.1, hre.2, him.1, him.2⟩

/-- The curve traverses exactly the boundary of a nondegenerate rectangle. -/
theorem bdryPath_image {R : QRect} (hR : R.Nondeg) :
    R.bdryPath '' Icc 0 4 = R.boundary := by
  have hx : (R.x₀ : ℝ) < R.x₁ := by exact_mod_cast hR.1
  have hy : (R.y₀ : ℝ) < R.y₁ := by exact_mod_cast hR.2
  apply Subset.antisymm
  · rintro z ⟨t, ⟨ht0, ht4⟩, rfl⟩
    refine ⟨bdryPath_mem_closedSet hR.1.le hR.2.le t, ?_⟩
    rw [mem_openSet, bdryPath_re, bdryPath_im]
    intro ⟨a, b, c, d⟩
    rcases le_total t 1 with h1 | h1
    · rw [clamp01_of_nonpos (show t - 1 ≤ 0 by linarith),
        clamp01_of_nonpos (show t - 3 ≤ 0 by linarith)] at c
      linarith
    rcases le_total t 2 with h2 | h2
    · rw [clamp01_of_one_le h1, clamp01_of_nonpos (show t - 2 ≤ 0 by linarith)] at b
      linarith
    rcases le_total t 3 with h3 | h3
    · rw [clamp01_of_one_le (show 1 ≤ t - 1 by linarith),
        clamp01_of_nonpos (show t - 3 ≤ 0 by linarith)] at d
      linarith
    · rw [clamp01_of_one_le (show 1 ≤ t by linarith),
        clamp01_of_one_le (show 1 ≤ t - 2 by linarith)] at a
      linarith
  · rintro z ⟨hz, hzo⟩
    rw [mem_closedSet] at hz
    obtain ⟨z0, z1, z2, z3⟩ := hz
    rw [mem_openSet] at hzo
    have hX : 0 < (R.x₁ : ℝ) - R.x₀ := by linarith
    have hY : 0 < (R.y₁ : ℝ) - R.y₀ := by linarith
    -- one of the four edge equations holds
    have hcase : z.im = R.y₀ ∨ z.re = R.x₁ ∨ z.im = R.y₁ ∨ z.re = R.x₀ := by
      by_contra hne
      simp only [not_or] at hne
      exact hzo ⟨lt_of_le_of_ne z0 (Ne.symm hne.2.2.2), lt_of_le_of_ne z1 hne.2.1,
        lt_of_le_of_ne z2 (Ne.symm hne.1), lt_of_le_of_ne z3 hne.2.2.1⟩
    rcases hcase with h | h | h | h
    · -- bottom edge, `t ∈ [0, 1]`
      set s := (z.re - R.x₀) / ((R.x₁ : ℝ) - R.x₀) with hs
      have s0 : 0 ≤ s := div_nonneg (by linarith) hX.le
      have s1 : s ≤ 1 := (div_le_one hX).2 (by linarith)
      refine ⟨s, ⟨s0, by linarith⟩, ?_⟩
      apply Complex.ext
      · rw [bdryPath_re, clamp01_of_mem s0 s1, clamp01_of_nonpos (show s - 2 ≤ 0 by linarith),
          hs]
        field_simp
        ring
      · rw [bdryPath_im, clamp01_of_nonpos (show s - 1 ≤ 0 by linarith),
          clamp01_of_nonpos (show s - 3 ≤ 0 by linarith), h]
        ring
    · -- right edge, `t ∈ [1, 2]`
      set s := (z.im - R.y₀) / ((R.y₁ : ℝ) - R.y₀) with hs
      have s0 : 0 ≤ s := div_nonneg (by linarith) hY.le
      have s1 : s ≤ 1 := (div_le_one hY).2 (by linarith)
      refine ⟨1 + s, ⟨by linarith, by linarith⟩, ?_⟩
      apply Complex.ext
      · rw [bdryPath_re, clamp01_of_one_le (show 1 ≤ 1 + s by linarith),
          clamp01_of_nonpos (show 1 + s - 2 ≤ 0 by linarith), h]
        ring
      · have e1 : 1 + s - 1 = s := by ring
        rw [bdryPath_im, e1, clamp01_of_mem s0 s1,
          clamp01_of_nonpos (show 1 + s - 3 ≤ 0 by linarith), hs]
        field_simp
        ring
    · -- top edge, `t ∈ [2, 3]`
      set s := ((R.x₁ : ℝ) - z.re) / ((R.x₁ : ℝ) - R.x₀) with hs
      have s0 : 0 ≤ s := div_nonneg (by linarith) hX.le
      have s1 : s ≤ 1 := (div_le_one hX).2 (by linarith)
      refine ⟨2 + s, ⟨by linarith, by linarith⟩, ?_⟩
      apply Complex.ext
      · have e1 : 2 + s - 2 = s := by ring
        rw [bdryPath_re, e1, clamp01_of_one_le (show 1 ≤ 2 + s by linarith),
          clamp01_of_mem s0 s1, hs]
        field_simp
        ring
      · rw [bdryPath_im, clamp01_of_one_le (show 1 ≤ 2 + s - 1 by linarith),
          clamp01_of_nonpos (show 2 + s - 3 ≤ 0 by linarith), h]
        ring
    · -- left edge, `t ∈ [3, 4]`
      set s := ((R.y₁ : ℝ) - z.im) / ((R.y₁ : ℝ) - R.y₀) with hs
      have s0 : 0 ≤ s := div_nonneg (by linarith) hY.le
      have s1 : s ≤ 1 := (div_le_one hY).2 (by linarith)
      refine ⟨3 + s, ⟨by linarith, by linarith⟩, ?_⟩
      apply Complex.ext
      · rw [bdryPath_re, clamp01_of_one_le (show 1 ≤ 3 + s by linarith),
          clamp01_of_one_le (show 1 ≤ 3 + s - 2 by linarith), h]
        ring
      · have e1 : 3 + s - 3 = s := by ring
        rw [bdryPath_im, e1, clamp01_of_one_le (show 1 ≤ 3 + s - 1 by linarith),
          clamp01_of_mem s0 s1, hs]
        field_simp
        ring

private theorem isClosed_closedSet (R : QRect) : IsClosed R.closedSet :=
  isClosed_Icc.reProdIm isClosed_Icc

theorem interior_closedSet (R : QRect) : interior R.closedSet = R.openSet := by
  rw [closedSet, Complex.interior_reProdIm, interior_Icc, interior_Icc]
  rfl

theorem frontier_closedSet (R : QRect) : frontier R.closedSet = R.boundary := by
  rw [frontier, R.isClosed_closedSet.closure_eq, interior_closedSet]
  rfl

theorem closure_openSet {R : QRect} (hR : R.Nondeg) : closure R.openSet = R.closedSet := by
  have hx : (R.x₀ : ℝ) ≠ R.x₁ := by
    have : (R.x₀ : ℝ) < R.x₁ := by exact_mod_cast hR.1
    exact this.ne
  have hy : (R.y₀ : ℝ) ≠ R.y₁ := by
    have : (R.y₀ : ℝ) < R.y₁ := by exact_mod_cast hR.2
    exact this.ne
  rw [openSet, Complex.closure_reProdIm, closure_Ioo hx, closure_Ioo hy]
  rfl

theorem isOpen_openSet (R : QRect) : IsOpen R.openSet :=
  isOpen_Ioo.reProdIm isOpen_Ioo

theorem isCompact_closedSet (R : QRect) : IsCompact R.closedSet :=
  Metric.isCompact_of_isClosed_isBounded R.isClosed_closedSet
    ((Metric.isBounded_Icc _ _).reProdIm (Metric.isBounded_Icc _ _))

theorem convex_closedSet (R : QRect) : Convex ℝ R.closedSet :=
  ((convex_Icc (R.x₀ : ℝ) R.x₁).linear_preimage Complex.reLm).inter
    ((convex_Icc (R.y₀ : ℝ) R.y₁).linear_preimage Complex.imLm)

end QRect

/-- The segments of a boundary chain are enclosed by their rational end-point boxes. -/
theorem IsBoundaryChain.mem_segHullQ {n : ℕ} {t : ℕ → ℚ} (ht : IsBoundaryChain n t)
    (R : QRect) {i : ℕ} (hi : i < n) {s : ℝ} (hs : s ∈ Icc ((t i : ℚ) : ℝ) (t (i + 1))) :
    R.bdryPath s ∈ (R.segHullQ (t i) (t (i + 1))).closedSet := by
  obtain ⟨e, he₀, he₁⟩ := ht.edge i hi
  have he₀' : (e : ℝ) ≤ ((t i : ℚ) : ℝ) := by exact_mod_cast he₀
  have he₁' : ((t (i + 1) : ℚ) : ℝ) ≤ (e : ℝ) + 1 := by exact_mod_cast he₁
  exact R.bdryPath_mem_segHullQ he₀' hs.1 hs.2 he₁'

/-- The real parameters of a boundary chain: `0 = t 0 ≤ ... ≤ t n = 4`. -/
theorem IsBoundaryChain.real_params {n : ℕ} {t : ℕ → ℚ} (ht : IsBoundaryChain n t) :
    ((t 0 : ℚ) : ℝ) = 0 ∧ ((t n : ℚ) : ℝ) = 4 ∧ ∀ i < n, ((t i : ℚ) : ℝ) ≤ t (i + 1) := by
  refine ⟨by rw [ht.start]; simp, by rw [ht.stop]; norm_num, fun i hi => ?_⟩
  exact_mod_cast (ht.lt i hi).le

end NonUniqueEuler
