import NonUniqueEuler.Defs.Verify.Winding
import NonUniqueEuler.Defs.Verify.Contour
import NonUniqueEuler.I.Verify.SegmentFormula
import NonUniqueEuler.I.Verify.ContourGeom

/-!
# Proof: the winding number of `λ - u` around a rectangle

Proof of the interface `NonUniqueEuler/I/Verify/WindingRect.lean` (same declarations, same
statements).

**Manuscript.** `A_verification.tex:509-512` and Lemma A.6 (`:540-560`).

* Inside: Proposition A.4 (`hasWinding_of_segments`, `I/Verify/SegmentFormula.lean`) on the
  four edges `[0,1], [1,2], [2,3], [3,4]` with types `P, P, P, N`: on the bottom edge
  `Im (γ - u) = y₀ - Im u < 0`, on the right edge `Re (γ - u) = x₁ - Re u > 0`, on the top edge
  `Im (γ - u) = y₁ - Im u > 0`, on the left edge `Re (γ - u) = x₀ - Re u < 0`. The indicator
  sum is `1[Im (γ 4 - u) < 0] - 1[Im (γ 3 - u) < 0] = 1 - 0`.
* Outside: the curve stays in the closed rectangle (`bdryPath_mem_closedSet`,
  `I/Verify/ContourGeom.lean`), so `γ - u` lies in an open half-plane `Re > 0`, `Re < 0`,
  `Im > 0` or `Im < 0`; one segment `[0, 4]` of type `P` or `N` covers the curve and the
  indicator sum vanishes because `γ 4 = γ 0`.

The edge values of `bdryPath` are computed directly from the `clamp01` closed form.
-/

open Set

namespace NonUniqueEuler

namespace QRect

/-! ### `clamp01` on the three pieces -/

private theorem clamp01_of_le_zero' {u : ℝ} (h : u ≤ 0) : clamp01 u = 0 := by
  rw [clamp01, min_eq_left (h.trans zero_le_one), max_eq_left h]

private theorem clamp01_of_one_le' {u : ℝ} (h : 1 ≤ u) : clamp01 u = 1 := by
  rw [clamp01, min_eq_right h, max_eq_right zero_le_one]

/-! ### The four edges -/

private theorem im_bdryPath_edge0 (R : QRect) {s : ℝ} (hs : s ≤ 1) :
    (R.bdryPath s).im = R.y₀ := by
  simp only [bdryPath]
  rw [clamp01_of_le_zero' (by linarith : s - 1 ≤ 0), clamp01_of_le_zero' (by linarith : s - 3 ≤ 0)]
  ring

private theorem re_bdryPath_edge1 (R : QRect) {s : ℝ} (h₀ : 1 ≤ s) (h₁ : s ≤ 2) :
    (R.bdryPath s).re = R.x₁ := by
  simp only [bdryPath]
  rw [clamp01_of_one_le' h₀, clamp01_of_le_zero' (by linarith : s - 2 ≤ 0)]
  ring

private theorem im_bdryPath_edge2 (R : QRect) {s : ℝ} (h₀ : 2 ≤ s) (h₁ : s ≤ 3) :
    (R.bdryPath s).im = R.y₁ := by
  simp only [bdryPath]
  rw [clamp01_of_one_le' (by linarith : 1 ≤ s - 1), clamp01_of_le_zero' (by linarith : s - 3 ≤ 0)]
  ring

private theorem re_bdryPath_edge3 (R : QRect) {s : ℝ} (h₀ : 3 ≤ s) :
    (R.bdryPath s).re = R.x₀ := by
  simp only [bdryPath]
  rw [clamp01_of_one_le' (by linarith : 1 ≤ s), clamp01_of_one_le' (by linarith : 1 ≤ s - 2)]
  ring

/-- The indicator sum for the types `P, P, P, N`. -/
private theorem segIndicatorSum_PPPN (x : ℕ → ℤ) :
    segIndicatorSum 4 (fun i => if i = 3 then SegKind.N else SegKind.P) x = x 4 - x 3 := by
  simp [segIndicatorSum, Finset.sum_range_succ, SegKind.isN]

/-- The boundary winds once around every point of the open rectangle. -/
theorem hasWinding_bdryPath_sub_of_mem_openSet {R : QRect} (hR : R.Nondeg) {u : ℂ}
    (hu : u ∈ R.openSet) : HasWinding (fun t => R.bdryPath t - u) 0 4 1 := by
  rw [mem_openSet] at hu
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hu
  have hcont : Continuous fun t => R.bdryPath t - u :=
    (continuous_bdryPath R).sub continuous_const
  have key := hasWinding_of_segments (c := fun t => R.bdryPath t - u) (n := 4)
    (t := fun i => (i : ℝ)) (κ := fun i => if i = 3 then SegKind.N else SegKind.P)
    (by norm_num) (fun i _ => by simp) hcont.continuousOn
    (by simp only [Nat.cast_zero, Nat.cast_ofNat, bdryPath_four]) (by
      intro i hi s hs
      simp only [mem_Icc] at hs
      push_cast at hs
      obtain ⟨hs₀, hs₁⟩ := hs
      interval_cases i <;> norm_num at hs₀ hs₁
      · change SegKind.P.Admits (R.bdryPath s - u)
        simp only [SegKind.Admits, Complex.mem_slitPlane_iff, Complex.sub_im, Complex.sub_re]
        right
        rw [im_bdryPath_edge0 R hs₁]
        linarith
      · change SegKind.P.Admits (R.bdryPath s - u)
        simp only [SegKind.Admits, Complex.mem_slitPlane_iff, Complex.sub_im, Complex.sub_re]
        left
        rw [re_bdryPath_edge1 R hs₀ hs₁]
        linarith
      · change SegKind.P.Admits (R.bdryPath s - u)
        simp only [SegKind.Admits, Complex.mem_slitPlane_iff, Complex.sub_im, Complex.sub_re]
        right
        rw [im_bdryPath_edge2 R hs₀ hs₁]
        linarith
      · change SegKind.N.Admits (R.bdryPath s - u)
        simp only [SegKind.Admits, Complex.mem_slitPlane_iff, Complex.neg_re, Complex.neg_im,
          Complex.sub_im, Complex.sub_re]
        left
        rw [re_bdryPath_edge3 R hs₀]
        linarith)
  simp only [Nat.cast_zero, Nat.cast_ofNat] at key
  rw [segIndicatorSum_PPPN] at key
  have h4 : negImInd (R.bdryPath ((4 : ℕ) : ℝ) - u) = 1 := by
    have : (R.bdryPath ((4 : ℕ) : ℝ) - u).im < 0 := by
      rw [Complex.sub_im, Nat.cast_ofNat, bdryPath_four, im_bdryPath_edge0 R (by norm_num)]
      linarith
    simp only [negImInd, this, ↓reduceIte]
  have h3 : negImInd (R.bdryPath ((3 : ℕ) : ℝ) - u) = 0 := by
    have : ¬ (R.bdryPath ((3 : ℕ) : ℝ) - u).im < 0 := by
      rw [Complex.sub_im, im_bdryPath_edge2 R (by norm_num) (by norm_num)]
      linarith
    simp only [negImInd, this, ↓reduceIte]
  rw [h4, h3] at key
  simpa using key

/-- The boundary does not wind around points outside the closed rectangle. -/
theorem hasWinding_bdryPath_sub_of_not_mem_closedSet {R : QRect} (hR : R.Nondeg) {u : ℂ}
    (hu : u ∉ R.closedSet) : HasWinding (fun t => R.bdryPath t - u) 0 4 0 := by
  have hmem : ∀ s, R.bdryPath s ∈ R.closedSet := fun s =>
    bdryPath_mem_closedSet (le_of_lt hR.1) (le_of_lt hR.2) s
  simp only [mem_closedSet] at hmem hu
  have hκ : ∃ κ₀ : SegKind, ∀ s, κ₀.Admits (R.bdryPath s - u) := by
    by_cases h1 : (R.x₀ : ℝ) ≤ u.re
    · by_cases h2 : u.re ≤ R.x₁
      · by_cases h3 : (R.y₀ : ℝ) ≤ u.im
        · have h4 : (R.y₁ : ℝ) < u.im := by
            by_contra h4
            exact hu ⟨h1, h2, h3, not_lt.mp h4⟩
          refine ⟨SegKind.P, fun s => ?_⟩
          simp only [SegKind.Admits, Complex.mem_slitPlane_iff, Complex.sub_im]
          right
          have := (hmem s).2.2.2
          linarith
        · refine ⟨SegKind.P, fun s => ?_⟩
          simp only [SegKind.Admits, Complex.mem_slitPlane_iff, Complex.sub_im]
          right
          have := (hmem s).2.2.1
          push Not at h3
          linarith
      · refine ⟨SegKind.N, fun s => ?_⟩
        simp only [SegKind.Admits, Complex.mem_slitPlane_iff, Complex.neg_re, Complex.sub_re]
        left
        have := (hmem s).2.1
        push Not at h2
        linarith
    · refine ⟨SegKind.P, fun s => ?_⟩
      simp only [SegKind.Admits, Complex.mem_slitPlane_iff, Complex.sub_re]
      left
      have := (hmem s).1
      push Not at h1
      linarith
  obtain ⟨κ₀, hκ₀⟩ := hκ
  have hcont : Continuous fun t => R.bdryPath t - u :=
    (continuous_bdryPath R).sub continuous_const
  have key := hasWinding_of_segments (c := fun t => R.bdryPath t - u) (n := 1)
    (t := fun i => 4 * (i : ℝ)) (κ := fun _ => κ₀)
    (by norm_num) (fun i _ => by simp) hcont.continuousOn
    (by simp only [Nat.cast_zero, Nat.cast_one, mul_zero, mul_one, bdryPath_four])
    (fun i _ s _ => hκ₀ s)
  simp only [Nat.cast_zero, Nat.cast_one, mul_zero, mul_one] at key
  have hsum : segIndicatorSum 1 (fun _ => κ₀)
      (fun i => negImInd (R.bdryPath (4 * (i : ℝ)) - u)) = 0 := by
    simp [segIndicatorSum, bdryPath_four]
  rw [hsum] at key
  exact key

end QRect

end NonUniqueEuler
