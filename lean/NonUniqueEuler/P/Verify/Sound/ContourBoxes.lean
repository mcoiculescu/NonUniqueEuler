import NonUniqueEuler.Defs.Verify.Encl
import NonUniqueEuler.I.Verify.ContourGeom

/-!
# Proof: the segment boxes of the certification contain their contour segments

Proof of `NonUniqueEuler/I/Verify/Sound/ContourBoxes.lean` (same declarations, statements copied
verbatim). Manuscript: the certification (`A_verification.tex:559-571`): by (CP),
`Λ^b = (X_p ∪ X_q) + i(Y_p ∪ Y_q) ⊇ [p, q]`.

Used black box: `QRect.bdryPath_mem_segHullQ` (`I/Verify/ContourGeom`): on one edge the image
of the parameter segment lies in the rational box spanned by its end points. Then each
coordinate lies between the coordinates of the end points, and `Ball.mem_union_of_between`
with `Ball.mem_ofRat` gives the containment in the union balls of `segBox`.
-/

noncomputable section

open Set

namespace NonUniqueEuler.Verify

/-- **The segment box** (`seg_box`): if the parameter segment `[t₀, t₁]` lies in one edge
`[e, e+1]`, its box contains the contour point `γ(t)` for every `t ∈ [t₀, t₁]`. -/
theorem mem_segBox (p : ℕ) (R : Rect) {s : Seg} {e : ℤ} (he0 : (e : ℚ) ≤ s.t0)
    (he1 : s.t1 ≤ e + 1) {t : ℝ} (ht0 : (s.t0 : ℝ) ≤ t) (ht1 : t ≤ s.t1) :
    R.toQRect.bdryPath t ∈ segBox p R s := by
  have h₀ : ((e : ℤ) : ℝ) ≤ ((s.t0 : ℚ) : ℝ) := by exact_mod_cast he0
  have h₃ : ((s.t1 : ℚ) : ℝ) ≤ (e : ℝ) + 1 := by exact_mod_cast he1
  have hmem := QRect.bdryPath_mem_segHullQ R.toQRect h₀ ht0 ht1 h₃
  rw [QRect.mem_closedSet] at hmem
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hmem
  simp only [QRect.segHullQ, Rat.cast_min, Rat.cast_max] at hx0 hx1 hy0 hy1
  rw [CBox.mem_def]
  simp only [segBox, Rect.ptQ_eq_bdryPtQ]
  exact ⟨Ball.mem_union_of_between (Ball.mem_ofRat p _) (Ball.mem_ofRat p _) hx0 hx1,
    Ball.mem_union_of_between (Ball.mem_ofRat p _) (Ball.mem_ofRat p _) hy0 hy1⟩

end NonUniqueEuler.Verify
