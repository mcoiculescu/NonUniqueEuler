import NonUniqueEuler.Verify.Comp.Runs
import NonUniqueEuler.Defs.Verify.Winding
import NonUniqueEuler.Defs.Verify.SemOps
import NonUniqueEuler.Defs.Verify.NPrime
import NonUniqueEuler.Defs.Verify.Contour

/-!
# Basic facts about the certification code (proved)

Code: `Verify/Comp/{Contour,Certify,RunCore}.lean`.

These lemmas read only the plain data and the evidence that the search returns; none of them
is about the search itself (`oneRound`, `runRounds`, `certifyAdaptive`).

* `SegTy.toKind` (code type ↦ `SegKind` of `Defs/Verify/Winding.lean`) and `classify_sound`:
  an accepted box is of the claimed type.
* `AccSeg.spec`, `indAt_spec`: what an accepted segment and a decided indicator mean
  (an `evansEncl` box and a certain comparison).
* `junctionSumC_eq`: the code's indicator sum is `junctionSum` of `Defs/Verify/Winding.lean`.
* `certifyCell_spec`, `finishCell_spec`: a certified winding comes from `finishCell` on accepted
  segments, with `chainOK`, all junction indicators decided, and the junction sum;
  `segTs_size`, `segTs_getD`, `kindAt_segKs`, `cellInds_getD` read the arrays.
* `chainT`, `chainOK_spec`: the accepted segments of a certified cell form an
  `IsBoundaryChain` (`Defs/Verify/Contour.lean`), segment `i` being `[chainT ts i, chainT ts (i+1)]`.
* `coverOK_sound`: the coverage check of the runs.
* Bridges to `Defs/Verify/{Contour,NPrime}.lean`: `Rect.ptQ_eq_bdryPtQ`, `clampQ_eq`,
  `rectA_toQRect`, `rectOK_count`, `rectOK_gap`, `gmaxQ_eq`.
-/

namespace NonUniqueEuler.Verify

/-! ### Segment types -/

/-- The segment kind of `Defs/Verify/Winding.lean` of a code segment type. -/
def SegTy.toKind : SegTy → SegKind
  | .P => .P
  | .N => .N

@[simp] theorem SegTy.isN_toKind (t : SegTy) : t.toKind.isN = t.isN := by cases t <;> rfl

/-- `classify` is sound: every point of an accepted box is admissible for its type. -/
theorem classify_sound {B : CBox} {ty : SegTy} (h : classify B = some ty) {z : ℂ}
    (hz : z ∈ B) : ty.toKind.Admits z := by
  unfold classify at h
  split at h
  · simp at h
  · split at h
    · rename_i _ hP
      cases h
      simp only [SegTy.toKind, SegKind.Admits, Complex.mem_slitPlane_iff]
      simp only [Bool.or_eq_true] at hP
      rcases hP with (hP | hP) | hP
      · exact Or.inr (Ball.posC_sound hP hz.2).ne'
      · exact Or.inr (Ball.negC_sound hP hz.2).ne
      · exact Or.inl (Ball.posC_sound hP hz.1)
    · split at h
      · rename_i _ _ hN
        cases h
        simp only [SegTy.toKind, SegKind.Admits, Complex.mem_slitPlane_iff, Complex.neg_re]
        exact Or.inl (by linarith [Ball.negC_sound hN hz.1])
      · simp at h

/-! ### Evidence carried by the search -/

/-- An accepted segment: `evansEncl` on its segment box returned a box that `classify` accepted
with the recorded type. -/
theorem AccSeg.spec {cx : CellCtx} (a : AccSeg cx) :
    ∃ B, evansEncl cx.p cx.gr cx.ℓ (segBox cx.p cx.R a.1.1) cx.Gb = some B ∧
      classify B = some a.1.2 :=
  Option.bind_eq_some_iff.1 a.2

/-- A decided indicator: `evansEncl` on the point box returned a box whose imaginary part is
certainly negative (value `1`) or certainly positive (value `0`). -/
theorem indAt_spec {cx : CellCtx} {t : ℚ} {v : ℤ} (h : indAt cx t = some v) :
    ∃ B, evansEncl cx.p cx.gr cx.ℓ (ptBox cx.p cx.R t) cx.Gb = some B ∧
      ((v = 1 ∧ B.im.negC = true) ∨ (v = 0 ∧ B.im.posC = true)) := by
  unfold indAt at h
  split at h
  · rename_i B hB
    refine ⟨B, hB, ?_⟩
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true] at hc
      exact Or.inl ⟨rfl, hc.2⟩
    · split at h
      · rename_i _ hc
        cases h
        simp only [Bool.and_eq_true] at hc
        exact Or.inr ⟨rfl, hc.2⟩
      · simp at h
  · simp at h

/-! ### The indicator sum -/

theorem foldl_add_range (n : ℕ) (f : ℕ → ℤ) :
    (List.range n).foldl (fun acc i => acc + f i) 0 = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]; simp

/-- The code's indicator sum is `junctionSum` (`Defs/Verify/Winding.lean`). -/
theorem junctionSumC_eq (n : ℕ) (κ : ℕ → SegTy) (x : ℕ → ℤ) :
    junctionSumC n κ x = junctionSum n (fun i => (κ i).toKind) x := by
  unfold junctionSumC junctionSum
  rw [foldl_add_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [junctionTerm, SegTy.isN_toKind, Verify.cycNext, NonUniqueEuler.cycNext,
    Verify.cycPrev, NonUniqueEuler.cycPrev]
  rfl

/-! ### `certifyCell` and `finishCell` -/

/-- A certified winding number comes from `finishCell` on some accepted segments, and the
rectangle lies in `{Re λ > 0}`. -/
theorem certifyCell_spec {p : ℕ} {gr : Grid} {ℓ : ℕ} {R : Rect} {lo hi ν : ℚ} {J K : ℕ} {w : ℤ}
    (h : (certifyCell p gr ℓ R lo hi ν J K).winding = some w) :
    0 < R.x0 ∧ ∃ segs nev, (finishCell ⟨p, gr, ℓ, R, gBall p lo hi⟩ segs nev).winding = some w := by
  unfold certifyCell at h
  split at h
  · simp [CellOut.deadOut] at h
  · rename_i hx
    refine ⟨by simpa using hx, ?_⟩
    dsimp only at h
    split at h
    · simp [CellOut.deadOut] at h
    · exact ⟨_, _, h⟩

/-- A certified winding number of `finishCell`: the accepted segments form a closed chain
(`chainOK`), every junction indicator is decided, and the result is the junction sum. -/
theorem finishCell_spec {cx : CellCtx} {segs : List (AccSeg cx)} {nev : ℕ} {w : ℤ}
    (h : (finishCell cx segs nev).winding = some w) :
    chainOK (segTs segs) = true ∧
      allDecided (segTs segs).size (kindAt (segKs segs))
        (fun i => (cellInds cx (segTs segs) (kindAt (segKs segs))).getD i none) = true ∧
      w = junctionSumC (segTs segs).size (kindAt (segKs segs))
        (indVal (cellInds cx (segTs segs) (kindAt (segKs segs)))) := by
  unfold finishCell at h
  dsimp only at h
  split at h
  · simp [CellOut.deadOut] at h
  · rename_i hc
    refine ⟨by simpa using hc, ?_⟩
    dsimp only at h
    split at h
    · rename_i hw
      rw [Bool.and_eq_true] at hw
      exact ⟨hw.2, (Option.some.inj h).symm⟩
    · simp at h

@[simp] theorem segTs_size {cx : CellCtx} (segs : List (AccSeg cx)) :
    (segTs segs).size = segs.length := by
  simp [segTs]

theorem segTs_getD {cx : CellCtx} (segs : List (AccSeg cx)) {i : ℕ} (hi : i < segs.length) :
    (segTs segs).getD i default = (segs[i]'hi).1.1 := by
  simp [segTs, hi]

theorem kindAt_segKs {cx : CellCtx} (segs : List (AccSeg cx)) {i : ℕ} (hi : i < segs.length) :
    kindAt (segKs segs) i = (segs[i]'hi).1.2 := by
  simp [kindAt, segKs, hi]

theorem cellInds_getD (cx : CellCtx) (ts : Array Seg) (κ : ℕ → SegTy) {i : ℕ}
    (hi : i < ts.size) :
    (cellInds cx ts κ).getD i none =
      if isJunction ts.size κ i then indAt cx (ts.getD i default).t0 else some 0 := by
  simp [cellInds, hi]

/-! ### The chain of accepted segments -/

/-- The parameters of the chain: `t i` is the start of segment `i` (`i < n`), and `t n = 4`. -/
def chainT (ts : Array Seg) (i : ℕ) : ℚ := if i < ts.size then (ts.getD i default).t0 else 4

theorem chainOK_spec {ts : Array Seg} (h : chainOK ts = true) :
    IsBoundaryChain ts.size (chainT ts) ∧
      ∀ i < ts.size, (ts.getD i default).t1 = chainT ts (i + 1) := by
  unfold chainOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨hn, h0⟩, hlast⟩, hall⟩ := h
  have hnext : ∀ i < ts.size, (ts.getD i default).t1 = chainT ts (i + 1) := by
    intro i hi
    by_cases hi1 : i + 1 < ts.size
    · rcases (hall i hi).2 with h1 | h1
      · omega
      · simp only [chainT, hi1, ite_true]
        exact h1
    · have : i = ts.size - 1 := by omega
      subst this
      simp only [chainT, hi1, ite_false]
      exact hlast
  refine ⟨⟨hn, ?_, ?_, ?_, ?_⟩, hnext⟩
  · simp only [chainT, hn, ite_true]; exact h0
  · simp [chainT]
  · intro i hi
    rw [← hnext i hi]
    simp only [chainT, hi, ite_true]
    exact (hall i hi).1.1
  · intro i hi
    rw [← hnext i hi]
    have he := (hall i hi).1.2
    simp only [edgeOK, Bool.and_eq_true, decide_eq_true_eq] at he
    refine ⟨Rat.floor (ts.getD i default).t0, ?_, he.2⟩
    simp only [chainT, hi, ite_true]
    exact he.1

/-! ### Coverage -/

/-- `coverOK l a b`: every `G ∈ [a, b]` lies in one of the (nonempty list of) intervals. -/
theorem coverOK_sound (l : List (ℚ × ℚ)) : ∀ (a b : ℚ), l ≠ [] → coverOK l a b = true →
    ∀ G : ℝ, (a : ℝ) ≤ G → G ≤ b → ∃ c ∈ l, (c.1 : ℝ) ≤ G ∧ G ≤ c.2 := by
  induction l with
  | nil => intro a b h; exact absurd rfl h
  | cons c rest ih =>
    intro a b _ h G hG1 hG2
    simp only [coverOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, _⟩, h3⟩ := h
    by_cases hG : G ≤ c.2
    · refine ⟨c, by simp, ?_, hG⟩
      have : (c.1 : ℝ) = a := by exact_mod_cast h1
      linarith
    · push Not at hG
      rcases rest with _ | ⟨d, rest'⟩
      · simp only [coverOK, decide_eq_true_eq] at h3
        have : (c.2 : ℝ) = b := by exact_mod_cast h3
        linarith
      · obtain ⟨e, he, he'⟩ := ih c.2 b (List.cons_ne_nil _ _) h3 G hG.le hG2
        exact ⟨e, List.mem_cons_of_mem _ he, he'⟩

/-! ### Bridges to the contour and the rectangles of (N1′), (N2′) -/

theorem clampQ_eq (u : ℚ) : clampQ u = clamp01Q u := rfl

theorem Rect.ptQ_eq_bdryPtQ (R : Rect) (t : ℚ) : R.ptQ t = R.toQRect.bdryPtQ t := rfl

theorem rectA_toQRect : rectA.toQRect = RA := rfl

theorem rectOK_count {R : Rect} (h : rectOK .count R = true) : R.toQRect = RA := by
  simp only [rectOK, decide_eq_true_eq] at h
  rw [h]; rfl

theorem rectOK_gap {R : Rect} (h : rectOK .gap R = true) : GapRectOK R.toQRect := by
  simp only [rectOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, ⟨h2, h3⟩, QRect.closedSet_subset_closedSet h4 h5 h6 h7⟩

theorem gmaxQ_eq : ((gmaxQ : ℚ) : ℝ) = RingData.d := by
  simp only [gmaxQ, RingData.d]; norm_num

end NonUniqueEuler.Verify
