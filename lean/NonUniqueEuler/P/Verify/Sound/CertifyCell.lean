import NonUniqueEuler.Defs.Verify.Encl
import NonUniqueEuler.I.Verify.Sound.EvansEncl
import NonUniqueEuler.I.Verify.Sound.ContourBoxes
import NonUniqueEuler.I.Verify.SegmentFormula
import NonUniqueEuler.I.Verify.ContourGeom
import NonUniqueEuler.I.Evans.ODE

/-!
# Proof: the soundness of the certification of one cell (`certifyCell`)

Proves the interface `I/Verify/Sound/CertifyCell.lean` (same declarations, statements copied
verbatim). See the docstring there for the manuscript location (Proposition A.7, with
Propositions A.3 and A.4) and the proof sketch.

Helper (proved here): `exists_seg_of_mem` (a point of `[f 0, f (n+1)]` lies in one of the
intervals `[f i, f (i+1)]`, `i ≤ n`), used for `Re γ(t) > 0` on all of `[0, 4]`.

Continuity of `E_3(γ(·); G)` on `[0, 4]` uses `evans_differentiableOn` (`I/Evans/ODE`) for the
fixed `G` (holomorphy in `λ` on `{Re λ > 0}` implies continuity there); the docstring of the
interface suggests the joint `evans_continuousOn`, either works.
-/

noncomputable section

open Set

namespace NonUniqueEuler.Verify

open RingData

/-- **An accepted segment** (`segAccept … s = some ty`, the evidence of an `AccSeg`): on the
segment, the contour lies in `{Re λ > 0}` and `E_ℓ(·; G)` takes values admissible for the type
`ty`, for every `G` in the `G`-ball. -/
theorem segAccept_sound {p q hpow N ℓ : ℕ} (hN : 1 ≤ N) (hℓ : 1 ≤ ℓ) {χ : ℝ → ℝ}
    (hχ : IsAdmissibleCutoff χ) {R : Rect} {Gb : Ball} {s : Seg} {ty : SegTy}
    (h : segAccept ⟨p, Grid.build q hpow N, ℓ, R, Gb⟩ s = some ty) {e : ℤ}
    (he0 : (e : ℚ) ≤ s.t0) (he1 : s.t1 ≤ e + 1) {t : ℝ} (ht0 : (s.t0 : ℝ) ≤ t)
    (ht1 : t ≤ s.t1) {G : ℝ} (hG : G ∈ Gb) :
    0 < (R.toQRect.bdryPath t).re ∧ ty.toKind.Admits (evans χ ℓ (R.toQRect.bdryPath t) G) := by
  obtain ⟨B, hB, hc⟩ := AccSeg.spec (cx := ⟨p, Grid.build q hpow N, ℓ, R, Gb⟩) ⟨(s, ty), h⟩
  have hz := mem_segBox p R he0 he1 ht0 ht1
  exact ⟨evansEncl_re_pos hB hz, classify_sound hc (evansEncl_sound hN hℓ hχ hB hz hG)⟩

/-- **A decided indicator** (`indAt … t = some v`) is `1[Im E_ℓ(γ(t); G) < 0]` for every `G`
in the `G`-ball. -/
theorem indAt_sound {p q hpow N ℓ : ℕ} (hN : 1 ≤ N) (hℓ : 1 ≤ ℓ) {χ : ℝ → ℝ}
    (hχ : IsAdmissibleCutoff χ) {R : Rect} {Gb : Ball} {t : ℚ} {v : ℤ}
    (h : indAt ⟨p, Grid.build q hpow N, ℓ, R, Gb⟩ t = some v) {G : ℝ} (hG : G ∈ Gb) :
    v = negImInd (evans χ ℓ (R.toQRect.bdryPath t) G) := by
  obtain ⟨B, hB, hv⟩ := indAt_spec h
  have hmem := evansEncl_sound hN hℓ hχ hB (mem_ptBox p R t) hG
  rcases hv with ⟨rfl, hneg⟩ | ⟨rfl, hpos⟩
  · have him := Ball.negC_sound hneg hmem.2
    simp [negImInd, him]
  · have him := Ball.posC_sound hpos hmem.2
    simp [negImInd, not_lt.2 him.le]

/-- A point of `[f 0, f (n + 1)]` lies in one of the intervals `[f i, f (i + 1)]`, `i ≤ n`. -/
theorem exists_seg_of_mem (f : ℕ → ℝ) {s : ℝ} (h0 : f 0 ≤ s) :
    ∀ n : ℕ, s ≤ f (n + 1) → ∃ i ≤ n, f i ≤ s ∧ s ≤ f (i + 1)
  | 0, h => ⟨0, le_rfl, h0, h⟩
  | n + 1, h => by
    by_cases hs : s ≤ f (n + 1)
    · obtain ⟨i, hi, h1, h2⟩ := exists_seg_of_mem f h0 n hs
      exact ⟨i, by omega, h1, h2⟩
    · exact ⟨n + 1, le_rfl, (not_le.1 hs).le, h⟩

/-- **The certification of one cell is sound** (Proposition A.7 for one cell, with
Propositions A.3 and A.4): if `certifyCell` succeeds on the cell `[lo, hi]` and the rectangle
`R` with result `w`, then for every `G ∈ [lo, hi]` (`G ≥ 0`), `E_3(·; G)` is nonvanishing on the
boundary of `R` and its winding number about `0` along it is `w`. -/
theorem certifyCell_sound {p q hpow N : ℕ} (hN : 1 ≤ N) {χ : ℝ → ℝ}
    (hχ : IsAdmissibleCutoff χ) {R : Rect} {lo hi ν : ℚ} {J K : ℕ} {w : ℤ}
    (h : (certifyCell p (Grid.build q hpow N) 3 R lo hi ν J K).winding = some w) :
    CellCertified χ ⟨⟨lo, hi⟩, R.toQRect⟩ w := by
  obtain ⟨-, segs, nev, hfin⟩ := certifyCell_spec h
  obtain ⟨hchain, hdec, hw⟩ := finishCell_spec hfin
  have hsz : (segTs segs).size = segs.length := segTs_size segs
  have hgetD : ∀ i (hi : i < segs.length), (segTs segs).getD i default = (segs[i]'hi).1.1 :=
    fun i hi => segTs_getD segs hi
  have hk : ∀ i (hi : i < segs.length), kindAt (segKs segs) i = (segs[i]'hi).1.2 :=
    fun i hi => kindAt_segKs segs hi
  generalize segTs segs = ts at hchain hdec hw hsz hgetD
  generalize kindAt (segKs segs) = κc at hdec hw hk
  obtain ⟨hbc, hnext⟩ := chainOK_spec hchain
  obtain ⟨hr0, hrn, hrmono⟩ := hbc.real_params
  -- the parameters of segment `i`
  have hti : ∀ i < ts.size, chainT ts i = (ts.getD i default).t0 := fun i hi => by
    simp only [chainT, hi, ite_true]
  intro G hG _
  have hG' : (lo : ℝ) ≤ G ∧ G ≤ hi := hG
  have hGb : G ∈ gBall p lo hi := mem_gBall p hG'.1 hG'.2
  -- the evidence of segment `i`
  have hseg : ∀ i < ts.size, ∀ s ∈ Icc ((chainT ts i : ℚ) : ℝ) (chainT ts (i + 1)),
      0 < (R.toQRect.bdryPath s).re ∧
        (κc i).toKind.Admits (evans χ 3 (R.toQRect.bdryPath s) G) := by
    intro i hin s hs
    have hil : i < segs.length := hsz ▸ hin
    obtain ⟨e, he0, he1⟩ := hbc.edge i hin
    rw [hti i hin, hgetD i hil] at he0
    rw [← hnext i hin, hgetD i hil] at he1
    have hs0 : (((segs[i]'hil).1.1.t0 : ℚ) : ℝ) ≤ s := by
      have := hs.1; rw [hti i hin, hgetD i hil] at this; exact this
    have hs1 : s ≤ (((segs[i]'hil).1.1.t1 : ℚ) : ℝ) := by
      have := hs.2; rw [← hnext i hin, hgetD i hil] at this; exact this
    rw [hk i hil]
    exact segAccept_sound hN (by norm_num) hχ (segs[i]'hil).2 he0 he1 hs0 hs1 hGb
  have hpos : ts.size = (ts.size - 1) + 1 := by have := hbc.pos; omega
  -- continuity on `[0, 4]`
  have hcont : ContinuousOn (fun t => evans χ 3 (R.toQRect.bdryPath t) G)
      (Icc ((chainT ts 0 : ℚ) : ℝ) (chainT ts ts.size)) := by
    have hmaps : MapsTo R.toQRect.bdryPath (Icc ((chainT ts 0 : ℚ) : ℝ) (chainT ts ts.size))
        {z : ℂ | 0 < z.re} := by
      intro s hs
      have hs2 : s ≤ ((chainT ts ((ts.size - 1) + 1) : ℚ) : ℝ) := by rw [← hpos]; exact hs.2
      obtain ⟨i, hi, h1, h2⟩ :=
        exists_seg_of_mem (fun i => ((chainT ts i : ℚ) : ℝ)) hs.1 (ts.size - 1) hs2
      exact (hseg i (by omega) s ⟨h1, h2⟩).1
    exact ((evans_differentiableOn χ hχ 3 G).continuousOn).comp
      (QRect.continuous_bdryPath _).continuousOn hmaps
  have hcl : evans χ 3 (R.toQRect.bdryPath ((chainT ts 0 : ℚ) : ℝ)) G =
      evans χ 3 (R.toQRect.bdryPath ((chainT ts ts.size : ℚ) : ℝ)) G := by
    rw [hr0, hrn, QRect.bdryPath_four]
  have hJ : ∀ i < ts.size, IsJunction ts.size (fun i => (κc i).toKind) i →
      indVal (cellInds ⟨p, Grid.build q hpow N, 3, R, gBall p lo hi⟩ ts κc) i =
        negImInd (evans χ 3 (R.toQRect.bdryPath ((chainT ts i : ℚ) : ℝ)) G) := by
    intro i hin hjun
    have hjc : isJunction ts.size κc i = true := by
      simp only [IsJunction, SegTy.isN_toKind] at hjun
      simp only [isJunction, Verify.cycPrev, NonUniqueEuler.cycPrev] at hjun ⊢
      simpa using hjun
    have hd := hdec
    simp only [allDecided, List.all_eq_true, List.mem_range, Bool.or_eq_true] at hd
    have hd' := hd i hin
    simp only [cellInds_getD _ ts κc hin, hjc, ↓reduceIte, Bool.not_true, Bool.false_eq_true,
      false_or] at hd'
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hd'
    have hval : indVal (cellInds ⟨p, Grid.build q hpow N, 3, R, gBall p lo hi⟩ ts κc) i = v := by
      simp only [indVal, cellInds_getD _ ts κc hin, hjc, ↓reduceIte, hv, Option.getD_some]
    rw [hval, indAt_sound hN (by norm_num) hχ hv hGb, hti i hin]
  have hwind := hasWinding_of_segments_junction (c := fun t => evans χ 3 (R.toQRect.bdryPath t) G)
    (t := fun i => ((chainT ts i : ℚ) : ℝ)) (κ := fun i => (κc i).toKind) hbc.pos hrmono hcont
    hcl (fun i hi s hs => (hseg i hi s hs).2) hJ
  rw [hr0, hrn, ← junctionSumC_eq, ← hw] at hwind
  exact hwind

end NonUniqueEuler.Verify
