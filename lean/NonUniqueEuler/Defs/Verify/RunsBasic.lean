import NonUniqueEuler.Defs.Verify.CertifyBasic

/-!
# The runs: from `checkCore` to (N1′) and (N2′), given the soundness of one certification

Code: `Verify/Comp/RunCore.lean`.

`checkCore_sound`: if `checkCore p spec = true`, and every certification that `checkCore`
performs is sound (the hypothesis `H`, which is `certifyCell_sound`, proved from
Proposition A.3 and Proposition A.4 in `P/Verify/Sound/CertifyCell.lean`), then (N1′) and (N2′)
hold. The certified sub-cells of the runs, with their rectangles, are the cells of (N1′) and (N2′)
(`CertRes.toCertCell`). No property of the search is used: each certified sub-cell carries its
evidence.
-/

namespace NonUniqueEuler.Verify

open Set

/-- A certified sub-cell of a run as a statement-layer cell (interval and rectangle). -/
def CertRes.toCertCell {p : ℕ} {gr : Grid} {item : Item} {spec : RunSpec}
    (r : CertRes p gr item spec) : CertCell :=
  ⟨⟨r.1.2.lo, r.1.2.hi⟩, r.1.1.toQRect⟩

/-- What `itemOK` checks: the certified sub-cells cover `[0, d]`, every result is `1`, and every
rectangle is as required. -/
theorem itemOK_spec {p : ℕ} {gr : Grid} {item : Item} {spec : RunSpec}
    {out : List (CertRes p gr item spec) × List (ℚ × ℚ) × ℕ} (h : itemOK item out = true) :
    (∀ G ∈ Icc (0 : ℝ) RingData.d, ∃ c ∈ out.1, G ∈ c.toCertCell.G.toSet) ∧
      ∀ c ∈ out.1, c.1.2.winding = 1 ∧ rectOK item c.1.1 = true := by
  unfold itemOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    List.isEmpty_eq_false_iff] at h
  obtain ⟨⟨⟨⟨_, hne⟩, hw⟩, hr⟩, hc⟩ := h
  refine ⟨fun G hG => ?_, fun c hc' => ⟨hw c hc', hr c hc'⟩⟩
  have hne' : out.1.map (fun r => (r.1.2.lo, r.1.2.hi)) ≠ [] := by simpa using hne
  obtain ⟨c', hc', h1, h2⟩ := coverOK_sound _ 0 gmaxQ hne' hc G (by simpa using hG.1)
    (by rw [gmaxQ_eq]; exact hG.2)
  obtain ⟨r, hr', rfl⟩ := List.mem_map.1 hc'
  exact ⟨r, hr', h1, h2⟩

/-- (N1′) from a successful (N1′) run whose certifications are sound. -/
theorem N1'_of_itemOK {χ : ℝ → ℝ} {p : ℕ} {gr : Grid} {spec : RunSpec}
    {out : List (CertRes p gr .count spec) × List (ℚ × ℚ) × ℕ} (h : itemOK .count out = true)
    (hcert : ∀ c ∈ out.1, CellCertified χ c.toCertCell c.1.2.winding) : N1' χ := by
  obtain ⟨hcov, hall⟩ := itemOK_spec h
  refine N1'_of_cells (out.1.map CertRes.toCertCell) (fun G hG => ?_) (fun c hc => ?_)
    (fun c hc => ?_)
  · obtain ⟨c, hc, hGc⟩ := hcov G hG
    exact ⟨_, List.mem_map_of_mem hc, hGc⟩
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hc
    exact rectOK_count (hall r hr).2
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hc
    have := hcert r hr
    rwa [(hall r hr).1] at this

/-- (N2′) from a successful (N2′) run whose certifications are sound. -/
theorem N2'_of_itemOK {χ : ℝ → ℝ} {p : ℕ} {gr : Grid} {spec : RunSpec}
    {out : List (CertRes p gr .gap spec) × List (ℚ × ℚ) × ℕ} (h : itemOK .gap out = true)
    (hcert : ∀ c ∈ out.1, CellCertified χ c.toCertCell c.1.2.winding) : N2' χ := by
  obtain ⟨hcov, hall⟩ := itemOK_spec h
  refine N2'_of_cells (out.1.map CertRes.toCertCell) (fun G hG => ?_) (fun c hc => ?_)
    (fun c hc => ?_)
  · obtain ⟨c, hc, hGc⟩ := hcov G hG
    exact ⟨_, List.mem_map_of_mem hc, hGc⟩
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hc
    exact rectOK_gap (hall r hr).2
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hc
    have := hcert r hr
    rwa [(hall r hr).1] at this

/-- **The runs** (Proposition A.7, given the soundness `H` of each certification): if
`checkCore p spec = true` then (N1′) and (N2′) hold. -/
theorem checkCore_sound {p : ℕ} {spec : CertSpec} (h : checkCore p spec = true) {χ : ℝ → ℝ}
    (H : ∀ (R : Rect) (lo hi ν : ℚ) (J K : ℕ) (w : ℤ),
      (certifyCell p (Grid.build p gridHpow gridOrder) 3 R lo hi ν J K).winding = some w →
        CellCertified χ ⟨⟨lo, hi⟩, R.toQRect⟩ w) :
    N1' χ ∧ N2' χ := by
  unfold checkCore at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨_, hc, hg⟩ := And.intro h.1 h.2
  exact ⟨N1'_of_itemOK hc fun c _ => H _ _ _ _ _ _ _ c.2,
    N2'_of_itemOK hg fun c _ => H _ _ _ _ _ _ _ c.2⟩

/-- The same for the checker `check` of the statement layer.

(Named `check_sound_of_certifyCell`, not `check_sound`: the final theorem
`Verify.check_sound : CheckerSound Verify.check` (`I/Verify/Final.lean`) has that name.) -/
theorem check_sound_of_certifyCell {cert : CertificateData} (h : check cert = true) {χ : ℝ → ℝ}
    (H : ∀ (R : Rect) (lo hi ν : ℚ) (J K : ℕ) (w : ℤ),
      (certifyCell defaultPrec (Grid.build defaultPrec gridHpow gridOrder) 3 R lo hi ν J K).winding
        = some w → CellCertified χ ⟨⟨lo, hi⟩, R.toQRect⟩ w) :
    N1' χ ∧ N2' χ :=
  checkCore_sound h H

end NonUniqueEuler.Verify
