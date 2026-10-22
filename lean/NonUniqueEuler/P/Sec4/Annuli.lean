import NonUniqueEuler.Defs.Sec4.Ring

/-!
# Proof: `lem:annuli` (the chain of annuli and the radial `a/16` slack)

Proof of `I/Sec4/Annuli.lean` (`04_ring.tex:111-132`). Same declarations, statements copied
verbatim.

The chain: inner radii `b, 7b/8, 3b/4, 5b/8, b/2, b/4` decrease and outer radii
`1, 5/4, 3/2, 7/4, 2, 3` increase; the open annulus `{5b/8 < |y| < 7/4}` is open and contains
`{3b/4 ≤ |y| ≤ 3/2}`. The slack: `||y'| - |y|| ≤ b/16` with `b < 1` and linear arithmetic; the
distance form via `abs_norm_sub_norm_le`. The ring instance uses `0 < a < 1` from
`a = exp(ξL - ξR)` and `ξL < 0 < ξR`.
-/

noncomputable section

open Set

namespace NonUniqueEuler

namespace RingData

open Sect

/-- `{3b/4 ≤ |y| ≤ 3/2} ⊆ int {5b/8 ≤ |y| ≤ 7/4}` for `b > 0`. -/
private theorem closedAnnulus_subset_interior {b : ℝ} (hb : 0 < b) :
    closedAnnulus (3 / 4 * b) (3 / 2) ⊆ interior (closedAnnulus (5 / 8 * b) (7 / 4)) := by
  have hopen : IsOpen ({y : ℂ | 5 / 8 * b < ‖y‖} ∩ {y : ℂ | ‖y‖ < 7 / 4}) :=
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  have hsub : {y : ℂ | 5 / 8 * b < ‖y‖} ∩ {y : ℂ | ‖y‖ < 7 / 4} ⊆
      closedAnnulus (5 / 8 * b) (7 / 4) := fun y hy => ⟨hy.1.le, hy.2.le⟩
  intro y hy
  refine interior_maximal hsub hopen ⟨?_, ?_⟩
  · show 5 / 8 * b < ‖y‖
    have := hy.1
    linarith
  · show ‖y‖ < 7 / 4
    have := hy.2
    linarith

/-- `lem:annuli`, chain of inclusions, for a general `b ∈ (0,1)`:
`{b ≤ |y| ≤ 1} ⊆ 𝒩₋ ⊆ 𝒩 ⊆ int N♭`, `N♭ ⊆ N ⊆ N'`. -/
theorem annuli_chain_of {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    closedAnnulus b 1 ⊆ closedAnnulus (7 / 8 * b) (5 / 4) ∧
      closedAnnulus (7 / 8 * b) (5 / 4) ⊆ closedAnnulus (3 / 4 * b) (3 / 2) ∧
      closedAnnulus (3 / 4 * b) (3 / 2) ⊆ interior (closedAnnulus (5 / 8 * b) (7 / 4)) ∧
      closedAnnulus (5 / 8 * b) (7 / 4) ⊆ closedAnnulus (b / 2) 2 ∧
      closedAnnulus (b / 2) 2 ⊆ closedAnnulus (b / 4) 3 := by
  refine ⟨?_, ?_, closedAnnulus_subset_interior hb, ?_, ?_⟩ <;>
  · rintro y ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

/-- `lem:annuli`, the radial slack, for a general `b ∈ (0,1)`: if every `y' ∈ T'` satisfies
`||y'| - |y|| ≤ b/16` for some `y ∈ T`, then `T ⊆ {b ≤ |y| ≤ 1}` gives `T' ⊆ 𝒩₋`, and `T ⊆ 𝒩₋`
gives `T' ⊆ 𝒩`. -/
theorem annuli_slack_of {b : ℝ} (hb : 0 < b) (hb1 : b < 1) {T T' : Set ℂ}
    (hT' : ∀ y' ∈ T', ∃ y ∈ T, |‖y'‖ - ‖y‖| ≤ b / 16) :
    (T ⊆ closedAnnulus b 1 → T' ⊆ closedAnnulus (7 / 8 * b) (5 / 4)) ∧
      (T ⊆ closedAnnulus (7 / 8 * b) (5 / 4) → T' ⊆ closedAnnulus (3 / 4 * b) (3 / 2)) := by
  refine ⟨fun hT y' hy' => ?_, fun hT y' hy' => ?_⟩ <;>
  · obtain ⟨y, hy, hd⟩ := hT' y' hy'
    obtain ⟨h1, h2⟩ := hT hy
    obtain ⟨hd1, hd2⟩ := abs_le.mp hd
    exact ⟨by linarith, by linarith⟩

/-- `lem:annuli`, the slack in the distance form ("in particular if every point of `T'` lies
within distance `b/16` of `T`"), for a general `b ∈ (0,1)`. -/
theorem annuli_slack_dist_of {b : ℝ} (hb : 0 < b) (hb1 : b < 1) {T T' : Set ℂ}
    (hT' : ∀ y' ∈ T', ∃ y ∈ T, ‖y' - y‖ ≤ b / 16) :
    (T ⊆ closedAnnulus b 1 → T' ⊆ closedAnnulus (7 / 8 * b) (5 / 4)) ∧
      (T ⊆ closedAnnulus (7 / 8 * b) (5 / 4) → T' ⊆ closedAnnulus (3 / 4 * b) (3 / 2)) := by
  refine annuli_slack_of hb hb1 fun y' hy' => ?_
  obtain ⟨y, hy, hd⟩ := hT' y' hy'
  exact ⟨y, hy, (abs_norm_sub_norm_le y' y).trans hd⟩

/-- `0 < a < 1` for the ring's `a = e^{ξL - ξR}`. -/
private theorem a_pos_lt_one : 0 < a ∧ a < 1 := by
  refine ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr ?_⟩
  unfold ξL ξR
  norm_num

/-- `lem:annuli` for the ring's `a`: `{a ≤ |y| ≤ 1} ⊆ 𝒩₋ ⊆ 𝒩 ⊆ int N♭ ⊆ N♭ ⊆ N ⊆ N'`. -/
theorem annuli_chain :
    ringAnn ⊆ annNm ∧ annNm ⊆ annNn ∧ annNn ⊆ interior annNflat ∧ annNflat ⊆ annN ∧
      annN ⊆ annN' :=
  annuli_chain_of a_pos_lt_one.1 a_pos_lt_one.2

/-- `lem:annuli`, radial slack, for the ring's `a`. -/
theorem annuli_slack {T T' : Set ℂ} (hT' : ∀ y' ∈ T', ∃ y ∈ T, |‖y'‖ - ‖y‖| ≤ a / 16) :
    (T ⊆ ringAnn → T' ⊆ annNm) ∧ (T ⊆ annNm → T' ⊆ annNn) :=
  annuli_slack_of a_pos_lt_one.1 a_pos_lt_one.2 hT'

/-- `lem:annuli`, distance form of the slack, for the ring's `a`. -/
theorem annuli_slack_dist {T T' : Set ℂ} (hT' : ∀ y' ∈ T', ∃ y ∈ T, ‖y' - y‖ ≤ a / 16) :
    (T ⊆ ringAnn → T' ⊆ annNm) ∧ (T ⊆ annNm → T' ⊆ annNn) :=
  annuli_slack_dist_of a_pos_lt_one.1 a_pos_lt_one.2 hT'

end RingData

end NonUniqueEuler
