import NonUniqueEuler.Defs.Sec5.All

/-!
# Helper for `lem:bilinear`: the cutoff `χ_N` (`05_single_ring.tex:221-223`)

Helper of `P/Sec5/Bilinear.lean`. The cutoff `χ_N ∈ C_c^∞(N₁)` equal to `1` near `N` is the
difference `b₂ - b₁` of two smooth bumps centred at `0`: `b₂ = 1` on `\bar B_{5/2}`, supported in
`B_{11/4}`; `b₁ = 1` on `\bar B_{3a/8}`, supported in `B_{7a/16}`. Then `χ_N = 1` on the open
annulus `{7a/16 < |y| < 5/2} ⊇ N = {a/2 ≤ |y| ≤ 2}` and `supp χ_N ⊆ {3a/8 ≤ |y| ≤ 11/4} ⊆ N₁`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ContDiff

namespace NonUniqueEuler

namespace OneRing

namespace BilinearH

open RingData

theorem a_pos' : 0 < a := Real.exp_pos _

theorem a_lt_one' : a < 1 := by
  unfold a
  rw [Real.exp_lt_one_iff]
  norm_num [ξL, ξR]

/-- The outer bump: `1` on `\bar B_{5/2}`, support `B_{11/4}`. -/
def bumpOut : ContDiffBump (0 : ℂ) where
  rIn := 5 / 2
  rOut := 11 / 4
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The inner bump: `1` on `\bar B_{3a/8}`, support `B_{7a/16}`. -/
def bumpIn : ContDiffBump (0 : ℂ) where
  rIn := 3 * a / 8
  rOut := 7 * a / 16
  rIn_pos := by have := a_pos'; positivity
  rIn_lt_rOut := by have := a_pos'; linarith

/-- The cutoff `χ_N = b₂ - b₁`. -/
def chiN (x : ℂ) : ℝ := bumpOut x - bumpIn x

theorem chiN_eq_one {x : ℂ} (h1 : 7 * a / 16 < ‖x‖) (h2 : ‖x‖ < 5 / 2) : chiN x = 1 := by
  have e1 : bumpOut x = 1 :=
    bumpOut.one_of_mem_closedBall (by simpa [bumpOut, dist_zero_right] using h2.le)
  have e2 : bumpIn x = 0 :=
    bumpIn.zero_of_le_dist (by simpa [bumpIn, dist_zero_right] using h1.le)
  simp [chiN, e1, e2]

theorem support_chiN_subset :
    Function.support chiN ⊆ {x : ℂ | 3 * a / 8 ≤ ‖x‖ ∧ ‖x‖ ≤ 11 / 4} := by
  intro x hx
  have ha := a_pos'
  have ha1 := a_lt_one'
  rw [Function.mem_support] at hx
  constructor
  · by_contra h
    push Not at h
    have e1 : bumpOut x = 1 :=
      bumpOut.one_of_mem_closedBall (by
        simp only [bumpOut, mem_closedBall, dist_zero_right]; linarith)
    have e2 : bumpIn x = 1 :=
      bumpIn.one_of_mem_closedBall (by
        simp only [bumpIn, mem_closedBall, dist_zero_right]; linarith)
    exact hx (by simp [chiN, e1, e2])
  · by_contra h
    push Not at h
    have e1 : bumpOut x = 0 :=
      bumpOut.zero_of_le_dist (by simp only [bumpOut, dist_zero_right]; linarith)
    have e2 : bumpIn x = 0 :=
      bumpIn.zero_of_le_dist (by simp only [bumpIn, dist_zero_right]; linarith)
    exact hx (by simp [chiN, e1, e2])

theorem tsupport_chiN_subset : tsupport chiN ⊆ annN1 := by
  have ha := a_pos'
  have hcl : IsClosed {x : ℂ | 3 * a / 8 ≤ ‖x‖ ∧ ‖x‖ ≤ 11 / 4} :=
    (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  refine (closure_minimal support_chiN_subset hcl).trans ?_
  intro x hx
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- `05_single_ring.tex:221-223`: the setting of `lem:Hk-calculus` for `(N, N₁, χ_N)`. -/
theorem hkCalcSetting_chiN : Sob.HkCalcSetting annN annN1 chiN where
  isCompact := isCompact_annN
  isOpen := isOpen_annN1
  isBounded := Metric.isBounded_ball.subset (fun x hx => by
    simpa [mem_ball, dist_zero_right] using hx.2 : annN1 ⊆ ball (0 : ℂ) 3)
  subset := fun x hx => by
    have ha := a_pos'
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  contDiff := bumpOut.contDiff.sub bumpIn.contDiff
  hasCompactSupport := bumpOut.hasCompactSupport.sub bumpIn.hasCompactSupport
  tsupport_subset := tsupport_chiN_subset
  eq_one_near := by
    have ha := a_pos'
    refine ⟨{x : ℂ | 7 * a / 16 < ‖x‖ ∧ ‖x‖ < 5 / 2},
      (isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const), fun x hx => ?_, fun x hx => ?_⟩
    · exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    · exact chiN_eq_one hx.1 hx.2

end BilinearH

end OneRing

end NonUniqueEuler
