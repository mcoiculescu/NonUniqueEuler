import NonUniqueEuler.Defs.Sec11.All
import NonUniqueEuler.I.Sec10.ConstantsPos
import NonUniqueEuler.I.Sec9.Standing
import NonUniqueEuler.I.Sec6.Clock
import NonUniqueEuler.I.Sec7.SkSmall

/-!
# Helper for `P/Sec11/Geometry.lean`: elementary facts

Helper of the proof of `lem:geometry` (`11_bootstrap.tex:146-218`): positivity of `A_k`, `s_k`,
`r_k`, `C_*`; `s_k ≤ a/32` and `r_j ≤ (a/32) r_i` for `i < j` (`eq:sk-small`); the norm bounds on
`N♭_i = r_i N♭ = {⅝ar_i ≤ |x| ≤ 7r_i/4}` and `N♭_i ⊂ N_i`; `D_k = S_k ∪ D_{k+1}`; and the order facts
of the clock that the proof uses (`lem:clock`(1)): a quiet ring is not debris, `t♯_j ≤ e_j`,
`T_{j+1} ≤ t♯_j`, `T_{j+1} ≥ 0`, `T_j ≤ T_i` for `i ≤ j`, the rings `i ≤ j` are not debris before
`e_j`, and a ring `j` that is not debris at `t' ≤ T_end` has `t' ≤ e_j`. All proved.
(Some of these are also proved, independently, in the helpers of other Section 11 proofs; helper
files of other proofs may not be imported (import rules, `README.md`).)
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

namespace GeometryH

open RingData Datum Sect

variable {S : Standing}

/-! ### Constants and radii -/

/-- The signs of the constants (`lem:nonempty`), from (SA). -/
theorem constPos (hS : S.Holds) : S.ConstPos :=
  constants_pos S hS.admissible hS.hN hS.σ'_gt hS.σ'_lt_sigma hS.δ₀_pos hS.one_lt_μ hS.Tpin_pos

theorem gsmall (hS : S.Holds) : S.P.GSmall := (standing_levels S hS).2.2.1

theorem A_pos (hS : S.Holds) (k : ℕ) : 0 < S.P.A k := hS.valid.A_pos k

theorem s_pos (hS : S.Holds) (k : ℕ) : 0 < S.P.s k := hS.valid.s_pos k

theorem r_pos (hS : S.Holds) (k : ℕ) : 0 < S.P.r k := hS.valid.r_pos k

theorem σ'_pos (hS : S.Holds) : 0 < S.σ' := lt_trans (by norm_num) hS.σ'_gt

/-- `C_* > 0`. -/
theorem Cstar_pos : 0 < Cstar := by
  unfold Cstar BS.cLpLinf
  have hc : (4 : ℝ).conjExponent = 4 / 3 := by
    rw [Real.conjExponent]; norm_num
  rw [hc]
  have hb : 0 ≤ 2 * Real.pi / (2 - 4 / 3 : ℝ) := by
    have := Real.pi_pos
    have : (0 : ℝ) < 2 - 4 / 3 := by norm_num
    positivity
  have h1 := Real.rpow_nonneg hb (1 / (4 / 3))
  have := Real.pi_pos
  have h2 : 0 < Real.sqrt Mvort := Real.sqrt_pos.2 Mvort_pos
  have h3 : 0 < 1 + (2 * Real.pi / (2 - 4 / 3 : ℝ)) ^ (1 / (4 / 3 : ℝ)) := by linarith
  positivity

theorem s_le (hS : S.Holds) {k : ℕ} (hk : 1 ≤ k) : S.P.s k ≤ a / 32 :=
  ((Rings.sk_small S.P hS.valid).1 k hk).2.2

/-- `r_j ≤ (a/32) r_i` for `1 ≤ i < j` (`eq:sk-small`). -/
theorem r_le_of_lt (hS : S.Holds) {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) :
    S.P.r j ≤ a / 32 * S.P.r i := by
  have h1 := (Rings.sk_small S.P hS.valid).2.1 i j hi hij
  have hri := r_pos hS i
  have hsb0 : 0 ≤ S.P.sbar := hS.sbar_pos.le
  have hsb1 : S.P.sbar ≤ 1 := by
    have := hS.sbar_le
    have := a_lt_one
    linarith
  have hpow : S.P.sbar ^ (j - i - 1) ≤ 1 := pow_le_one₀ hsb0 hsb1
  have hs : S.P.s (j - 1) ≤ a / 32 := s_le hS (by omega)
  have hs0 : 0 < S.P.s (j - 1) := s_pos hS _
  have h2 : S.P.s (j - 1) * S.P.sbar ^ (j - i - 1) ≤ a / 32 := by
    calc S.P.s (j - 1) * S.P.sbar ^ (j - i - 1) ≤ S.P.s (j - 1) * 1 :=
          mul_le_mul_of_nonneg_left hpow hs0.le
      _ ≤ a / 32 := by rw [mul_one]; exact hs
  have h3 : S.P.r j / S.P.r i ≤ a / 32 := h1.trans h2
  rwa [div_le_iff₀ hri] at h3

/-! ### The annuli -/

theorem mem_scaleSet_closedAnnulus {r ρm ρp : ℝ} (hr : 0 < r) {x : ℂ} :
    x ∈ scaleSet r (closedAnnulus ρm ρp) ↔ ρm * r ≤ ‖x‖ ∧ ‖x‖ ≤ ρp * r := by
  rw [mem_scaleSet, mem_closedAnnulus, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hr, ← div_eq_inv_mul, le_div_iff₀ hr, div_le_iff₀ hr]

/-- `N♭_i = {⅝ar_i ≤ |x| ≤ 7r_i/4}`. -/
theorem norm_of_mem_Nflatk (hS : S.Holds) {i : ℕ} {x : ℂ} (hx : x ∈ S.P.Nflatk i) :
    5 / 8 * a * S.P.r i ≤ ‖x‖ ∧ ‖x‖ ≤ 7 / 4 * S.P.r i :=
  (mem_scaleSet_closedAnnulus (r_pos hS i)).1 hx

/-- `N♭_i ⊂ N_i`. -/
theorem Nflatk_subset_Nk (hS : S.Holds) (i : ℕ) : S.P.Nflatk i ⊆ S.P.Nk i := by
  intro x hx
  have hr := r_pos hS i
  obtain ⟨h1, h2⟩ := norm_of_mem_Nflatk hS hx
  have ha := zero_lt_a
  show x ∈ scaleSet (S.P.r i) (closedAnnulus (a / 2) 2)
  rw [mem_scaleSet_closedAnnulus hr]
  constructor <;> nlinarith

/-- `N♭_i ⊂ {|x| ≥ ar_i/2}`. -/
theorem half_le_of_mem_Nflatk (hS : S.Holds) {i : ℕ} {x : ℂ} (hx : x ∈ S.P.Nflatk i) :
    a / 2 * S.P.r i ≤ ‖x‖ := by
  have hr := r_pos hS i
  have ha := zero_lt_a
  have := (norm_of_mem_Nflatk hS hx).1
  nlinarith

/-- `N♭_i ⊂ ℝ² ∖ B_{6r_j}` for `1 ≤ i < j`: `⅝ar_i ≥ 20r_j` (`11_bootstrap.tex:151-157`). -/
theorem Nflatk_subset_compl_ball (hS : S.Holds) {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) :
    S.P.Nflatk i ⊆ (ball (0 : ℂ) (6 * S.P.r j))ᶜ := by
  intro x hx hxb
  rw [mem_ball_zero_iff] at hxb
  have h1 := (norm_of_mem_Nflatk hS hx).1
  have h2 := r_le_of_lt hS hi hij
  have hr := r_pos hS i
  have ha := zero_lt_a
  nlinarith

/-- `D_k(t) = S_k(t) ∪ D_{k+1}(t)` for `k ≤ n`. -/
theorem D_eq_union {k : ℕ} (hk : k ≤ S.P.n) (t : ℝ) :
    S.P.D k t = S.P.St k t ∪ S.P.D (k + 1) t := by
  ext x
  simp only [Approx.D, Set.mem_iUnion, Set.mem_union, Finset.mem_Icc, exists_prop]
  constructor
  · rintro ⟨i, ⟨hi1, hi2⟩, hx⟩
    rcases Nat.eq_or_lt_of_le hi1 with h | h
    · subst h; exact Or.inl hx
    · exact Or.inr ⟨i, ⟨h, hi2⟩, hx⟩
  · rintro (hx | ⟨i, ⟨hi1, hi2⟩, hx⟩)
    · exact ⟨k, ⟨le_rfl, hk⟩, hx⟩
    · exact ⟨i, ⟨by omega, hi2⟩, hx⟩

/-! ### The clock -/

/-- `σ_i ≥ σ_b > 0` for every level `i ∈ [1, n]` (`standing_levels`). -/
theorem sigma_pos (hS : S.Holds) {i : ℕ} (hi : i ∈ Finset.Icc 1 S.P.n) : 0 < S.P.sigma i := by
  obtain ⟨hb, -, -, hlev⟩ := standing_levels S hS
  exact lt_of_lt_of_le hb (hlev i hi).2.2

/-- `t♯_i ≤ T_i` when `T_i` is defined. -/
theorem tsh_le_T (hS : S.Holds) {i : ℕ} (hi : i ∈ Finset.Icc 1 S.P.n) (hc : S.P.ClockUpTo i) :
    S.P.tsh i ≤ S.P.T i := by
  have hin := (Finset.mem_Icc.1 hi).2
  have hκ := hc.ksh_mem le_rfl hin
  have hσ := sigma_pos hS hi
  have h1 : 1 ≤ S.P.δ₀ / S.P.ksh i := by
    rw [le_div_iff₀ hκ.1]
    linarith [hκ.2]
  have hT : 0 ≤ S.P.That i := mul_nonneg (inv_nonneg.2 hσ.le) (Real.log_nonneg h1)
  rw [S.P.T_of_ne (by omega)]
  have := div_nonneg hT (A_pos hS i).le
  linarith

/-- A ring that is quiet at `t'` is not debris at `t'`. -/
theorem not_debris_of_quiet (hS : S.Holds) {j : ℕ} (hj : j ∈ Finset.Icc 1 S.P.n) {t' : ℝ}
    (hq : S.P.QuietAt j t') : ¬ S.P.DebrisAt j t' := by
  rintro ⟨hc, hT⟩
  rcases hq with hq | hq
  · exact hq (hc.mono (Nat.le_succ j))
  · have := tsh_le_T hS hj hc
    linarith

/-- `t♯_j ≤ e_j`. -/
theorem tsh_le_endW (hS : S.Holds) {j : ℕ} (hj : j ∈ Finset.Icc 1 S.P.n) :
    S.P.tsh j ≤ S.P.endW j := by
  by_cases hc : S.P.ClockUpTo j
  · rw [Approx.endW_of_clockUpTo hc]
    exact tsh_le_T hS hj hc
  · rw [Approx.endW_of_not_clockUpTo hc]

/-- `T_{j+1} ≤ t♯_j` for `j < n` (`t♯_j = T_{j+1} + T_pin/A_{j+1}`). -/
theorem T_succ_le_tsh (hS : S.Holds) {j : ℕ} (hjn : j < S.P.n) : S.P.T (j + 1) ≤ S.P.tsh j := by
  rw [S.P.tsh_eq_T_add hjn]
  have := div_pos hS.Tpin_pos (A_pos hS (j + 1))
  linarith

/-- `A_{j+1}(t - T_{j+1}) ≤ T_pin` for `t ≤ t♯_j`, `j < n`. -/
theorem kickTime_le_Tpin (hS : S.Holds) {j : ℕ} (hjn : j < S.P.n) {t : ℝ}
    (ht : t ≤ S.P.tsh j) : S.P.kickTime j t ≤ S.P.Tpin := by
  have hA := A_pos hS (j + 1)
  rw [S.P.tsh_eq_T_add hjn] at ht
  have h1 : t - S.P.T (j + 1) ≤ S.P.Tpin / S.P.A (j + 1) := by linarith
  have h2 := mul_le_mul_of_nonneg_left h1 hA.le
  rw [mul_div_cancel₀ _ hA.ne'] at h2
  exact h2

/-- `T_{j+1} ≥ 0` when the clock is defined up to level `j+1 ≤ n` (`lem:clock`(1)). -/
theorem T_succ_nonneg (hS : S.Holds) {j : ℕ} (hjn : j < S.P.n) (hc : S.P.ClockUpTo (j + 1)) :
    0 ≤ S.P.T (j + 1) := by
  have hmem : j + 1 ∈ Finset.Icc (j + 1) S.P.n := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
  have h0 := (Approx.clock_order S.P hS.valid hS.hN (gsmall hS) (by omega) hc).2.2.2 (j + 1) hmem
  have h1 := tsh_le_T hS (Finset.mem_Icc.2 ⟨by omega, by omega⟩) hc
  linarith

/-- `T_j ≤ T_i` for `1 ≤ i ≤ j ≤ n` when `T_i` is defined (`lem:clock`(1)). -/
theorem T_le_T (hS : S.Holds) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) (hjn : j ≤ S.P.n)
    (hc : S.P.ClockUpTo i) : S.P.T j ≤ S.P.T i := by
  rcases Nat.eq_or_lt_of_le hij with h | h
  · subst h; exact le_rfl
  · have h1 := (Approx.clock_order S.P hS.valid hS.hN (gsmall hS) hi hc).2.2.1 i j le_rfl h hjn
    have h2 := tsh_le_T hS (Finset.mem_Icc.2 ⟨hi, by omega⟩) hc
    linarith

/-- The rings `i ≤ j` are not debris at a time `t' ≤ e_j` (`11_bootstrap.tex:172-175`). -/
theorem not_debris_of_le_endW (hS : S.Holds) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j)
    (hjn : j ≤ S.P.n) {t' : ℝ} (ht' : t' ≤ S.P.endW j) : ¬ S.P.DebrisAt i t' := by
  rintro ⟨hc, hT⟩
  have hcj : S.P.ClockUpTo j := hc.mono hij
  rw [Approx.endW_of_clockUpTo hcj] at ht'
  have := T_le_T hS hi hij hjn hc
  linarith

/-- A ring `j` (with `t♯_j` defined) that is not debris at `t' ≤ T_end` has `t' ≤ e_j`
(`11_bootstrap.tex:194-197`). -/
theorem le_endW_of_not_debris {j : ℕ} (hj : j ∈ Finset.Icc 1 S.P.n)
    (hc : S.P.ClockUpTo (j + 1)) {t' : ℝ} (hTend : t' ≤ S.P.Tend) (hd : ¬ S.P.DebrisAt j t') :
    t' ≤ S.P.endW j := by
  by_cases hcj : S.P.ClockUpTo j
  · rw [Approx.endW_of_clockUpTo hcj]
    by_contra hlt
    exact hd ⟨hcj, lt_of_not_ge hlt⟩
  · have hstop : S.P.StopsAt j := ⟨(Finset.mem_Icc.1 hj).1, (Finset.mem_Icc.1 hj).2, hc, hcj⟩
    rw [Approx.endW_of_not_clockUpTo hcj, ← hstop.Tend_eq]
    exact hTend

end GeometryH

end Relay

end NonUniqueEuler
