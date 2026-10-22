import NonUniqueEuler.H.Sec11.Geometry.Window
import NonUniqueEuler.I.Sec7.Confine

/-!
# Helper for `P/Sec11/Geometry.lean`: the downward induction

Helper of the proof of `lem:geometry` (`11_bootstrap.tex:159-200`): the downward induction on the
level `j = n, n-1, …, 1`, which proves `D_{j+1}(t') ⊂ B_{ar_j/8}` at every `t' ∈ [0, t]` at which
ring `j` is not debris, and, for `j < n`, conclusion (a) for `k = j`.
* `window_step`: (a) for `k = j` from the claim for `j + 1` (hypotheses (i)–(iv) of
  `prop:confine`, `Rings.confine`, and `ϱ_j ≤ Λr_{j+1} < Λ^conf_j s_j r_j ≤ ar_j/8`);
* `inner_step`: the claim on `D_{j+1}` from the claim for `j + 1` and (a) for `k = j`;
* `inner_all`: the induction.
All proved.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

namespace GeometryH

open RingData Datum

variable {S : Standing}

/-- `r_{j+1} = s_j r_j` for `j ≥ 1`. -/
theorem r_succ {j : ℕ} (hj : 1 ≤ j) : S.P.r (j + 1) = S.P.s j * S.P.r j :=
  radius_succ _ _ hj

/-- **(a) for `k = j`** (`11_bootstrap.tex:166-191`), from the claim of the induction for `j + 1`:
the hypotheses of `prop:confine` with `t₀ = T_{j+1}`, `t₁ = min(t, e_j)`, and its conclusions,
with `\bar B_{ϱ_j(t')} ⊂ B_{ar_j/8}`. -/
theorem window_step (hS : S.Holds) (hL : S.ParamLists) {t : ℝ} (h : S.GeometryHyp t) {j : ℕ}
    (hj1 : 1 ≤ j) (hjn : j < S.P.n)
    (hIH : ∀ t' ∈ Icc (0 : ℝ) t, ¬ S.P.DebrisAt (j + 1) t' → S.P.HInDefined (j + 1) t')
    (hc : S.P.ClockUpTo (j + 1)) (hTt : S.P.T (j + 1) ≤ t) : S.GeometryWindow j t := by
  have hjmem : j ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.2 ⟨hj1, hjn.le⟩
  have hj1mem : j + 1 ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.2 ⟨by omega, hjn⟩
  have hT0 : 0 ≤ S.P.T (j + 1) := T_succ_nonneg hS hjn hc
  have hTe : S.P.T (j + 1) ≤ S.P.endW j := (T_succ_le_tsh hS hjn).trans (tsh_le_endW hS hjmem)
  have hTt₁ : S.P.T (j + 1) ≤ min t (S.P.endW j) := le_min hTt hTe
  have hΛ := confLambda_lt hS hL h hj1 hjn hc hTt₁ (min_le_right _ _) (min_le_left _ _)
  have hΛ0 := confLambda_nonneg hS hTt₁
  have hs := s_pos hS j
  have hr1 := r_pos hS (j + 1)
  have ha := zero_lt_a
  have ha1 := a_lt_one
  have hb5 := hL.sbar.b5 j hj1
  have hnd : ¬ S.P.DebrisAt (j + 1) (S.P.T (j + 1)) := fun hd => lt_irrefl _ hd.2
  have hT0t : S.P.T (j + 1) ∈ Icc (0 : ℝ) t := ⟨hT0, hTt⟩
  have hCH : S.P.ConfineHyp j (min t (S.P.endW j)) :=
    { one_le := hj1
      lt_n := hjn
      clock := hc
      le_t₁ := hTt₁
      init := by
        intro x hx
        rw [D_eq_union hjn (S.P.T (j + 1))] at hx
        rw [mem_closedBall_zero_iff]
        rcases hx with hx | hx
        · have := (norm_of_mem_Nflatk hS (h.ba1 _ hT0t (j + 1) hj1mem hnd hx)).2
          linarith
        · have h1 := mem_ball_zero_iff.1 (hIH _ hT0t hnd hx)
          have h2 : a * S.P.r (j + 1) / 8 ≤ 2 * S.P.r (j + 1) := by nlinarith
          linarith
      cl := by
        intro t'' ht'' i hi x hx
        have hi' := Finset.mem_Icc.1 hi
        have ht''t : t'' ∈ Icc (0 : ℝ) t := ⟨hT0.trans ht''.1, ht''.2.trans (min_le_left _ _)⟩
        have hnd' := not_debris_of_le_endW hS hi'.1 hi'.2 hjn.le (ht''.2.trans (min_le_right _ _))
        exact half_le_of_mem_Nflatk hS
          (h.ba1 t'' ht''t i (Finset.mem_Icc.2 ⟨hi'.1, by omega⟩) hnd' hx)
      sbar_le := hS.sbar_le
      sbar_pow_le := hS.sbar_pow_le
      mu_sbar_le := hS.mu_sbar_le
      lambda_le := (mul_le_mul_of_nonneg_right hΛ.le hs.le).trans hb5.1
      lambda_pow_le := by
        refine le_trans ?_ hb5.2
        have hpow : S.P.confLambda j (min t (S.P.endW j)) ^ (3 - 1) ≤ S.Lconf j ^ (3 - 1) :=
          pow_le_pow_left₀ hΛ0 hΛ.le _
        have h2a : 0 < 2 / a := div_pos two_pos ha
        have hc0 : 0 ≤ 8 / 3 * (2 / a) ^ 3 := by positivity
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hc0)
          (pow_nonneg hs.le _) }
  refine ⟨hCH, fun t' ht' => ?_⟩
  have hcc := Rings.confine S.P hS.valid hS.hN (gsmall hS) hCH t' ht'
  refine ⟨hcc.supp, closedBall_subset_ball ?_, hcc.q_le⟩
  have hk := kickTime_mono hS j ht'.2
  have hC := Cstar_pos
  have hrj := r_pos hS j
  have hle : S.P.confRadius j t' ≤ S.P.confLambda j (min t (S.P.endW j)) * S.P.r (j + 1) := by
    simp only [Approx.confRadius, Approx.confLambda]
    have : 2 * Cstar * S.P.kickTime j t' ≤ 2 * Cstar * S.P.kickTime j (min t (S.P.endW j)) :=
      mul_le_mul_of_nonneg_left hk (by positivity)
    exact mul_le_mul_of_nonneg_right (by linarith) hr1.le
  calc S.P.confRadius j t' ≤ S.P.confLambda j (min t (S.P.endW j)) * S.P.r (j + 1) := hle
    _ < S.Lconf j * S.P.r (j + 1) := mul_lt_mul_of_pos_right hΛ hr1
    _ = S.Lconf j * S.P.s j * S.P.r j := by rw [r_succ hj1]; ring
    _ ≤ a / 8 * S.P.r j := mul_le_mul_of_nonneg_right hb5.1 hrj.le
    _ = a * S.P.r j / 8 := by ring

/-- **The claim on `D_{j+1}`** (`11_bootstrap.tex:192-200`), from the claim for `j + 1` and (a) for
`k = j`: `D_{j+1}(t') ⊂ B_{ar_j/8}` at every `t' ∈ [0, t]` at which ring `j` is not debris. -/
theorem inner_step (hS : S.Holds) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) S.P.Tend)
    (h : S.GeometryHyp t) {j : ℕ} (hj1 : 1 ≤ j) (hjn : j < S.P.n)
    (hIH : ∀ t' ∈ Icc (0 : ℝ) t, ¬ S.P.DebrisAt (j + 1) t' → S.P.HInDefined (j + 1) t')
    (hW : S.P.ClockUpTo (j + 1) → S.P.T (j + 1) ≤ t → S.GeometryWindow j t) :
    ∀ t' ∈ Icc (0 : ℝ) t, ¬ S.P.DebrisAt j t' → S.P.HInDefined j t' := by
  intro t' ht' hd x hx
  have hjmem : j ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.2 ⟨hj1, hjn.le⟩
  have hj1mem : j + 1 ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.2 ⟨by omega, hjn⟩
  by_cases hd1 : S.P.DebrisAt (j + 1) t'
  · obtain ⟨hc, hT⟩ := hd1
    have he : t' ≤ S.P.endW j := le_endW_of_not_debris hjmem hc (ht'.2.trans ht.2) hd
    have hW' := (hW hc (hT.le.trans ht'.2)).2 t' ⟨hT.le, le_min ht'.2 he⟩
    exact hW'.2.1 (hW'.1 hx)
  · rw [mem_ball_zero_iff]
    have hr := r_pos hS j
    have hr1 : S.P.r (j + 1) ≤ a / 32 * S.P.r j := r_le_of_lt hS hj1 (Nat.lt_succ_self j)
    have ha := zero_lt_a
    have ha1 := a_lt_one
    have har : 0 < a * S.P.r j := mul_pos ha hr
    rw [D_eq_union hjn t'] at hx
    rcases hx with hx | hx
    · have h1 := (norm_of_mem_Nflatk hS (h.ba1 t' ht' (j + 1) hj1mem hd1 hx)).2
      nlinarith
    · have h1 := mem_ball_zero_iff.1 (hIH t' ht' hd1 hx)
      have hr1' : S.P.r (j + 1) ≤ S.P.r j := by nlinarith
      have h2 : a * S.P.r (j + 1) ≤ a * S.P.r j := mul_le_mul_of_nonneg_left hr1' ha.le
      linarith

/-- **The downward induction** (`11_bootstrap.tex:159-200`): for every level `j ∈ [1, n]`,
`D_{j+1}(t') ⊂ B_{ar_j/8}` at every `t' ∈ [0, t]` at which ring `j` is not debris, and, if `j < n`,
(a) holds for `k = j`. Stated with `j + m = n`, by induction on `m`. -/
theorem inner_all (hS : S.Holds) (hL : S.ParamLists) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) S.P.Tend)
    (h : S.GeometryHyp t) : ∀ m j : ℕ, j + m = S.P.n → 1 ≤ j →
      (∀ t' ∈ Icc (0 : ℝ) t, ¬ S.P.DebrisAt j t' → S.P.HInDefined j t') ∧
      (j < S.P.n → S.P.ClockUpTo (j + 1) → S.P.T (j + 1) ≤ t → S.GeometryWindow j t) := by
  intro m
  induction m with
  | zero =>
    intro j hj _
    rw [Nat.add_zero] at hj
    subst hj
    refine ⟨fun t' _ _ => ?_, fun h' => absurd h' (lt_irrefl _)⟩
    intro x hx
    simp [Approx.D_succ_n] at hx
  | succ m ih =>
    intro j hj hj1
    have hjn : j < S.P.n := by omega
    have hIH := (ih (j + 1) (by omega) (by omega)).1
    have hW : S.P.ClockUpTo (j + 1) → S.P.T (j + 1) ≤ t → S.GeometryWindow j t :=
      fun hc hT => window_step hS hL h hj1 hjn hIH hc hT
    exact ⟨inner_step hS ht h hj1 hjn hIH hW, fun _ => hW⟩

/-- The claim of the induction for every level `j ∈ [1, n]`. -/
theorem inner_of_mem (hS : S.Holds) (hL : S.ParamLists) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) S.P.Tend)
    (h : S.GeometryHyp t) {j : ℕ} (hj : j ∈ Finset.Icc 1 S.P.n) :
    (∀ t' ∈ Icc (0 : ℝ) t, ¬ S.P.DebrisAt j t' → S.P.HInDefined j t') ∧
      (j < S.P.n → S.P.ClockUpTo (j + 1) → S.P.T (j + 1) ≤ t → S.GeometryWindow j t) := by
  have hj' := Finset.mem_Icc.1 hj
  exact inner_all hS hL ht h (S.P.n - j) j (by omega) hj'.1

end GeometryH

end Relay

end NonUniqueEuler
