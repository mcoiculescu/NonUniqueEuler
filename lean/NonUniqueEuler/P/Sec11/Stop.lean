import NonUniqueEuler.Defs.Sec11.All
import NonUniqueEuler.I.Sec6.Clock
import NonUniqueEuler.I.Sec9.Standing

/-!
# Proof: the remarks after `def:stop` (phase intervals and phases up to `T_end`)

Proof of `I/Sec11/Stop.lean` (`11_bootstrap.tex:32-69`). Same declarations, statements copied
verbatim.

* `stopsAt_not_cond`, `phase_trichotomy`: purely definitional (no ordering of the clock needed).
* `quiet_of_lt`, `phase_intervals` (first three parts): the ordering of the clock,
  `lem:clock`(1) (`Datum.Approx.clock_order`, `I/Sec6/Clock.lean`), with `P.GSmall` from
  `standing_levels` (`I/Sec9/Standing.lean`).
* the covering part of `phase_intervals`: downward induction on the level `m`, showing
  `[0, T_m] ⊆ Ph_n ∪ Pin_{n-1} ∪ … ∪ Ph_m` (consecutive intervals share endpoints, `t♯_n = 0`);
  no ordering is needed for it.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

open RingData Datum

/-! ### Helpers on the order of the clock -/

section Helpers

variable {P : Datum.Approx}

/-- From `lem:clock`(1) with base level `k`: `t♯_i < T_i` and `0 ≤ t♯_i` for `i ∈ [k, n]`. -/
private theorem tsh_lt_T_of (hP : P.Valid) (hN : NumericalHypothesis P.χ) (hG : P.GSmall)
    {k i : ℕ} (hk : 1 ≤ k) (hc : P.ClockUpTo k) (hki : k ≤ i) (hin : i ≤ P.n) :
    P.tsh i < P.T i ∧ 0 ≤ P.tsh i := by
  obtain ⟨h1, -, -, h4⟩ := Datum.Approx.clock_order P hP hN hG hk hc
  have hmem : i ∈ Finset.Icc k P.n := Finset.mem_Icc.2 ⟨hki, hin⟩
  exact ⟨h1 i hmem, h4 i hmem⟩

/-- If `t♯_i` is defined (`P.ClockUpTo (i+1)`), `1 ≤ i < j ≤ n`, then `T_j < t♯_i`. -/
private theorem T_lt_tsh_of (hP : P.Valid) (hN : NumericalHypothesis P.χ) (hG : P.GSmall)
    {i j : ℕ} (hi : 1 ≤ i) (hc : P.ClockUpTo (i + 1)) (hij : i < j) (hjn : j ≤ P.n) :
    P.T j < P.tsh i := by
  obtain ⟨h1, h2, h3, -⟩ := Datum.Approx.clock_order P hP hN hG (by omega : 1 ≤ i + 1) hc
  have hmem : i + 1 ∈ Finset.Icc (i + 1) P.n := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
  have hT : P.T (i + 1) < P.tsh i := by
    simpa using h2 (i + 1) hmem (by omega)
  rcases Nat.lt_or_ge (i + 1) j with hlt | hge
  · have ha : P.T j < P.tsh (i + 1) := h3 (i + 1) j le_rfl hlt hjn
    have hb : P.tsh (i + 1) < P.T (i + 1) := h1 (i + 1) hmem
    linarith
  · have hj : j = i + 1 := by omega
    rw [hj]
    exact hT

/-- If `T_i` is defined (`P.ClockUpTo i`), `1 ≤ i ≤ j ≤ n`, then `T_j ≤ T_i`. -/
private theorem T_le_T_of (hP : P.Valid) (hN : NumericalHypothesis P.χ) (hG : P.GSmall)
    {i j : ℕ} (hi : 1 ≤ i) (hc : P.ClockUpTo i) (hij : i ≤ j) (hjn : j ≤ P.n) :
    P.T j ≤ P.T i := by
  rcases Nat.lt_or_ge i j with hlt | hge
  · obtain ⟨h1, -, h3, -⟩ := Datum.Approx.clock_order P hP hN hG hi hc
    have ha : P.T j < P.tsh i := h3 i j le_rfl hlt hjn
    have hb : P.tsh i < P.T i := h1 i (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩)
    linarith
  · have hj : j = i := by omega
    rw [hj]

/-- If `t♯_k` is defined (`P.ClockUpTo (k+1)`), `1 ≤ k ≤ n`, then `0 ≤ t♯_k`. -/
private theorem tsh_nonneg_of (hP : P.Valid) (hN : NumericalHypothesis P.χ) (hG : P.GSmall)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ P.n) (hc : P.ClockUpTo (k + 1)) : 0 ≤ P.tsh k := by
  rcases Nat.lt_or_ge k P.n with hlt | hge
  · have ha : P.T (k + 1) < P.tsh k := T_lt_tsh_of hP hN hG hk hc (by omega) (by omega)
    obtain ⟨hb, hc'⟩ := tsh_lt_T_of hP hN hG (by omega : 1 ≤ k + 1) hc le_rfl (by omega)
    linarith
  · have hkn' : k = P.n := by omega
    rw [hkn', Datum.Approx.tsh_n]

/-- **The covering of `[0, T_m]`**: if the clock is defined up to level `m ∈ [1, n]`, every
`t ∈ [0, T_m]` lies in some `Ph_k` with `T_k` defined or some `Pin_k` with `t♯_k` defined, `k < n`.
Downward induction on `m` (here on `d = n - m`); no ordering of the clock is needed. -/
private theorem cover_of_clockUpTo (d : ℕ) :
    ∀ m : ℕ, m + d = P.n → 1 ≤ m → P.ClockUpTo m → ∀ t ∈ Icc (0 : ℝ) (P.T m),
      ∃ k ∈ Finset.Icc 1 P.n, (P.ClockUpTo k ∧ t ∈ P.Phase k) ∨
        (k < P.n ∧ P.ClockUpTo (k + 1) ∧ t ∈ P.Pin k) := by
  induction d with
  | zero =>
    intro m hm h1 hc t ht
    have hmn : m = P.n := by omega
    rw [hmn] at h1 hc ht
    refine ⟨P.n, Finset.mem_Icc.2 ⟨h1, le_rfl⟩, Or.inl ⟨hc, ?_⟩⟩
    rw [Datum.Approx.Phase, Datum.Approx.tsh_n]
    exact ht
  | succ d ih =>
    intro m hm h1 hc t ht
    have hc' : P.ClockUpTo (m + 1) := Datum.Approx.ClockUpTo.mono hc (Nat.le_succ m)
    have hmn : m < P.n := by omega
    rcases le_or_gt t (P.T (m + 1)) with h₁ | h₁
    · exact ih (m + 1) (by omega) (by omega) hc' t ⟨ht.1, h₁⟩
    · rcases le_or_gt t (P.tsh m) with h₂ | h₂
      · exact ⟨m, Finset.mem_Icc.2 ⟨h1, hmn.le⟩, Or.inr ⟨hmn, hc', h₁.le, h₂⟩⟩
      · exact ⟨m, Finset.mem_Icc.2 ⟨h1, hmn.le⟩, Or.inl ⟨hc, h₂.le, ht.2⟩⟩

end Helpers

/-- **The phase intervals up to `T_end`** (`11_bootstrap.tex:49-56`): `T_end ≥ 0`; `Ph_k ⊂ [0, T_end]`
whenever `T_k` is defined; `Pin_k ⊂ [0, T_end]` whenever `t♯_k` is defined (`k < n`); and, if the
clock is defined up to level `n` (i.e. it does not stop at level `n`), every `t ∈ [0, T_end]` lies in
some `Ph_k` with `T_k` defined or some `Pin_k` with `t♯_k` defined. -/
theorem phase_intervals (S : Standing) (hS : S.Holds) :
    0 ≤ S.P.Tend ∧
    (∀ k ∈ Finset.Icc 1 S.P.n, S.P.ClockUpTo k → S.P.Phase k ⊆ Icc 0 S.P.Tend) ∧
    (∀ k ∈ Finset.Ico 1 S.P.n, S.P.ClockUpTo (k + 1) → S.P.Pin k ⊆ Icc 0 S.P.Tend) ∧
    (S.P.ClockUpTo S.P.n → ∀ t ∈ Icc (0 : ℝ) S.P.Tend, ∃ k ∈ Finset.Icc 1 S.P.n,
      (S.P.ClockUpTo k ∧ t ∈ S.P.Phase k) ∨
        (k < S.P.n ∧ S.P.ClockUpTo (k + 1) ∧ t ∈ S.P.Pin k)) := by
  obtain ⟨-, -, hG, -⟩ := standing_levels S hS
  have hP := hS.valid
  have hN := hS.hN
  have hn2 := hS.two_le_n
  by_cases h1 : S.P.ClockUpTo 1
  · -- the clock is defined up to level `1`: `T_end = T₁`
    have hTend : S.P.Tend = S.P.T 1 := Datum.Approx.Tend_of_clockUpTo h1
    have h0 : 0 < S.P.T 1 := by
      obtain ⟨ha, hb⟩ := tsh_lt_T_of hP hN hG le_rfl h1 le_rfl (by omega)
      linarith
    refine ⟨by rw [hTend]; exact h0.le, ?_, ?_, ?_⟩
    · intro k hk hck
      rw [Finset.mem_Icc] at hk
      obtain ⟨-, hb⟩ := tsh_lt_T_of hP hN hG hk.1 hck le_rfl hk.2
      rw [hTend, Datum.Approx.Phase]
      exact Icc_subset_Icc hb (T_le_T_of hP hN hG le_rfl h1 hk.1 hk.2)
    · intro k hk hck
      rw [Finset.mem_Ico] at hk
      obtain ⟨ha, hb⟩ := tsh_lt_T_of hP hN hG (by omega : 1 ≤ k + 1) hck le_rfl (by omega)
      have hck' : S.P.ClockUpTo k := Datum.Approx.ClockUpTo.mono h1 hk.1
      obtain ⟨hc, -⟩ := tsh_lt_T_of hP hN hG hk.1 hck' le_rfl hk.2.le
      have hd : S.P.T k ≤ S.P.T 1 := T_le_T_of hP hN hG le_rfl h1 hk.1 hk.2.le
      rw [hTend, Datum.Approx.Pin]
      exact Icc_subset_Icc (by linarith) (by linarith)
    · intro _ t ht
      rw [hTend] at ht
      exact cover_of_clockUpTo (S.P.n - 1) 1 (by omega) le_rfl h1 t ht
  · -- the clock stops at level `k_s`: `T_end = t♯_{k_s}`
    have hst := Datum.Approx.stopsAt_stopLevel h1
    have hTend : S.P.Tend = S.P.tsh S.P.stopLevel := hst.Tend_eq
    have hiff := hst.clockUpTo_iff
    obtain ⟨hks1, hksn, hcks, -⟩ := hst
    have h0 : 0 ≤ S.P.tsh S.P.stopLevel := tsh_nonneg_of hP hN hG hks1 hksn hcks
    refine ⟨by rw [hTend]; exact h0, ?_, ?_, ?_⟩
    · intro k hk hck
      rw [Finset.mem_Icc] at hk
      have hlt : S.P.stopLevel < k := (hiff k).1 hck
      obtain ⟨-, hb⟩ := tsh_lt_T_of hP hN hG hk.1 hck le_rfl hk.2
      rw [hTend, Datum.Approx.Phase]
      exact Icc_subset_Icc hb (T_lt_tsh_of hP hN hG hks1 hcks hlt hk.2).le
    · intro k hk hck
      rw [Finset.mem_Ico] at hk
      have hle : S.P.stopLevel < k + 1 := (hiff (k + 1)).1 hck
      obtain ⟨ha, hb⟩ := tsh_lt_T_of hP hN hG (by omega : 1 ≤ k + 1) hck le_rfl (by omega)
      rw [hTend, Datum.Approx.Pin]
      refine Icc_subset_Icc (by linarith) ?_
      rcases Nat.lt_or_ge S.P.stopLevel k with hlt | hge
      · have hck' : S.P.ClockUpTo k := (hiff k).2 hlt
        obtain ⟨hc, -⟩ := tsh_lt_T_of hP hN hG hk.1 hck' le_rfl hk.2.le
        exact (hc.trans (T_lt_tsh_of hP hN hG hks1 hcks hlt hk.2.le)).le
      · have hk' : k = S.P.stopLevel := by omega
        rw [hk']
    · intro hcn t ht
      have hlt : S.P.stopLevel < S.P.n := (hiff S.P.n).1 hcn
      rw [hTend] at ht
      rcases le_or_gt t (S.P.T (S.P.stopLevel + 1)) with h₁ | h₁
      · exact cover_of_clockUpTo (S.P.n - (S.P.stopLevel + 1)) (S.P.stopLevel + 1) (by omega)
          (by omega) hcks t ⟨ht.1, h₁⟩
      · exact ⟨S.P.stopLevel, Finset.mem_Icc.2 ⟨hks1, hksn⟩, Or.inr ⟨hlt, hcks, h₁.le, ht.2⟩⟩

/-- **The clock stops for a reason** (`11_bootstrap.tex:47-48`): if the clock stops at level `k`,
then `S_k(t♯_k) ⊄ N_k` or `κ♯_k ∉ (0, δ₀)`. -/
theorem stopsAt_not_cond (S : Standing) {k : ℕ} (h : S.P.StopsAt k) :
    ¬ (S.P.St k (S.P.tsh k) ⊆ S.P.Nk k ∧ S.P.ksh k ∈ Ioo (0 : ℝ) S.P.δ₀) := by
  rintro ⟨hSt, hk⟩
  obtain ⟨-, -, hc, hnc⟩ := h
  apply hnc
  intro i hi
  rw [Finset.mem_Icc] at hi
  rcases Nat.lt_or_ge k i with hlt | hge
  · exact hc i (Finset.mem_Icc.2 ⟨hlt, hi.2⟩)
  · have hik : i = k := by omega
    subst hik
    exact ⟨hSt, hk⟩

/-- **Every ring has a phase at every `t ≤ T_end`** (`11_bootstrap.tex:61-66`): ring `j ∈ [1, n]` is
quiet, active or debris at `t` (conventions of `def:loc`). -/
theorem phase_trichotomy (S : Standing) {t : ℝ} (ht : t ≤ S.P.Tend) {j : ℕ}
    (hj : j ∈ Finset.Icc 1 S.P.n) :
    S.P.QuietAt j t ∨ S.P.ActiveAt j t ∨ S.P.DebrisAt j t := by
  rw [Finset.mem_Icc] at hj
  by_cases hcj : S.P.ClockUpTo j
  · rcases le_or_gt t (S.P.tsh j) with h₁ | h₁
    · exact Or.inl (Or.inr h₁)
    · rcases le_or_gt t (S.P.T j) with h₂ | h₂
      · exact Or.inr (Or.inl ⟨hcj, h₁.le, h₂⟩)
      · exact Or.inr (Or.inr ⟨hcj, h₂⟩)
  · by_cases hcj1 : S.P.ClockUpTo (j + 1)
    · -- the clock stops at level `j`, so `t ≤ T_end = t♯_j`
      have hst : S.P.StopsAt j := ⟨hj.1, hj.2, hcj1, hcj⟩
      refine Or.inl (Or.inr ?_)
      rw [← hst.Tend_eq]
      exact ht
    · exact Or.inl (Or.inl hcj1)

/-- **Rings outside a quiet or active ring are quiet** (`11_bootstrap.tex:67-69`, by `lem:clock`(1)):
if ring `j ∈ [1, n]` is quiet or active at `t`, then every ring `i ∈ [1, j)` is quiet at `t`. -/
theorem quiet_of_lt (S : Standing) (hS : S.Holds) {t : ℝ} {j : ℕ} (hj : j ∈ Finset.Icc 1 S.P.n)
    (h : S.P.QuietAt j t ∨ S.P.ActiveAt j t) : ∀ i ∈ Finset.Ico 1 j, S.P.QuietAt i t := by
  obtain ⟨-, -, hG, -⟩ := standing_levels S hS
  have hP := hS.valid
  have hN := hS.hN
  rw [Finset.mem_Icc] at hj
  intro i hi
  rw [Finset.mem_Ico] at hi
  by_cases hci : S.P.ClockUpTo (i + 1)
  · refine Or.inr ?_
    have hcj : S.P.ClockUpTo j := Datum.Approx.ClockUpTo.mono hci (by omega)
    have hT : S.P.T j < S.P.tsh i := T_lt_tsh_of hP hN hG hi.1 hci hi.2 hj.2
    obtain ⟨ha, -⟩ := tsh_lt_T_of hP hN hG hj.1 hcj le_rfl hj.2
    rcases h with h | h
    · rcases h with h | h
      · exact absurd (Datum.Approx.ClockUpTo.mono hcj (Nat.le_succ j)) h
      · linarith
    · linarith [h.2.2]
  · exact Or.inl hci

end Relay

end NonUniqueEuler
