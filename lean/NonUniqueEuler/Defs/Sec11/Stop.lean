import NonUniqueEuler.Defs.Sec6.Clock

/-!
# Section 11: the stopping time of the clock (definitions)

Manuscript `def:stop`
(`11_bootstrap.tex:32-39`), the remarks after it (`:41-69`) and the end of the window `e_k` of
`lem:geometry` (`:125-126`).

* `P.StopsAt k`: the clock **stops at level `k`**: `k ∈ [1, n]`, the clock is defined up to level
  `k+1` but not up to level `k` (for `k = n` the first condition is void, `clockUpTo_succ_n`);
* `P.stopLevel`: the level `k_s` (chosen; junk `0` when the clock is defined up to level `1`);
* `P.Tend`: `T_end = T₁` if the clock is defined up to level `1`, else `t♯_{k_s}`;
* `P.endW k`: `e_k = T_k` if `T_k` is defined (clock up to level `k`), else `t♯_k`.

The phases at a time `t ∈ [0, T_end]` (quiet, active, debris) are `P.QuietAt`, `P.ActiveAt`,
`P.DebrisAt` of `Defs/Sec6/Clock.lean` (the conventions of `def:loc`, `11_bootstrap.tex:61-69`).
All lemmas here are fully proved: uniqueness of the stopping level, its existence when the clock is
not defined up to level `1` (`11_bootstrap.tex:41-45`), and `P.ClockUpTo j ↔ k_s < j`.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Datum

namespace Approx

variable (P : Approx)

/-- **The clock stops at level `k`** (`def:stop`, `11_bootstrap.tex:34-38`): `k ∈ {1, …, n}`, the
clock is defined up to level `k+1` but not up to level `k` (for `k = n` the first condition is
void: `P.ClockUpTo (P.n + 1)` holds, `clockUpTo_succ_n`). -/
def StopsAt (k : ℕ) : Prop := 1 ≤ k ∧ k ≤ P.n ∧ P.ClockUpTo (k + 1) ∧ ¬ P.ClockUpTo k

open Classical in
/-- **The stopping level `k_s`** (`def:stop`, `11_bootstrap.tex:35-38`): the unique `k` with
`P.StopsAt k` (`StopsAt.unique`; it exists iff the clock is not defined up to level `1`,
`exists_stopsAt`); junk `0` otherwise. -/
def stopLevel : ℕ := if h : ∃ k, P.StopsAt k then h.choose else 0

open Classical in
/-- **The stopping time `T_end`** (`def:stop`, `11_bootstrap.tex:34-38`): `T_end = T₁` if the clock
is defined up to level `1`, and `T_end = t♯_{k_s}` otherwise. -/
def Tend : ℝ := if P.ClockUpTo 1 then P.T 1 else P.tsh P.stopLevel

open Classical in
/-- **The end `e_k` of the confinement window** (`lem:geometry`, `11_bootstrap.tex:125-126`), for a
level `k < n` with `T_{k+1}` defined: `e_k = T_k` if `T_k` is defined (the clock is defined up to
level `k`), and `e_k = t♯_k` otherwise. -/
def endW (k : ℕ) : ℝ := if P.ClockUpTo k then P.T k else P.tsh k

/-! ### Basic lemmas (fully proved) -/

variable {P}

/-- If the clock stops at level `k`, it is defined up to level `j` exactly for `j > k`
(`11_bootstrap.tex:41-45`). -/
theorem StopsAt.clockUpTo_iff {k : ℕ} (h : P.StopsAt k) (j : ℕ) : P.ClockUpTo j ↔ k < j := by
  constructor
  · intro hj
    by_contra hkj
    exact h.2.2.2 (ClockUpTo.mono hj (by omega))
  · intro hkj
    exact ClockUpTo.mono h.2.2.1 (by omega)

/-- The stopping level is unique (`11_bootstrap.tex:41-45`). -/
theorem StopsAt.unique {k k' : ℕ} (h : P.StopsAt k) (h' : P.StopsAt k') : k = k' := by
  have h1 := (h.clockUpTo_iff (k' + 1)).1 h'.2.2.1
  have h2 := (h'.clockUpTo_iff (k + 1)).1 h.2.2.1
  omega

theorem StopsAt.not_clockUpTo_one {k : ℕ} (h : P.StopsAt k) : ¬ P.ClockUpTo 1 := by
  rw [h.clockUpTo_iff 1]
  have := h.1
  omega

/-- If the clock is not defined up to level `1`, it stops at some level
(`11_bootstrap.tex:41-45`). -/
theorem exists_stopsAt (h : ¬ P.ClockUpTo 1) : ∃ k, P.StopsAt k := by
  classical
  have hex : ∃ j, P.ClockUpTo (j + 1) := ⟨P.n, P.clockUpTo_succ_n⟩
  set j₀ := Nat.find hex with hj₀
  have hspec : P.ClockUpTo (j₀ + 1) := Nat.find_spec hex
  have hle : j₀ ≤ P.n := Nat.find_min' hex P.clockUpTo_succ_n
  have hpos : 1 ≤ j₀ := by
    by_contra h0
    have : j₀ = 0 := by omega
    rw [this] at hspec
    exact h hspec
  refine ⟨j₀, hpos, hle, hspec, ?_⟩
  have hmin := Nat.find_min hex (show j₀ - 1 < j₀ by omega)
  rwa [show j₀ - 1 + 1 = j₀ by omega] at hmin

theorem stopsAt_stopLevel (h : ¬ P.ClockUpTo 1) : P.StopsAt P.stopLevel := by
  classical
  have hex := exists_stopsAt h
  rw [stopLevel, dite_eq_left hex]
  exact hex.choose_spec

theorem StopsAt.stopLevel_eq {k : ℕ} (h : P.StopsAt k) : P.stopLevel = k :=
  (stopsAt_stopLevel h.not_clockUpTo_one).unique h

theorem Tend_of_clockUpTo (h : P.ClockUpTo 1) : P.Tend = P.T 1 := by
  classical
  simp [Tend, h]

theorem Tend_of_not_clockUpTo (h : ¬ P.ClockUpTo 1) : P.Tend = P.tsh P.stopLevel := by
  classical
  simp [Tend, h]

/-- If the clock stops at level `k`, then `T_end = t♯_k` (`def:stop`). -/
theorem StopsAt.Tend_eq {k : ℕ} (h : P.StopsAt k) : P.Tend = P.tsh k := by
  rw [Tend_of_not_clockUpTo h.not_clockUpTo_one, h.stopLevel_eq]

/-- If the clock stops at level `n`, then `T_end = 0` (`11_bootstrap.tex:58`). -/
theorem StopsAt.Tend_eq_zero (h : P.StopsAt P.n) : P.Tend = 0 := by
  rw [h.Tend_eq, tsh_n]

theorem endW_of_clockUpTo {k : ℕ} (h : P.ClockUpTo k) : P.endW k = P.T k := by
  classical
  simp [endW, h]

theorem endW_of_not_clockUpTo {k : ℕ} (h : ¬ P.ClockUpTo k) : P.endW k = P.tsh k := by
  classical
  simp [endW, h]

end Approx

end Datum

end NonUniqueEuler
