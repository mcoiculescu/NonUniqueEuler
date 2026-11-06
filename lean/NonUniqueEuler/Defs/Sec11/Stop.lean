import NonUniqueEuler.Defs.Sec6.Clock

/-!
# The stopping time of the clock (legacy `Sec11` definitions)

Current sources: Part II Definition 6.1 (`def:stop`) and the following phase conventions
in §6 (`manuscript/part2/sections/09_relay.tex`), and the endpoint `e_k` in Lemma C.17
(`lem:geometry`, Appendix C.14, `C_bootstrap_details.tex`).

* `P.StopsAt k`: the clock stops at level `k ∈ [1, n]`; it is defined up to `k+1` but not `k`.
  At `k = n`, `clockUpTo_succ_n` supplies the first condition.
* `P.stopLevel`: the chosen stopping level `k_s`, with junk value `0` if the clock reaches `1`.
* `P.Tend`: `T_end = T₁` if the clock reaches `1`, and `t♯_{k_s}` otherwise.
* `P.endW k`: `e_k = T_k` if `T_k` is defined, and `t♯_k` otherwise.

`P.QuietAt`, `P.ActiveAt` and `P.DebrisAt` are defined in `Defs/Sec6/Clock.lean` and implement
Definition 4.4 (`def:loc`). The lemmas prove the existence and uniqueness of a stopping level
when the clock does not reach `1`, and `P.ClockUpTo j ↔ k_s < j` when it stops at `k_s`.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Datum

namespace Approx

variable (P : Approx)

/-- **The clock stops at level `k`** (Part II Definition 6.1, `def:stop`): `k ∈ {1, …, n}`, the
clock is defined up to level `k+1` but not up to level `k` (for `k = n` the first condition is
void: `P.ClockUpTo (P.n + 1)` holds, `clockUpTo_succ_n`). -/
def StopsAt (k : ℕ) : Prop := 1 ≤ k ∧ k ≤ P.n ∧ P.ClockUpTo (k + 1) ∧ ¬ P.ClockUpTo k

open Classical in
/-- **The stopping level `k_s`** (Part II Definition 6.1, `def:stop`): the unique `k` with
`P.StopsAt k` (`StopsAt.unique`; it exists iff the clock is not defined up to level `1`,
`exists_stopsAt`); junk `0` otherwise. -/
def stopLevel : ℕ := if h : ∃ k, P.StopsAt k then h.choose else 0

open Classical in
/-- **The stopping time `T_end`** (Part II Definition 6.1, `def:stop`): `T_end = T₁` if the clock
is defined up to level `1`, and `T_end = t♯_{k_s}` otherwise. -/
def Tend : ℝ := if P.ClockUpTo 1 then P.T 1 else P.tsh P.stopLevel

open Classical in
/-- **The end `e_k` of the confinement window** (Part II Lemma C.17, `lem:geometry`), for a
level `k < n` with `T_{k+1}` defined: `e_k = T_k` if `T_k` is defined (the clock is defined up to
level `k`), and `e_k = t♯_k` otherwise. -/
def endW (k : ℕ) : ℝ := if P.ClockUpTo k then P.T k else P.tsh k

/-! ### Basic lemmas (fully proved) -/

variable {P}

/-- If the clock stops at level `k`, it is defined up to level `j` exactly for `j > k`
(Part II Definition 6.1 (`def:stop`) and the phase conventions in §6). -/
theorem StopsAt.clockUpTo_iff {k : ℕ} (h : P.StopsAt k) (j : ℕ) : P.ClockUpTo j ↔ k < j := by
  constructor
  · intro hj
    by_contra hkj
    exact h.2.2.2 (ClockUpTo.mono hj (by omega))
  · intro hkj
    exact ClockUpTo.mono h.2.2.1 (by omega)

/-- The stopping level is unique (Part II Definition 6.1 (`def:stop`) and the phase conventions in §6). -/
theorem StopsAt.unique {k k' : ℕ} (h : P.StopsAt k) (h' : P.StopsAt k') : k = k' := by
  have h1 := (h.clockUpTo_iff (k' + 1)).1 h'.2.2.1
  have h2 := (h'.clockUpTo_iff (k + 1)).1 h.2.2.1
  omega

theorem StopsAt.not_clockUpTo_one {k : ℕ} (h : P.StopsAt k) : ¬ P.ClockUpTo 1 := by
  rw [h.clockUpTo_iff 1]
  have := h.1
  omega

/-- If the clock is not defined up to level `1`, it stops at some level
(Part II Definition 6.1 (`def:stop`) and the phase conventions in §6). -/
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

/-- If the clock stops at level `n`, then `T_end = 0` (Part II Definition 6.1 (`def:stop`) and the
phase conventions in §6). -/
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
