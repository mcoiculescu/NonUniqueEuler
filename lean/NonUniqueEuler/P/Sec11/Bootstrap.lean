import NonUniqueEuler.Defs.Sec11.Extra2Boot
import NonUniqueEuler.I.Sec11.BootStart
import NonUniqueEuler.I.Sec11.BootContinuity
import NonUniqueEuler.I.Sec11.BootSteps
import NonUniqueEuler.I.Sec11.Stop
import NonUniqueEuler.I.Sec6.Clock
import NonUniqueEuler.I.Sec7.Confine
import NonUniqueEuler.I.Sec9.Standing
import NonUniqueEuler.I.Sec9.Time

/-!
# Proof: `prop:bootstrap` (the joint bootstrap)

Proof of `I/Sec11/Bootstrap.lean` (`11_bootstrap.tex:94-113`, proof `:220-605`): same
declarations, same statements. The assembly of the step interfaces (restructuring R10):
* Step 0 (`boot_start`), Step 7 (`boot_continuity`: (BA°)(t) on `[0, T_end]`), and Steps 1–6
  (`boot_steps`) at `t = T_end` (`T_end ≥ 0`: `phase_intervals`).
* "The clock does not stop" (`:592-596`): otherwise it stops at `k_s` (`stopsAt_stopLevel`),
  `k_s < n` by Step 0 (`StopsAt.clockUpTo_iff`), `T_end = t♯_{k_s}` (`StopsAt.Tend_eq`), and Step 3
  at `k_s` (`HandoffStep.clock`) gives the clock up to level `k_s`, a contradiction.
* The items (`:597-605`): `t♯_k < T_k` (`clock_order`) and `Ph_k ⊂ [0, T_end]`
  (`phase_intervals`) give `t♯_k, T_k ≤ T_end = T_1`; (1) Step 3 and Step 0; (2) Step 6; (3) Step 3
  and Step 4 at `t' = T_k` (active time `A_k(T_k - t♯_k) = T̂_k`, `activeTime_T`); (4)
  `lem:geometry`(a) at `T_1` with `e_k = T_k ≤ T_1` and `prop:confine` (`Rings.confine`); (5)
  `lem:time`.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

open RingData Datum

/-- The active time of `T_k` is `T̂_k`: `A_k(T_k - t♯_k) = T̂_k` for `k ≠ n + 1`
(`06_datum.tex:408`, `:417`). -/
private theorem activeTime_T {P : Approx} (hP : P.Valid) {k : ℕ} (hk : k ≠ P.n + 1) :
    P.activeTime k (P.T k) = P.That k := by
  have hA : P.A k ≠ 0 := (hP.A_pos k).ne'
  rw [Approx.activeTime, Approx.T_of_ne P hk, add_sub_cancel_left]
  field_simp

/-- **`prop:bootstrap`** (`11_bootstrap.tex:94-113`), at the standing level: under (N) and
(P0)–(P6) (with `A₁ > 0`, `n ≥ 2` and `ω = ω^{(n)}`, all contained in `S.Holds`), the conclusions
(1)–(5) hold (`S.BootConcl`). -/
theorem bootstrap (S : Standing) (hS : S.Holds) (hL : S.ParamLists) : S.BootConcl := by
  -- Step 0, Step 7 and Steps 1–6 at `T_end`.
  have h0 : S.BootStartConcl := boot_start S hS hL
  have hPI := phase_intervals S hS
  have hTend0 : 0 ≤ S.P.Tend := hPI.1
  have hsteps : S.BootStepsConcl S.P.Tend :=
    boot_steps S hS hL ⟨hTend0, le_rfl⟩ h0 (boot_continuity S hS hL _ ⟨hTend0, le_rfl⟩)
  -- The clock does not stop (`11_bootstrap.tex:592-596`).
  have hclock : S.P.ClockUpTo 1 := by
    by_contra hc
    have hst : S.P.StopsAt S.P.stopLevel := Approx.stopsAt_stopLevel hc
    have hlt : S.P.stopLevel < S.P.n := (hst.clockUpTo_iff S.P.n).1 h0.clock_n
    have hmem : S.P.stopLevel ∈ Finset.Ico 1 S.P.n := Finset.mem_Ico.2 ⟨hst.1, hlt⟩
    have hstep := hsteps.handoff S.P.stopLevel hmem hst.2.2.1 hst.Tend_eq.ge
    exact hst.2.2.2 hstep.clock
  have hTend : S.P.Tend = S.P.T 1 := Approx.Tend_of_clockUpTo hclock
  have hG : S.P.GSmall := (standing_levels S hS).2.2.1
  have hord := Approx.clock_order S.P hS.valid hS.hN hG le_rfl hclock
  have hck : ∀ k ∈ Finset.Icc 1 S.P.n, S.P.ClockUpTo k := fun k hk =>
    hclock.mono (Finset.mem_Icc.1 hk).1
  -- `Ph_k ⊂ [0, T_end]` with `t♯_k < T_k`: `t♯_k ≤ T_1` and `T_k ≤ T_1`.
  have hPh : ∀ k ∈ Finset.Icc 1 S.P.n, S.P.tsh k ∈ Icc 0 S.P.Tend ∧ S.P.T k ∈ Icc 0 S.P.Tend :=
    fun k hk => ⟨hPI.2.1 k hk (hck k hk) ⟨le_rfl, (hord.1 k hk).le⟩,
      hPI.2.1 k hk (hck k hk) ⟨(hord.1 k hk).le, le_rfl⟩⟩
  have hsucc : ∀ k ∈ Finset.Ico 1 S.P.n, k + 1 ∈ Finset.Icc 1 S.P.n := fun k hk => by
    have := Finset.mem_Ico.1 hk
    exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hIco : ∀ k ∈ Finset.Ico 1 S.P.n, k ∈ Finset.Icc 1 S.P.n := fun k hk => by
    have := Finset.mem_Ico.1 hk
    exact Finset.mem_Icc.2 ⟨this.1, this.2.le⟩
  rw [hTend] at hsteps hPh
  -- Step 3 at every level `k < n`.
  have hhand : ∀ k ∈ Finset.Ico 1 S.P.n, S.HandoffStep k := fun k hk =>
    hsteps.handoff k hk (hck (k + 1) (hsucc k hk)) (hPh k (hIco k hk)).1.2
  -- Step 4 at `t' = T_k`, i.e. at the active time `T̂_k`.
  have hact : ∀ k ∈ Finset.Icc 1 S.P.n, S.ActiveStep k (S.P.That k) := by
    intro k hk
    have hkne : k ≠ S.P.n + 1 := by
      have := Finset.mem_Icc.1 hk
      omega
    have h := hsteps.active k hk (hck k hk) (S.P.T k) ⟨(hord.1 k hk).le, le_rfl⟩ (hord.1 k hk)
      (hPh k hk).2.2
    rwa [activeTime_T hS.valid hkne] at h
  have hamp : ∀ k ∈ Finset.Ico 1 S.P.n,
      S.Klo * S.P.s k ^ (3 + 2) ≤ S.P.ksh k ∧ S.P.ksh k ≤ S.Kup * S.P.s k ^ (3 + 2) :=
    fun k hk => ⟨(hhand k hk).amp_lo, (hhand k hk).amp_up⟩
  refine
    { clock := hclock
      amp := hamp
      amp_n := h0.ksh_n
      ba_star := hsteps.ba_star
      handoff := fun k hk => (hhand k hk).handoff
      active := fun k hk u hu => (hact k hk).concl u hu
      coef := fun k hk => (hact k hk).coef rfl
      confine := ?_
      time := time S hS hL.det hclock (fun k hk => (hamp k hk).1) h0.ksh_n.1 }
  -- Item (4): `lem:geometry`(a) at `T_1` with `e_k = T_k`, and `prop:confine`.
  intro k hk
  have hck1 : S.P.ClockUpTo (k + 1) := hck (k + 1) (hsucc k hk)
  have hW := hsteps.geom.window k hk hck1 (hPh (k + 1) (hsucc k hk)).2.2
  have hmin : min (S.P.T 1) (S.P.endW k) = S.P.T k := by
    rw [Approx.endW_of_clockUpTo (hck k (hIco k hk))]
    exact min_eq_right (hPh k (hIco k hk)).2.2
  unfold Standing.GeometryWindow at hW
  rw [hmin] at hW
  refine ⟨hW.1, fun t ht => ⟨Rings.confine S.P hS.valid hS.hN hG hW.1 t ht, ?_⟩⟩
  exact (hW.2 t ht).1.trans (hW.2 t ht).2.1

/-- **`prop:bootstrap`** (`11_bootstrap.tex:94-113`), at the parameter level: assume (N1)–(N3) and
(P0)–(P6) for the parameters `p`. Then for every `A₁ > 0` and every `n ≥ 2`, the conclusions
(1)–(5) hold for the standing datum `p.standing A₁ n` (`ω = ω^{(n)}`). -/
theorem bootstrap_params (p : Params) (hχ : IsAdmissibleCutoff p.χ)
    (hN : NumericalHypothesis p.χ) (hL : p.Lists) {A₁ : ℝ} (hA₁ : 0 < A₁) {n : ℕ} (hn : 2 ≤ n) :
    (p.standing A₁ n).BootConcl :=
  bootstrap (p.standing A₁ n) (hL.holds hχ hN hA₁ hn) (hL.standing A₁ n)

end Relay

end NonUniqueEuler
