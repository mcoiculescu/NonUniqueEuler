import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Topology.Order.OrderClosed
import NonUniqueEuler.Defs.Sec11.Extra2Boot
import NonUniqueEuler.I.Sec6.Clock
import NonUniqueEuler.I.Sec9.Standing
import NonUniqueEuler.I.Sec10.ConstantsPos

/-!
# Helpers for `P/Sec11/BootContinuity`: generic facts and facts on the phases

Helper file of the proof of Step 7 of `prop:bootstrap` (`11_bootstrap.tex:540-591`).

* generic real-analysis facts: an eventual property on `𝓝[>] t` holds on some `(t, t + δ]`
  (`exists_delta_of_eventually`); a function continuous from the left at `t` and `≤ c` on `[a, t)`
  is `≤ c` at `t` (`le_of_forall_Ico`); an `ε`-family of upper bounds (`le_of_forall_eps`);
* the phases (`11_bootstrap.tex:57-69`, `lem:clock`(1)): `quietAt_anti`, `not_debris_of_quiet`,
  `tsh_nonneg_of_clock`, `tsh_nonneg_of_succ`;
* constants: `sigma_gt` (`σ' < σ_k`), `one_le_C2'` (`C₂ ≥ 1`), `isClosed_Nflatk`;
* continuity of the active time and of the envelope `â_k` along it.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace Relay

namespace BootContinuityH

open RingData Datum

/-! ### Generic real-analysis facts -/

/-- An eventual property on `𝓝[>] t` holds on some interval `(t, t + δ]`. -/
theorem exists_delta_of_eventually {t : ℝ} {p : ℝ → Prop} (h : ∀ᶠ s in 𝓝[>] t, p s) :
    ∃ δ > 0, ∀ s ∈ Ioc t (t + δ), p s := by
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 h
  refine ⟨u - t, sub_pos.2 hu, fun s hs => hsub ?_⟩
  have he : t + (u - t) = u := by ring
  rw [he] at hs
  exact hs

/-- A function continuous at `t` from the left, bounded by `c` on `[a, t)`, is bounded by `c`
at `t`. -/
theorem le_of_forall_Ico {f : ℝ → ℝ} {a t c : ℝ} (hat : a < t)
    (hf : ContinuousWithinAt f (Ico a t) t) (h : ∀ s ∈ Ico a t, f s ≤ c) : f t ≤ c := by
  have : (𝓝[Ico a t] t).NeBot := by
    rw [nhdsWithin_Ico_eq_nhdsLT hat]
    infer_instance
  exact le_of_tendsto hf (eventually_nhdsWithin_of_forall h)

/-- If `x ≤ X + c ε` for every `ε > 0`, with `c ≥ 0`, then `x ≤ X`. -/
theorem le_of_forall_eps {x X c : ℝ} (hc : 0 ≤ c) (h : ∀ ε : ℝ, 0 < ε → x ≤ X + c * ε) :
    x ≤ X := by
  refine le_of_forall_pos_le_add fun ε' hε' => ?_
  have hpos : 0 < c + 1 := by linarith
  have h1 := h (ε' / (c + 1)) (div_pos hε' hpos)
  have h2 : c * (ε' / (c + 1)) ≤ ε' := by
    rw [mul_div_assoc', div_le_iff₀ hpos]
    nlinarith
  linarith

/-! ### Phases -/

variable (S : Standing)

/-- `G_k ≤ G₁` for every level (`standing_levels`). -/
theorem gsmall (hS : S.Holds) : S.P.GSmall := (standing_levels S hS).2.2.1

/-- A ring quiet at `s` is quiet at every earlier time. -/
theorem quietAt_anti {j : ℕ} {s s' : ℝ} (h : S.P.QuietAt j s) (hs : s' ≤ s) :
    S.P.QuietAt j s' :=
  h.imp id (fun h' => hs.trans h')

/-- `0 ≤ t♯_k` when the clock is defined up to level `k ≥ 1` (`lem:clock`(1)). -/
theorem tsh_nonneg_of_clock (hS : S.Holds) {k : ℕ} (hk : 1 ≤ k) (hc : S.P.ClockUpTo k) :
    0 ≤ S.P.tsh k := by
  by_cases hkn : k ≤ S.P.n
  · exact (S.P.clock_order hS.valid hS.hN (gsmall S hS) hk hc).2.2.2 k
      (Finset.mem_Icc.2 ⟨le_rfl, hkn⟩)
  · have h0 : S.P.n - k = 0 := by omega
    simp [Datum.Approx.tsh, h0]

/-- `t♯_k < T_k` when the clock is defined up to level `k ∈ [1, n]` (`lem:clock`(1)). -/
theorem tsh_lt_T (hS : S.Holds) {k : ℕ} (hk : k ∈ Finset.Icc 1 S.P.n) (hc : S.P.ClockUpTo k) :
    S.P.tsh k < S.P.T k :=
  (S.P.clock_order hS.valid hS.hN (gsmall S hS) (Finset.mem_Icc.1 hk).1 hc).1 k
    (Finset.mem_Icc.2 ⟨le_rfl, (Finset.mem_Icc.1 hk).2⟩)

/-- `0 ≤ t♯_k` when `t♯_k` is defined (the clock is defined up to level `k + 1`), `k ∈ [1, n]`
(`lem:clock`(1): `0 ≤ t♯_{k+1} < T_{k+1} < t♯_k`; `t♯_n = 0`). -/
theorem tsh_nonneg_of_succ (hS : S.Holds) {k : ℕ} (hk : k ∈ Finset.Icc 1 S.P.n)
    (hc : S.P.ClockUpTo (k + 1)) : 0 ≤ S.P.tsh k := by
  obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.1 hk
  rcases lt_or_eq_of_le hkn with hlt | heq
  · have hord := S.P.clock_order hS.valid hS.hN (gsmall S hS) (by omega : 1 ≤ k + 1) hc
    have hmem : k + 1 ∈ Finset.Icc (k + 1) S.P.n := Finset.mem_Icc.2 ⟨le_rfl, hlt⟩
    have h1 := hord.2.1 (k + 1) hmem (by omega)
    have h2 := hord.1 (k + 1) hmem
    have h3 := hord.2.2.2 (k + 1) hmem
    simp only [Nat.add_sub_cancel] at h1
    linarith
  · rw [heq, S.P.tsh_n]

/-- A ring that is quiet at `s` is not debris at `s` (`lem:clock`(1): `t♯_j < T_j`). -/
theorem not_debris_of_quiet (hS : S.Holds) {j : ℕ} (hj : j ∈ Finset.Icc 1 S.P.n) {s : ℝ}
    (hq : S.P.QuietAt j s) : ¬ S.P.DebrisAt j s := by
  rintro ⟨hc, hT⟩
  have hc1 : S.P.ClockUpTo (j + 1) := hc.mono (Nat.le_succ j)
  have hs : s ≤ S.P.tsh j := hq.resolve_left (not_not.2 hc1)
  have := tsh_lt_T S hS hj hc
  linarith

/-! ### Constants -/

/-- `σ' < σ_k` for every level `k ∈ [1, n]` (`σ' < σ_b ≤ σ_k`, (SA1), `standing_levels`). -/
theorem sigma_gt (hS : S.Holds) {k : ℕ} (hk : k ∈ Finset.Icc 1 S.P.n) : S.σ' < S.P.sigma k :=
  lt_of_lt_of_le hS.σ'_lt_sigb ((standing_levels S hS).2.2.2 k hk).2.2

/-- `C₂ ≥ 1` (`constants_pos`). -/
theorem one_le_C2' (hS : S.Holds) : 1 ≤ S.C2 :=
  (constants_pos S hS.valid.admissible hS.hN hS.σ'_gt hS.σ'_lt_sigma hS.δ₀_pos hS.one_lt_μ
    hS.Tpin_pos).one_le_C2

/-- `N♭_j` is closed. -/
theorem isClosed_Nflatk (j : ℕ) : IsClosed (S.P.Nflatk j) :=
  (Sect.isClosed_closedAnnulus _ _).preimage (continuous_const.mul continuous_id)

/-! ### The active time and the envelope -/

theorem continuous_activeTime (k : ℕ) : Continuous (S.P.activeTime k) :=
  continuous_const.mul (continuous_id.sub continuous_const)

theorem activeTime_le_activeTime (hS : S.Holds) (k : ℕ) {s s' : ℝ} (h : s ≤ s') :
    S.P.activeTime k s ≤ S.P.activeTime k s' :=
  mul_le_mul_of_nonneg_left (sub_le_sub_right h _) (hS.valid.A_pos k).le

theorem activeTime_lt_activeTime (hS : S.Holds) (k : ℕ) {s s' : ℝ} (h : s < s') :
    S.P.activeTime k s < S.P.activeTime k s' :=
  mul_lt_mul_of_pos_left (sub_lt_sub_right h _) (hS.valid.A_pos k)

theorem activeTime_nonneg (hS : S.Holds) (k : ℕ) {s : ℝ} (h : S.P.tsh k ≤ s) :
    0 ≤ S.P.activeTime k s :=
  mul_nonneg (hS.valid.A_pos k).le (sub_nonneg.2 h)

/-- `s ↦ 2C₂ â_k(A_k(s - t♯_k))` is continuous. -/
theorem continuous_envelope (k : ℕ) :
    Continuous (fun s => 2 * S.C2 * S.ahatK k (S.P.activeTime k s)) := by
  have h : Continuous (fun u => S.ahatK k u) := by
    simp only [Standing.ahatK_def]
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  exact continuous_const.mul (h.comp (continuous_activeTime S k))

/-- `2C₂ â_k ≥ 0`. -/
theorem envelope_nonneg (hS : S.Holds) (k : ℕ) (s : ℝ) :
    0 ≤ 2 * S.C2 * S.ahatK k (S.P.activeTime k s) :=
  mul_nonneg (by linarith [one_le_C2' S hS]) (S.ahatK_nonneg k _)

/-- `ρ̂_k` is `OneRing.rhoHatOf σ_k σ' C₀`. -/
theorem rhoHatK_eq (C₀ : ℝ) (k : ℕ) (u : ℝ) :
    S.rhoHatK C₀ k u = OneRing.rhoHatOf (S.P.sigma k) S.σ' C₀ u := rfl

end BootContinuityH

end Relay

end NonUniqueEuler
