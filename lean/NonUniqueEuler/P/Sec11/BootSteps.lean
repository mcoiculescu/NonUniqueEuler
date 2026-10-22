import NonUniqueEuler.Defs.Sec11.Extra2Boot
import NonUniqueEuler.I.Sec4.Annuli
import NonUniqueEuler.I.Sec6.Clock
import NonUniqueEuler.I.Sec9.Standing
import NonUniqueEuler.I.Sec11.Stop
import NonUniqueEuler.I.Sec11.BA
import NonUniqueEuler.I.Sec11.Geometry
import NonUniqueEuler.I.Sec11.BootQuiet
import NonUniqueEuler.I.Sec11.BootHandoff
import NonUniqueEuler.I.Sec11.BootActive
import NonUniqueEuler.I.Sec11.BootQuietSize

/-!
# Proof: Steps 1–6 of the proof of `prop:bootstrap` ((BA°)(t) implies (BA)(t) and (BA*)(t))

Proof of `I/Sec11/BootSteps.lean` (`11_bootstrap.tex:221-224`, `:251-260`, `:532-538`).

The manuscript treats the phase intervals of `[0, t]` in chronological order. The only conclusion
that a later step needs from an earlier *level* is the hand-off (Step 3): Step 1 (`lem:geometry`) at
a time `τ` needs `κ♯_k ≥ K_lo s_k^{m+2}` at the levels with `t♯_k < τ`, and Steps 2, 4 at a time
`τ` need nothing else from earlier levels (`boot_quiet`, `boot_active` take Steps 1, 2 at `τ` and
Step 3 at the levels with `t♯_i < τ`). So the chronological order is formalized as follows.
* `BootStepsH.geom_of`, `quiet_of`, `active_of`: Steps 1, 2, 4 at (or up to) a time `τ ≤ t`, given
  Step 3 at every level `k` with `t♯_k < τ`.
* `BootStepsH.handoff_of`: Step 3 at the level `k`, given Step 3 at the levels `i` with
  `t♯_i < t♯_k`; it uses Steps 1, 2 on `[0, t♯_k]` and Step 4 for ring `k+1` at `T_{k+1} < t♯_k`.
* `BootStepsH.handoff_all`: Step 3 at every level `k` with `t♯_k ≤ t`, by downward induction on the
  level (`t♯_i < t♯_k` forces `i > k`, `lem:clock`(1)).
* `BootStepsH.bastar_of`: Step 6 ((BA*)(t)), from Steps 0, 2, 3, 4, 5.
The main theorem `boot_steps` assembles these with Step 5 (`boot_quiet_size`) and
(BA*)(t) ⇒ (BA)(t) (`BA_of_BAstar`).
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

open RingData Datum

namespace BootStepsH

variable {S : Standing}

/-! ### The order of the activation times (`lem:clock`(1)) -/

/-- `t♯_b < t♯_a` for levels `1 ≤ a < b ≤ n` when the clock is defined up to level `a + 1`
(`lem:clock`(1): `t♯_b < T_b < t♯_{a+1} < T_{a+1} < t♯_a`). -/
theorem tsh_lt_tsh (hS : S.Holds) {a b : ℕ} (ha : 1 ≤ a) (hc : S.P.ClockUpTo (a + 1))
    (hab : a < b) (hbn : b ≤ S.P.n) : S.P.tsh b < S.P.tsh a := by
  obtain ⟨_, _, hG, _⟩ := standing_levels S hS
  obtain ⟨h1, h2, h3, _⟩ :=
    Approx.clock_order S.P hS.valid hS.hN hG (by omega : 1 ≤ a + 1) hc
  have hb1 : S.P.tsh b < S.P.T b := h1 b (Finset.mem_Icc.2 ⟨by omega, hbn⟩)
  have ha1 : S.P.T (a + 1) < S.P.tsh a := by
    have := h2 (a + 1) (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩) (by omega)
    simpa using this
  rcases Nat.lt_or_ge (a + 1) b with hlt | hge
  · have hb2 : S.P.T b < S.P.tsh (a + 1) := h3 (a + 1) b le_rfl hlt hbn
    have hb3 : S.P.tsh (a + 1) < S.P.T (a + 1) :=
      h1 (a + 1) (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩)
    linarith
  · have hb : b = a + 1 := by omega
    subst hb
    linarith

/-- `t♯_i ≤ t♯_k` for levels `1 ≤ k ≤ i ≤ n` when the clock is defined up to level `k`. -/
theorem tsh_le_tsh (hS : S.Holds) {k i : ℕ} (hk : 1 ≤ k) (hc : S.P.ClockUpTo k) (hki : k ≤ i)
    (hin : i ≤ S.P.n) : S.P.tsh i ≤ S.P.tsh k := by
  rcases hki.lt_or_eq with h | h
  · exact (tsh_lt_tsh hS hk (hc.mono (by omega)) h hin).le
  · rw [h]

/-- If `t♯_i < t♯_k` (both defined), then `k < i`. -/
theorem lt_of_tsh_lt (hS : S.Holds) {k i : ℕ} (hkn : k ≤ S.P.n) (hi : 1 ≤ i)
    (hci : S.P.ClockUpTo (i + 1)) (hlt : S.P.tsh i < S.P.tsh k) : k < i := by
  by_contra hki
  rcases (not_lt.1 hki).lt_or_eq with h | h
  · exact lt_asymm hlt (tsh_lt_tsh hS hi hci h hkn)
  · subst h
    exact lt_irrefl _ hlt

/-- `0 ≤ t♯_k` when the clock is defined up to level `k ≥ 1`. -/
theorem tsh_nonneg (hS : S.Holds) {k : ℕ} (hk : 1 ≤ k) (hc : S.P.ClockUpTo k)
    (hkn : k ≤ S.P.n) : 0 ≤ S.P.tsh k := by
  obtain ⟨_, _, hG, _⟩ := standing_levels S hS
  exact (Approx.clock_order S.P hS.valid hS.hN hG hk hc).2.2.2 k
    (Finset.mem_Icc.2 ⟨le_rfl, hkn⟩)

/-- `0 ≤ t♯_k` for a level `k < n` with `t♯_k` defined. -/
theorem tsh_nonneg' (hS : S.Holds) {k : ℕ} (hk : k ∈ Finset.Ico 1 S.P.n)
    (hc : S.P.ClockUpTo (k + 1)) : 0 ≤ S.P.tsh k := by
  have hk' := Finset.mem_Ico.1 hk
  have h := tsh_lt_tsh hS hk'.1 hc hk'.2 le_rfl
  rw [Approx.tsh_n] at h
  exact h.le

/-- `t♯_k < T_k` when the clock is defined up to level `k ≥ 1`. -/
theorem tsh_lt_T (hS : S.Holds) {k : ℕ} (hk : 1 ≤ k) (hc : S.P.ClockUpTo k)
    (hkn : k ≤ S.P.n) : S.P.tsh k < S.P.T k := by
  obtain ⟨_, _, hG, _⟩ := standing_levels S hS
  exact (Approx.clock_order S.P hS.valid hS.hN hG hk hc).1 k (Finset.mem_Icc.2 ⟨le_rfl, hkn⟩)

/-- `T_{k+1} < t♯_k` for a level `k < n` with `t♯_k` defined. -/
theorem T_succ_lt_tsh (hS : S.Holds) {k : ℕ} (hk : k ∈ Finset.Ico 1 S.P.n)
    (hc : S.P.ClockUpTo (k + 1)) : S.P.T (k + 1) < S.P.tsh k := by
  have hk' := Finset.mem_Ico.1 hk
  obtain ⟨_, _, hG, _⟩ := standing_levels S hS
  have := (Approx.clock_order S.P hS.valid hS.hN hG (by omega : 1 ≤ k + 1) hc).2.1 (k + 1)
    (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩) (by omega)
  simpa using this

/-- `A_k(T_k - t♯_k) = T̂_k` for a level `k ≤ n`. -/
theorem activeTime_T (hS : S.Holds) {k : ℕ} (hkn : k ≤ S.P.n) :
    S.P.activeTime k (S.P.T k) = S.P.That k := by
  have hA : S.P.A k ≠ 0 := (hS.valid.A_pos k).ne'
  rw [Approx.activeTime, Approx.T_of_ne S.P (by omega : k ≠ S.P.n + 1)]
  field_simp
  ring

/-- `t♯_k + A_k(t' - t♯_k)/A_k = t'`. -/
theorem tsh_add_activeTime (hS : S.Holds) (k : ℕ) (t' : ℝ) :
    S.P.tsh k + S.P.activeTime k t' / S.P.A k = t' := by
  have hA : S.P.A k ≠ 0 := (hS.valid.A_pos k).ne'
  rw [Approx.activeTime, mul_div_cancel_left₀ _ hA]
  ring

theorem activeTime_nonneg (hS : S.Holds) {k : ℕ} {t' : ℝ} (h : S.P.tsh k ≤ t') :
    0 ≤ S.P.activeTime k t' := by
  rw [Approx.activeTime]
  exact mul_nonneg (hS.valid.A_pos k).le (by linarith)

/-- `𝒩₋_j ⊂ 𝒩_j` (`lem:annuli`). -/
theorem Nmk_subset_Nnk (j : ℕ) : S.P.Nmk j ⊆ S.P.Nnk j := fun _ hx =>
  Datum.mem_scaleSet.2 (annuli_chain.2.1 (Datum.mem_scaleSet.1 hx))

/-! ### Steps 1, 2, 4 at a time `τ`, given the hand-offs before `τ` -/

/-- **Step 1 at `τ`**: `lem:geometry` with `τ`, given (BA°)(τ) and Step 3 at the levels `k` with
`t♯_k < τ` (which gives `κ♯_k ≥ K_lo s_k^{m+2}`). -/
theorem geom_of (hS : S.Holds) (hL : S.ParamLists) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) S.P.Tend)
    (hBA : S.BAcirc τ)
    (hH : ∀ k ∈ Finset.Ico 1 S.P.n, S.P.ClockUpTo (k + 1) → S.P.tsh k < τ → S.HandoffStep k) :
    S.GeometryConcl τ :=
  geometry S hS hL hτ ⟨hBA.ba1, fun k hk hc hlt => (hH k hk hc hlt).amp_lo⟩

/-- **Step 2 on `[0, τ]`**, given (BA°)(τ) and Step 3 at the levels `k` with `t♯_k < τ`. -/
theorem quiet_of (hS : S.Holds) (hL : S.ParamLists) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) S.P.Tend)
    (h0 : S.BootStartConcl) (hBA : S.BAcirc τ)
    (hH : ∀ k ∈ Finset.Ico 1 S.P.n, S.P.ClockUpTo (k + 1) → S.P.tsh k < τ → S.HandoffStep k) :
    ∀ t' ∈ Icc (0 : ℝ) τ, S.QuietStepAt t' := by
  intro t' ht'
  have hle : t' ≤ τ := ht'.2
  have ht'T : t' ∈ Icc (0 : ℝ) S.P.Tend := ⟨ht'.1, hle.trans hτ.2⟩
  have hBA' := hBA.mono hle
  exact boot_quiet S hS hL ht'T h0 hBA'
    (geom_of hS hL ht'T hBA' fun k hk hc hlt => hH k hk hc (hlt.trans_le hle))

/-- **Step 4 for ring `k` up to `t' ∈ Ph_k`**, `t♯_k < t' ≤ T_end`, given (BA°)(t') and Step 3 at
the levels `i` with `t♯_i < t'`. -/
theorem active_of (hS : S.Holds) (hL : S.ParamLists) {k : ℕ} (hk : k ∈ Finset.Icc 1 S.P.n)
    (hc : S.P.ClockUpTo k) {t' : ℝ} (ht' : t' ∈ S.P.Phase k) (htsh : S.P.tsh k < t')
    (hTend : t' ≤ S.P.Tend) (h0 : S.BootStartConcl) (hBA : S.BAcirc t')
    (hH : ∀ i ∈ Finset.Ico 1 S.P.n, S.P.ClockUpTo (i + 1) → S.P.tsh i < t' → S.HandoffStep i) :
    S.ActiveStep k (S.P.activeTime k t') := by
  have hk' := Finset.mem_Icc.1 hk
  have h0k : 0 ≤ S.P.tsh k := tsh_nonneg hS hk'.1 hc hk'.2
  have ht'T : t' ∈ Icc (0 : ℝ) S.P.Tend := ⟨h0k.trans htsh.le, hTend⟩
  refine boot_active S hS hL hk hc ht' htsh hTend h0 hBA
    (geom_of hS hL ht'T hBA hH) (quiet_of hS hL ht'T h0 hBA hH) ?_
  intro i hi
  have hi' := Finset.mem_Ico.1 hi
  exact hH i (Finset.mem_Ico.2 ⟨by omega, hi'.2⟩) (hc.mono (by omega))
    ((tsh_le_tsh hS hk'.1 hc hi'.1 hi'.2.le).trans_lt htsh)

/-! ### Step 3 by downward induction on the level -/

/-- **Step 3 at the level `k`**, given (BA°)(t♯_k) and Step 3 at the levels `i` with `t♯_i < t♯_k`
(`11_bootstrap.tex:255-260`: Step 3 at `t♯_k` uses Steps 1, 2 on `[0, t♯_k]`, Step 4 on
`[0, T_{k+1}]` and Step 3 at the levels `i > k`). -/
theorem handoff_of (hS : S.Holds) (hL : S.ParamLists) {k : ℕ} (hk : k ∈ Finset.Ico 1 S.P.n)
    (hc : S.P.ClockUpTo (k + 1)) (hkT : S.P.tsh k ≤ S.P.Tend) (h0 : S.BootStartConcl)
    (hBA : S.BAcirc (S.P.tsh k))
    (hH : ∀ i ∈ Finset.Ico 1 S.P.n, S.P.ClockUpTo (i + 1) → S.P.tsh i < S.P.tsh k →
      S.HandoffStep i) :
    S.HandoffStep k := by
  have hk' := Finset.mem_Ico.1 hk
  have hkI : S.P.tsh k ∈ Icc (0 : ℝ) S.P.Tend := ⟨tsh_nonneg' hS hk hc, hkT⟩
  have hdeep : ∀ i ∈ Finset.Ioo k S.P.n, S.HandoffStep i := by
    intro i hi
    have hi' := Finset.mem_Ioo.1 hi
    exact hH i (Finset.mem_Ico.2 ⟨by omega, hi'.2⟩) (hc.mono (by omega))
      (tsh_lt_tsh hS hk'.1 hc hi'.1 hi'.2.le)
  have hk1 : k + 1 ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hTlt : S.P.T (k + 1) < S.P.tsh k := T_succ_lt_tsh hS hk hc
  have hshT : S.P.tsh (k + 1) < S.P.T (k + 1) := tsh_lt_T hS (by omega) hc (by omega)
  have hact := active_of hS hL hk1 hc ⟨hshT.le, le_rfl⟩ hshT (hTlt.le.trans hkT) h0
    (hBA.mono hTlt.le) (fun i hi hci hlt => hH i hi hci (hlt.trans hTlt))
  rw [activeTime_T hS (by omega)] at hact
  exact boot_handoff S hS hL hk hc hkT h0 hBA (geom_of hS hL hkI hBA hH)
    (quiet_of hS hL hkI h0 hBA hH) hdeep hact

/-- **Step 3 at every level `k < n` with `t♯_k ≤ t`**, by downward induction on the level. -/
theorem handoff_all (hS : S.Holds) (hL : S.ParamLists) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) S.P.Tend)
    (h0 : S.BootStartConcl) (hBA : S.BAcirc t) :
    ∀ k ∈ Finset.Ico 1 S.P.n, S.P.ClockUpTo (k + 1) → S.P.tsh k ≤ t → S.HandoffStep k := by
  suffices h : ∀ m : ℕ, ∀ k ∈ Finset.Ico 1 S.P.n, S.P.n - k ≤ m → S.P.ClockUpTo (k + 1) →
      S.P.tsh k ≤ t → S.HandoffStep k from
    fun k hk => h _ k hk le_rfl
  intro m
  induction m with
  | zero =>
    intro k hk hm
    have := Finset.mem_Ico.1 hk
    omega
  | succ m ih =>
    intro k hk hm hc hkt
    have hk' := Finset.mem_Ico.1 hk
    refine handoff_of hS hL hk hc (hkt.trans ht.2) h0 (hBA.mono hkt) ?_
    intro i hi hci hlt
    have hi' := Finset.mem_Ico.1 hi
    have hki : k < i := lt_of_tsh_lt hS hk'.2.le hi'.1 hci hlt
    exact ih i hi (by omega) hci (hlt.le.trans hkt)

/-! ### Step 6: (BA*)(t) -/

/-- **Step 6** (`11_bootstrap.tex:532-538`): (BA1) with `𝒩_j` from `eq:boot-quiet` (quiet rings;
ring `n` by Step 0), Step 4 and `eq:handoff` (active rings); (BA2) with `Ā` from Step 5; (BA3) with
`C₂` from Step 4, `eq:boot-switch` and `eq:boot-start`. -/
theorem bastar_of (hS : S.Holds) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) S.P.Tend)
    (h0 : S.BootStartConcl)
    (hhand : ∀ k ∈ Finset.Ico 1 S.P.n, S.P.ClockUpTo (k + 1) → S.P.tsh k ≤ t → S.HandoffStep k)
    (hquiet : ∀ t' ∈ Icc (0 : ℝ) t, S.QuietStepAt t')
    (hact : ∀ k ∈ Finset.Icc 1 S.P.n, S.P.ClockUpTo k → ∀ t' ∈ S.P.Phase k, S.P.tsh k < t' →
      t' ≤ t → S.ActiveStep k (S.P.activeTime k t'))
    (hqs : ∀ t' ∈ Icc (0 : ℝ) t, S.BA2At S.Abar t') :
    S.BAstar t := by
  refine ⟨?_, hqs, ?_⟩
  · -- (BA1) with `𝒩_j`
    intro t' ht' j hj hnd
    have hj' := Finset.mem_Icc.1 hj
    rcases phase_trichotomy S (ht'.2.trans ht.2) hj with hq | ha | hd
    · by_cases hjn : j < S.P.n
      · exact ((hquiet t' ht' j (Finset.mem_Ico.2 ⟨hj'.1, hjn⟩) hq).quiet_eq t'
          ⟨ht'.1, le_rfl⟩).1.trans (Nmk_subset_Nnk j)
      · have hjn' : j = S.P.n := by omega
        subst hjn'
        have ht0 : t' = S.P.tsh S.P.n := by
          rcases hq with hq | hq
          · exact absurd S.P.clockUpTo_succ_n hq
          · rw [Approx.tsh_n] at hq ⊢
            exact le_antisymm hq ht'.1
        rw [ht0]
        exact h0.init_n.2.trans (Nmk_subset_Nnk _)
    · rcases ha.2.1.lt_or_eq with hlt | heq
      · have hA := hact j hj ha.1 t' ⟨ha.2.1, ha.2.2⟩ hlt ht'.2
        have hu : S.P.activeTime j t' ∈ Icc (0 : ℝ) (S.P.activeTime j t') :=
          ⟨activeTime_nonneg hS ha.2.1, le_rfl⟩
        have := (hA.concl _ hu).supp
        rwa [tsh_add_activeTime hS] at this
      · rw [← heq]
        by_cases hjn : j < S.P.n
        · exact (hhand j (Finset.mem_Ico.2 ⟨hj'.1, hjn⟩) (ha.1.mono (by omega))
            (heq ▸ ht'.2)).handoff.2.2.2.2.trans (Nmk_subset_Nnk j)
        · have hjn' : j = S.P.n := by omega
          subst hjn'
          exact h0.init_n.2.trans (Nmk_subset_Nnk _)
    · exact absurd hd hnd
  · -- (BA3) with `C₂`
    intro t' ht' k hk ha
    have hk' := Finset.mem_Icc.1 hk
    rcases ha.2.1.lt_or_eq with hlt | heq
    · have hA := hact k hk ha.1 t' ⟨ha.2.1, ha.2.2⟩ hlt ht'.2
      have hu : S.P.activeTime k t' ∈ Icc (0 : ℝ) (S.P.activeTime k t') :=
        ⟨activeTime_nonneg hS ha.2.1, le_rfl⟩
      have := (hA.concl _ hu).bound
      rwa [tsh_add_activeTime hS] at this
    · rw [← heq, Approx.activeTime_tsh]
      by_cases hkn : k < S.P.n
      · have hh := hhand k (Finset.mem_Ico.2 ⟨hk'.1, hkn⟩) (ha.1.mono (by omega))
          (heq ▸ ht'.2)
        exact (hh.switch_le.trans hh.switch_C0).trans hh.switch_lt.le
      · have hkn' : k = S.P.n := by omega
        subst hkn'
        rw [Approx.tsh_n]
        exact h0.start_le.trans h0.start_lt.le

end BootStepsH

/-- **Steps 1–6 of the proof of `prop:bootstrap`** (`11_bootstrap.tex:221-224`, `:251-538`): for
`t ∈ [0, T_end]`, Step 0 and (BA°)(t) imply the conclusions of Steps 1–6 on `[0, t]`
(`S.BootStepsConcl t`), in particular (BA)(t) and (BA*)(t). -/
theorem boot_steps (S : Standing) (hS : S.Holds) (hL : S.ParamLists) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) S.P.Tend) (h0 : S.BootStartConcl) (hBA : S.BAcirc t) :
    S.BootStepsConcl t := by
  have hhand := BootStepsH.handoff_all hS hL ht h0 hBA
  have hH : ∀ τ ≤ t, ∀ k ∈ Finset.Ico 1 S.P.n, S.P.ClockUpTo (k + 1) → S.P.tsh k < τ →
      S.HandoffStep k := fun τ hτ k hk hc hlt => hhand k hk hc (hlt.le.trans hτ)
  have hquiet := BootStepsH.quiet_of hS hL ht h0 hBA (hH t le_rfl)
  have hact : ∀ k ∈ Finset.Icc 1 S.P.n, S.P.ClockUpTo k → ∀ t' ∈ S.P.Phase k, S.P.tsh k < t' →
      t' ≤ t → S.ActiveStep k (S.P.activeTime k t') :=
    fun k hk hc t' ht' hlt hle => BootStepsH.active_of hS hL hk hc ht' hlt (hle.trans ht.2) h0
      (hBA.mono hle) (hH t' hle)
  have hqs : ∀ t' ∈ Icc (0 : ℝ) t, S.BA2At S.Abar t' := by
    intro t' ht'
    have ht'T : t' ∈ Icc (0 : ℝ) S.P.Tend := ⟨ht'.1, ht'.2.trans ht.2⟩
    refine boot_quiet_size S hS hL ht'T h0 (hBA.mono ht'.2)
      (BootStepsH.geom_of hS hL ht'T (hBA.mono ht'.2) (hH t' ht'.2))
      (fun t'' ht'' => hquiet t'' ⟨ht''.1, ht''.2.trans ht'.2⟩)
      (fun i hi hc hle => hhand i hi hc (hle.trans ht'.2)) ?_
    intro i hi hc hlt
    have hi' := Finset.mem_Icc.1 hi
    have hTi : S.P.tsh i < S.P.T i := BootStepsH.tsh_lt_T hS hi'.1 hc hi'.2
    exact hact i hi hc _ ⟨le_min hlt.le hTi.le, min_le_right _ _⟩ (lt_min hlt hTi)
      ((min_le_left _ _).trans ht'.2)
  have hstar := BootStepsH.bastar_of hS ht h0 hhand hquiet hact hqs
  exact
    { geom := BootStepsH.geom_of hS hL ht hBA (hH t le_rfl)
      quiet := hquiet
      handoff := hhand
      active := hact
      quiet_size := hqs
      ba := BA_of_BAstar S hS hL hstar
      ba_star := hstar }

end Relay

end NonUniqueEuler
