import NonUniqueEuler.Defs.Sec6.All

/-!
# Helper for `lem:clock`: the order of the clock and the agreement of the recursion

Helper of `P/Sec6/Clock.lean` (`06_datum.tex:462-497`). Everything here uses only the definitions
of `Defs/Sec6`; the analytic inputs are hypotheses:
* `order_core` (the proof of `lem:clock`(1), `06_datum.tex:463-466`): if every `A_j > 0`,
  `T_pin > 0`, `σ_j > 0` for `j ∈ [k, n]` and the clock is defined up to level `k`, then
  `t♯_j < T_j`, `T_j < t♯_{j-1}` (`j ≥ 1`) and `t♯` is antitone on `[k-1, n]`. It is stated for an
  arbitrary `Approx` (not necessarily valid), so that it applies to the clock of a comparison
  vorticity ("the proof of (1) applies to the clock of `ω̃` wherever it is defined",
  `06_datum.tex:487-489`).
* the agreement lemmas (the induction of `lem:clock`(2), `06_datum.tex:474-484`): if the flows of
  `P` and `P.withOm ω̃` agree on `[0, t̄]` and `ω̃ = ω^{(n)}` there, then `S_j(t)`, `w_j(t)`, `G_j`,
  `σ_j`, and the recursion `tshRev` agree as long as the activation times stay in `[0, t̄]`
  (`causal_core`, `clockUpTo_withOm`).
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Datum

namespace Approx

open RingData

namespace ClockH

variable (P : Approx)

/-! ### The order of the clock (the proof of `lem:clock`(1)) -/

theorem tsh_lt_T_of {k i : ℕ} (hA : ∀ j, 0 < P.A j) (hσ : 0 < P.sigma i) (hc : P.ClockUpTo k)
    (hki : k ≤ i) (hin : i ≤ P.n) : P.tsh i < P.T i := by
  have hne : i ≠ P.n + 1 := by omega
  rw [T_of_ne P hne]
  have hk := hc.ksh_mem hki hin
  have hlog : 0 < Real.log (P.δ₀ / P.ksh i) := Real.log_pos ((one_lt_div hk.1).mpr hk.2)
  have : 0 < P.That i / P.A i := div_pos (mul_pos (inv_pos.mpr hσ) hlog) (hA i)
  linarith

theorem T_lt_tsh_pred_of {i : ℕ} (hA : ∀ j, 0 < P.A j) (hTpin : 0 < P.Tpin) (hi : 1 ≤ i)
    (hin : i ≤ P.n) : P.T i < P.tsh (i - 1) := by
  have h := tsh_eq_T_add P (k := i - 1) (by omega)
  have hi' : i - 1 + 1 = i := by omega
  rw [hi'] at h
  have : 0 < P.Tpin / P.A i := div_pos hTpin (hA i)
  linarith

/-- **The order of the clock** (the proof of `lem:clock`(1), `06_datum.tex:463-466`), for any
data with `A_j > 0`, `T_pin > 0` and `σ_j > 0` on `[k, n]`. -/
theorem order_core (hA : ∀ j, 0 < P.A j) (hTpin : 0 < P.Tpin) {k : ℕ}
    (hσ : ∀ j ∈ Finset.Icc k P.n, 0 < P.sigma j) (hc : P.ClockUpTo k) :
    (∀ i ∈ Finset.Icc k P.n, P.tsh i < P.T i) ∧
    (∀ i ∈ Finset.Icc k P.n, 1 ≤ i → P.T i < P.tsh (i - 1)) ∧
    (∀ i j : ℕ, k ≤ i + 1 → i ≤ j → j ≤ P.n → P.tsh j ≤ P.tsh i) := by
  have h1 : ∀ i ∈ Finset.Icc k P.n, P.tsh i < P.T i := fun i hi => by
    rw [Finset.mem_Icc] at hi
    exact tsh_lt_T_of P hA (hσ i (Finset.mem_Icc.mpr hi)) hc hi.1 hi.2
  have h2 : ∀ i ∈ Finset.Icc k P.n, 1 ≤ i → P.T i < P.tsh (i - 1) := fun i hi h1i => by
    rw [Finset.mem_Icc] at hi
    exact T_lt_tsh_pred_of P hA hTpin h1i hi.2
  refine ⟨h1, h2, ?_⟩
  have hstep : ∀ i : ℕ, k ≤ i + 1 → i + 1 ≤ P.n → P.tsh (i + 1) ≤ P.tsh i := fun i hki hin => by
    have hmem : i + 1 ∈ Finset.Icc k P.n := Finset.mem_Icc.mpr ⟨hki, hin⟩
    have a := h1 (i + 1) hmem
    have b := h2 (i + 1) hmem (by omega)
    rw [Nat.add_sub_cancel] at b
    linarith
  have hd : ∀ d i : ℕ, k ≤ i + 1 → i + d ≤ P.n → P.tsh (i + d) ≤ P.tsh i := by
    intro d
    induction d with
    | zero => intro i _ _; simp
    | succ d ih =>
      intro i hki hin
      have e : i + (d + 1) = (i + d) + 1 := by omega
      rw [e]
      exact (hstep (i + d) (by omega) (by omega)).trans (ih i hki (by omega))
  intro i j hki hij hjn
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  exact hd d i hki hjn

/-! ### Agreement of the recursion (the induction of `lem:clock`(2)) -/

section Agree

variable {P} {om' : ℝ → ℂ → ℝ} {tbar : ℝ}
  (hfl : ∀ t ∈ Icc (0 : ℝ) tbar, (P.withOm om').flow t = P.flow t)
  (heq : ∀ t ∈ Icc (0 : ℝ) tbar, om' t = P.om t)

include hfl in
theorem St_agree {t : ℝ} (ht : t ∈ Icc (0 : ℝ) tbar) (k : ℕ) :
    (P.withOm om').St k t = P.St k t := by
  show (P.withOm om').flow t '' P.S k = P.flow t '' P.S k
  rw [hfl t ht]

include hfl heq in
theorem omegaRing_agree {t : ℝ} (ht : t ∈ Icc (0 : ℝ) tbar) (k : ℕ) :
    (P.withOm om').omegaRing k t = P.omegaRing k t := by
  show ((P.withOm om').St k t).indicator (om' t) = (P.St k t).indicator (P.om t)
  rw [St_agree hfl ht, heq t ht]

include hfl heq in
theorem w_agree {t : ℝ} (ht : t ∈ Icc (0 : ℝ) tbar) (k : ℕ) :
    (P.withOm om').w k t = P.w k t := by
  unfold w wR
  rw [omegaRing_agree hfl heq ht]
  rfl

include hfl in
theorem D_agree {t : ℝ} (ht : t ∈ Icc (0 : ℝ) tbar) (j : ℕ) :
    (P.withOm om').D j t = P.D j t := by
  unfold D
  simp only [St_agree hfl ht, withOm_n]

include hfl heq in
theorem omegaGe_agree {t : ℝ} (ht : t ∈ Icc (0 : ℝ) tbar) (j : ℕ) :
    (P.withOm om').omegaGe j t = P.omegaGe j t := by
  unfold omegaGe
  rw [D_agree hfl ht, withOm_om, heq t ht]

include hfl heq in
theorem G_agree (h0 : 0 ≤ tbar) (k : ℕ) : (P.withOm om').G k = P.G k := by
  unfold G
  rw [omegaGe_agree hfl heq ⟨le_rfl, h0⟩]
  rfl

include hfl heq in
theorem sigma_agree (h0 : 0 ≤ tbar) (k : ℕ) : (P.withOm om').sigma k = P.sigma k := by
  unfold sigma
  rw [G_agree hfl heq h0]
  rfl

include hfl heq in
theorem kshAt_agree {t : ℝ} (ht : t ∈ Icc (0 : ℝ) tbar) (k : ℕ) :
    (P.withOm om').kshAt k t = P.kshAt k t := by
  unfold kshAt
  rw [G_agree hfl heq (ht.1.trans ht.2), w_agree hfl heq ht]
  rfl

include hfl heq in
theorem ThatAt_agree {t : ℝ} (ht : t ∈ Icc (0 : ℝ) tbar) (k : ℕ) :
    (P.withOm om').ThatAt k t = P.ThatAt k t := by
  unfold ThatAt
  rw [sigma_agree hfl heq (ht.1.trans ht.2), kshAt_agree hfl heq ht]
  rfl

include hfl heq in
theorem tshRev_agree :
    ∀ j : ℕ, (∀ j' < j, P.tshRev j' ∈ Icc (0 : ℝ) tbar) →
      (P.withOm om').tshRev j = P.tshRev j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro h
    have hj : P.tshRev j ∈ Icc (0 : ℝ) tbar := h j (Nat.lt_succ_self j)
    rw [tshRev_succ (P.withOm om'), tshRev_succ P, ih fun j' hj' => h j' (by omega),
      ThatAt_agree hfl heq hj]
    rfl

end Agree

/-! ### The causal core (`lem:clock`(2), `06_datum.tex:474-484`) -/

/-- **The causal core**: if the clock of `P` is defined up to level `k`, the order hypotheses hold,
and the flows and vorticities of `P` and `P.withOm ω̃` agree on `[0, t̄]` with `t♯_i ≤ t̄`
(`i ∈ [k, n]`), then `t♯_i`, `c_i(0)`, `κ♯_i`, `T_i`, `t♯_{i-1}` and `S_i(t♯_i)` agree. -/
theorem causal_core (hA : ∀ j, 0 < P.A j) (hTpin : 0 < P.Tpin) {k : ℕ}
    (hσ : ∀ j ∈ Finset.Icc k P.n, 0 < P.sigma j) (hc : P.ClockUpTo k) {i : ℕ}
    (hi : i ∈ Finset.Icc k P.n) {tbar : ℝ} (ht : P.tsh i ≤ tbar) {om' : ℝ → ℂ → ℝ}
    (hfl : ∀ t ∈ Icc (0 : ℝ) tbar, (P.withOm om').flow t = P.flow t)
    (heq : ∀ t ∈ Icc (0 : ℝ) tbar, om' t = P.om t) :
    (P.withOm om').tsh i = P.tsh i ∧ (P.withOm om').c0 i = P.c0 i ∧
    (P.withOm om').ksh i = P.ksh i ∧ (P.withOm om').T i = P.T i ∧
    (1 ≤ i → (P.withOm om').tsh (i - 1) = P.tsh (i - 1)) ∧
    (P.withOm om').St i ((P.withOm om').tsh i) = P.St i (P.tsh i) := by
  rw [Finset.mem_Icc] at hi
  have hmono := (order_core P hA hTpin hσ hc).2.2
  have hti0 : 0 ≤ P.tsh i := by
    have := hmono i P.n (by omega) hi.2 le_rfl
    rwa [tsh_n] at this
  have hti : P.tsh i ∈ Icc (0 : ℝ) tbar := ⟨hti0, ht⟩
  have h0 : 0 ≤ tbar := hti0.trans ht
  have hrev : ∀ j' < P.n - i + 1, P.tshRev j' ∈ Icc (0 : ℝ) tbar := by
    intro j' hj'
    have e : P.tshRev j' = P.tsh (P.n - j') := by
      unfold tsh
      congr 1
      omega
    rw [e]
    refine ⟨?_, (hmono i (P.n - j') (by omega) (by omega) (by omega)).trans ht⟩
    have := hmono (P.n - j') P.n (by omega) (by omega) le_rfl
    rwa [tsh_n] at this
  have e1 : (P.withOm om').tshRev (P.n - i) = P.tshRev (P.n - i) :=
    tshRev_agree hfl heq _ fun j' hj' => hrev j' (by omega)
  have e2 : (P.withOm om').tshRev (P.n - i + 1) = P.tshRev (P.n - i + 1) :=
    tshRev_agree hfl heq _ hrev
  have htsh : (P.withOm om').tsh i = P.tsh i := e1
  have hc0 : (P.withOm om').c0 i = P.c0 i := by
    unfold c0
    rw [htsh, G_agree hfl heq h0, w_agree hfl heq hti]
    rfl
  have hksh : (P.withOm om').ksh i = P.ksh i := by
    unfold ksh
    rw [hc0]
  have hne : i ≠ P.n + 1 := by omega
  have hT : (P.withOm om').T i = P.T i := by
    rw [T_of_ne (P.withOm om') hne, T_of_ne P hne, htsh]
    unfold That
    rw [sigma_agree hfl heq h0, hksh]
    rfl
  refine ⟨htsh, hc0, hksh, hT, fun h1i => ?_, ?_⟩
  · have e : P.n - (i - 1) = P.n - i + 1 := by omega
    show (P.withOm om').tshRev (P.n - (i - 1)) = P.tshRev (P.n - (i - 1))
    rw [e, e2]
  · rw [htsh, St_agree hfl hti]

/-- Under the hypotheses of `causal_core`, the clock of `P.withOm ω̃` is defined up to level `i`. -/
theorem clockUpTo_withOm (hA : ∀ j, 0 < P.A j) (hTpin : 0 < P.Tpin) {k : ℕ}
    (hσ : ∀ j ∈ Finset.Icc k P.n, 0 < P.sigma j) (hc : P.ClockUpTo k) {i : ℕ}
    (hi : i ∈ Finset.Icc k P.n) {tbar : ℝ} (ht : P.tsh i ≤ tbar) {om' : ℝ → ℂ → ℝ}
    (hfl : ∀ t ∈ Icc (0 : ℝ) tbar, (P.withOm om').flow t = P.flow t)
    (heq : ∀ t ∈ Icc (0 : ℝ) tbar, om' t = P.om t) :
    (P.withOm om').ClockUpTo i := by
  have hmono := (order_core P hA hTpin hσ hc).2.2
  rw [Finset.mem_Icc] at hi
  intro j hj
  rw [withOm_n, Finset.mem_Icc] at hj
  have hjm : j ∈ Finset.Icc k P.n := Finset.mem_Icc.mpr ⟨hi.1.trans hj.1, hj.2⟩
  have htj : P.tsh j ≤ tbar := (hmono i j (by omega) hj.1 hj.2).trans ht
  obtain ⟨-, -, hksh, -, -, hSt⟩ := causal_core P hA hTpin hσ hc hjm htj hfl heq
  have hcj := hc j hjm
  refine ⟨?_, ?_⟩
  · rw [hSt]
    exact hcj.1
  · rw [hksh]
    exact hcj.2

end ClockH

end Approx

end Datum

end NonUniqueEuler
