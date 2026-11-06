import NonUniqueEuler.Defs.Sec10.Params
import NonUniqueEuler.Defs.Sec11.Stop

/-!
# Bootstrap and geometry bundles (legacy `Sec11` modules)

Current sources are the unnumbered bootstrap bounds in Part II §6 (`sec:relay`),
Lemma C.17 (`lem:geometry`, Appendix C.14), Equation (50) (`eq:handoff`, Appendix C.10),
and Proposition 8.1 (`prop:bootstrap`, §8).

The Lean bundles retain the earlier decomposition. `S.BAcirc t` corresponds to the current
manuscript's (BA)(t): its active bound is required only strictly after activation.
`S.BA t` also imposes that bound at activation, and `S.BAstar t` gives the improved bounds,
including activation. The legacy label `def:BA` is no longer a numbered manuscript definition.
`S.BootConcl` retains five groups of all-ring conclusions. Proposition 8.1 now states four
consequences for ring 1; the stronger information remains in its proof and Proposition 6.2
(`prop:relay-step`). The numbered groups below describe the Lean bundle, not the four items
of the current proposition.

For the standing datum `S = p.standing A₁ n` (`Defs/Sec10/Params.lean`):
* `S.BA1At U t'`, `S.BA2At A t'`, `S.BA3At C k t'` encode the three bounds at one time;
* `S.BA t`, `S.BAstar t`, `S.BAcirc t` impose them on every `t' ∈ [0, t]` as described above;
* `S.HandoffEq k` is `eq:handoff` at `t♯_k` with `K₁ = S.K1` from Definition C.13 (`def:K1`);
* `S.GeometryHyp t`, `S.GeometryWindow k t`, `S.GeometryRing j t'`, `S.GeometryConcl t`
  encode the hypotheses and conclusions (a)–(c) of Lemma C.17;
* `S.BootConcl` is the stronger all-ring conclusion used by the Lean proof.

Here `m = 3`, and the envelope and transient use `C₀ = S.C0` from (P4). Lean's envelope
argument is local active time, while §6 writes these functions in physical time.
The restriction `t ∈ [0, T_end]` is a hypothesis of the relevant results, not part of these
definitions. All lemmas here are proved.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

open RingData Datum

namespace Standing

variable (S : Standing)

/-! ### Bootstrap bounds from Part II §6 (`sec:relay`) -/

/-- **(BA1) at time `t'`**, with the sets `U` (Part II §6, `sec:relay`): every
ring `j ∈ [1, n]` that is not debris at `t'` has `S_j(t') ⊂ U_j`. Lean `BA` uses
`U_j = N♭_j` (`S.P.Nflatk`), and `BAstar` uses `U_j = 𝒩_j` (`S.P.Nnk`). -/
def BA1At (U : ℕ → Set ℂ) (t' : ℝ) : Prop :=
  ∀ j ∈ Finset.Icc 1 S.P.n, ¬ S.P.DebrisAt j t' → S.P.St j t' ⊆ U j

/-- **(BA2) at time `t'`**, with factor `A` (Part II §6, `sec:relay`): for every
quiet ring `j < n`, the field `h_j` is defined on `[0, t']` and
`maj_j(A_j t') ≤ A ε_j`. Lean `BA` and `BAcirc` use `A = 2Ā`; `BAstar` uses `A = Ā`.
Lean takes the majorant in ring-`j` time; the current manuscript writes it in physical time. -/
def BA2At (A t' : ℝ) : Prop :=
  ∀ j ∈ Finset.Ico 1 S.P.n, S.P.QuietAt j t' →
    (∀ t'' ∈ Icc (0 : ℝ) t', S.P.HDefined j t'') ∧ S.maj j (S.P.A j * t') ≤ A * S.P.eps j

/-- **The active bound for ring `k` at time `t'`**, with factor `C`:
if the ring is active, then with `u = A_k(t' - t♯_k)`,
`‖w_k(t')‖_{H^s} ≤ C â_k(u)(1 + ρ̂_k(u))`. The transient uses `C₀ = S.C0`.
Lean `BA` uses `C = 2C₂`, and `BAstar` uses `C = C₂`. The strict-after-activation
restriction of current (BA3) in Part II §6 (`sec:relay`) is imposed by `BAcirc`. -/
def BA3At (C : ℝ) (k : ℕ) (t' : ℝ) : Prop :=
  S.P.ActiveAt k t' →
    Sob.normH S.s (S.P.w k t') ≤
      C * S.ahatK k (S.P.activeTime k t') * (1 + S.rhoHatK S.C0 k (S.P.activeTime k t'))

/-- **Lean (BA)(t)**: on `[0, t]`, (BA1) with `N♭_j`, (BA2) with `2Ā`, and the
active bound with `2C₂`, including activation. This is stronger than current (BA)(t)
in Part II §6 (`sec:relay`), which corresponds to `BAcirc`. -/
structure BA (t : ℝ) : Prop where
  ba1 : ∀ t' ∈ Icc (0 : ℝ) t, S.BA1At S.P.Nflatk t'
  ba2 : ∀ t' ∈ Icc (0 : ℝ) t, S.BA2At (2 * S.Abar) t'
  ba3 : ∀ t' ∈ Icc (0 : ℝ) t, ∀ k ∈ Finset.Icc 1 S.P.n, S.BA3At (2 * S.C2) k t'

/-- **Lean (BA*)(t)**: the improved bounds of Part II §6 (`sec:relay`), with `𝒩_j`,
`Ā` and `C₂`, including the bound at activation supplied by the seed or hand-off. -/
structure BAstar (t : ℝ) : Prop where
  ba1 : ∀ t' ∈ Icc (0 : ℝ) t, S.BA1At S.P.Nnk t'
  ba2 : ∀ t' ∈ Icc (0 : ℝ) t, S.BA2At S.Abar t'
  ba3 : ∀ t' ∈ Icc (0 : ℝ) t, ∀ k ∈ Finset.Icc 1 S.P.n, S.BA3At S.C2 k t'

/-- **Lean (BA°)(t)**, corresponding to current (BA)(t) in Part II §6 (`sec:relay`):
Lean `BA` with the active bound omitted at `t' = t♯_k`. Since an active ring has
`t' ≥ t♯_k`, the remaining active bound is precisely the strict-after-activation one. -/
structure BAcirc (t : ℝ) : Prop where
  ba1 : ∀ t' ∈ Icc (0 : ℝ) t, S.BA1At S.P.Nflatk t'
  ba2 : ∀ t' ∈ Icc (0 : ℝ) t, S.BA2At (2 * S.Abar) t'
  ba3 : ∀ t' ∈ Icc (0 : ℝ) t, ∀ k ∈ Finset.Icc 1 S.P.n, t' ≠ S.P.tsh k → S.BA3At (2 * S.C2) k t'

/-! ### Equation (50) (`eq:handoff`) at activation -/

/-- **Equation (50) (`eq:handoff`, Part II Appendix C.10) at `t♯_k`**, with
`K₁ = S.K1` from Definition C.13 (`def:K1`): in ring-`k` units,
`½|c^in_k| ≤ κ♯_k ≤ (3/2)|c^in_k|`, `maj_k(t̄♯_k) ≤ K₁κ♯_k`,
`‖w_k(t♯_k)‖_{H^{s_h}} ≤ C_hand κ♯_k`, where `C_hand = K₁C_Q = S.Chand`, and
`supp(Φ + w_k(t♯_k)) ⊂ 𝒩₋`, equivalently `S_k(t♯_k) ⊂ 𝒩₋_k`.
This is the conclusion of `Relay.handoff` with `K₁ = S.K1`, used in Proposition 6.2(b)
(`prop:relay-step`) and retained in `BootConcl.handoff`. -/
def HandoffEq (k : ℕ) : Prop :=
  1 / 2 * ‖S.P.cinK k‖ ≤ S.P.ksh k ∧ S.P.ksh k ≤ 3 / 2 * ‖S.P.cinK k‖ ∧
    S.maj k (S.P.tash k) ≤ S.K1 * S.P.ksh k ∧
    Sob.normH S.sh (S.P.w k (S.P.tsh k)) ≤ S.K1 * S.CQ * S.P.ksh k ∧
    S.P.St k (S.P.tsh k) ⊆ S.P.Nmk k

/-! ### `lem:geometry` (Part II Appendix C.14 (`lem:geometry`, Lemma C.17)) -/

/-- **The hypotheses of `lem:geometry` at the time `t`** (Part II Appendix C.14 (`lem:geometry`,
Lemma C.17); `t ∈ [0, T_end]`
is a separate hypothesis): (BA1) holds at every `t' ∈ [0, t]` (with `N♭_j`), and
`κ♯_k ≥ K_lo s_k^{m+2}` for every level `k < n` with `t♯_k < t` (`t♯_k` defined: the clock is
defined up to level `k+1`). -/
structure GeometryHyp (t : ℝ) : Prop where
  ba1 : ∀ t' ∈ Icc (0 : ℝ) t, S.BA1At S.P.Nflatk t'
  amp : ∀ k ∈ Finset.Ico 1 S.P.n, S.P.ClockUpTo (k + 1) → S.P.tsh k < t →
    S.Klo * S.P.s k ^ (3 + 2) ≤ S.P.ksh k

/-- **Conclusion (a) of `lem:geometry` for the level `k` at the time `t`** (Part II Appendix C.14
(`lem:geometry`, Lemma C.17)),
for `k < n` with `T_{k+1}` defined and `T_{k+1} ≤ t`: the hypotheses of `prop:confine` hold with
`t₀ = T_{k+1}` and `t₁ = min(t, e_k)` (`P.ConfineHyp`), and for every `t' ∈ [T_{k+1}, min(t, e_k)]`:
`D_{k+1}(t') ⊂ \bar B_{ϱ_k(t')} ⊂ B_{ar_k/8}` and `|q_{k+1}(t')| ≤ C_mom(1 + A_{k+1}(t' - T_{k+1}))^m`,
with `ϱ_k(t') = (2 + 2C_*A_{k+1}(t' - T_{k+1}))r_{k+1}` (`P.confRadius`) and
`A_{k+1}(t' - T_{k+1}) = P.kickTime k t'`. -/
def GeometryWindow (k : ℕ) (t : ℝ) : Prop :=
  S.P.ConfineHyp k (min t (S.P.endW k)) ∧
    ∀ t' ∈ Icc (S.P.T (k + 1)) (min t (S.P.endW k)),
      S.P.D (k + 1) t' ⊆ closedBall 0 (S.P.confRadius k t') ∧
        closedBall (0 : ℂ) (S.P.confRadius k t') ⊆ ball 0 (a * S.P.r k / 8) ∧
        ‖S.P.q (k + 1) t'‖ ≤ Rings.Cmom * (1 + S.P.kickTime k t') ^ 3

/-- **Conclusion (b) of `lem:geometry` for the ring `j` at the time `t'`** (Part II Appendix C.14
(`lem:geometry`, Lemma C.17)),
for `j` not debris at `t'`: every ring `i < j` is quiet at `t'` and satisfies
`S_i(t') ⊂ N♭_i ⊂ ℝ² ∖ B_{6r_j}`; `D_{j+1}(t') ⊂ B_{ar_j/8}` (`HInDefined`); hence `h_j` is defined
at `t'` (`HDefined`; this is also the support hypothesis of `lem:reduction` for ring `j` in ring-`j`
units, Part II Lemma 2.2 (`lem:reduction`) and Lemma C.17(b) (`lem:geometry`)); and, if `j < n`,
`η_j(A_j t') ≤ 1`. -/
def GeometryRing (j : ℕ) (t' : ℝ) : Prop :=
  (∀ i ∈ Finset.Ico 1 j, S.P.QuietAt i t' ∧ S.P.St i t' ⊆ S.P.Nflatk i ∧
      S.P.Nflatk i ⊆ (ball (0 : ℂ) (6 * S.P.r j))ᶜ) ∧
    S.P.HInDefined j t' ∧ S.P.HDefined j t' ∧ (j < S.P.n → S.eta j (S.P.A j * t') ≤ 1)

/-- **The conclusions (a)–(c) of `lem:geometry` at the time `t`** (Part II Appendix C.14
(`lem:geometry`, Lemma C.17)):
(a) `GeometryWindow k t` for every level `k < n` with `T_{k+1}` defined (the clock is defined up to
level `k+1`) and `T_{k+1} ≤ t`; (b) `GeometryRing j t'` for every `t' ∈ [0, t]` and every ring
`j ∈ [1, n]` not debris at `t'`; (c) (Loc) at every `t' ∈ [0, t]` (`P.Loc`). -/
structure GeometryConcl (t : ℝ) : Prop where
  window : ∀ k ∈ Finset.Ico 1 S.P.n, S.P.ClockUpTo (k + 1) → S.P.T (k + 1) ≤ t →
    S.GeometryWindow k t
  ring : ∀ t' ∈ Icc (0 : ℝ) t, ∀ j ∈ Finset.Icc 1 S.P.n, ¬ S.P.DebrisAt j t' →
    S.GeometryRing j t'
  loc : ∀ t' ∈ Icc (0 : ℝ) t, S.P.Loc t'

/-! ### The stronger all-ring bootstrap conclusion -/

/-- **The five groups of the Lean all-ring bootstrap conclusion**, for the standing datum `S`.
They retain the earlier statement of `prop:bootstrap`; current Part II Proposition 8.1
states four ring-1 consequences. The following numbering is internal to this Lean bundle:
1. `T_end = T₁`, i.e. the clock is defined up to level `1` (`clock`; `P.Tend_of_clockUpTo`);
   `K_lo s_k^{m+2} ≤ κ♯_k ≤ K_up s_k^{m+2}` for `k < n` (`amp`) and
   `κ♯_n ∈ [½κ_seed, 2κ_seed]` (`amp_n`);
2. (BA*)(T₁) (`ba_star`);
3. `eq:handoff` at `t♯_k` for every `k < n` (`handoff`); for every `k ≤ n`, the conclusions of
   `thm:active` and `cor:active-moment` for ring `k` on `Ph_k` with `G = G_k`, `κ = κ♯_k`, the
   constant `C₀ = S.C0` of (P4) and `η_b = η_{b,k}` (`S.etabK S.C0 S.K1 k`) (`active`), and
   `|c_k(T̂_k)|e^{σ_k T̂_k} ∈ [15δ₀/16, 17δ₀/16]` (`coef`);
4. for every `k < n`: the hypotheses of `prop:confine` with `t₀ = T_{k+1}`, `t₁ = T_k`, its
   conclusions on `W_k` (`P.ConfineConcl`, which contains (a) and (c), and also (b), which
   `prop:confine` gives under these hypotheses), and `D_{k+1}(t) ⊂ B_{ar_k/8}` for `t ∈ W_k`
   (`HInDefined`) (`confine`);
5. `T₁ ≤ T_*` (`time`). -/
structure BootConcl : Prop where
  clock : S.P.ClockUpTo 1
  amp : ∀ k ∈ Finset.Ico 1 S.P.n,
    S.Klo * S.P.s k ^ (3 + 2) ≤ S.P.ksh k ∧ S.P.ksh k ≤ S.Kup * S.P.s k ^ (3 + 2)
  amp_n : S.P.ksh S.P.n ∈ Icc (1 / 2 * S.P.κs) (2 * S.P.κs)
  ba_star : S.BAstar (S.P.T 1)
  handoff : ∀ k ∈ Finset.Ico 1 S.P.n, S.HandoffEq k
  active : ∀ k ∈ Finset.Icc 1 S.P.n, S.ActiveConcl S.C0 (S.etabK S.C0 S.K1 k) k
  coef : ∀ k ∈ Finset.Icc 1 S.P.n,
    ‖S.P.runCoefK k (S.P.That k)‖ * Real.exp (S.P.sigma k * S.P.That k) ∈
      Icc (15 / 16 * S.P.δ₀) (17 / 16 * S.P.δ₀)
  confine : ∀ k ∈ Finset.Ico 1 S.P.n, S.P.ConfineHyp k (S.P.T k) ∧
    ∀ t ∈ S.P.W k, S.P.ConfineConcl k (S.P.T k) t ∧ S.P.HInDefined k t
  time : S.P.T 1 ≤ S.Tstar

/-! ### Basic lemmas (fully proved) -/

variable {S}

theorem BA.mono {t t' : ℝ} (h : S.BA t) (ht : t' ≤ t) : S.BA t' where
  ba1 s hs := h.ba1 s ⟨hs.1, hs.2.trans ht⟩
  ba2 s hs := h.ba2 s ⟨hs.1, hs.2.trans ht⟩
  ba3 s hs := h.ba3 s ⟨hs.1, hs.2.trans ht⟩

theorem BAstar.mono {t t' : ℝ} (h : S.BAstar t) (ht : t' ≤ t) : S.BAstar t' where
  ba1 s hs := h.ba1 s ⟨hs.1, hs.2.trans ht⟩
  ba2 s hs := h.ba2 s ⟨hs.1, hs.2.trans ht⟩
  ba3 s hs := h.ba3 s ⟨hs.1, hs.2.trans ht⟩

theorem BAcirc.mono {t t' : ℝ} (h : S.BAcirc t) (ht : t' ≤ t) : S.BAcirc t' where
  ba1 s hs := h.ba1 s ⟨hs.1, hs.2.trans ht⟩
  ba2 s hs := h.ba2 s ⟨hs.1, hs.2.trans ht⟩
  ba3 s hs := h.ba3 s ⟨hs.1, hs.2.trans ht⟩

/-- (BA)(t) implies (BA°)(t). -/
theorem BA.toBAcirc {t : ℝ} (h : S.BA t) : S.BAcirc t where
  ba1 := h.ba1
  ba2 := h.ba2
  ba3 s hs k hk _ := h.ba3 s hs k hk

/-- (BA°)(t) together with (BA3) at the activation times gives (BA)(t). -/
theorem BAcirc.toBA {t : ℝ} (h : S.BAcirc t)
    (hsh : ∀ k ∈ Finset.Icc 1 S.P.n, S.P.tsh k ∈ Icc (0 : ℝ) t →
      S.BA3At (2 * S.C2) k (S.P.tsh k)) : S.BA t where
  ba1 := h.ba1
  ba2 := h.ba2
  ba3 s hs k hk := by
    by_cases hks : s = S.P.tsh k
    · subst hks
      exact hsh k hk hs
    · exact h.ba3 s hs k hk hks

/-- (BA1) with smaller sets is stronger. -/
theorem BA1At.mono {U V : ℕ → Set ℂ} {t' : ℝ} (h : S.BA1At U t')
    (hUV : ∀ j ∈ Finset.Icc 1 S.P.n, U j ⊆ V j) : S.BA1At V t' :=
  fun j hj hd => (h j hj hd).trans (hUV j hj)

/-- (BA2) with a smaller factor is stronger. -/
theorem BA2At.mono {A A' t' : ℝ} (h : S.BA2At A t') (hA : A ≤ A')
    (hε : ∀ j ∈ Finset.Ico 1 S.P.n, 0 ≤ S.P.eps j) : S.BA2At A' t' :=
  fun j hj hq => ⟨(h j hj hq).1,
    (h j hj hq).2.trans (mul_le_mul_of_nonneg_right hA (hε j hj))⟩

/-- (BA3) with a smaller factor is stronger. -/
theorem BA3At.mono {C C' : ℝ} {k : ℕ} {t' : ℝ} (h : S.BA3At C k t') (hC : C ≤ C')
    (hρ : 0 ≤ 1 + S.rhoHatK S.C0 k (S.P.activeTime k t')) : S.BA3At C' k t' := by
  intro ha
  refine (h ha).trans ?_
  have h0 : 0 ≤ S.ahatK k (S.P.activeTime k t') := S.ahatK_nonneg k _
  have := mul_le_mul_of_nonneg_right hC h0
  exact mul_le_mul_of_nonneg_right this hρ

theorem GeometryConcl.mono {t t' : ℝ} (h : S.GeometryConcl t) (ht : t' ≤ t)
    (hw : ∀ k ∈ Finset.Ico 1 S.P.n, S.P.ClockUpTo (k + 1) → S.P.T (k + 1) ≤ t' →
      S.GeometryWindow k t') : S.GeometryConcl t' where
  window := hw
  ring s hs := h.ring s ⟨hs.1, hs.2.trans ht⟩
  loc s hs := h.loc s ⟨hs.1, hs.2.trans ht⟩

theorem handoffEq_iff (k : ℕ) : S.HandoffEq k ↔
    1 / 2 * ‖S.P.cinK k‖ ≤ S.P.ksh k ∧ S.P.ksh k ≤ 3 / 2 * ‖S.P.cinK k‖ ∧
      S.maj k (S.P.tash k) ≤ S.K1 * S.P.ksh k ∧
      Sob.normH S.sh (S.P.w k (S.P.tsh k)) ≤ S.Chand * S.P.ksh k ∧
      S.P.St k (S.P.tsh k) ⊆ S.P.Nmk k := Iff.rfl

/-- The clock consequence of `BootConcl`, also Part II Proposition 8.1(1) (`prop:bootstrap`). -/
theorem BootConcl.Tend_eq (h : S.BootConcl) : S.P.Tend = S.P.T 1 :=
  Approx.Tend_of_clockUpTo h.clock

end Standing

end Relay

end NonUniqueEuler
