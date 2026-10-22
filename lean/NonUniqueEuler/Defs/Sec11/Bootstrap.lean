import NonUniqueEuler.Defs.Sec10.Params
import NonUniqueEuler.Defs.Sec11.Stop

/-!
# Section 11: the bootstrap assumptions and the bundles of `lem:geometry` and `prop:bootstrap`
(definitions)

Manuscript `11_bootstrap.tex`:
`def:BA` (`:71-92`), `lem:geometry` (`:121-144`), `prop:bootstrap` (`:94-113`), and
`eq:handoff` (`09_relay.tex:877-884`) as used in `prop:bootstrap`(3).

Throughout Section 11 the standing datum is `S = p.standing A₁ n` (`Defs/Sec10/Params.lean`), and
`â_k`, `ρ̂_k` are taken with the constant `C₀ = S.C0` of (P4) (`11_bootstrap.tex:17-18`). The
objects:
* `S.BA1At U t'`, `S.BA2At A t'`, `S.BA3At C k t'`: the three conditions of `def:BA` at one time
  `t'` (with the sets `U_j`, the factor `A` in place of `2Ā` and the factor `C` in place of `2C₂`);
* `S.BA t`, `S.BAstar t`, `S.BAcirc t`: (BA)(t), (BA*)(t), (BA°)(t) (conditions at every
  `t' ∈ [0, t]`);
* `S.HandoffEq k`: `eq:handoff` at `t♯_k` with the `K_1` of `def:K1` (the conclusion of
  `Relay.handoff` for `K₁ = S.K1`, by definition);
* `S.GeometryHyp t`, `S.GeometryWindow k t`, `S.GeometryRing j t'`, `S.GeometryConcl t`: the
  hypotheses and the conclusions (a)–(c) of `lem:geometry`;
* `S.BootConcl`: the conclusions (1)–(5) of `prop:bootstrap`.

The restriction `t ∈ [0, T_end]` of `def:BA` and `lem:geometry` is a hypothesis of the statements,
not part of the definitions. Here `m = 3`. All lemmas here are fully proved.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

open RingData Datum

namespace Standing

variable (S : Standing)

/-! ### `def:BA` (`11_bootstrap.tex:71-92`) -/

/-- **(BA1) at the time `t'`** for the family of sets `U` (`def:BA`, `11_bootstrap.tex:75`): every
ring `j ∈ [1, n]` that is not debris at `t'` has `S_j(t') ⊂ U_j`. (BA) uses `U_j = N♭_j`
(`S.P.Nflatk`), (BA*) uses `U_j = 𝒩_j` (`S.P.Nnk`). -/
def BA1At (U : ℕ → Set ℂ) (t' : ℝ) : Prop :=
  ∀ j ∈ Finset.Icc 1 S.P.n, ¬ S.P.DebrisAt j t' → S.P.St j t' ⊆ U j

/-- **(BA2) at the time `t'`** with the factor `A` (`def:BA`, `11_bootstrap.tex:76-77`): for every
ring `j < n` that is quiet at `t'`, the field `h_j` is defined at every time in `[0, t']`, and
`maj_j(A_j t') ≤ A ε_j`. (BA) uses `A = 2Ā`, (BA*) uses `A = Ā` (`S.Abar`). -/
def BA2At (A t' : ℝ) : Prop :=
  ∀ j ∈ Finset.Ico 1 S.P.n, S.P.QuietAt j t' →
    (∀ t'' ∈ Icc (0 : ℝ) t', S.P.HDefined j t'') ∧ S.maj j (S.P.A j * t') ≤ A * S.P.eps j

/-- **(BA3) for ring `k` at the time `t'`** with the factor `C` (`def:BA`, `11_bootstrap.tex:78-79`):
if ring `k` is active at `t'`, then with `u = A_k(t' - t♯_k)`,
`‖w_k(t')‖_{H^s} ≤ C â_k(u)(1 + ρ̂_k(u))`, `ρ̂_k` with the constant `C₀ = S.C0` of (P4). (BA) uses
`C = 2C₂`, (BA*) uses `C = C₂` (`S.C2`). -/
def BA3At (C : ℝ) (k : ℕ) (t' : ℝ) : Prop :=
  S.P.ActiveAt k t' →
    Sob.normH S.s (S.P.w k t') ≤
      C * S.ahatK k (S.P.activeTime k t') * (1 + S.rhoHatK S.C0 k (S.P.activeTime k t'))

/-- **(BA)(t)** (`def:BA`, `11_bootstrap.tex:73-80`): for every `t' ∈ [0, t]`, (BA1) with `N♭_j`,
(BA2) with `2Ā` and (BA3) with `2C₂` (for every ring `k ∈ [1, n]`). -/
structure BA (t : ℝ) : Prop where
  ba1 : ∀ t' ∈ Icc (0 : ℝ) t, S.BA1At S.P.Nflatk t'
  ba2 : ∀ t' ∈ Icc (0 : ℝ) t, S.BA2At (2 * S.Abar) t'
  ba3 : ∀ t' ∈ Icc (0 : ℝ) t, ∀ k ∈ Finset.Icc 1 S.P.n, S.BA3At (2 * S.C2) k t'

/-- **(BA*)(t)** (`def:BA`, `11_bootstrap.tex:81-82`): (BA)(t) with `N♭_j`, `2Ā`, `2C₂` replaced by
`𝒩_j`, `Ā`, `C₂`. -/
structure BAstar (t : ℝ) : Prop where
  ba1 : ∀ t' ∈ Icc (0 : ℝ) t, S.BA1At S.P.Nnk t'
  ba2 : ∀ t' ∈ Icc (0 : ℝ) t, S.BA2At S.Abar t'
  ba3 : ∀ t' ∈ Icc (0 : ℝ) t, ∀ k ∈ Finset.Icc 1 S.P.n, S.BA3At S.C2 k t'

/-- **(BA°)(t)** (`def:BA`, `11_bootstrap.tex:82-84`): (BA)(t) without, for each level `k`, the
instance of (BA3) for ring `k` at `t' = t♯_k`. -/
structure BAcirc (t : ℝ) : Prop where
  ba1 : ∀ t' ∈ Icc (0 : ℝ) t, S.BA1At S.P.Nflatk t'
  ba2 : ∀ t' ∈ Icc (0 : ℝ) t, S.BA2At (2 * S.Abar) t'
  ba3 : ∀ t' ∈ Icc (0 : ℝ) t, ∀ k ∈ Finset.Icc 1 S.P.n, t' ≠ S.P.tsh k → S.BA3At (2 * S.C2) k t'

/-! ### `eq:handoff` at `t♯_k` (`09_relay.tex:877-884`; `prop:bootstrap`(3)) -/

/-- **Equation `eq:handoff` at `t♯_k`** with the constant `K_1 = S.K1` of `def:K1`
(`09_relay.tex:877-884`; `prop:bootstrap`(3), `11_bootstrap.tex:103`; Step 3, `:376`), in ring-`k`
units: `½|c^in_k| ≤ κ♯_k ≤ (3/2)|c^in_k|`, `maj_k(t̄♯_k) ≤ K_1 κ♯_k`,
`‖w_k(t♯_k)‖_{H^{s_h}} ≤ C_hand κ♯_k` with `C_hand = K_1C_Q` (`= S.Chand`, `Chand_def`), and
`supp(Φ + w_k(t♯_k)) ⊂ 𝒩₋`, i.e. `S_k(t♯_k) ⊂ 𝒩₋_k`. This is the conclusion of the interface
`Relay.handoff` with `K₁ = S.K1`, literally. -/
def HandoffEq (k : ℕ) : Prop :=
  1 / 2 * ‖S.P.cinK k‖ ≤ S.P.ksh k ∧ S.P.ksh k ≤ 3 / 2 * ‖S.P.cinK k‖ ∧
    S.maj k (S.P.tash k) ≤ S.K1 * S.P.ksh k ∧
    Sob.normH S.sh (S.P.w k (S.P.tsh k)) ≤ S.K1 * S.CQ * S.P.ksh k ∧
    S.P.St k (S.P.tsh k) ⊆ S.P.Nmk k

/-! ### `lem:geometry` (`11_bootstrap.tex:121-144`) -/

/-- **The hypotheses of `lem:geometry` at the time `t`** (`11_bootstrap.tex:123-124`; `t ∈ [0, T_end]`
is a separate hypothesis): (BA1) holds at every `t' ∈ [0, t]` (with `N♭_j`), and
`κ♯_k ≥ K_lo s_k^{m+2}` for every level `k < n` with `t♯_k < t` (`t♯_k` defined: the clock is
defined up to level `k+1`). -/
structure GeometryHyp (t : ℝ) : Prop where
  ba1 : ∀ t' ∈ Icc (0 : ℝ) t, S.BA1At S.P.Nflatk t'
  amp : ∀ k ∈ Finset.Ico 1 S.P.n, S.P.ClockUpTo (k + 1) → S.P.tsh k < t →
    S.Klo * S.P.s k ^ (3 + 2) ≤ S.P.ksh k

/-- **Conclusion (a) of `lem:geometry` for the level `k` at the time `t`** (`11_bootstrap.tex:128-135`),
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

/-- **Conclusion (b) of `lem:geometry` for the ring `j` at the time `t'`** (`11_bootstrap.tex:136-141`),
for `j` not debris at `t'`: every ring `i < j` is quiet at `t'` and satisfies
`S_i(t') ⊂ N♭_i ⊂ ℝ² ∖ B_{6r_j}`; `D_{j+1}(t') ⊂ B_{ar_j/8}` (`HInDefined`); hence `h_j` is defined
at `t'` (`HDefined`; this is also the support hypothesis of `lem:reduction` for ring `j` in ring-`j`
units, `09_relay.tex:72-80`); and, if `j < n`, `η_j(A_j t') ≤ 1`. -/
def GeometryRing (j : ℕ) (t' : ℝ) : Prop :=
  (∀ i ∈ Finset.Ico 1 j, S.P.QuietAt i t' ∧ S.P.St i t' ⊆ S.P.Nflatk i ∧
      S.P.Nflatk i ⊆ (ball (0 : ℂ) (6 * S.P.r j))ᶜ) ∧
    S.P.HInDefined j t' ∧ S.P.HDefined j t' ∧ (j < S.P.n → S.eta j (S.P.A j * t') ≤ 1)

/-- **The conclusions (a)–(c) of `lem:geometry` at the time `t`** (`11_bootstrap.tex:127-143`):
(a) `GeometryWindow k t` for every level `k < n` with `T_{k+1}` defined (the clock is defined up to
level `k+1`) and `T_{k+1} ≤ t`; (b) `GeometryRing j t'` for every `t' ∈ [0, t]` and every ring
`j ∈ [1, n]` not debris at `t'`; (c) (Loc) at every `t' ∈ [0, t]` (`P.Loc`). -/
structure GeometryConcl (t : ℝ) : Prop where
  window : ∀ k ∈ Finset.Ico 1 S.P.n, S.P.ClockUpTo (k + 1) → S.P.T (k + 1) ≤ t →
    S.GeometryWindow k t
  ring : ∀ t' ∈ Icc (0 : ℝ) t, ∀ j ∈ Finset.Icc 1 S.P.n, ¬ S.P.DebrisAt j t' →
    S.GeometryRing j t'
  loc : ∀ t' ∈ Icc (0 : ℝ) t, S.P.Loc t'

/-! ### The conclusions of `prop:bootstrap` (`11_bootstrap.tex:94-113`) -/

/-- **The conclusions (1)–(5) of `prop:bootstrap`** for the standing datum `S`
(`11_bootstrap.tex:98-112`; in Section 11, `S = p.standing A₁ n`):
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

/-- Item (1) of `prop:bootstrap`: `T_end = T₁`. -/
theorem BootConcl.Tend_eq (h : S.BootConcl) : S.P.Tend = S.P.T 1 :=
  Approx.Tend_of_clockUpTo h.clock

end Standing

end Relay

end NonUniqueEuler
