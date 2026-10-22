import NonUniqueEuler.Defs.Sec11.All

/-!
# Section 11: the conclusions of the steps of the proof of `prop:bootstrap` (definitions)

Manuscript: the proof of
`prop:bootstrap`, `11_bootstrap.tex:220-605`.

The proof of `prop:bootstrap` is split (restructuring R10) into the
interfaces `I/Sec11/Boot*.lean`, one per step of the manuscript's proof. The bundles below are the
conclusions of the steps, so that a later step can take the conclusions of the earlier steps as
hypotheses ("each step uses (BA°)(t), the conclusions of the steps already carried out, and nothing
else", `11_bootstrap.tex:255-257`):
* `S.BootStartConcl`: Step 0 (the initial time, `:230-250`, with `eq:boot-start`);
* `S.QuietStep j t'`, `S.QuietStepAt t'`: Step 2 (quiet rings at the time `t'`, `:270-296`, with
  `eq:boot-quiet`);
* `S.HandoffStep k`: Step 3 (the hand-off of ring `k < n` at `t♯_k`, `:298-388`, with
  `eq:boot-kappa`, `eq:boot-kick`, `eq:boot-theta`, `eq:handoff`, `eq:boot-switch`);
* `S.ActiveStep k ū`: Step 4 (the active phase of ring `k` up to the active time `ū > 0`,
  `:390-484`, with `eq:boot-inner`);
* `S.BootStepsConcl t`: Steps 1–6 together at the time `t` (the conclusion of "(BA°)(t) implies
  (BA)(t) and (BA*)(t), together with the hand-off and the bounds on the active rings up to time
  `t`", `:221-224`, `:532-538`).
Step 1 is `lem:geometry` (`S.GeometryConcl`), Step 5 is `S.BA2At S.Abar` (`(BA2)` with `Ā`), Step 6
is `S.BA t ∧ S.BAstar t`. Throughout, `C₀ = S.C0` of (P4), `K₁ = S.K1` of `def:K1`,
`η_{b,k} = S.etabK S.C0 S.K1 k` and `m = 3`. Only definitions; nothing to prove.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

open RingData Datum

namespace Standing

variable (S : Standing)

/-! ### Step 0 (`11_bootstrap.tex:230-250`) -/

/-- **The conclusions of Step 0 of the proof of `prop:bootstrap`** (the initial time,
`11_bootstrap.tex:230-250`): the clock is defined up to level `n`; `κ♯_n ∈ [½κ_seed, 2κ_seed]`;
(Init) for ring `n` with `C₀` (`‖w_n(0)‖_{H^{M-1}} ≤ C₀κ♯_n`, `S_n = S_n(0) ⊂ 𝒩₋_n`; `t♯_n = 0`);
`ρ̂_n(0) = C₀`; `eq:boot-start`: `‖w_n(0)‖_{H^s} ≤ C₀κ♯_n < C₂â_n(0)(1 + ρ̂_n(0))`; for `j < n`:
`S_j(0) ⊂ 𝒩₋_j`, `w_j(0) = 0` (ring `j` starts at `Φ` in ring-`j` units; `maj_j(0) = 0` is
`maj_zero`) and `h_j` is defined at `0`; and (BA*)(0). -/
structure BootStartConcl : Prop where
  clock_n : S.P.ClockUpTo S.P.n
  ksh_n : S.P.ksh S.P.n ∈ Icc (1 / 2 * S.P.κs) (2 * S.P.κs)
  init_n : S.ActiveInitK S.C0 S.P.n
  rho_n : S.rhoHatK S.C0 S.P.n 0 = S.C0
  start_le : Sob.normH S.s (S.P.w S.P.n 0) ≤ S.C0 * S.P.ksh S.P.n
  start_lt : S.C0 * S.P.ksh S.P.n < S.C2 * S.ahatK S.P.n 0 * (1 + S.rhoHatK S.C0 S.P.n 0)
  quiet0 : ∀ j ∈ Finset.Ico 1 S.P.n,
    S.P.St j 0 ⊆ S.P.Nmk j ∧ S.P.w j 0 = 0 ∧ S.P.HDefined j 0
  ba_star : S.BAstar 0

/-! ### Step 2 (`11_bootstrap.tex:270-296`) -/

/-- **The conclusions of Step 2 for the quiet ring `j < n` at the time `t'`**
(`11_bootstrap.tex:270-296`), with `τ = A_j t'`:
* `eq:boot-quiet`: for `t'' ∈ [0, t']`, `S_j(t'') ⊂ 𝒩₋_j` and `‖w_j(t'')‖_{H^{s_h}} ≤ C_Q maj_j(A_jt'')`;
* `thm:quiet` applies to ring `j` on `[0, τ]` (`QuietHyp`, `QuietConcl`);
* if `t♯_j` is defined: the hypotheses and conclusions of `lem:O` for `j` and `τ` (`OHyp`, `OConcl`;
  in particular `η^out_j ≤ θ_j maj_j` on `[0, τ]`);
* if `t♯_j` is not defined (the clock stops at `k_s > j`):
  `maj_j(A_jt') ≤ ¾ P̃_{j,k_s} maj_{k_s}(A_{k_s}t')`. -/
structure QuietStep (j : ℕ) (t' : ℝ) : Prop where
  quiet_eq : ∀ t'' ∈ Icc (0 : ℝ) t', S.P.St j t'' ⊆ S.P.Nmk j ∧
    Sob.normH S.sh (S.P.w j t'') ≤ S.CQ * S.maj j (S.P.A j * t'')
  hyp : S.QuietHyp j (S.P.A j * t')
  concl : S.QuietConcl j (S.P.A j * t')
  lemO : S.P.ClockUpTo (j + 1) → S.OHyp j (S.P.A j * t') ∧ S.OConcl j (S.P.A j * t')
  stopped : ¬ S.P.ClockUpTo (j + 1) →
    S.maj j (S.P.A j * t') ≤
      3 / 4 * S.Ptil j S.P.stopLevel * S.maj S.P.stopLevel (S.P.A S.P.stopLevel * t')

/-- **The conclusions of Step 2 at the time `t'`** (`11_bootstrap.tex:270-296`): `QuietStep j t'`
for every ring `j < n` that is quiet at `t'`. -/
def QuietStepAt (t' : ℝ) : Prop :=
  ∀ j ∈ Finset.Ico 1 S.P.n, S.P.QuietAt j t' → S.QuietStep j t'

/-! ### Step 3 (`11_bootstrap.tex:298-388`) -/

/-- **The conclusions of Step 3, the hand-off of ring `k < n` at `t♯_k`** (`11_bootstrap.tex:298-388`),
with `C₀ = S.C0`, `K₁ = S.K1`:
* `eq:boot-kappa`: `0 < κ♯_{k+1} ≤ 2κ_seed`;
* `eq:boot-kick` (the conclusions of `lem:kicktrue`): `|q_s| ∈ [15/16, 17/16]·2π|pout_*(G_{k+1})|δ₀`
  and `|β_k||q_s|/(10|z|(μ-1)) ≤ |A^in(τ_K)| ≤ 3|β_k||q_s|μ/(|z|(μ-1))` for `τ_K ∈ [0, T_pin]`;
* `eq:boot-theta`: `θ_k t̄♯_k ≤ θ_k τ̄♯_k ≤ min{1/2, 1/(4C_lsK₁)}`;
* `eq:relay` at `t̄♯_k` (`prop:relay`), and (`lem:K1`) `maj_k(t̄♯_k) ≤ Āε_k`,
  `2maj_k(t̄♯_k) ≤ ½K₁|c^in_k|`;
* `eq:handoff` at `t♯_k` (`HandoffEq`);
* (`cor:amp`) `K_lo s_k^{m+2} ≤ κ♯_k ≤ K_up s_k^{m+2}`;
* the clock is defined up to level `k`;
* `eq:boot-switch`: `‖w_k(t♯_k)‖_{H^s} ≤ C_hand κ♯_k ≤ C₀κ♯_k < C₂â_k(0)(1 + ρ̂_k(0))`. -/
structure HandoffStep (k : ℕ) : Prop where
  kappa_pos : 0 < S.P.ksh (k + 1)
  kappa_le : S.P.ksh (k + 1) ≤ 2 * S.P.κs
  qs_mem : ‖S.P.kickQs k‖ ∈
    Icc (15 / 16 * (2 * Real.pi * ‖Eig.pout S.P.χ (S.P.G (k + 1))‖ * S.P.δ₀))
      (17 / 16 * (2 * Real.pi * ‖Eig.pout S.P.χ (S.P.G (k + 1))‖ * S.P.δ₀))
  kick : ∀ τK ∈ Icc (0 : ℝ) S.P.Tpin,
    ‖S.P.betaK k‖ * ‖S.P.kickQs k‖ / (10 * ‖S.z‖ * (S.P.μ - 1)) ≤ ‖S.P.Ain k τK‖ ∧
      ‖S.P.Ain k τK‖ ≤ 3 * ‖S.P.betaK k‖ * ‖S.P.kickQs k‖ * S.P.μ / (‖S.z‖ * (S.P.μ - 1))
  theta_le : S.theta k * S.P.tash k ≤ S.theta k * S.tauBarSh k
  theta_small : S.theta k * S.tauBarSh k ≤ min (1 / 2) (1 / (4 * Eig.Cls S.P.χ * S.K1))
  relay : S.maj k (S.P.tash k) ≤ S.relayBound k (S.XiNext S.C0 S.K1 k)
  maj_le : S.maj k (S.P.tash k) ≤ S.Abar * S.P.eps k
  maj_le_cin : 2 * S.maj k (S.P.tash k) ≤ 1 / 2 * S.K1 * ‖S.P.cinK k‖
  handoff : S.HandoffEq k
  amp_lo : S.Klo * S.P.s k ^ (3 + 2) ≤ S.P.ksh k
  amp_up : S.P.ksh k ≤ S.Kup * S.P.s k ^ (3 + 2)
  clock : S.P.ClockUpTo k
  switch_le : Sob.normH S.s (S.P.w k (S.P.tsh k)) ≤ S.Chand * S.P.ksh k
  switch_C0 : S.Chand * S.P.ksh k ≤ S.C0 * S.P.ksh k
  switch_lt : S.C0 * S.P.ksh k < S.C2 * S.ahatK k 0 * (1 + S.rhoHatK S.C0 k 0)

/-! ### Step 4 (`11_bootstrap.tex:390-484`) -/

/-- **The conclusions of Step 4 for ring `k` up to the active time `ū ∈ (0, T̂_k]`**
(`11_bootstrap.tex:390-484`; the real time is `t' = t♯_k + ū/A_k ∈ Ph_k`), with `C₀ = S.C0`,
`K₁ = S.K1`, `C_F = S.CF`, `η_{b,k} = S.etabK S.C0 S.K1 k`; for `u ∈ [0, ū]`:
* `eq:boot-inner`: `h^in_k(t̄♯_k + u) ∈ C^{M_h}(N')` with norm `≤ C_F κ♯_k ⟨u⟩^m` (for `k = n`,
  `h^in_n = 0`);
* (`lem:Oprime`) `h^out_k(t̄♯_k + u) ∈ C^{M_h}(N')` with norm `≤ η_{b,k} â_k(u)`;
* (Field) of `thm:active` on `[0, ū]` with `C₀` and `η_{b,k}` (`ActiveFieldK`);
* the hypotheses (i)–(iv) of `lem:drift` for ring `k`, `ū` and `η = η_{b,k}` (`DriftHyp`), and
  `C_ls η_{b,k} T̂_k ≤ 1/32`;
* (Coef) on `[0, ū]` (`CoefK`), and, if `ū = T̂_k`, `|c_k(T̂_k)|e^{σ_kT̂_k} ∈ [15δ₀/16, 17δ₀/16]`;
* the conclusions of `thm:active` and `cor:active-moment` for ring `k` on `[0, ū]`
  (`ActiveConclAt`; in particular `S_k(t'') ⊂ 𝒩_k` and `‖w_k(t'')‖_{H^s} ≤ C₂â_k(u)(1 + ρ̂_k(u))`
  for `t'' = t♯_k + u/A_k`). -/
structure ActiveStep (k : ℕ) (ubar : ℝ) : Prop where
  ubar_pos : 0 < ubar
  ubar_le : ubar ≤ S.P.That k
  inner : ∀ u ∈ Icc (0 : ℝ) ubar, MemCk S.Mh annN' (S.P.hIn k (S.P.tash k + u)) ∧
    S.etaIn k (S.P.tash k + u) ≤ S.CF * S.P.ksh k * Prelim.jap u ^ 3
  outer : ∀ u ∈ Icc (0 : ℝ) ubar, MemCk S.Mh annN' (S.P.hOut k (S.P.tash k + u)) ∧
    S.etaOut k (S.P.tash k + u) ≤ S.etabK S.C0 S.K1 k * S.ahatK k u
  field : S.ActiveFieldK S.C0 (S.etabK S.C0 S.K1 k) k ubar
  drift : S.DriftHyp k ubar (S.etabK S.C0 S.K1 k)
  cls : Eig.Cls S.P.χ * S.etabK S.C0 S.K1 k * S.P.That k ≤ 1 / 32
  coefK : S.CoefK S.C0 k ubar
  coef : ubar = S.P.That k →
    ‖S.P.runCoefK k (S.P.That k)‖ * Real.exp (S.P.sigma k * S.P.That k) ∈
      Icc (15 / 16 * S.P.δ₀) (17 / 16 * S.P.δ₀)
  concl : ∀ u ∈ Icc (0 : ℝ) ubar, S.ActiveConclAt S.C0 (S.etabK S.C0 S.K1 k) k u

/-! ### Steps 1–6 together (`11_bootstrap.tex:221-224`, `:251-260`, `:532-538`) -/

/-- **The conclusions of Steps 1–6 at the time `t ∈ [0, T_end]`** (`11_bootstrap.tex:221-224`,
`:251-260`, `:532-538`), i.e. what (BA°)(t) implies:
* Step 1: `lem:geometry` with `t` (`GeometryConcl t`);
* Step 2: `QuietStepAt t'` for every `t' ∈ [0, t]`;
* Step 3: `HandoffStep k` for every level `k < n` with `t♯_k` defined and `t♯_k ≤ t`;
* Step 4: `ActiveStep k (A_k(t' - t♯_k))` for every ring `k` with `T_k` defined and every
  `t' ∈ Ph_k ∩ [0, t]` with `t' > t♯_k`;
* Step 5: (BA2) with `Ā` at every `t' ∈ [0, t]`;
* Step 6: (BA)(t) and (BA*)(t). -/
structure BootStepsConcl (t : ℝ) : Prop where
  geom : S.GeometryConcl t
  quiet : ∀ t' ∈ Icc (0 : ℝ) t, S.QuietStepAt t'
  handoff : ∀ k ∈ Finset.Ico 1 S.P.n, S.P.ClockUpTo (k + 1) → S.P.tsh k ≤ t → S.HandoffStep k
  active : ∀ k ∈ Finset.Icc 1 S.P.n, S.P.ClockUpTo k → ∀ t' ∈ S.P.Phase k, S.P.tsh k < t' →
    t' ≤ t → S.ActiveStep k (S.P.activeTime k t')
  quiet_size : ∀ t' ∈ Icc (0 : ℝ) t, S.BA2At S.Abar t'
  ba : S.BA t
  ba_star : S.BAstar t

end Standing

end Relay

end NonUniqueEuler
