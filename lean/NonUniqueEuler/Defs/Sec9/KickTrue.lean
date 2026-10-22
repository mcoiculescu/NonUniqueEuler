import NonUniqueEuler.Defs.Sec9.Handoff

/-!
# Section 9.4: the kick on the true field — `lem:prehistory`, `lem:deep`, `lem:kicktrue`
(definitions)

Manuscript `09_relay.tex:1025-1397`.

* `lem:prehistory` (`:1042-1057`): `Relay.Cqr` (`C_qr = max(2^m, 4π)`) and the hypotheses
  `S.PrehistoryHyp j`;
* `lem:deep` (`:1103-1132`): `P.qRing k τ_K` (`q^ring`) and `P.qDeep k τ_K` (`q^deep`), functions of
  the kick time `τ_K` of ring `k`, and `S.Cdeep` (`C_deep`);
* `lem:kicktrue` (`:1179-1231`): `S.poutMax` (`max_{[0,G₁]}|pout_*|`), `S.Cid`, `S.Cod`, `S.Ctr C₀`
  (`C_id`, `C_od`, `C_tr(C₀)`), `P.kickQs k` (`q_s`), the inequalities (a)–(f)
  (`S.kickIneqA` … `S.kickIneqF`; (c)–(e) as functions of a generic `κ`, the form of (κ1)–(κ3) of
  `def:P5`), and the hypothesis list `S.KickTrueHyp C₀ K₁ k`.

Here `m = 3`. All lemmas here are fully proved.
-/

noncomputable section

open MeasureTheory Set Metric ComplexConjugate

namespace NonUniqueEuler

namespace Datum

namespace Approx

open RingData

variable (P : Approx)

/-- `q^ring = conj(Q_m[ω^{(n)}(t) 1_{S_{k+1}(t)}])/(A_{k+1} r_{k+1}^{m+2})` (`lem:deep`(1),
`09_relay.tex:1113`), as a function of the kick time `τ_K = A_{k+1}(t - T_{k+1})` of ring `k`
(`t = T_{k+1} + τ_K/A_{k+1}`, as in `P.qKick`). -/
def qRing (k : ℕ) (τK : ℝ) : ℂ :=
  conj (BS.Qm 3 fun x =>
      ((P.omegaRing (k + 1) (P.T (k + 1) + τK / P.A (k + 1)) x : ℝ) : ℂ)) /
    ((P.A (k + 1) * P.r (k + 1) ^ (3 + 2) : ℝ) : ℂ)

/-- `q^deep(τ_K) = μ s_{k+1}^{m+2} q_{k+2}(T_pin + μ(τ_K + T_g))`, `T_g = T̂_{k+1}`
(`lem:deep`(1), `09_relay.tex:1114`), the argument of `q_{k+2}` being the kick time of ring `k+1`
(`P.qKick (k + 1)`). For `k + 1 = n` it vanishes (`qDeep_of_succ_eq_n`). -/
def qDeep (k : ℕ) (τK : ℝ) : ℂ :=
  ((P.μ * P.s (k + 1) ^ (3 + 2) : ℝ) : ℂ) *
    P.qKick (k + 1) (P.Tpin + P.μ * (τK + P.That (k + 1)))

/-- The amplitude `q_s = 2π pout_*(G_{k+1}) c_{k+1}(T̂_{k+1}) e^{λ_{k+1} T̂_{k+1}}` of
`lem:kicktrue` (`09_relay.tex:1192-1193`). -/
def kickQs (k : ℕ) : ℂ :=
  2 * Real.pi * Eig.pout P.χ (P.G (k + 1)) * P.runCoefK (k + 1) (P.That (k + 1)) *
    Complex.exp (P.lam (k + 1) * P.That (k + 1))

/-! ### Basic lemmas (fully proved) -/

/-- `q_{n+1} = 0` (`D_{n+1} = ∅`). -/
theorem q_succ_n (t : ℝ) : P.q (P.n + 1) t = 0 := by
  simp [q, omegaGe_succ_n, BS.Qm]

/-- `q^deep ≡ 0` if `k + 1 = n` (`lem:deep`(1), `09_relay.tex:1116-1117`). -/
theorem qDeep_of_succ_eq_n {k : ℕ} (hk : k + 1 = P.n) (τK : ℝ) : P.qDeep k τK = 0 := by
  simp only [qDeep, qKick]
  rw [show k + 1 + 1 = P.n + 1 by omega, q_succ_n, mul_zero]

end Approx

end Datum

namespace Relay

open RingData Datum

/-- `C_qr = max(2^m, 4π)` (`lem:prehistory`, `09_relay.tex:1044`). -/
def Cqr : ℝ := max (2 ^ 3) (4 * Real.pi)

namespace Standing

variable (S : Standing)

/-! ### `lem:prehistory` (`09_relay.tex:1042-1057`) -/

/-- **The hypotheses of `lem:prehistory`** for the level `j` (`09_relay.tex:1044-1050`; (SA) is
separate): `2 ≤ j < n`, the clock is defined up to level `j+1`, and the hypotheses of
`thm:quiet` hold for ring `j` on `[0, t̄♯_j]` (`QuietHyp`, which contains `D_{j+1}(t) ⊂ B_{ar_j/8}`
and the rings `i < j` outside `B_{6r_j}` for `t ∈ [0, t♯_j]`). -/
structure PrehistoryHyp (j : ℕ) : Prop where
  two_le : 2 ≤ j
  lt_n : j < S.P.n
  clock : S.P.ClockUpTo (j + 1)
  quiet : S.QuietHyp j (S.P.tash j)

/-! ### `lem:deep` (`09_relay.tex:1103-1132`) -/

/-- `C_deep = 4μ C_mom (1 + T_pin + 32/(15σ))^m/(σ K_lo)` (`lem:deep`(3), `09_relay.tex:1128`). -/
def Cdeep : ℝ :=
  4 * S.P.μ * Rings.Cmom * (1 + S.P.Tpin + 32 / (15 * S.sigma0)) ^ 3 / (S.sigma0 * S.Klo)

/-! ### `lem:kicktrue` (`09_relay.tex:1179-1231`) -/

/-- `max_{G ∈ [0,G₁]} |pout_*(G)|` (`09_relay.tex:1184-1185`), as a supremum (attained, `lem:uniform`). -/
def poutMax : ℝ := sSup ((fun G => ‖Eig.pout S.P.χ G‖) '' Icc 0 Gbar)

/-- `C_id = 4π(17/16)^m max_{[0,G₁]}|pout_*|` (`09_relay.tex:1184`). -/
def Cid : ℝ := 4 * Real.pi * (17 / 16) ^ 3 * S.poutMax

/-- `C_od = (32π/9) C_ls max_{[0,G₁]}|pout_*|` (`09_relay.tex:1185`). -/
def Cod : ℝ := 32 * Real.pi / 9 * Eig.Cls S.P.χ * S.poutMax

/-- `C_tr(C₀) = (32πC₃/(15σ))(1 + 16/(15σ))^m C(C₀)` (`09_relay.tex:1186`). -/
def Ctr (C₀ : ℝ) : ℝ :=
  32 * Real.pi * S.C3 / (15 * S.sigma0) * (1 + 16 / (15 * S.sigma0)) ^ 3 * S.Cact C₀

/-- Inequality **(a)** of `lem:kicktrue` (`09_relay.tex:1212`):
`(16/15)(2πC₃δ₀²/σ) ≤ (1/4)(15/16) c_out δ₀/(20|z|)`. -/
def kickIneqA : Prop :=
  16 / 15 * (2 * Real.pi * S.C3 * S.P.δ₀ ^ 2 / S.sigma0) ≤
    1 / 4 * (15 / 16) * (Eig.cout S.P.χ * S.P.δ₀ / (20 * ‖S.z‖))

/-- Inequality **(b)** of `lem:kicktrue` (`09_relay.tex:1213`):
`μ - 1 ≤ (15/16) c_out δ₀/(10|z| C_mom I_m(σ/4))`. -/
def kickIneqB : Prop :=
  S.P.μ - 1 ≤ 15 / 16 * Eig.cout S.P.χ * S.P.δ₀ / (10 * ‖S.z‖ * Rings.Cmom * Ip 3 (S.sigma0 / 4))

/-- Inequality **(c)** of `lem:kicktrue` for `κ` (`09_relay.tex:1214`; (κ1) of `def:P5`):
`κ ≤ δ₀ 4^{-μ/(μ-1)}`. -/
def kickIneqC (κ : ℝ) : Prop := κ ≤ S.P.δ₀ * (4 : ℝ) ^ (-(S.P.μ / (S.P.μ - 1)))

/-- Inequality **(d)** of `lem:kicktrue` for `κ` (`09_relay.tex:1215-1219`; (κ2) of `def:P5`):
`2πC₃κ^{1/2}μ/((3/4)σ(μ-1)) + C_tr(C₀)(κ/δ₀)^{γ_μ} log^{m+1}(δ₀/κ)
 + [C_deep + C_id r_T(T_pin) I_m(σ/8)](κ/δ₀)^{ϑ_μ} log^m(δ₀/κ) ≤ ½ (15/16) c_out/(20|z|(μ-1))`. -/
def kickIneqD (C₀ κ : ℝ) : Prop :=
  2 * Real.pi * S.C3 * Real.sqrt κ * S.P.μ / (3 / 4 * S.sigma0 * (S.P.μ - 1)) +
      S.Ctr C₀ * (κ / S.P.δ₀) ^ S.gammaMu * Real.log (S.P.δ₀ / κ) ^ (3 + 1) +
      (S.Cdeep + S.Cid * S.rT S.P.Tpin * Ip 3 (S.sigma0 / 8)) * (κ / S.P.δ₀) ^ S.varthetaMu *
        Real.log (S.P.δ₀ / κ) ^ 3 ≤
    1 / 2 * (15 / 16) * (Eig.cout S.P.χ / (20 * ‖S.z‖ * (S.P.μ - 1)))

/-- Inequality **(e)** of `lem:kicktrue` for `K₁` and `κ` (`09_relay.tex:1220`; (κ3) of `def:P5`
with `K₁ = S.K1`): `C_qr(4μC_{L1}C_Q/(3σ(μ-1)) + 1) K₁ (κ/δ₀)^{ϑ_μ} ≤ (15/16) c_out/(20|z|(μ-1))`. -/
def kickIneqE (K₁ κ : ℝ) : Prop :=
  Cqr * (4 * S.P.μ * Rings.CL1 * S.CQ / (3 * S.sigma0 * (S.P.μ - 1)) + 1) * K₁ *
      (κ / S.P.δ₀) ^ S.varthetaMu ≤
    15 / 16 * (Eig.cout S.P.χ / (20 * ‖S.z‖ * (S.P.μ - 1)))

/-- Inequality **(f)** of `lem:kicktrue` (`09_relay.tex:1221-1222`; second part of (B11)), with
`η_b = S.etab C₀ K₁`: `C_od η_b δ₀ μ²/(σ²(μ-1)²) + 2πC₃η_b 4μδ₀/(3σ(μ-1))
 ≤ (1/4)(15/16) c_out δ₀/(20|z|(μ-1))`. -/
def kickIneqF (C₀ K₁ : ℝ) : Prop :=
  S.Cod * S.etab C₀ K₁ * S.P.δ₀ * (S.P.μ ^ 2 / (S.sigma0 ^ 2 * (S.P.μ - 1) ^ 2)) +
      2 * Real.pi * S.C3 * S.etab C₀ K₁ * (4 * S.P.μ * S.P.δ₀ / (3 * S.sigma0 * (S.P.μ - 1))) ≤
    1 / 4 * (15 / 16) * (Eig.cout S.P.χ * S.P.δ₀ / (20 * ‖S.z‖ * (S.P.μ - 1)))

/-- **The hypotheses of `lem:kicktrue`** for the level `k` and the constants `C₀`, `K₁`
(`09_relay.tex:1189-1224`; (SA), (Det), `C₀ ≥ 1`, `K₁ > 0`, `1 ≤ k < n` and the clock defined up to
level `k+1` are separate), with `κ = κ♯_{k+1}`, `T_g = T̂_{k+1}`, `η_b = S.etab C₀ K₁`:
* `D_{k+1}(t) ⊂ B_{ar_k/8}` for `t ∈ [0, t♯_k]` (the hypotheses of `lem:coupling`(2));
* the conclusions of `thm:active` and `cor:active-moment` hold for ring `k+1` on `Ph_{k+1}` with the
  constant `C₀` and `η_b`;
* the hypotheses (i)–(iv) of `lem:drift` hold for ring `k+1` with `ū = T̂_{k+1}` and some
  `η ∈ [0, η_b]` with `C_ls η T̂_{k+1} ≤ 1/32`, and `r_T(T_pin) ≤ 1/64`;
* if `k+1 < n`: the hypotheses of `lem:prehistory` for `j = k+1`, `maj_{k+1}(t̄♯_{k+1}) ≤ K₁κ`, the
  hypotheses of `lem:deep`(2) (those of `prop:confine` at level `k+1` with `t₁ = T_{k+1}`), and
  `κ ≥ K_lo s_{k+1}^{m+2}`;
* `|q_{k+1}| ≤ C_mom(1 + τ_K)^m` for kick times `τ_K ∈ [0, T_pin]`;
* the inequalities (a)–(f). -/
structure KickTrueHyp (C₀ K₁ : ℝ) (k : ℕ) : Prop where
  hin : ∀ t ∈ Icc (0 : ℝ) (S.P.tsh k), S.P.HInDefined k t
  active : S.ActiveConcl C₀ (S.etab C₀ K₁) (k + 1)
  drift : ∃ η ∈ Icc (0 : ℝ) (S.etab C₀ K₁), S.DriftHyp (k + 1) (S.P.That (k + 1)) η ∧
    Eig.Cls S.P.χ * η * S.P.That (k + 1) ≤ 1 / 32
  rT_le : S.rT S.P.Tpin ≤ 1 / 64
  deeper : k + 1 < S.P.n →
    S.PrehistoryHyp (k + 1) ∧ S.maj (k + 1) (S.P.tash (k + 1)) ≤ K₁ * S.P.ksh (k + 1) ∧
      S.P.ConfineHyp (k + 1) (S.P.T (k + 1)) ∧ S.Klo * S.P.s (k + 1) ^ (3 + 2) ≤ S.P.ksh (k + 1)
  pin : ∀ τK ∈ Icc (0 : ℝ) S.P.Tpin, ‖S.P.qKick k τK‖ ≤ Rings.Cmom * (1 + τK) ^ 3
  ineqA : S.kickIneqA
  ineqB : S.kickIneqB
  ineqC : S.kickIneqC (S.P.ksh (k + 1))
  ineqD : S.kickIneqD C₀ (S.P.ksh (k + 1))
  ineqE : S.kickIneqE K₁ (S.P.ksh (k + 1))
  ineqF : S.kickIneqF C₀ K₁

/-! ### Basic lemmas (fully proved) -/

theorem Cdeep_def : S.Cdeep =
    4 * S.P.μ * Rings.Cmom * (1 + S.P.Tpin + 32 / (15 * S.sigma0)) ^ 3 / (S.sigma0 * S.Klo) := rfl

theorem Ctr_def (C₀ : ℝ) : S.Ctr C₀ =
    32 * Real.pi * S.C3 / (15 * S.sigma0) * (1 + 16 / (15 * S.sigma0)) ^ 3 * S.Cact C₀ := rfl

end Standing

theorem Cqr_pos : 0 < Cqr := lt_max_of_lt_left (by norm_num)

end Relay

end NonUniqueEuler
