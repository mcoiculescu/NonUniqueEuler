import NonUniqueEuler.Defs.Sec9.QuietRings

/-!
# Section 9.3: the active ring and the hand-off — `lem:drift`, `lem:handoff`, `def:K1` (definitions)

Manuscript `09_relay.tex:741-1023`.

* `lem:drift` (`:769-801`): the hypotheses (i)–(iv) `S.DriftHyp k ū η` (used again by
  `lem:kicktrue` for ring `k+1`);
* `lem:handoff` (`:863-885`): the hypotheses (i)–(iv) `S.HandoffHyp θ K₁ k`;
* `def:K1` (`:931-945`): `S.cK` (`c_K`), `S.K1` (`K_1`), `S.Abar` (`Ā`), `S.Klo` (`K_lo`), `S.Kup`
  (`K_up`), `S.Chand` (`C_hand = K₁C_Q`).

`lem:K1` and `cor:amp` need no new definition. Here `m = 3`. All lemmas here are fully proved.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

open RingData Datum

namespace Standing

variable (S : Standing)

/-! ### `lem:drift` (`09_relay.tex:769-801`) -/

/-- **The hypotheses (i)–(iv) of `lem:drift`** for the level `k`, `ū` and `η`
(`09_relay.tex:772-785`; (SA), (Det), `1 ≤ k ≤ n`, the clock defined up to level `k`,
`0 ≤ ū ≤ T̂_k` and `η ≥ 0` are separate):
* (i) if `k < n`: `|q_{k+1}| ≤ C_mom(1 + τ_K)^m` for kick times `τ_K ∈ [T_pin, T_pin + μū]`;
* (ii) if `k < n`: the hypotheses of `lem:coupling`(2) (`D_{k+1}(t) ⊂ B_{ar_k/8}` for
  `t ∈ [0, t♯_k]`; the clock up to level `k+1` follows from the clock up to level `k`),
  `κ♯_k ≥ ½ e^{x_k T_pin}|A^in(T_pin)|`, and there is `q' ≠ 0` with
  `|A^in(T_pin)| ≥ |β_k||q'|/(10|z|(μ-1))` and `μ - 1 ≤ |q'|/(10|z| C_mom I_m(σ/4))`;
* (iii) `‖h^out_k(t̄♯_k + u)‖_{C^0(N')} ≤ η â_k(u)` for `u ∈ [0, ū]`;
* (iv) for `t ∈ [t♯_k, t♯_k + ū/A_k]`: `D_{k+1}(t) ⊂ B_{ar_k/8}` and the rings `i < k` lie outside
  `B_{6r_k}` (`HDefined`), so that `h_k` and `c_k` are defined there.
The conclusions are about `c_k = P.runCoefK k`; (Coef) is `S.CoefK`. -/
structure DriftHyp (k : ℕ) (ubar η : ℝ) : Prop where
  moment : k < S.P.n → ∀ τK ∈ Icc S.P.Tpin (S.P.Tpin + S.P.μ * ubar),
    ‖S.P.qKick k τK‖ ≤ Rings.Cmom * (1 + τK) ^ 3
  kick : k < S.P.n →
    (∀ t ∈ Icc (0 : ℝ) (S.P.tsh k), S.P.HInDefined k t) ∧
      1 / 2 * Real.exp (S.P.xk k * S.P.Tpin) * ‖S.P.Ain k S.P.Tpin‖ ≤ S.P.ksh k ∧
      ∃ q' : ℂ, q' ≠ 0 ∧
        ‖S.P.betaK k‖ * ‖q'‖ / (10 * ‖S.z‖ * (S.P.μ - 1)) ≤ ‖S.P.Ain k S.P.Tpin‖ ∧
        S.P.μ - 1 ≤ ‖q'‖ / (10 * ‖S.z‖ * Rings.Cmom * Ip 3 (S.sigma0 / 4))
  outer : ∀ u ∈ Icc (0 : ℝ) ubar,
    normCk 0 annN' (S.P.hOut k (S.P.tash k + u)) ≤ η * S.ahatK k u
  geom : ∀ t ∈ Icc (S.P.tsh k) (S.P.tsh k + ubar / S.P.A k), S.P.HDefined k t

/-! ### `lem:handoff` (`09_relay.tex:863-885`) -/

/-- **The hypotheses (i)–(iv) of `lem:handoff`** for the level `k`, a number `θ` (the `θ_k` of the
lemma) and `K₁` (`09_relay.tex:866-876`; (SA), (Det), `K₁ > 0`, `1 ≤ k < n` and the clock defined
up to level `k+1` are separate):
* (i) the hypotheses of `thm:quiet` hold for ring `k` on `[0, t̄♯_k]` (`QuietHyp`; it contains
  `D_{k+1}(t) ⊂ B_{ar_k/8}` and the rings `i < k` outside `B_{6r_k}` for `t ∈ [0, t♯_k]`);
* (ii) `θ ≥ 0`, `η^out_k ≤ θ maj_k` on `[0, t̄♯_k]` and `C_ls θ t̄♯_k K₁ ≤ 1/4`;
* (iii) `maj_k(t̄♯_k) ≤ ½ K₁|c^in_k|`;
* (iv) `‖ℓ_*‖ C_Q K₁ maj_k(t̄♯_k) ≤ ½`.
The conclusion `eq:handoff` has `C_hand = K₁C_Q` for this `K₁`. -/
structure HandoffHyp (θ K₁ : ℝ) (k : ℕ) : Prop where
  quiet : S.QuietHyp k (S.P.tash k)
  θ_nonneg : 0 ≤ θ
  etaOut_le : ∀ τ ∈ Icc (0 : ℝ) (S.P.tash k), S.etaOut k τ ≤ θ * S.maj k τ
  theta_small : Eig.Cls S.P.χ * θ * S.P.tash k * K₁ ≤ 1 / 4
  maj_le_cin : S.maj k (S.P.tash k) ≤ 1 / 2 * K₁ * ‖S.P.cinK k‖
  maj_small : Eig.ellNorm S.P.χ * S.CQ * K₁ * S.maj k (S.P.tash k) ≤ 1 / 2

/-! ### `def:K1` (`09_relay.tex:931-945`) -/

/-- `c_K = 3c_N/(32μ)` (`def:K1`, `09_relay.tex:933`). -/
def cK : ℝ := 3 * Eig.cN S.P.χ / (32 * S.P.μ)

/-- `K_1 = (8C_M|z|/c_K)[(4C₂+1)/σ_b + C_D(T_pin)(μ-1)/δ₀]` (`eq:K1`, `09_relay.tex:937`). -/
def K1 : ℝ :=
  8 * S.CM * ‖S.z‖ / S.cK * ((4 * S.C2 + 1) / S.sigb + CD S.P.Tpin * (S.P.μ - 1) / S.P.δ₀)

/-- `Ā = 2C_M e^{17σT_pin/16}[(4C₂+1)δ₀/(σ_b(μ-1)) + C_D(T_pin)]` (`eq:K1`, `09_relay.tex:938`). -/
def Abar : ℝ :=
  2 * S.CM * Real.exp (17 * S.sigma0 * S.P.Tpin / 16) *
    ((4 * S.C2 + 1) * S.P.δ₀ / (S.sigb * (S.P.μ - 1)) + CD S.P.Tpin)

/-- `K_lo = c_N δ₀/(22|z|(μ-1))` (`def:K1`, `09_relay.tex:943`). -/
def Klo : ℝ := Eig.cN S.P.χ * S.P.δ₀ / (22 * ‖S.z‖ * (S.P.μ - 1))

/-- `K_up = (5C_N δ₀ μ/(|z|(μ-1))) e^{17σT_pin/16}` (`def:K1`, `09_relay.tex:943`). -/
def Kup : ℝ :=
  5 * Eig.CN S.P.χ * S.P.δ₀ * S.P.μ / (‖S.z‖ * (S.P.μ - 1)) *
    Real.exp (17 * S.sigma0 * S.P.Tpin / 16)

/-- `C_hand = K_1 C_Q` with the `K_1` of `def:K1` (`09_relay.tex:943`; in `lem:handoff` the same
formula is used with the lemma's `K₁`). -/
def Chand : ℝ := S.K1 * S.CQ

/-! ### Basic lemmas (fully proved) -/

theorem cK_def : S.cK = 3 * Eig.cN S.P.χ / (32 * S.P.μ) := rfl

theorem K1_def : S.K1 =
    8 * S.CM * ‖S.z‖ / S.cK * ((4 * S.C2 + 1) / S.sigb + CD S.P.Tpin * (S.P.μ - 1) / S.P.δ₀) :=
  rfl

theorem Abar_def : S.Abar = 2 * S.CM * Real.exp (17 * S.sigma0 * S.P.Tpin / 16) *
    ((4 * S.C2 + 1) * S.P.δ₀ / (S.sigb * (S.P.μ - 1)) + CD S.P.Tpin) := rfl

theorem Klo_def : S.Klo = Eig.cN S.P.χ * S.P.δ₀ / (22 * ‖S.z‖ * (S.P.μ - 1)) := rfl

theorem Kup_def : S.Kup = 5 * Eig.CN S.P.χ * S.P.δ₀ * S.P.μ / (‖S.z‖ * (S.P.μ - 1)) *
    Real.exp (17 * S.sigma0 * S.P.Tpin / 16) := rfl

theorem Chand_def : S.Chand = S.K1 * S.CQ := rfl

theorem ahatK_nonneg (k : ℕ) (u : ℝ) : 0 ≤ S.ahatK k u :=
  mul_nonneg (S.P.ksh_nonneg k) (Real.exp_pos _).le

variable {S}

theorem DriftHyp.mono {k : ℕ} {ubar ubar' η η' : ℝ} (h : S.DriftHyp k ubar η) (hu : ubar' ≤ ubar)
    (hη : η ≤ η') (hA : 0 ≤ S.P.A k) (hμ : 0 ≤ S.P.μ) : S.DriftHyp k ubar' η' where
  moment hk τK hτ := h.moment hk τK ⟨hτ.1, hτ.2.trans (by
    have := mul_le_mul_of_nonneg_left hu hμ
    linarith)⟩
  kick := h.kick
  outer u hu' := (h.outer u ⟨hu'.1, hu'.2.trans hu⟩).trans
    (mul_le_mul_of_nonneg_right hη (S.ahatK_nonneg k u))
  geom t ht := h.geom t ⟨ht.1, ht.2.trans (by gcongr)⟩

end Standing

end Relay

end NonUniqueEuler
