import NonUniqueEuler.Defs.Sec9.All

/-!
# Section 10: the parameter lists (P0)–(P6) (definitions)

Manuscript `10_parameters.tex`:
`def:P0-P4` (`:20-71`), `def:P5` (`:96-120`), `def:P6` (`:132-168`) with `eq:E22` (`:151-154`),
and the constants they introduce.

The conditions are Props on a standing datum `S : Relay.Standing` (the parameters
`χ, s, σ', δ₀, μ, T_pin, κ_seed, s̄` are `S.P.χ, S.s, S.σ', S.P.δ₀, S.P.μ, S.P.Tpin, S.P.κs,
S.P.sbar`). Every constant they use is a function of the parameters only: none reads
`S.P.A₁`, `S.P.n` or `S.P.om` (so the lists do not depend on `A₁`, `n`, `ω^{(n)}`;
`Params.lists_iff` in `Defs/Sec10/Params.lean` checks this: the fields for two standing data
with the same parameters are definitionally equal), and each list reads only the parameters
chosen at earlier steps (Table `tab:param`; `Params.structural_with`, `Params.kappaOK_with_iff`).

* the structural list (P0)–(P4): `CondP0` ((P0.2) = (SA1)), `deltaKick`, `deltaRd`, `CondP1`,
  `cPrime`, `muMax`, `CondP2`, `CondP3`, `CF` (`C_F`), `C0` (`C_0` of (P4)), `StructuralList`;
  every other constant of (P0)–(P4) is already a definition of Sections 4–9;
* the κ-list (P5): `Cpre` (`C_pre`), `CondKappa κ` ((κ1)–(κ7) at one amplitude `κ`),
  `KappaList κs` (`κs > 0` and (κ1)–(κ7) for every `κ ∈ (0, 2κs]`);
* the s̄-list (P6): `Lconf k` (`Λ^conf_k`), `CondE22` (`eq:E22`), `CondB7`, `SbarList`;
* `ParamLists`: (P0)–(P6) together.

Here `m = p = p_K = 3` is the literal `3`. All lemmas here are fully proved.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

open RingData Datum

namespace Standing

variable (S : Standing)

/-! ### The structural list (P0)–(P4) (`def:P0-P4`, `10_parameters.tex:20-71`) -/

/-- **(P0.2)**: an integer `s` and a number `σ'` as in (SA1) (`10_parameters.tex:30-31`,
`09_relay.tex:33`): `s ≥ 3` and `σ' ∈ (9/200, min(σ_b, 3σ/4))`. The rest of (P0) fixes
constants that are definitions. -/
structure CondP0 : Prop where
  three_le_s : 3 ≤ S.s
  σ'_gt : 9 / 200 < S.σ'
  σ'_lt_sigb : S.σ' < Eig.sigb S.P.χ
  σ'_lt_sigma : S.σ' < 3 / 4 * Eig.sigma S.P.χ 0

/-- `δ_kick = 225 σ c_out / (40960 π |z| C₃)` ((P1), `10_parameters.tex:49`). -/
def deltaKick : ℝ := 225 * S.sigma0 * Eig.cout S.P.χ / (40960 * Real.pi * ‖S.z‖ * S.C3)

/-- `δ_rd = c_out / (16 π C_p C₂)` ((P1), `10_parameters.tex:49`). -/
def deltaRd : ℝ := Eig.cout S.P.χ / (16 * Real.pi * Eig.Cp * S.C2)

/-- **(P1)** (`10_parameters.tex:47-53`): `δ₀ ∈ (0, min(d_H, δ_kick, δ_rd)]`, written as three
upper bounds (`CondP1.mem_Ioc_min`). -/
structure CondP1 : Prop where
  δ₀_pos : 0 < S.P.δ₀
  δ₀_le_dH : S.P.δ₀ ≤ S.dH
  δ₀_le_kick : S.P.δ₀ ≤ S.deltaKick
  δ₀_le_rd : S.P.δ₀ ≤ S.deltaRd

/-- `c' = (15/16) c_out / (10 |z| Q̄ I_{p_K}(σ/4))`, `(Q̄, p_K) = (C_mom, 3)` ((P2),
`10_parameters.tex:56`). -/
def cPrime : ℝ :=
  15 / 16 * (Eig.cout S.P.χ / (10 * ‖S.z‖ * Rings.Cmom * Ip 3 (S.sigma0 / 4)))

/-- `μ_max = 1 + min(c'δ₀, 1/16)` ((P2), `10_parameters.tex:55`). -/
def muMax : ℝ := 1 + min (S.cPrime * S.P.δ₀) (1 / 16)

/-- **(P2)** (`10_parameters.tex:54-58`): `μ ∈ (1, μ_max]`. The quantities fixed after it
(`ϑ_μ`, `γ_μ`, `γ'_μ`, `C_Duh`, `K_O`) are `S.varthetaMu`, `S.gammaMu`, `S.gammaMu'`, `S.CDuh`,
`S.KO`. -/
structure CondP2 : Prop where
  one_lt_μ : 1 < S.P.μ
  μ_le : S.P.μ ≤ S.muMax

/-- **(P3)** (`10_parameters.tex:59-65`): `T_pin > 0` with `r_T(T_pin) ≤ 1/64`. The quantities
fixed after it are `CD S.P.Tpin`, `S.cK`, `S.K1`, `S.Abar`, `S.Klo`, `S.Kup`, `S.Chand`, `S.CF`,
`S.Cdeep`, `S.Tz`, `S.Ctau`. -/
structure CondP3 : Prop where
  Tpin_pos : 0 < S.P.Tpin
  rT_le : S.rT S.P.Tpin ≤ 1 / 64

/-- `C_F = C_in μ (2 + 2C_* T_pin)^m (1 + 2C_*)^m / K_lo` ((P3), `10_parameters.tex:63`; the
constant of `eq:boot-inner`, `11_bootstrap.tex:429-434`). -/
def CF : ℝ := S.Cin * S.P.μ * (2 + 2 * Cstar * S.P.Tpin) ^ 3 * (1 + 2 * Cstar) ^ 3 / S.Klo

/-- **`C₀ = max{1, 2C_seed, C_hand, C_F}`** ((P4), `10_parameters.tex:66`), with `C_seed` of
`lem:seed` for the index `s` (`OneRing.Cseed`), `C_hand = K₁C_Q` and `C_F` of (P3). The quantities
fixed after it are `S.kappa0 S.C0`, `OneRing.tOneBar S.P.χ S.σ' S.C0`, `S.Cact S.C0`, `S.Ctr S.C0`,
`S.CXi S.C0 S.K1`, `S.Cop S.C0 S.K1`. Not to be confused with `S.c0 = ½A₁c_outδ₀`. -/
def C0 : ℝ := max (max (max 1 (2 * OneRing.Cseed S.P.χ S.s)) S.Chand) S.CF

/-- **The structural list (P0)–(P4)** (`def:P0-P4`): the conditions on the choices `s, σ'`
((P0.2)), `δ₀` ((P1)), `μ` ((P2)) and `T_pin` ((P3)); (P4) fixes `C₀ = S.C0` without a
condition. -/
structure StructuralList : Prop where
  p0 : S.CondP0
  p1 : S.CondP1
  p2 : S.CondP2
  p3 : S.CondP3

/-! ### The κ-list (P5) (`def:P5`, `10_parameters.tex:96-120`) -/

/-- `C_pre = C_qr (4μ C_{L1} C_Q/(3σ(μ-1)) + 1) K_1` ((κ3), `10_parameters.tex:109`), with `K_1`
of `def:K1`. -/
def Cpre : ℝ := Cqr * (4 * S.P.μ * Rings.CL1 * S.CQ / (3 * S.sigma0 * (S.P.μ - 1)) + 1) * S.K1

/-- **The conditions (κ1)–(κ7) of the κ-list (P5) at the amplitude `κ`**
(`10_parameters.tex:100-119`), with `C₀ = S.C0` of (P4) and `K_1 = S.K1` of `def:K1`:
* (κ1) `κ ≤ δ₀ 4^{-μ/(μ-1)}` (`kickIneqC`, hypothesis (c) of `lem:kicktrue`);
* (κ2) the three-term bound of hypothesis (d) of `lem:kicktrue` with `C_tr(C₀)` (`kickIneqD`);
* (κ3) `C_pre (κ/δ₀)^{ϑ_μ} ≤ (15/16) c_out/(20|z|(μ-1))` (`kickIneqE` with `K_1`, `Cpre`);
* (κ4) `κ ≤ κ₀(C₀)`;
* (κ5) for every `G ∈ [0, G₁]`, with `ρ̂` the transient of `thm:active` for `(C₀, G)` and
  `T̂ = σ(G)⁻¹ log(δ₀/κ)`: `C_p C₂ (ρ̂(T̂) + κ^{1/2}) ≤ c_out/(16π)`;
* (κ6) `κ ≤ κ_L`;
* (κ7) `C_Ξ(C₀,K₁)(1 + 1/(σ_b(μ-1)))(κ/δ₀)^{γ'_μ} ⟨log(δ₀/κ)⟩^{m+1} ≤ 1/(σ_b(μ-1))`. -/
structure CondKappa (κ : ℝ) : Prop where
  k1 : S.kickIneqC κ
  k2 : S.kickIneqD S.C0 κ
  k3 : S.kickIneqE S.K1 κ
  k4 : κ ≤ S.kappa0 S.C0
  k5 : ∀ G ∈ Icc (0 : ℝ) Gbar,
    Eig.Cp * S.C2 * (OneRing.rhoHat S.P.χ S.σ' S.C0 G
        (OneRing.That (Eig.sigma S.P.χ G) S.P.δ₀ κ) + Real.sqrt κ) ≤
      Eig.cout S.P.χ / (16 * Real.pi)
  k6 : κ ≤ OneRing.kL S.P.χ
  k7 : S.CXi S.C0 S.K1 * (1 + 1 / (S.sigb * (S.P.μ - 1))) * (κ / S.P.δ₀) ^ S.gammaMu' *
      Prelim.jap (Real.log (S.P.δ₀ / κ)) ^ (3 + 1) ≤ 1 / (S.sigb * (S.P.μ - 1))

/-- **The κ-list (P5)** for the seed size `κs` (`def:P5`, `10_parameters.tex:98-99`): `κs > 0`, and
(κ1)–(κ7) hold for every `κ ∈ (0, 2κs]`. For a standing datum the seed size is `S.P.κs`
(`ParamLists`); the argument lets one speak of the set of admissible seed sizes
(`lem:nonempty`). -/
def KappaList (κs : ℝ) : Prop := 0 < κs ∧ ∀ κ ∈ Ioc (0 : ℝ) (2 * κs), S.CondKappa κ

/-! ### The s̄-list (P6) (`def:P6`, `10_parameters.tex:132-168`) -/

/-- `Λ^conf_k = 2 + 2C_*μ[T_pin + 1 + σ'⁻¹((m+2) log(1/s_k) + log₊(δ₀/K_lo))]` ((B5),
`10_parameters.tex:145-146`), written `2 + 2C_*(μ[…])` (the form of `lem:window-length`). -/
def Lconf (k : ℕ) : ℝ :=
  2 + 2 * Cstar * (S.P.μ * (S.P.Tpin + 1 + 1 / S.σ' *
    ((3 + 2) * Real.log (1 / S.P.s k) + Real.posLog (S.P.δ₀ / S.Klo))))

/-- **Equation `eq:E22`** (`10_parameters.tex:151-154`):
`K_O s̄^{2m}[T_z + 2 log(1/s̄) + 1/(μ-1)] ≤ (μ-1)/(4C_OC_QC_τ) · min{1/2, 1/(4C_ls K_1)}`,
written multiplicatively:
`4C_OC_QC_τ · K_O s̄^{2m}[T_z + 2 log(1/s̄) + 1/(μ-1)] ≤ (μ-1) · min{1/2, 1/(4C_ls K_1)}`.
This is equivalent to the manuscript's form when `C_OC_QC_τ > 0` (`condE22_iff_div`). It is the
form `lem:theta-quiet` uses (`10_parameters.tex:268-272`, which multiplies by `4C_OC_QC_τ/(μ-1)`).
It avoids Lean's `x/0 = 0`: the constant `C_Q` of `thm:quiet` is only specified with `C_Q ≥ 0`
(`OneRing.IsQuietConst`, junk `0`). If `C_Q = 0`, the division form would demand
`… ≤ 0` and fail for every `s̄ > 0`. Under the manuscript's reading the right side is `+∞`, and the
condition is vacuous, as it is here. -/
def CondE22 : Prop :=
  4 * S.CO * S.CQ * S.Ctau *
      (S.KO * S.P.sbar ^ (2 * 3) * (S.Tz + 2 * Real.log (1 / S.P.sbar) + 1 / (S.P.μ - 1))) ≤
    (S.P.μ - 1) * min (1 / 2) (1 / (4 * Eig.Cls S.P.χ * S.K1))

/-- **(B7)** (`10_parameters.tex:149-154`): the three smallness conditions of `lem:O`
(`OSmall`: `16C_OC_QC_DuhK_Os̄^{2m} ≤ 1`, `K_Os̄^{2m} ≤ 1/4`, `K_Oμs̄^{m+2} ≤ 1/2`) and `eq:E22`. -/
structure CondB7 : Prop where
  small : S.OSmall
  e22 : S.CondE22

/-- **The s̄-list (P6)** (`def:P6`, `10_parameters.tex:132-167`), with `s_k = S.P.s k`,
`η_{b,1} = 0` and `η_{b,k} = S.etabK S.C0 S.K1 k`, `η_b = S.etab S.C0 S.K1` (`eq:etab` with the
constants of (P4) and `def:K1`):
* (B1) `s̄ ≤ a/16`, `s̄^{m-2} ≤ 1/2`; (B2) `μ⁴s̄² ≤ 1/8`; (B3) `C_Gμs̄² ≤ G₁`; (B4) (Det);
* (B5) for every `k ≥ 1`: `Λ^conf_k s_k ≤ a/8` and `(8/3)(2/a)^m (Λ^conf_k)^{m-1} s_k^{m-2} ≤ μC_*`;
* (B6) `K_up s̄^{m+2} ≤ κ_seed`; (B7) `CondB7`;
* (B8) `η_b ≤ ½η_max`; for every `k ≥ 2`,
  `(C_ls η_{b,k}/σ')[(m+2) log(1/s_k) + log₊(δ₀/K_lo)] ≤ 1/32`; `C_ls η_b σ'⁻¹ log(2δ₀/κ_seed) ≤ 1/32`;
* (B9) `2Āμs̄^{m+2} ≤ maj_*` and `C_η(μs̄² + s̄^{m-2}) ≤ 1` (`C_η = Rings.Ceta χ M_h`);
* (B10) `4C_M(2C_Q/(σ_b(μ-1)) + 1)μs̄^{m+2} ≤ 1/2`;
* (B11) `‖ℓ_*‖C_QK_1Āμs̄^{m+2} ≤ 1/2` and hypothesis (f) of `lem:kicktrue` (`kickIneqF`).
The positivity `s̄ > 0` ("choose `s̄ > 0`", `:134`) is the field `sbar_pos`. -/
structure SbarList : Prop where
  sbar_pos : 0 < S.P.sbar
  b1_le : S.P.sbar ≤ a / 16
  b1_pow : S.P.sbar ^ (3 - 2) ≤ 1 / 2
  b2 : S.P.μ ^ 4 * S.P.sbar ^ 2 ≤ 1 / 8
  b3 : CG S.P.χ * S.P.μ * S.P.sbar ^ 2 ≤ Gbar
  b4 : S.Det
  b5 : ∀ k : ℕ, 1 ≤ k → S.Lconf k * S.P.s k ≤ a / 8 ∧
    8 / 3 * (2 / a) ^ 3 * S.Lconf k ^ (3 - 1) * S.P.s k ^ (3 - 2) ≤ S.P.μ * Cstar
  b6 : S.Kup * S.P.sbar ^ (3 + 2) ≤ S.P.κs
  b7 : S.CondB7
  b8_etab : S.etab S.C0 S.K1 ≤ 1 / 2 * OneRing.etaMax
  b8_level : ∀ k : ℕ, 2 ≤ k → Eig.Cls S.P.χ * S.etabK S.C0 S.K1 k / S.σ' *
    ((3 + 2) * Real.log (1 / S.P.s k) + Real.posLog (S.P.δ₀ / S.Klo)) ≤ 1 / 32
  b8_seed : Eig.Cls S.P.χ * S.etab S.C0 S.K1 * S.σ'⁻¹ * Real.log (2 * S.P.δ₀ / S.P.κs) ≤ 1 / 32
  b9_maj : 2 * S.Abar * S.P.μ * S.P.sbar ^ (3 + 2) ≤ S.majst
  b9_eta : Rings.Ceta S.P.χ S.Mh * (S.P.μ * S.P.sbar ^ 2 + S.P.sbar ^ (3 - 2)) ≤ 1
  b10 : 4 * S.CM * (2 * S.CQ / (S.sigb * (S.P.μ - 1)) + 1) * S.P.μ * S.P.sbar ^ (3 + 2) ≤ 1 / 2
  b11_handoff : Eig.ellNorm S.P.χ * S.CQ * S.K1 * S.Abar * S.P.μ * S.P.sbar ^ (3 + 2) ≤ 1 / 2
  b11_kick : S.kickIneqF S.C0 S.K1

/-- **The parameter lists (P0)–(P6)** for the parameters of `S` (`def:P0-P4`, `def:P5`,
`def:P6`): the structural list, the κ-list for `κ_seed = S.P.κs`, and the s̄-list. -/
structure ParamLists : Prop where
  structural : S.StructuralList
  kappa : S.KappaList S.P.κs
  sbar : S.SbarList

/-! ### Basic lemmas (fully proved) -/

theorem deltaKick_def : S.deltaKick =
    225 * S.sigma0 * Eig.cout S.P.χ / (40960 * Real.pi * ‖S.z‖ * S.C3) := rfl

theorem deltaRd_def : S.deltaRd = Eig.cout S.P.χ / (16 * Real.pi * Eig.Cp * S.C2) := rfl

theorem cPrime_def : S.cPrime =
    15 / 16 * (Eig.cout S.P.χ / (10 * ‖S.z‖ * Rings.Cmom * Ip 3 (S.sigma0 / 4))) := rfl

theorem muMax_def : S.muMax = 1 + min (S.cPrime * S.P.δ₀) (1 / 16) := rfl

theorem CF_def : S.CF =
    S.Cin * S.P.μ * (2 + 2 * Cstar * S.P.Tpin) ^ 3 * (1 + 2 * Cstar) ^ 3 / S.Klo := rfl

theorem C0_def : S.C0 = max (max (max 1 (2 * OneRing.Cseed S.P.χ S.s)) S.Chand) S.CF := rfl

theorem Cpre_def : S.Cpre =
    Cqr * (4 * S.P.μ * Rings.CL1 * S.CQ / (3 * S.sigma0 * (S.P.μ - 1)) + 1) * S.K1 := rfl

theorem Lconf_def (k : ℕ) : S.Lconf k =
    2 + 2 * Cstar * (S.P.μ * (S.P.Tpin + 1 + 1 / S.σ' *
      ((3 + 2) * Real.log (1 / S.P.s k) + Real.posLog (S.P.δ₀ / S.Klo)))) := rfl

theorem one_le_C0 : 1 ≤ S.C0 :=
  le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)

theorem C0_pos : 0 < S.C0 := lt_of_lt_of_le one_pos S.one_le_C0

theorem two_Cseed_le_C0 : 2 * OneRing.Cseed S.P.χ S.s ≤ S.C0 :=
  le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)

theorem Chand_le_C0 : S.Chand ≤ S.C0 := le_trans (le_max_right _ _) (le_max_left _ _)

theorem CF_le_C0 : S.CF ≤ S.C0 := le_max_right _ _

/-- (κ3) in the manuscript's form `C_pre (κ/δ₀)^{ϑ_μ} ≤ (15/16) c_out/(20|z|(μ-1))`. -/
theorem kickIneqE_K1_iff (κ : ℝ) : S.kickIneqE S.K1 κ ↔
    S.Cpre * (κ / S.P.δ₀) ^ S.varthetaMu ≤
      15 / 16 * (Eig.cout S.P.χ / (20 * ‖S.z‖ * (S.P.μ - 1))) := Iff.rfl

/-- (B10) in terms of the constant `C_M(2C_Q/(σ_b(μ-1)) + 1)` of `prop:relay` (`S.Crelay`). -/
theorem b10_iff_Crelay :
    4 * S.CM * (2 * S.CQ / (S.sigb * (S.P.μ - 1)) + 1) * S.P.μ * S.P.sbar ^ (3 + 2) ≤ 1 / 2 ↔
      4 * S.Crelay * S.P.μ * S.P.sbar ^ (3 + 2) ≤ 1 / 2 := by
  unfold Crelay
  constructor <;> intro h <;> linarith

/-- `eq:E22` in the manuscript's form (`10_parameters.tex:151-154`)
`K_O s̄^{2m}[T_z + 2 log(1/s̄) + 1/(μ-1)] ≤ (μ-1)/(4C_OC_QC_τ) · min{1/2, 1/(4C_ls K_1)}`,
given `4C_OC_QC_τ > 0`. -/
theorem condE22_iff_div (hD : 0 < 4 * S.CO * S.CQ * S.Ctau) :
    S.CondE22 ↔
      S.KO * S.P.sbar ^ (2 * 3) * (S.Tz + 2 * Real.log (1 / S.P.sbar) + 1 / (S.P.μ - 1)) ≤
        (S.P.μ - 1) / (4 * S.CO * S.CQ * S.Ctau) *
          min (1 / 2) (1 / (4 * Eig.Cls S.P.χ * S.K1)) := by
  rw [CondE22, div_mul_eq_mul_div, le_div_iff₀ hD, mul_comm (4 * S.CO * S.CQ * S.Ctau)]

/-- `eq:E22` holds when `C_Q = 0`. The lemma that uses it, `lem:theta-quiet`, needs nothing in
that case, because `θ_j = 4C_OC_QK_Os_{j-1}^{2m} = 0`. -/
theorem condE22_of_CQ_eq_zero (hCQ : S.CQ = 0) (hμ : 1 < S.P.μ)
    (hCls : 0 < Eig.Cls S.P.χ) (hK1 : 0 < S.K1) : S.CondE22 := by
  rw [CondE22, hCQ, mul_zero, zero_mul, zero_mul]
  have h4 : 0 < 4 * Eig.Cls S.P.χ * S.K1 := by positivity
  exact mul_nonneg (by linarith) (le_min (by norm_num) (one_div_pos.2 h4).le)

variable {S}

theorem CondP1.mem_Ioc_min (h : S.CondP1) :
    S.P.δ₀ ∈ Ioc (0 : ℝ) (min S.dH (min S.deltaKick S.deltaRd)) :=
  ⟨h.δ₀_pos, le_min h.δ₀_le_dH (le_min h.δ₀_le_kick h.δ₀_le_rd)⟩

theorem CondP1.of_mem_Ioc_min (h : S.P.δ₀ ∈ Ioc (0 : ℝ) (min S.dH (min S.deltaKick S.deltaRd))) :
    S.CondP1 where
  δ₀_pos := h.1
  δ₀_le_dH := h.2.trans (min_le_left _ _)
  δ₀_le_kick := h.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  δ₀_le_rd := h.2.trans ((min_le_right _ _).trans (min_le_right _ _))

/-- The second "equivalent" form of (P1) (`10_parameters.tex:52-53`):
`C_p C₂ δ₀ ≤ c_out/(16π)` (the first smallness hypothesis of `lem:readout`), given `C_p C₂ > 0`. -/
theorem CondP1.Cp_C2_mul_le (h : S.CondP1) (hpos : 0 < Eig.Cp * S.C2) :
    Eig.Cp * S.C2 * S.P.δ₀ ≤ Eig.cout S.P.χ / (16 * Real.pi) := by
  have hd := h.δ₀_le_rd
  have hpi : 0 < 16 * Real.pi := by positivity
  have hden : 0 < 16 * Real.pi * Eig.Cp * S.C2 := by
    have := mul_pos hpi hpos
    simpa [mul_assoc] using this
  rw [deltaRd, le_div_iff₀ hden] at hd
  rw [le_div_iff₀ hpi]
  linarith

/-- The first "equivalent" form of (P1) (`10_parameters.tex:52`): hypothesis (a) of
`lem:kicktrue`, `(16/15)(2πC₃δ₀²/σ) ≤ (1/4)(15/16) c_out δ₀/(20|z|)`, given `σ, |z|, C₃ > 0`. -/
theorem CondP1.kickIneqA (h : S.CondP1) (hσ : 0 < S.sigma0) (hz : 0 < ‖S.z‖) (hC3 : 0 < S.C3) :
    S.kickIneqA := by
  have hd := h.δ₀_le_kick
  have hδ := h.δ₀_pos
  have hden : 0 < 40960 * Real.pi * ‖S.z‖ * S.C3 := by positivity
  rw [deltaKick, le_div_iff₀ hden] at hd
  unfold Standing.kickIneqA
  rw [show 16 / 15 * (2 * Real.pi * S.C3 * S.P.δ₀ ^ 2 / S.sigma0) =
      (32 * Real.pi * S.C3 * S.P.δ₀) * S.P.δ₀ / (15 * S.sigma0) by ring,
    show 1 / 4 * (15 / 16) * (Eig.cout S.P.χ * S.P.δ₀ / (20 * ‖S.z‖)) =
      15 * Eig.cout S.P.χ * S.P.δ₀ / (1280 * ‖S.z‖) by ring,
    div_le_div_iff₀ (by positivity) (by positivity)]
  have key : 32 * Real.pi * S.C3 * S.P.δ₀ * (1280 * ‖S.z‖) ≤
      15 * Eig.cout S.P.χ * (15 * S.sigma0) := by
    nlinarith [hd]
  have := mul_le_mul_of_nonneg_right key hδ.le
  nlinarith [this]

theorem CondP2.mu_le_muMax_le (h : S.CondP2) : S.P.μ ≤ 17 / 16 := by
  have := h.μ_le
  rw [muMax] at this
  have := min_le_right (S.cPrime * S.P.δ₀) (1 / 16)
  linarith

theorem CondP2.mu_sub_one_le (h : S.CondP2) : S.P.μ - 1 ≤ S.cPrime * S.P.δ₀ := by
  have := h.μ_le
  rw [muMax] at this
  have := min_le_left (S.cPrime * S.P.δ₀) (1 / 16)
  linarith

/-- The cap `c'δ₀` of (P2) is hypothesis (b) of `lem:kicktrue` (`10_parameters.tex:75-76`). -/
theorem CondP2.kickIneqB (h : S.CondP2) : S.kickIneqB := by
  have h1 := h.mu_sub_one_le
  unfold Standing.kickIneqB
  unfold cPrime at h1
  calc S.P.μ - 1 ≤ 15 / 16 * (Eig.cout S.P.χ /
        (10 * ‖S.z‖ * Rings.Cmom * Ip 3 (S.sigma0 / 4))) * S.P.δ₀ := h1
    _ = 15 / 16 * Eig.cout S.P.χ * S.P.δ₀ /
        (10 * ‖S.z‖ * Rings.Cmom * Ip 3 (S.sigma0 / 4)) := by ring

theorem KappaList.pos {κs : ℝ} (h : S.KappaList κs) : 0 < κs := h.1

theorem KappaList.cond {κs : ℝ} (h : S.KappaList κs) {κ : ℝ} (hκ : 0 < κ) (hκ' : κ ≤ 2 * κs) :
    S.CondKappa κ :=
  h.2 κ ⟨hκ, hκ'⟩

/-- (κ1)–(κ7) at `κ = 2κ_seed`. -/
theorem KappaList.cond_two {κs : ℝ} (h : S.KappaList κs) : S.CondKappa (2 * κs) :=
  h.cond (by linarith [h.pos]) le_rfl

/-- (κ1)–(κ7) at `κ = κ_seed`. -/
theorem KappaList.cond_self {κs : ℝ} (h : S.KappaList κs) : S.CondKappa κs :=
  h.cond h.pos (by linarith [h.pos])

/-- `κ_seed ≤ κ_L`, by (κ6) at `κ = 2κ_seed` (`10_parameters.tex:383`). -/
theorem KappaList.le_kL {κs : ℝ} (h : S.KappaList κs) : κs ≤ OneRing.kL S.P.χ := by
  have := h.cond_two.k6
  linarith [h.pos]

/-- `2κ_seed < δ₀`, by (κ1) at `κ = 2κ_seed` (`11_bootstrap.tex:236`), given `δ₀ > 0`, `μ > 1`. -/
theorem KappaList.two_lt_δ₀ {κs : ℝ} (h : S.KappaList κs) (hδ : 0 < S.P.δ₀) (hμ : 1 < S.P.μ) :
    2 * κs < S.P.δ₀ := by
  have h1 := h.cond_two.k1
  unfold kickIneqC at h1
  have hexp : -(S.P.μ / (S.P.μ - 1)) < 0 := by
    have : 0 < S.P.μ / (S.P.μ - 1) := div_pos (by linarith) (by linarith)
    linarith
  have hlt : (4 : ℝ) ^ (-(S.P.μ / (S.P.μ - 1))) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hexp
  calc 2 * κs ≤ S.P.δ₀ * (4 : ℝ) ^ (-(S.P.μ / (S.P.μ - 1))) := h1
    _ < S.P.δ₀ * 1 := mul_lt_mul_of_pos_left hlt hδ
    _ = S.P.δ₀ := mul_one _

/-- **The standing assumptions from the lists** (the last sentence of `lem:nonempty`,
`10_parameters.tex:287-289`, `:377-389`, for a single depth): if (P0)–(P6) hold, (N) holds, `χ` is
admissible, `A₁ > 0`, `n ≥ 2` and `ω = ω^{(n)}`, then (SA) holds. -/
theorem ParamLists.holds (hL : S.ParamLists) (hN : NumericalHypothesis S.P.χ)
    (hχ : IsAdmissibleCutoff S.P.χ) (hA₁ : 0 < S.P.A₁) (hn : 2 ≤ S.P.n)
    (hom : S.P.om = Smooth.sol S.P.f) : S.Holds where
  hN := hN
  valid :=
    { admissible := hχ
      datumParams :=
        { A₁_pos := hA₁
          one_lt_μ := hL.structural.p2.one_lt_μ
          μ_le_two := by linarith [hL.structural.p2.mu_le_muMax_le]
          sbar_pos := hL.sbar.sbar_pos
          sbar_le := hL.sbar.b1_le }
      two_le_n := hn
      kseed_pos := hL.kappa.pos
      kseed_le := hL.kappa.le_kL
      δ₀_pos := hL.structural.p1.δ₀_pos
      Tpin_pos := hL.structural.p3.Tpin_pos
      om_eq := hom }
  three_le_s := hL.structural.p0.three_le_s
  σ'_gt := hL.structural.p0.σ'_gt
  σ'_lt_sigb := hL.structural.p0.σ'_lt_sigb
  σ'_lt_sigma := hL.structural.p0.σ'_lt_sigma
  δ₀_le_dH := hL.structural.p1.δ₀_le_dH
  μ_le := hL.structural.p2.mu_le_muMax_le
  sbar_pow_le := hL.sbar.b1_pow
  mu_sbar_le := hL.sbar.b2
  CG_le := hL.sbar.b3

/-- (Det) from the lists: it is (B4) (`10_parameters.tex:388-389`). -/
theorem ParamLists.det (hL : S.ParamLists) : S.Det := hL.sbar.b4

end Standing

end Relay

end NonUniqueEuler
