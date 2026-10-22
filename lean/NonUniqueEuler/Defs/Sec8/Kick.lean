import NonUniqueEuler.Defs.Sec4.Eigendata
import NonUniqueEuler.Defs.Infra.Ip

/-!
# Section 8: the kick setting (definitions)

Manuscript `08_kick.tex:156-255`
(the setting before `lem:pinning`, `eq:kick-A`, `lem:pinning`, `lem:kick-lower`, `prop:kick`).

The setting (`08_kick.tex:157-167`): `ζ₀, β ∈ ℂ` with `x = Re ζ₀ > 0`, `-∞ < τ₀ < τ₁ ≤ ∞`,
`I = [τ₀, τ₁]` (or `[τ₀, ∞)`), `q : I → ℂ` continuous, `c` the solution of `c' = ζ₀ c + β q`,
`c(τ₀) = 0`, and `A(τ) = e^{-ζ₀τ} c(τ)`. In Lean `τ₁ : EReal` (`⊤` for `∞`), `I = Kick.interval τ₀ τ₁`,
`IsSetting ζ₀ β τ₀ τ₁ q` holds the conditions, and the solution is given by the variation of constants
formula: `Kick.amp ζ₀ β τ₀ q τ = β ∫_{τ₀}^τ e^{-ζ₀ s} q(s) ds` (this is `A`, `eq:kick-A`) and
`Kick.coef = e^{ζ₀τ} A` (this is `c`; that it solves the ODE is an interface statement).

`lem:kick-lower`: the hypotheses (Q1)–(Q3) (`Q1`, `Q2`, `Q3`) and the numbers `𝖪` (`kickK`),
`Err_g` (`errG`), `Err_pre` (`errPre`), `𝖱` (`kickR`). `prop:kick`: `Detuned` and the hypothesis list
`KickHyp` ((Kick1)–(Kick4) with the detuning). Namespace `NonUniqueEuler.Kick`.
All lemmas here are fully proved.
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler

namespace Kick

open RingData

/-! ### The setting (`08_kick.tex:156-171`) -/

/-- The interval `I = {τ : τ₀ ≤ τ ≤ τ₁}`: `[τ₀, τ₁]` if `τ₁ < ∞`, `[τ₀, ∞)` if `τ₁ = ∞`
(`08_kick.tex:159-160`). -/
def interval (τ₀ : ℝ) (τ₁ : EReal) : Set ℝ := {τ : ℝ | τ₀ ≤ τ ∧ (τ : EReal) ≤ τ₁}

/-- **The setting of Section 8** (`08_kick.tex:157-161`): `x = Re ζ₀ > 0`, `τ₀ < τ₁ ≤ ∞`, and `q`
continuous on `I`. -/
structure IsSetting (ζ₀ β : ℂ) (τ₀ : ℝ) (τ₁ : EReal) (q : ℝ → ℂ) : Prop where
  re_pos : 0 < ζ₀.re
  lt : (τ₀ : EReal) < τ₁
  continuousOn : ContinuousOn q (interval τ₀ τ₁)

/-- The kick amplitude `A(τ) = β ∫_{τ₀}^τ e^{-ζ₀ s} q(s) ds` (`eq:kick-A`, `08_kick.tex:164-167`). -/
def amp (ζ₀ β : ℂ) (τ₀ : ℝ) (q : ℝ → ℂ) (τ : ℝ) : ℂ :=
  β * ∫ s in τ₀..τ, Complex.exp (-(ζ₀ * s)) * q s

/-- The solution `c(τ) = e^{ζ₀τ} A(τ)` of `c' = ζ₀ c + β q`, `c(τ₀) = 0` (`08_kick.tex:161-163`;
variation of constants). -/
def coef (ζ₀ β : ℂ) (τ₀ : ℝ) (q : ℝ → ℂ) (τ : ℝ) : ℂ :=
  Complex.exp (ζ₀ * τ) * amp ζ₀ β τ₀ q τ

/-! ### `lem:kick-lower` (`08_kick.tex:193-212`) -/

/-- **(Q1)** (`08_kick.tex:198-200`): `q_s ≠ 0` and `|q(τ) - q_s e^{z'τ}| ≤ err(τ)` on `[-T_g, 0]`,
with `err ≥ 0` there. The manuscript asks `err` measurable; we ask `err` integrable on `[-T_g, 0]`
(otherwise `Err_g = ∞` and the lemmas using (Q1) are vacuous; Lean's integral would be `0`). -/
def Q1 (q : ℝ → ℂ) (z' : ℂ) (Tg : ℝ) (qs : ℂ) (err : ℝ → ℝ) : Prop :=
  qs ≠ 0 ∧ IntegrableOn err (Icc (-Tg) 0) ∧ (∀ τ ∈ Icc (-Tg) 0, 0 ≤ err τ) ∧
    ∀ τ ∈ Icc (-Tg) 0, ‖q τ - qs * Complex.exp (z' * τ)‖ ≤ err τ

/-- **(Q2)** (`08_kick.tex:201-203`): `|q(τ)| ≤ Q_pre(τ)` on `[τ₀, -T_g]`, `Q_pre ≥ 0` there
(integrable on `[τ₀, -T_g]`, as in `Q1`). -/
def Q2 (q : ℝ → ℂ) (τ₀ Tg : ℝ) (Qpre : ℝ → ℝ) : Prop :=
  IntegrableOn Qpre (Icc τ₀ (-Tg)) ∧ (∀ τ ∈ Icc τ₀ (-Tg), 0 ≤ Qpre τ) ∧
    ∀ τ ∈ Icc τ₀ (-Tg), ‖q τ‖ ≤ Qpre τ

/-- **(Q3)** (`08_kick.tex:204`; also the hypothesis of `lem:pinning`, `:176`):
`|q(τ)| ≤ Q̄ (1 + τ)^p` for `τ ∈ I ∩ [0, ∞)`. -/
def Q3 (q : ℝ → ℂ) (τ₀ : ℝ) (τ₁ : EReal) (Qbar : ℝ) (p : ℕ) : Prop :=
  ∀ τ ∈ interval τ₀ τ₁, 0 ≤ τ → ‖q τ‖ ≤ Qbar * (1 + τ) ^ p

/-- `𝖪 = β q_s (1 - e^{-w T_g})/w` (`08_kick.tex:206`). -/
def kickK (β qs w : ℂ) (Tg : ℝ) : ℂ := β * qs * (1 - Complex.exp (-(w * Tg))) / w

/-- `Err_g = ∫_{-T_g}^0 e^{-xτ} err(τ) dτ` (`08_kick.tex:207`). -/
def errG (x Tg : ℝ) (err : ℝ → ℝ) : ℝ := ∫ τ in (-Tg)..0, Real.exp (-(x * τ)) * err τ

/-- `Err_pre = ∫_{τ₀}^{-T_g} e^{-xτ} Q_pre(τ) dτ` (`08_kick.tex:208`). -/
def errPre (x τ₀ Tg : ℝ) (Qpre : ℝ → ℝ) : ℝ := ∫ τ in τ₀..(-Tg), Real.exp (-(x * τ)) * Qpre τ

/-- `𝖱 = |β| (Err_g + Err_pre + Q̄ I_p(x))` (`08_kick.tex:209`). -/
def kickR (β : ℂ) (x τ₀ Tg : ℝ) (err Qpre : ℝ → ℝ) (Qbar : ℝ) (p : ℕ) : ℝ :=
  ‖β‖ * (errG x Tg err + errPre x τ₀ Tg Qpre + Qbar * Ip p x)

/-! ### `prop:kick` (`08_kick.tex:229-255`) -/

/-- The detuning condition `|λ_*(G) - z| ≤ σ(μ-1)/(8μ)` of `prop:kick` (`08_kick.tex:237-238`),
`z = λ_*(0)`, `σ = Re z`. -/
def Detuned (χ : ℝ → ℝ) (μ G : ℝ) : Prop :=
  ‖Eig.lam χ G - Eig.z χ‖ ≤ Eig.sigma χ 0 * (μ - 1) / (8 * μ)

/-- **The hypotheses of `prop:kick`** (`08_kick.tex:234-249`), with `ζ₀ = λ_*(G)/μ`,
`x = Re ζ₀`, `z' = λ_*(G')`, `w = z' - ζ₀`, `z = λ_*(0)`, `σ = Re z`: the setting with these `ζ₀`
and `β`; `1 < μ ≤ 2`; `G, G' ∈ [0, G₁]`, both detuned; `T_g > 0`, `τ₀ < -T_g`, `τ₁ > 0`, `Q̄ > 0`;
(Q1)–(Q3); (Kick1) `μ - 1 ≤ |q_s|/(10|z| Q̄ I_p(σ/4))`; (Kick2) `e^{-Re w T_g} ≤ 1/2`;
(Kick3) `Err_g ≤ |q_s|/(20|z|(μ-1))`; (Kick4) `Err_pre ≤ |q_s|/(20|z|(μ-1))`. -/
structure KickHyp (χ : ℝ → ℝ) (μ G G' : ℝ) (β : ℂ) (τ₀ : ℝ) (τ₁ : EReal) (q : ℝ → ℂ)
    (Tg Qbar : ℝ) (p : ℕ) (qs : ℂ) (err Qpre : ℝ → ℝ) : Prop where
  setting : IsSetting (Eig.lam χ G / μ) β τ₀ τ₁ q
  one_lt_μ : 1 < μ
  μ_le_two : μ ≤ 2
  G_mem : G ∈ Icc (0 : ℝ) Gbar
  G'_mem : G' ∈ Icc (0 : ℝ) Gbar
  detuned : Detuned χ μ G
  detuned' : Detuned χ μ G'
  Tg_pos : 0 < Tg
  τ₀_lt : τ₀ < -Tg
  τ₁_pos : (0 : EReal) < τ₁
  Qbar_pos : 0 < Qbar
  q1 : Q1 q (Eig.lam χ G') Tg qs err
  q2 : Q2 q τ₀ Tg Qpre
  q3 : Q3 q τ₀ τ₁ Qbar p
  kick1 : μ - 1 ≤ ‖qs‖ / (10 * ‖Eig.z χ‖ * Qbar * Ip p (Eig.sigma χ 0 / 4))
  kick2 : Real.exp (-((Eig.lam χ G' - Eig.lam χ G / μ).re * Tg)) ≤ 1 / 2
  kick3 : errG (Eig.lam χ G / μ).re Tg err ≤ ‖qs‖ / (20 * ‖Eig.z χ‖ * (μ - 1))
  kick4 : errPre (Eig.lam χ G / μ).re τ₀ Tg Qpre ≤ ‖qs‖ / (20 * ‖Eig.z χ‖ * (μ - 1))

/-! ### Basic lemmas (fully proved) -/

/-- `A(τ) = e^{-ζ₀τ} c(τ)` (`08_kick.tex:161-162`). -/
theorem amp_eq_exp_mul_coef (ζ₀ β : ℂ) (τ₀ : ℝ) (q : ℝ → ℂ) (τ : ℝ) :
    amp ζ₀ β τ₀ q τ = Complex.exp (-(ζ₀ * τ)) * coef ζ₀ β τ₀ q τ := by
  rw [coef, ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]

/-- `A(τ₀) = 0` and `c(τ₀) = 0`. -/
theorem amp_self (ζ₀ β : ℂ) (τ₀ : ℝ) (q : ℝ → ℂ) : amp ζ₀ β τ₀ q τ₀ = 0 := by
  simp [amp]

theorem coef_self (ζ₀ β : ℂ) (τ₀ : ℝ) (q : ℝ → ℂ) : coef ζ₀ β τ₀ q τ₀ = 0 := by
  simp [coef, amp_self]

theorem mem_interval {τ₀ : ℝ} {τ₁ : EReal} {τ : ℝ} :
    τ ∈ interval τ₀ τ₁ ↔ τ₀ ≤ τ ∧ (τ : EReal) ≤ τ₁ := Iff.rfl

theorem interval_top (τ₀ : ℝ) : interval τ₀ ⊤ = Ici τ₀ := by
  ext τ
  simp [interval]

theorem interval_coe (τ₀ τ₁ : ℝ) : interval τ₀ (τ₁ : EReal) = Icc τ₀ τ₁ := by
  ext τ
  simp [interval]

end Kick

end NonUniqueEuler
