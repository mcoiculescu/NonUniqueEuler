import NonUniqueEuler.Defs.Sec7.Transfer

/-!
# Section 7.2: confinement on a window, localization, field bound (definitions)

Manuscript `prop:confine`
(`07_several_rings.tex:285-314`), `def:loc` (`:464-478`), `lem:field-bound` (`:483-491`).

* `Rings.Cmom = M_vort (2 max(1, C_*))^m` (`prop:confine`(c));
* `P.confRadius k t = ϱ_k(t) = (2 + 2 C_* A_{k+1}(t - T_{k+1})) r_{k+1}` (`prop:confine`(a) with
  `t₀ = T_{k+1}`; `def:loc`(2)), `P.confLambda k t₁ = Λ = 2 + 2 C_* A_{k+1}(t₁ - T_{k+1})`;
* `P.ConfineHyp k t₁`: the hypotheses (i)–(iv) of `prop:confine` (with `t₀ = T_{k+1}`);
  `P.ConfineConcl k t₁ t`: its conclusions (a)–(c) at a time `t ∈ [t₀, t₁]`;
* `P.Loc t`: the localization hypothesis (Loc) of `def:loc`;
* `IsFieldBoundConst χ M_h C_η` and the chosen `Rings.Ceta χ M_h` (`lem:field-bound`; `C_η` enters
  the parameter condition (B9), so it is used by value).

Here `m = 3`. All lemmas here are fully proved.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Rings

open RingData Datum

/-- `C_mom = M_vort (2 max(1, C_*))^m`, `m = 3` (`prop:confine`(c), `07_several_rings.tex:310`). -/
def Cmom : ℝ := Mvort * (2 * max 1 Cstar) ^ 3

theorem Cmom_pos : 0 < Cmom :=
  mul_pos Mvort_pos (pow_pos (by positivity) _)

end Rings

namespace Datum

namespace Approx

open RingData

variable (P : Approx)

/-! ### `prop:confine` (`07_several_rings.tex:285-314`) -/

/-- `ϱ_k(t) = (2 + 2 C_* A_{k+1}(t - T_{k+1})) r_{k+1}` (`prop:confine`(a), `07_several_rings.tex:302`;
`def:loc`(2), `:474-476`; with the kick time `τ_K = A_{k+1}(t - T_{k+1})`). -/
def confRadius (k : ℕ) (t : ℝ) : ℝ := (2 + 2 * Cstar * P.kickTime k t) * P.r (k + 1)

/-- `Λ = 2 + 2 C_* A_{k+1}(t₁ - t₀)` with `t₀ = T_{k+1}` (`prop:confine`, `07_several_rings.tex:289`). -/
def confLambda (k : ℕ) (t₁ : ℝ) : ℝ := 2 + 2 * Cstar * P.kickTime k t₁

/-- **The hypotheses of `prop:confine`** for the level `k` and the end time `t₁`
(`07_several_rings.tex:287-298`): `1 ≤ k < n`, the clock is defined up to level `k+1`,
`t₀ = T_{k+1} ≤ t₁`, and
(i) `D_{k+1}(t₀) ⊂ \bar B_{2 r_{k+1}}`;
(ii) (Cl): `S_j(t) ⊂ {|x| ≥ a r_j/2}` for every `t ∈ [t₀, t₁]` and every `j ≤ k`;
(iii) `s̄ ≤ a/16`, `s̄^{m-2} ≤ 1/2`, `μ⁴ s̄² ≤ 1/8`;
(iv) `Λ s_k ≤ a/8` and `(8/3)(2/a)^m Λ^{m-1} s_k^{m-2} ≤ μ C_*`. -/
structure ConfineHyp (k : ℕ) (t₁ : ℝ) : Prop where
  one_le : 1 ≤ k
  lt_n : k < P.n
  clock : P.ClockUpTo (k + 1)
  le_t₁ : P.T (k + 1) ≤ t₁
  init : P.D (k + 1) (P.T (k + 1)) ⊆ closedBall 0 (2 * P.r (k + 1))
  cl : ∀ t ∈ Icc (P.T (k + 1)) t₁, ∀ j ∈ Finset.Icc 1 k,
    P.St j t ⊆ {x : ℂ | a / 2 * P.r j ≤ ‖x‖}
  sbar_le : P.sbar ≤ a / 16
  sbar_pow_le : P.sbar ^ (3 - 2) ≤ 1 / 2
  mu_sbar_le : P.μ ^ 4 * P.sbar ^ 2 ≤ 1 / 8
  lambda_le : P.confLambda k t₁ * P.s k ≤ a / 8
  lambda_pow_le : 8 / 3 * (2 / a) ^ 3 * P.confLambda k t₁ ^ (3 - 1) * P.s k ^ (3 - 2) ≤ P.μ * Cstar

/-- **The conclusions of `prop:confine`** at a time `t ∈ [t₀, t₁]`, `t₀ = T_{k+1}`
(`07_several_rings.tex:299-311`):
(a) `D_{k+1}(t) ⊂ \bar B_{ϱ(t)}` and `ϱ(t) ≤ a r_k/8`;
(b) `|v(t, x)| ≤ 2 C_* A_{k+1} r_{k+1}` for `x ∈ \bar B_{Λ r_{k+1}}`;
(c) `∫ x^l ω_{≥k+1}(t) dx = 0` unless `m ∣ l`, `|∫ x^l ω_{≥k+1}(t) dx| ≤ M_vort A_{k+1} r_{k+1}² ϱ(t)^l`
for every `l ≥ 0`, and `|q_{k+1}(t)| ≤ C_mom (1 + τ_K)^m`, `τ_K = A_{k+1}(t - t₀)`
(`x^l` is the complex power, `m = 3`). -/
structure ConfineConcl (k : ℕ) (t₁ t : ℝ) : Prop where
  supp : P.D (k + 1) t ⊆ closedBall 0 (P.confRadius k t)
  radius_le : P.confRadius k t ≤ a / 8 * P.r k
  speed : ∀ x ∈ closedBall (0 : ℂ) (P.confLambda k t₁ * P.r (k + 1)),
    ‖P.vel t x‖ ≤ 2 * Cstar * P.A (k + 1) * P.r (k + 1)
  moment_zero : ∀ l : ℕ, ¬ 3 ∣ l → ∫ x, x ^ l * ((P.omegaGe (k + 1) t x : ℝ) : ℂ) = 0
  moment_le : ∀ l : ℕ, ‖∫ x, x ^ l * ((P.omegaGe (k + 1) t x : ℝ) : ℂ)‖ ≤
    Mvort * P.A (k + 1) * P.r (k + 1) ^ 2 * P.confRadius k t ^ l
  q_le : ‖P.q (k + 1) t‖ ≤ Rings.Cmom * (1 + P.kickTime k t) ^ 3

/-! ### `def:loc` (`07_several_rings.tex:464-478`) -/

/-- **The localization hypothesis (Loc) at `t`** (`def:loc`, `07_several_rings.tex:464-478`), with
"`t ≤ T_i`" and "`t ≤ t♯_i`" read as true when `T_i`, resp. `t♯_i`, is not defined:
(1) for every ring `i ∈ [1, n]` with `t ≤ T_i`: `S_i(t) ⊂ N_i`;
(2) for every ring `j ∈ [1, n]` quiet at `t` (`QuietAt`): `S_i(t) ∩ B_{6 r_j} = ∅` for `i < j`
(`HOutDefined`), `D_{j+1}(t) ⊂ B_{a r_j/8}` (`HInDefined`), and, if `T_{j+1}` is defined and
`t ≥ T_{j+1}`, `D_{j+1}(t) ⊂ \bar B_{ϱ_j(t)}`. (For `j = n`, `T_{n+1} = 0` and `D_{n+1} = ∅`.) -/
def Loc (t : ℝ) : Prop :=
  (∀ i ∈ Finset.Icc 1 P.n, (P.ClockUpTo i → t ≤ P.T i) → P.PertDefined i t) ∧
    ∀ j ∈ Finset.Icc 1 P.n, P.QuietAt j t →
      P.HOutDefined j t ∧ P.HInDefined j t ∧
        (P.ClockUpTo (j + 1) → P.T (j + 1) ≤ t → P.D (j + 1) t ⊆ closedBall 0 (P.confRadius j t))

/-! ### Basic lemmas (fully proved) -/

theorem confRadius_def (k : ℕ) (t : ℝ) :
    P.confRadius k t = (2 + 2 * Cstar * P.A (k + 1) * (t - P.T (k + 1))) * P.r (k + 1) := by
  simp [confRadius, kickTime, mul_assoc]

theorem confLambda_def (k : ℕ) (t₁ : ℝ) :
    P.confLambda k t₁ = 2 + 2 * Cstar * P.A (k + 1) * (t₁ - P.T (k + 1)) := by
  simp [confLambda, kickTime, mul_assoc]

/-- `ϱ(t₁) = Λ r_{k+1}` (`07_several_rings.tex:362`). -/
theorem confRadius_eq_confLambda (k : ℕ) (t₁ : ℝ) :
    P.confRadius k t₁ = P.confLambda k t₁ * P.r (k + 1) := rfl

end Approx

end Datum

namespace Rings

open RingData Datum

/-! ### `lem:field-bound` (`07_several_rings.tex:483-491`) -/

/-- **The constant `C_η` works in `lem:field-bound` at order `M_h`** (`07_several_rings.tex:483-491`):
`C_η > 0`, and for every valid approximation `P` with cutoff `χ` and `s̄^{m-2} ≤ 1/2`
(`s̄ ≤ a/16` is part of `Approx.Valid`), every `1 ≤ j < n` and `t ≥ 0` with `S_i(t) ⊂ N_i` and
`S_i(t) ∩ B_{6 r_j} = ∅` for every `i < j` and `D_{j+1}(t) ⊂ B_{a r_j/8}`:
`h^in_j(A_j t), h^out_j(A_j t) ∈ C^{M_h}(N')` and `η_j(A_j t) ≤ C_η (μ s̄² + s̄^{m-2})`, `m = 3`. The
manuscript's proof gives `C_η = max{(a/8)^m C_M, 4‖Φ‖_{L¹} C_O}`. -/
structure IsFieldBoundConst (χ : ℝ → ℝ) (Mh : ℕ) (C : ℝ) : Prop where
  pos : 0 < C
  bound : ∀ P : Approx, P.χ = χ → P.Valid → P.sbar ^ (3 - 2) ≤ 1 / 2 →
    ∀ j : ℕ, 1 ≤ j → j < P.n → ∀ t : ℝ, 0 ≤ t →
      (∀ i ∈ Finset.Ico 1 j, P.PertDefined i t) → P.HOutDefined j t → P.HInDefined j t →
      MemCk Mh annN' (P.hIn j (P.A j * t)) ∧ MemCk Mh annN' (P.hOut j (P.A j * t)) ∧
        P.eta Mh j (P.A j * t) ≤ C * (P.μ * P.sbar ^ 2 + P.sbar ^ (3 - 2))

open Classical in
/-- `C_η` of `lem:field-bound` at order `M_h` (`07_several_rings.tex:485`; chosen, junk `1`). -/
def Ceta (χ : ℝ → ℝ) (Mh : ℕ) : ℝ :=
  if h : ∃ C : ℝ, IsFieldBoundConst χ Mh C then h.choose else 1

/-- If a constant for `lem:field-bound` exists, the chosen one works. -/
theorem fieldBoundConst_spec {χ : ℝ → ℝ} {Mh : ℕ} (h : ∃ C : ℝ, IsFieldBoundConst χ Mh C) :
    IsFieldBoundConst χ Mh (Ceta χ Mh) := by
  classical
  rw [Ceta, dite_eq_left h]
  exact h.choose_spec

end Rings

end NonUniqueEuler
