import NonUniqueEuler.Defs.Sec10.Params
import NonUniqueEuler.Defs.Sec3.Criterion
import NonUniqueEuler.Statement.MainTheorem

/-!
# Section 11: `thm:main-explicit` and the proof of `prop:reduction` (definitions)

Manuscript `thm:main-explicit`
(`11_bootstrap.tex:665-683`, proof `:685-721`) and the proof of `prop:reduction`
(`11_bootstrap.tex:723-739`).

* `Params.MainExplicit p A₁`: the conclusions of `thm:main-explicit` for the parameters `p` and the
  amplitude `A₁` (`T_* ∈ [1/A₁, ∞)`, the second solution `ω_∞` and the time `t₀` with (i), (ii)),
  written with the statement-layer predicates of `Statement/WeakSolution.lean`;
* `Params.mainTheorem_of`: the logical content of the proof of `prop:reduction`
  (`11_bootstrap.tex:723-739`): parameters with (P0)–(P6), the datum properties of
  `prop:integrability` and `thm:main-explicit` for every `A₁ > 0` give `MainTheorem p.χ` (with
  `μ = p.μ`, `s̄ = p.s̄` fixed before `A₁`, and `T* = p.Tstar A₁`); fully proved;
* bridges to `prop:defect`: the readout test function `Ψ₁` is the test function `defectTest χ_out 3`
  of `prop:defect` (`readoutTest_eq_defectTest`, `11_bootstrap.tex:700-701`), and a readout cutoff
  is a radial test profile (`IsReadoutCutoff.isRadialTestProfile`).

All lemmas here are fully proved.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

open RingData Datum

/-! ### Bridges to `prop:defect` (`11_bootstrap.tex:700-703`) -/

/-- `Ψ₁(x) = χ_out(|x|) x̄^m` is the test function of `prop:defect` with `χ = χ_out`, `m = 3`
(`11_bootstrap.tex:700-701`). -/
theorem readoutTest_eq_defectTest (χo : ℝ → ℝ) : readoutTest χo = Compact.defectTest χo 3 := rfl

/-- A readout cutoff `χ_out ∈ C_c^∞((a/4, 3))` is a radial test profile of `prop:defect`
(`χ ∈ C_c^∞((0, ∞))`, `11_bootstrap.tex:701`). -/
theorem IsReadoutCutoff.isRadialTestProfile {χo : ℝ → ℝ} (h : IsReadoutCutoff χo) :
    Compact.IsRadialTestProfile χo where
  contDiff := h.contDiff
  hasCompactSupport := h.hasCompactSupport
  tsupport_subset := fun r hr => by
    have h1 := (h.tsupport_subset hr).1
    have h2 : 0 < a / 4 := by linarith [zero_lt_a]
    exact lt_trans h2 h1

namespace Params

variable (p : Params)

/-! ### `thm:main-explicit` (`11_bootstrap.tex:665-683`) -/

/-- **The conclusions of `thm:main-explicit`** for the parameters `p` and the amplitude `A₁`
(`11_bootstrap.tex:669-682`), with `f = p.datum A₁` (`def:datum`) and `T_* = p.Tstar A₁`
(`lem:time`): `T_* ∈ [1/A₁, ∞)`, and there are `ω_∞` and `t₀ ∈ [0, T_*)` such that
* `ω_∞` is a renormalized weak solution on `[0, ∞)` with datum `f`, `q = 2` (`def:weak`);
* (i) `ω_∞ ∈ C([0, ∞); L^q)` for every `q ∈ [1, ∞)`, and `ω_∞(t)` is equimeasurable with `f` and
  `3`-fold symmetric for every `t ≥ 0`;
* (ii) for every `T > t₀` and every `q ∈ (4/3, ∞)`, the stationary function `ω(t) = f` and `ω_∞`
  are renormalized weak solutions in `X_q(T)` with datum `f`, and they are distinct elements of
  `X_q(T)` (`DistinctInX T`, which does not depend on `q`). -/
def MainExplicit (A₁ : ℝ) : Prop :=
  1 / A₁ ≤ p.Tstar A₁ ∧
    ∃ ωinf : ℝ → ℂ → ℝ, ∃ t₀ : ℝ, 0 ≤ t₀ ∧ t₀ < p.Tstar A₁ ∧
      IsRenormalizedWeakSolutionOnHalfLine 2 (p.datum A₁) ωinf ∧
      (∀ q : ℝ, 1 ≤ q → ContinuousIntoLp (ENNReal.ofReal q) ωinf) ∧
      (∀ t : ℝ, 0 ≤ t → Equimeasurable (ωinf t) (p.datum A₁) ∧ IsMFoldSymmetric 3 (ωinf t)) ∧
      ∀ T : ℝ, t₀ < T → ∀ q : ℝ, 4 / 3 < q →
        IsRenormalizedWeakSolution q T (p.datum A₁) (stationary (p.datum A₁)) ∧
        IsRenormalizedWeakSolution q T (p.datum A₁) ωinf ∧
        DistinctInX T ωinf (stationary (p.datum A₁))

/-! ### The proof of `prop:reduction` (`11_bootstrap.tex:723-739`) -/

variable {p}

/-- **The assembly of `prop:reduction`** (`11_bootstrap.tex:723-739`): if `p` satisfies (P0)–(P6),
the datum `f` has the properties of `prop:integrability` for every `A₁ > 0`, and the conclusions of
`thm:main-explicit` hold for every `A₁ > 0`, then Theorem 1.1 holds for the cutoff `p.χ`, with
`μ = p.μ ∈ (1, 17/16]` and `s̄ = p.s̄ ∈ (0, a/16]` (fixed before `A₁`) and `T* = p.Tstar A₁`
(`T > T* > t₀`). -/
theorem mainTheorem_of (hL : p.Lists)
    (hD : ∀ A₁ : ℝ, 0 < A₁ → DatumProperties p.χ A₁ p.μ p.sbar)
    (hE : ∀ A₁ : ℝ, 0 < A₁ → p.MainExplicit A₁) : MainTheorem p.χ := by
  refine ⟨p.μ, hL.one_lt_μ, hL.μ_le, p.sbar, hL.sbar_pos, hL.sbar_le, fun A₁ hA₁ => ?_⟩
  obtain ⟨_, hrad, hnn, hLq, hnot⟩ := hD A₁ hA₁
  obtain ⟨hT, ωinf, t₀, ht₀, ht₀T, hhalf, hcont, heq, hsol⟩ := hE A₁ hA₁
  have hTpos : 0 < p.Tstar A₁ := lt_of_lt_of_le (one_div_pos.mpr hA₁) hT
  refine ⟨hrad, hnn, hLq, hnot, p.Tstar A₁, hTpos, ωinf, t₀, ht₀, ht₀T, ?_, hcont, heq, ?_,
    hhalf, ?_⟩
  · intro T hT' q hq
    exact hsol T (ht₀T.trans hT') q hq
  · intro T' hT' q hq
    exact (hsol T' hT' q hq).2.2
  · intro T hT' q hq
    exact ⟨(hsol T hT' q hq).1, (hsol T hT' q hq).2.1⟩

end Params

end Relay

end NonUniqueEuler
