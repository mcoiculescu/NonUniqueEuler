import NonUniqueEuler.Statement.WeakSolution
import NonUniqueEuler.Statement.Datum
import NonUniqueEuler.Statement.Evans

/-!
# Statement layer: the main theorem and the conditional theorem

Statement layer: definitions and statements only, no proofs.

Current manuscript sources: Part I and Part II, Theorem 1.1 (`thm:main` in each
part); Part II, Proposition 1.2 (`prop:reduction`), proved in Section 8
(`sec:bootstrap`, `manuscript/part2/sections/11_bootstrap.tex`). The former separate
`thm:main-explicit` is now part of that reduction proof; Lean retains its explicit
statement as an intermediate theorem.

`MainTheorem χ` packages Theorem 1.1 of both parts for the ring built from each
admissible cutoff `χ`, together with the explicit consequences of the current
Part II reduction proof. Its quantifiers are:

  ∃ μ ∈ (1, 17/16], ∃ s̄ ∈ (0, a/16], ∀ A₁ > 0,
    [f radial, f ≥ 0, f ∈ L^q ∀ q ∈ [1, ∞), f ∉ L^∞] ∧
    ∃ T* ∈ (0, ∞), ∃ ω_∞, ∃ t₀ ∈ [0, T*),
      (∀ T > T*, ∀ q ∈ (4/3, ∞): the stationary solution and ω_∞ are renormalized weak
         solutions in X_q(T) with datum f, distinct in X_q(T))            [thm:main]
      ∧ ω_∞ ∈ C([0, ∞); L^p) ∀ p ∈ [1, ∞)                               [thm:main (ii)]
      ∧ ∀ t ≥ 0, ω_∞(t) equimeasurable with f, invariant under O_{2π/3}  [thm:main (ii)]
      ∧ ∀ T' > t₀, ∀ q ∈ (4/3, ∞): ω_∞ and f distinct in X_q(T')         [thm:main, "More precisely"]
      ∧ ω_∞ is a renormalized weak solution on [0, ∞) with q = 2          [Part II reduction proof: global solution]
      ∧ ∀ T > t₀, ∀ q ∈ (4/3, ∞): both are renormalized weak solutions in
         X_q(T) with datum f                                               [Part II reduction proof: restriction to X_q(T)]

The last two lines retain the former explicit-theorem packaging; the current
proof of Part II, Proposition 1.2 supplies them through Part I, Corollary 3.9
(`cor:defect`) and the final restriction argument. They are additional clauses
beyond the headline statement of Theorem 1.1. The radiality of `f` is asserted
pointwise, which is stronger than the almost-everywhere convention of Part I,
Section 2.1 (`sec:prelim`).

The order of quantifiers matters: `μ` and `s̄` are chosen before `A₁` in the proof
of Part II, Proposition 1.2; `T*`, `ω_∞` and `t₀` may depend on `A₁`. The same
`ω_∞` works for every `T` and every `q`, as in Theorem 1.1 of both parts.
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler

open RingData

/-- The stationary space–time function `ω(t) = f` (Part II, Theorem 1.1(i), `thm:main`). -/
def stationary (f : ℂ → ℝ) : ℝ → ℂ → ℝ := fun _ x => f x

/-- **Theorem 1.1 of Parts I and II** (`thm:main`), with the additional explicit
clauses supplied in the proof of Part II, Proposition 1.2 (`prop:reduction`),
for the ring built from the cutoff `χ`. The former `thm:main-explicit` is no longer
a separate manuscript theorem. -/
def MainTheorem (χ : ℝ → ℝ) : Prop :=
  ∃ μ : ℝ, 1 < μ ∧ μ ≤ 17 / 16 ∧
  ∃ sbar : ℝ, 0 < sbar ∧ sbar ≤ a / 16 ∧
  ∀ A₁ : ℝ, 0 < A₁ →
    -- properties of the datum
    IsRadialPointwise (datum χ A₁ μ sbar) ∧
    (∀ x : ℂ, 0 ≤ datum χ A₁ μ sbar x) ∧
    (∀ q : ℝ, 1 ≤ q → MemLp (datum χ A₁ μ sbar) (ENNReal.ofReal q)) ∧
    ¬ MemLp (datum χ A₁ μ sbar) ⊤ ∧
    -- two distinct renormalized weak solutions
    ∃ Tstar : ℝ, 0 < Tstar ∧
    ∃ ωinf : ℝ → ℂ → ℝ,
    ∃ t₀ : ℝ, 0 ≤ t₀ ∧ t₀ < Tstar ∧
      (∀ T : ℝ, Tstar < T → ∀ q : ℝ, 4 / 3 < q →
        IsRenormalizedWeakSolution q T (datum χ A₁ μ sbar) (stationary (datum χ A₁ μ sbar)) ∧
        IsRenormalizedWeakSolution q T (datum χ A₁ μ sbar) ωinf ∧
        DistinctInX T ωinf (stationary (datum χ A₁ μ sbar))) ∧
      (∀ p : ℝ, 1 ≤ p → ContinuousIntoLp (ENNReal.ofReal p) ωinf) ∧
      (∀ t : ℝ, 0 ≤ t →
        Equimeasurable (ωinf t) (datum χ A₁ μ sbar) ∧ IsMFoldSymmetric 3 (ωinf t)) ∧
      (∀ T' : ℝ, t₀ < T' → ∀ q : ℝ, 4 / 3 < q →
        DistinctInX T' ωinf (stationary (datum χ A₁ μ sbar))) ∧
      IsRenormalizedWeakSolutionOnHalfLine 2 (datum χ A₁ μ sbar) ωinf ∧
      (∀ T : ℝ, t₀ < T → ∀ q : ℝ, 4 / 3 < q →
        IsRenormalizedWeakSolution q T (datum χ A₁ μ sbar) (stationary (datum χ A₁ μ sbar)) ∧
        IsRenormalizedWeakSolution q T (datum χ A₁ μ sbar) ωinf)

/-- **The conditional reduction** (Part II, Proposition 1.2, `prop:reduction`):
for every admissible cutoff `χ`, Hypothesis (N) for `χ` implies `MainTheorem χ`.
This Lean statement includes the explicit clauses documented above; it is not
the separate conditional theorem of Part I, Theorem 1.2 (`thm:conditional`).
It is proved as `main_theorem_of_N` (`P/Main/Reduction.lean`). -/
def ConditionalTheorem : Prop :=
  ∀ χ : ℝ → ℝ, IsAdmissibleCutoff χ → NumericalHypothesis χ → MainTheorem χ

end NonUniqueEuler
