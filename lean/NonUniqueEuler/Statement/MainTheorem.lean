import NonUniqueEuler.Statement.WeakSolution
import NonUniqueEuler.Statement.Datum
import NonUniqueEuler.Statement.Evans

/-!
# Statement layer: the main theorem and the conditional theorem

Statement layer: definitions and statements only, no proofs.

Manuscript sources: Theorem `thm:main` (`01_intro.tex:144-164`), Theorem `thm:main-explicit`
(`11_bootstrap.tex:665-683`), Proposition `prop:reduction` (`01_intro.tex:301-305`) and its
proof (`11_bootstrap.tex:723-739`).

`MainTheorem χ` is Theorem 1.1 for the ring built from the admissible cutoff `χ`, with the
quantifiers of the manuscript:

  ∃ μ ∈ (1, 17/16], ∃ s̄ ∈ (0, a/16], ∀ A₁ > 0,
    [f radial, f ≥ 0, f ∈ L^q ∀ q ∈ [1, ∞), f ∉ L^∞] ∧
    ∃ T* ∈ (0, ∞), ∃ ω_∞, ∃ t₀ ∈ [0, T*),
      (∀ T > T*, ∀ q ∈ (4/3, ∞): the stationary solution and ω_∞ are renormalized weak
         solutions in X_q(T) with datum f, distinct in X_q(T))            [thm:main]
      ∧ ω_∞ ∈ C([0, ∞); L^p) ∀ p ∈ [1, ∞)                               [thm:main (ii)]
      ∧ ∀ t ≥ 0, ω_∞(t) equimeasurable with f, invariant under O_{2π/3}  [thm:main (ii)]
      ∧ ∀ T' > t₀, ∀ q ∈ (4/3, ∞): ω_∞ and f distinct in X_q(T')         [thm:main, "More precisely"]
      ∧ ω_∞ is a renormalized weak solution on [0, ∞) with q = 2          [thm:main-explicit]
      ∧ ∀ T > t₀, ∀ q ∈ (4/3, ∞): both are renormalized weak solutions in
         X_q(T) with datum f                                               [thm:main-explicit (ii)]

The last two lines are the explicit form proved in `11_bootstrap.tex:665-721`; they strengthen
Theorem 1.1 (e.g. they make "distinct elements of `X_q(T')`" for `T' ∈ (t₀, T*]` refer to
elements of `X_q(T')`). The radiality of `f` is asserted pointwise, which is stronger than the
almost-everywhere notion of `02_prelim.tex:25`.

The order of quantifiers matters: `μ` and `s̄` are chosen before `A₁`
(`11_bootstrap.tex:737-738`); `T*`, `ω_∞` and `t₀` may depend on `A₁`; the same `ω_∞` works for
every `T` and every `q` (`01_intro.tex:167-169`).
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler

open RingData

/-- The stationary space–time function `ω(t) = f` (`01_intro.tex:155`). -/
def stationary (f : ℂ → ℝ) : ℝ → ℂ → ℝ := fun _ x => f x

/-- **Theorem 1.1** (`thm:main`, `01_intro.tex:144-164`), together with the explicit form
`thm:main-explicit` (`11_bootstrap.tex:665-683`), for the ring built from the cutoff `χ`. -/
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

/-- **The conditional theorem** (part (1); `prop:reduction`, `01_intro.tex:301-305`): for every
admissible cutoff `χ`, Hypothesis (N) for `χ` implies Theorem 1.1 for `χ`.
It is proved as `main_theorem_of_N` (`P/Main/Reduction.lean`). -/
def ConditionalTheorem : Prop :=
  ∀ χ : ℝ → ℝ, IsAdmissibleCutoff χ → NumericalHypothesis χ → MainTheorem χ

end NonUniqueEuler
