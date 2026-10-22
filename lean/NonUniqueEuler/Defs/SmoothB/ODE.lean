import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Topology.Order.Basic

/-!
# Appendix B: maximal solutions of ODEs and their flow (`lem:ode`)

Definitions for Lemma `lem:ode` (`B_global_smooth.tex:18-44`): for an
open set `U ⊆ ℝ × E` and `F : ℝ → E → E` of class `C^k` on `U`, the problem `ẋ = F(t,x)`,
`x(s) = y` has a unique maximal solution, defined on an open interval containing `s`; its value at
time `t` is `Φ_F(t, s, y)`.

The manuscript states `lem:ode` on `ℝⁿ`; here `E` is any real normed space (`E = ℂ` is used by
`lem:flow`). Time-dependent fields are curried, `F t x = F(t,x)` (as in Mathlib's
`IsIntegralCurve`).

* `IsLocalSol F U s y J γ`: `γ` solves `ẋ = F(t,x)`, `x(s) = y` on the open interval `J ∋ s`,
  with graph in `U`;
* `IsMaxSol F U s y J γ`: moreover every solution `(J', γ')` of the same problem has `J' ⊆ J` and
  `γ' = γ` on `J'` (so it is the unique maximal solution);
* `maxDomain F U s y` and `maxFlow F U t s y = Φ_F(t, s, y)`: the domain and the values of the
  maximal solution, chosen when one exists (`lem:ode`(i) proves existence for `F ∈ C¹(U)`, `U`
  open); junk values `∅` and `y` otherwise. Off its domain `maxFlow` is unspecified.

Uniqueness is built into `IsMaxSol`, so the choice is canonical (`IsMaxSol.maxDomain_eq`,
`IsMaxSol.maxFlow_eq`). All lemmas in this file are fully proved.
-/

noncomputable section

open Set

namespace NonUniqueEuler.Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `γ` is a solution of `ẋ = F(t,x)`, `x(s) = y` on the open interval `J ∋ s`, whose graph
`{(t, γ t) : t ∈ J}` lies in `U` (`lem:ode`(i), `B_global_smooth.tex:25-27`). -/
structure IsLocalSol (F : ℝ → E → E) (U : Set (ℝ × E)) (s : ℝ) (y : E) (J : Set ℝ)
    (γ : ℝ → E) : Prop where
  isOpen : IsOpen J
  ordConnected : J.OrdConnected
  mem : s ∈ J
  init : γ s = y
  graph : ∀ t ∈ J, (t, γ t) ∈ U
  hasDerivAt : ∀ t ∈ J, HasDerivAt γ (F t (γ t)) t

/-- `γ` on `J` is the maximal solution of `ẋ = F(t,x)`, `x(s) = y` in `U`
(`lem:ode`(i), `B_global_smooth.tex:25-27`): it is a solution, and every solution `(J', γ')`
satisfies `J' ⊆ J` and `γ' = γ` on `J'`. -/
structure IsMaxSol (F : ℝ → E → E) (U : Set (ℝ × E)) (s : ℝ) (y : E) (J : Set ℝ) (γ : ℝ → E) :
    Prop extends IsLocalSol F U s y J γ where
  maximal : ∀ (J' : Set ℝ) (γ' : ℝ → E), IsLocalSol F U s y J' γ' → J' ⊆ J ∧ EqOn γ' γ J'

/-- The (open) interval of existence of the maximal solution of `ẋ = F(t,x)`, `x(s) = y`; `∅`
if there is no maximal solution. -/
@[irreducible] def maxDomain (F : ℝ → E → E) (U : Set (ℝ × E)) (s : ℝ) (y : E) : Set ℝ :=
  open scoped Classical in
  if h : ∃ (J : Set ℝ) (γ : ℝ → E), IsMaxSol F U s y J γ then h.choose else ∅

/-- The solution map `Φ_F(t, s, y)` of `lem:ode`(i) (`B_global_smooth.tex:27-28`): the value at
time `t` of the maximal solution of `ẋ = F(t,x)`, `x(s) = y`. Meaningful for
`t ∈ maxDomain F U s y`; junk value `y` if there is no maximal solution. -/
@[irreducible] def maxFlow (F : ℝ → E → E) (U : Set (ℝ × E)) (t s : ℝ) (y : E) : E :=
  open scoped Classical in
  if h : ∃ (J : Set ℝ) (γ : ℝ → E), IsMaxSol F U s y J γ then h.choose_spec.choose t else y

/-! ### Basic lemmas (fully proved) -/

variable {F : ℝ → E → E} {U : Set (ℝ × E)} {s : ℝ} {y : E} {J J' : Set ℝ} {γ γ' : ℝ → E}

/-- Two maximal solutions of the same problem have the same domain and agree on it. -/
theorem IsMaxSol.unique (h : IsMaxSol F U s y J γ) (h' : IsMaxSol F U s y J' γ') :
    J' = J ∧ EqOn γ' γ J := by
  obtain ⟨h1, h2⟩ := h.maximal J' γ' h'.toIsLocalSol
  obtain ⟨h3, h4⟩ := h'.maximal J γ h.toIsLocalSol
  refine ⟨Subset.antisymm h1 h3, fun t ht => (h4 ht).symm⟩

/-- When a maximal solution exists, `maxDomain` and `maxFlow` are the maximal solution. -/
theorem isMaxSol_maxFlow (h : ∃ (J : Set ℝ) (γ : ℝ → E), IsMaxSol F U s y J γ) :
    IsMaxSol F U s y (maxDomain F U s y) (fun t => maxFlow F U t s y) := by
  classical
  have hd : maxDomain F U s y = h.choose := by
    rw [maxDomain, dite_eq_left_of_eq_true (eq_true h)]
  have hf : (fun t => maxFlow F U t s y) = h.choose_spec.choose := by
    funext t
    rw [maxFlow, dite_eq_left_of_eq_true (eq_true h)]
  rw [hd, hf]
  exact h.choose_spec.choose_spec

theorem IsMaxSol.maxDomain_eq (h : IsMaxSol F U s y J γ) : maxDomain F U s y = J :=
  ((isMaxSol_maxFlow ⟨J, γ, h⟩).unique h).1.symm

theorem IsMaxSol.maxFlow_eq (h : IsMaxSol F U s y J γ) {t : ℝ} (ht : t ∈ J) :
    maxFlow F U t s y = γ t := by
  have h' := isMaxSol_maxFlow ⟨J, γ, h⟩
  obtain ⟨hJ, heq⟩ := h.unique h'
  exact heq ht

/-- A solution on all of `ℝ` that agrees with every other solution is maximal. -/
theorem IsLocalSol.isMaxSol_univ (h : IsLocalSol F U s y univ γ)
    (huniq : ∀ (J' : Set ℝ) (γ' : ℝ → E), IsLocalSol F U s y J' γ' → EqOn γ' γ J') :
    IsMaxSol F U s y univ γ :=
  ⟨h, fun J' γ' h' => ⟨subset_univ _, huniq J' γ' h'⟩⟩

theorem IsLocalSol.continuousOn (h : IsLocalSol F U s y J γ) : ContinuousOn γ J :=
  fun t ht => (h.hasDerivAt t ht).continuousAt.continuousWithinAt

end NonUniqueEuler.Smooth
