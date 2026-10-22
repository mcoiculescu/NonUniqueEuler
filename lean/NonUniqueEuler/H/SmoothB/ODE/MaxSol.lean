import NonUniqueEuler.Defs.SmoothB.ODE
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Helper for `lem:ode`(i): uniqueness and the maximal solution

For `F ∈ C¹(U)`, `U ⊆ ℝ × E` open (`E` finite-dimensional):
* `exists_lipschitzOnWith_of_mem`: `F` is Lipschitz in `x`, uniformly in `t`, near each point of
  `U` (a `C¹` map on a compact convex set is Lipschitz);
* `eventuallyEq_of_local`: local uniqueness (`ODE_solution_unique_of_eventually`);
* `IsLocalSol.eqOn_inter`: two local solutions of the same problem agree on the intersection of
  their domains (connectedness of the intersection, an open interval);
* `exists_isMaxSol_of_local`: if some local solution exists, the union of all local solutions is
  the maximal solution (Teschl, Theorem 2.13).
-/

noncomputable section

open Set Function Metric Filter
open scoped Topology NNReal

namespace NonUniqueEuler.Smooth.ODEH

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : ℝ → E → E} {U : Set (ℝ × E)}

/-- A `C¹` field is Lipschitz in `x`, uniformly in `t`, on a small closed cylinder around each
point of `U`. -/
theorem exists_lipschitzOnWith_of_mem (hU : IsOpen U) (hF : ContDiffOn ℝ 1 (uncurry F) U)
    {q : ℝ × E} (hq : q ∈ U) :
    ∃ ε > 0, ∃ K : ℝ≥0, ∀ t ∈ closedBall q.1 ε, LipschitzOnWith K (F t) (closedBall q.2 ε) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU q hq
  refine ⟨ε / 2, by positivity, ?_⟩
  have hsub : closedBall q (ε / 2) ⊆ U :=
    (closedBall_subset_ball (by linarith)).trans hball
  obtain ⟨K, hK⟩ := (hF.mono hsub).exists_lipschitzOnWith one_ne_zero (convex_closedBall _ _)
    (isCompact_closedBall _ _)
  refine ⟨K, fun t ht x hx x' hx' => ?_⟩
  have h1 : (t, x) ∈ closedBall q (ε / 2) := by
    rw [mem_closedBall, Prod.dist_eq]; exact max_le ht hx
  have h2 : (t, x') ∈ closedBall q (ε / 2) := by
    rw [mem_closedBall, Prod.dist_eq]; exact max_le ht hx'
  have := hK h1 h2
  simpa [uncurry, Prod.edist_eq] using this

/-- Local uniqueness for a `C¹` field. -/
theorem eventuallyEq_of_local (hU : IsOpen U) (hF : ContDiffOn ℝ 1 (uncurry F) U) {t₀ : ℝ}
    {γ₁ γ₂ : ℝ → E} (h₁ : ∀ᶠ t in 𝓝 t₀, HasDerivAt γ₁ (F t (γ₁ t)) t)
    (h₂ : ∀ᶠ t in 𝓝 t₀, HasDerivAt γ₂ (F t (γ₂ t)) t) (hmem : (t₀, γ₁ t₀) ∈ U)
    (heq : γ₁ t₀ = γ₂ t₀) : γ₁ =ᶠ[𝓝 t₀] γ₂ := by
  obtain ⟨ε, hε, K, hK⟩ := exists_lipschitzOnWith_of_mem hU hF hmem
  have hc₁ : ContinuousAt γ₁ t₀ := h₁.self_of_nhds.continuousAt
  have hc₂ : ContinuousAt γ₂ t₀ := h₂.self_of_nhds.continuousAt
  have hb₁ : ∀ᶠ t in 𝓝 t₀, γ₁ t ∈ closedBall (γ₁ t₀) ε :=
    hc₁.eventually (closedBall_mem_nhds _ hε)
  have hb₂ : ∀ᶠ t in 𝓝 t₀, γ₂ t ∈ closedBall (γ₁ t₀) ε := by
    rw [heq]; exact hc₂.eventually (closedBall_mem_nhds _ hε)
  exact ODE_solution_unique_of_eventually (K := K) (s := fun _ => closedBall (γ₁ t₀) ε)
    (v := F) (Filter.mem_of_superset (closedBall_mem_nhds t₀ hε) (fun t ht => hK t ht))
    (h₁.and hb₁) (h₂.and hb₂) heq

/-- Two local solutions of the same problem agree on the intersection of their domains. -/
theorem IsLocalSol.eqOn_inter (hU : IsOpen U) (hF : ContDiffOn ℝ 1 (uncurry F) U) {s : ℝ}
    {y : E} {J₁ J₂ : Set ℝ} {γ₁ γ₂ : ℝ → E} (h₁ : IsLocalSol F U s y J₁ γ₁)
    (h₂ : IsLocalSol F U s y J₂ γ₂) : EqOn γ₁ γ₂ (J₁ ∩ J₂) := by
  have hSc : IsPreconnected (J₁ ∩ J₂) :=
    (h₁.ordConnected.inter h₂.ordConnected).isPreconnected
  have huo : IsOpen {t | γ₁ =ᶠ[𝓝 t] γ₂} := isOpen_setOfPred_eventually_nhds
  have hloc : ∀ t ∈ J₁ ∩ J₂, γ₁ t = γ₂ t → γ₁ =ᶠ[𝓝 t] γ₂ := by
    intro t ht he
    exact eventuallyEq_of_local hU hF
      (Filter.mem_of_superset (h₁.isOpen.mem_nhds ht.1) (fun τ hτ => h₁.hasDerivAt τ hτ))
      (Filter.mem_of_superset (h₂.isOpen.mem_nhds ht.2) (fun τ hτ => h₂.hasDerivAt τ hτ))
      (h₁.graph t ht.1) he
  have hsub : J₁ ∩ J₂ ⊆ {t | γ₁ =ᶠ[𝓝 t] γ₂} := by
    apply hSc.subset_of_closure_inter_subset huo
    · exact ⟨s, ⟨h₁.mem, h₂.mem⟩, hloc s ⟨h₁.mem, h₂.mem⟩ (h₁.init.trans h₂.init.symm)⟩
    · rintro t ⟨htc, htS⟩
      apply hloc t htS
      have hfr : ∃ᶠ τ in 𝓝 t, γ₁ τ = γ₂ τ := by
        rw [mem_closure_iff_frequently] at htc
        exact htc.mono fun τ hτ => hτ.eq_of_nhds
      exact tendsto_nhds_unique_of_frequently_eq (h₁.hasDerivAt t htS.1).continuousAt
        (h₂.hasDerivAt t htS.2).continuousAt hfr
  intro t ht
  exact (hsub ht).eq_of_nhds

/-- If the problem has a local solution, the union of all local solutions is the maximal
solution. -/
theorem exists_isMaxSol_of_local (hU : IsOpen U) (hF : ContDiffOn ℝ 1 (uncurry F) U) {s : ℝ}
    {y : E} (hex : ∃ (J : Set ℝ) (γ : ℝ → E), IsLocalSol F U s y J γ) :
    ∃ (J : Set ℝ) (γ : ℝ → E), IsMaxSol F U s y J γ := by
  classical
  let S : Set (Set ℝ × (ℝ → E)) := {p | IsLocalSol F U s y p.1 p.2}
  let J : Set ℝ := ⋃ p ∈ S, p.1
  let γ : ℝ → E := fun t => if h : ∃ p ∈ S, t ∈ p.1 then h.choose.2 t else y
  have hγ : ∀ p ∈ S, EqOn p.2 γ p.1 := by
    intro p hp t ht
    have h : ∃ p ∈ S, t ∈ p.1 := ⟨p, hp, ht⟩
    simp only [γ, dite_eq_left_of_eq_true (eq_true h)]
    exact IsLocalSol.eqOn_inter hU hF hp h.choose_spec.1 ⟨ht, h.choose_spec.2⟩
  have hJ : ∀ t, t ∈ J ↔ ∃ p ∈ S, t ∈ p.1 := by
    intro t; simp only [J, mem_iUnion, exists_prop]
  obtain ⟨J₀, γ₀, h₀⟩ := hex
  have hloc : IsLocalSol F U s y J γ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact isOpen_biUnion fun p hp => (show IsLocalSol F U s y p.1 p.2 from hp).isOpen
    · refine ⟨fun a ha b hb t ht => ?_⟩
      obtain ⟨p, hp, hap⟩ := (hJ a).1 ha
      obtain ⟨q, hq, hbq⟩ := (hJ b).1 hb
      have hp' : IsLocalSol F U s y p.1 p.2 := hp
      have hq' : IsLocalSol F U s y q.1 q.2 := hq
      rcases le_total t s with hts | hst
      · exact (hJ t).2 ⟨p, hp, hp'.ordConnected.out hap hp'.mem ⟨ht.1, hts⟩⟩
      · exact (hJ t).2 ⟨q, hq, hq'.ordConnected.out hq'.mem hbq ⟨hst, ht.2⟩⟩
    · exact (hJ s).2 ⟨(J₀, γ₀), h₀, h₀.mem⟩
    · rw [← hγ (J₀, γ₀) h₀ h₀.mem]; exact h₀.init
    · intro t ht
      obtain ⟨p, hp, htp⟩ := (hJ t).1 ht
      rw [← hγ p hp htp]
      exact (show IsLocalSol F U s y p.1 p.2 from hp).graph t htp
    · intro t ht
      obtain ⟨p, hp, htp⟩ := (hJ t).1 ht
      have hp' : IsLocalSol F U s y p.1 p.2 := hp
      have hev : γ =ᶠ[𝓝 t] p.2 :=
        Filter.mem_of_superset (hp'.isOpen.mem_nhds htp) (fun τ hτ => (hγ p hp hτ).symm)
      rw [← hγ p hp htp]
      exact (hp'.hasDerivAt t htp).congr_of_eventuallyEq hev
  refine ⟨J, γ, hloc, fun J' γ' h' => ⟨fun t ht => (hJ t).2 ⟨(J', γ'), h', ht⟩, ?_⟩⟩
  exact hγ (J', γ') h'

end NonUniqueEuler.Smooth.ODEH
