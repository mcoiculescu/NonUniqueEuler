import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Fintype.Card

/-!
# Proof: continuity (bootstrap) arguments on intervals (I-CONT, R10)

Proof of `NonUniqueEuler/I/Infra/Continuity/Bootstrap.lean` (same declarations, statements
copied verbatim). See the docstring of the interface file for the manuscript uses
(`thm:quiet`, `lem:window`, `thm:active`, `prop:bootstrap` Step 7).

* `forall_Icc_of_history`: supremum argument on `S = {t ∈ [a, b] | Q on [a, t]}`.
* `bootstrap_le`: `forall_Icc_of_history` applied to `Q' t := t ∈ [a, b] → ∀ i, F i t ≤ G i t`
  (the guard `t ∈ [a, b]` is needed because the extension step of `forall_Icc_of_history`
  asks for `Q'` on `(t, t + δ]`, which may leave `[a, b]`).
* `bootstrap_le_single`: the case `ι = Unit`.
* `forall_Icc_of_chain`: induction on the number of intervals.
-/

open Set Filter Topology

namespace NonUniqueEuler.Continuity

/-- Continuity argument with history ("real induction"). -/
theorem forall_Icc_of_history {a b : ℝ} {Q : ℝ → Prop} (h0 : Q a)
    (hlim : ∀ t ∈ Ioc a b, (∀ s ∈ Ico a t, Q s) → Q t)
    (hstep : ∀ t ∈ Ico a b, (∀ s ∈ Icc a t, Q s) → ∃ δ > 0, ∀ s ∈ Ioc t (t + δ), Q s) :
    ∀ t ∈ Icc a b, Q t := by
  intro t ht
  have hab : a ≤ b := ht.1.trans ht.2
  set S : Set ℝ := {u | u ∈ Icc a b ∧ ∀ s ∈ Icc a u, Q s} with hS
  have haS : a ∈ S := ⟨⟨le_rfl, hab⟩, fun s hs => by
    rw [le_antisymm hs.2 hs.1]; exact h0⟩
  have hne : S.Nonempty := ⟨a, haS⟩
  have hbdd : BddAbove S := ⟨b, fun u hu => hu.1.2⟩
  set T := sSup S with hT
  have haT : a ≤ T := le_csSup hbdd haS
  have hTb : T ≤ b := csSup_le hne fun u hu => hu.1.2
  -- `Q` holds on `[a, T)`.
  have hbelow : ∀ s ∈ Ico a T, Q s := by
    intro s hs
    obtain ⟨u, huS, hsu⟩ := exists_lt_of_lt_csSup hne hs.2
    exact huS.2 s ⟨hs.1, hsu.le⟩
  -- `Q` holds at `T`.
  have hTQ : Q T := by
    rcases eq_or_lt_of_le haT with h | h
    · rw [← h]; exact h0
    · exact hlim T ⟨h, hTb⟩ hbelow
  have hall : ∀ s ∈ Icc a T, Q s := by
    intro s hs
    rcases eq_or_lt_of_le hs.2 with h | h
    · rw [h]; exact hTQ
    · exact hbelow s ⟨hs.1, h⟩
  -- `T = b`.
  have hTeq : T = b := by
    by_contra hne'
    have hlt : T < b := lt_of_le_of_ne hTb hne'
    obtain ⟨δ, hδ, hQδ⟩ := hstep T ⟨haT, hlt⟩ hall
    set u := min (T + δ) b with hu
    have hTu : T < u := lt_min (by linarith) hlt
    have huS : u ∈ S := by
      refine ⟨⟨haT.trans hTu.le, min_le_right _ _⟩, fun s hs => ?_⟩
      rcases le_or_gt s T with h | h
      · exact hall s ⟨hs.1, h⟩
      · exact hQδ s ⟨h, hs.2.trans (min_le_left _ _)⟩
    have : u ≤ T := le_csSup hbdd huS
    linarith
  exact hall t ⟨ht.1, hTeq ▸ ht.2⟩

/-- The bootstrap argument (strict improvement) for finitely many continuous quantities. -/
theorem bootstrap_le {ι : Type*} [Finite ι] {a b : ℝ} {F G H : ι → ℝ → ℝ}
    (hF : ∀ i, ContinuousOn (F i) (Icc a b)) (hG : ∀ i, ContinuousOn (G i) (Icc a b))
    (hHG : ∀ i, ∀ t ∈ Icc a b, H i t < G i t) (h0 : ∀ i, F i a ≤ G i a)
    (himp : ∀ t ∈ Icc a b, (∀ s ∈ Icc a t, ∀ i, F i s ≤ G i s) → ∀ i, F i t ≤ H i t) :
    ∀ t ∈ Icc a b, ∀ i, F i t ≤ H i t := by
  -- The guarded bootstrap assumption.
  let Q : ℝ → Prop := fun t => t ∈ Icc a b → ∀ i, F i t ≤ G i t
  have hQ0 : Q a := fun _ => h0
  have hQlim : ∀ t ∈ Ioc a b, (∀ s ∈ Ico a t, Q s) → Q t := by
    intro t ht hhist htab i
    have hsub : Ico a t ⊆ Icc a b := fun s hs => ⟨hs.1, hs.2.le.trans ht.2⟩
    have hcl : t ∈ closure (Ico a t) := by
      rw [closure_Ico ht.1.ne]; exact right_mem_Icc.2 ht.1.le
    exact ContinuousWithinAt.closure_le hcl ((hF i t htab).mono hsub)
      ((hG i t htab).mono hsub) fun s hs => hhist s hs (hsub hs) i
  have hQstep : ∀ t ∈ Ico a b, (∀ s ∈ Icc a t, Q s) → ∃ δ > 0, ∀ s ∈ Ioc t (t + δ), Q s := by
    intro t ht hhist
    have htab : t ∈ Icc a b := Ico_subset_Icc_self ht
    have hlt : ∀ i, F i t < G i t := fun i =>
      (himp t htab (fun s hs => hhist s hs (Icc_subset_Icc_right ht.2.le hs)) i).trans_lt
        (hHG i t htab)
    have hev : ∀ᶠ s in 𝓝[Icc a b] t, ∀ i, F i s < G i s :=
      eventually_all.2 fun i =>
        Filter.Tendsto.eventually_lt (hF i t htab) (hG i t htab) (hlt i)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
    refine ⟨ε / 2, half_pos hε, fun s hs hsab i => ?_⟩
    have hdist : s ∈ Metric.ball t ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.2 hs.1)]
      linarith [hs.2]
    exact (hball ⟨hdist, hsab⟩ i).le
  have hQall := forall_Icc_of_history hQ0 hQlim hQstep
  intro t ht
  exact himp t ht fun s hs => hQall s (Icc_subset_Icc_right ht.2 hs)
    (Icc_subset_Icc_right ht.2 hs)

/-- The bootstrap argument for a single continuous quantity. -/
theorem bootstrap_le_single {a b : ℝ} {F G H : ℝ → ℝ} (hF : ContinuousOn F (Icc a b))
    (hG : ContinuousOn G (Icc a b)) (hHG : ∀ t ∈ Icc a b, H t < G t) (h0 : F a ≤ G a)
    (himp : ∀ t ∈ Icc a b, (∀ s ∈ Icc a t, F s ≤ G s) → F t ≤ H t) :
    ∀ t ∈ Icc a b, F t ≤ H t := by
  intro t ht
  exact bootstrap_le (ι := Unit) (F := fun _ => F) (G := fun _ => G) (H := fun _ => H)
    (fun _ => hF) (fun _ => hG) (fun _ => hHG) (fun _ => h0)
    (fun t ht h _ => himp t ht fun s hs => h s hs ()) t ht ()

-- `hτ` is not needed by the proof (kept: the statement is copied verbatim from the I file).
set_option linter.unusedVariables false in
/-- Chaining over consecutive intervals `[τ k, τ (k+1)]`. -/
theorem forall_Icc_of_chain {n : ℕ} {τ : ℕ → ℝ} (hτ : Monotone τ) {Q : ℝ → Prop}
    (h0 : Q (τ 0))
    (hstep : ∀ k < n, (∀ s ∈ Icc (τ 0) (τ k), Q s) → ∀ s ∈ Icc (τ k) (τ (k + 1)), Q s) :
    ∀ s ∈ Icc (τ 0) (τ n), Q s := by
  have key : ∀ m ≤ n, ∀ s ∈ Icc (τ 0) (τ m), Q s := by
    intro m
    induction m with
    | zero =>
      intro _ s hs
      rw [le_antisymm hs.2 hs.1]; exact h0
    | succ m ih =>
      intro hm s hs
      have ih' := ih (Nat.le_of_succ_le hm)
      rcases le_or_gt s (τ m) with h | h
      · exact ih' s ⟨hs.1, h⟩
      · exact hstep m (Nat.lt_of_succ_le hm) ih' s ⟨h.le, hs.2⟩
  exact key n le_rfl

end NonUniqueEuler.Continuity
