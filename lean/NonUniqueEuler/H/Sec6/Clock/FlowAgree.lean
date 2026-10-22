import NonUniqueEuler.Defs.SmoothB.Flow
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Helper for `lem:clock`(2): flows of fields that agree on a time slab

Helper of `P/Sec6/Clock.lean` (`06_datum.tex:475-478`): "the velocities agree on `[0, t̄] × ℝ²` and
are Lipschitz in `x`, so the two flows agree on `[0, t̄]`, by uniqueness for the flow equation".

`flowOf_eq_of_eqOn_Icc`: let `u` have the global maximal solution `t ↦ Φ_u(t, 0, y)`, let every
problem `ẋ = u'(t, x)`, `x(s) = z` have a maximal solution, and let `u' = u` on `[0, t̄]`. Then
`Φ_{u'}(t, 0, y) = Φ_u(t, 0, y)` for `t ∈ [0, t̄]`.

Proof: glue the maximal solution `γ'` of `u'` (for `t < 0`), the solution `γ` of `u` (on `[0, t̄]`)
and the maximal solution `γ₂` of `u'` through `(t̄, γ(t̄))` (for `t > t̄`) into a solution of `u'`
on an open interval containing `[0, t̄]`; maximality of `γ'` gives `γ' = γ` on `[0, t̄]`. The
gluing at the junctions uses one-sided derivatives.
-/

noncomputable section

open Set Filter Topology

namespace NonUniqueEuler.Smooth

namespace ClockH

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A function with the same one-sided derivative from the left and from the right is
differentiable. -/
theorem hasDerivAt_of_Iic_Ici {f : ℝ → E} {f' : E} {x : ℝ} (hl : HasDerivWithinAt f f' (Iic x) x)
    (hr : HasDerivWithinAt f f' (Ici x) x) : HasDerivAt f f' x := by
  have h := hl.union hr
  rw [Iic_union_Ici] at h
  exact h.hasDerivAt univ_mem

/-- **Flows of fields that agree on `[0, t̄]` agree on `[0, t̄]`.** -/
theorem flowOf_eq_of_eqOn_Icc {u u' : ℝ → ℂ → ℂ} {y : ℂ} {tbar : ℝ} (htbar : 0 ≤ tbar)
    (hγ : IsMaxSol u univ 0 y univ (fun t => flowOf u t 0 y))
    (hex' : ∀ (s : ℝ) (z : ℂ), ∃ (J : Set ℝ) (γ : ℝ → ℂ), IsMaxSol u' univ s z J γ)
    (heq : ∀ t ∈ Icc (0 : ℝ) tbar, u' t = u t) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) tbar) :
    flowOf u' t 0 y = flowOf u t 0 y := by
  set γ : ℝ → ℂ := fun t => flowOf u t 0 y with hγdef
  have hγd : ∀ s, HasDerivAt γ (u s (γ s)) s := fun s => hγ.hasDerivAt s (mem_univ s)
  have hγ0 : γ 0 = y := hγ.init
  have H₁ := isMaxSol_maxFlow (hex' 0 y)
  set J' := maxDomain u' univ 0 y with hJ'
  set γ' : ℝ → ℂ := fun t => maxFlow u' univ t 0 y with hγ'def
  have hfl : ∀ s, flowOf u' s 0 y = γ' s := fun s => rfl
  rw [hfl]
  have hγ'0 : γ' 0 = y := H₁.init
  rcases eq_or_lt_of_le htbar with h0 | hpos
  · -- `t̄ = 0`: only `t = 0`
    have : t = 0 := le_antisymm (h0 ▸ ht.2) ht.1
    subst this
    rw [hγ'0]
    exact hγ0.symm
  -- the maximal solution of `u'` through `(t̄, γ(t̄))`
  have H₂ := isMaxSol_maxFlow (hex' tbar (γ tbar))
  set J₂ := maxDomain u' univ tbar (γ tbar) with hJ₂
  set γ₂ : ℝ → ℂ := fun t => maxFlow u' univ t tbar (γ tbar) with hγ₂def
  have hγ₂0 : γ₂ tbar = γ tbar := H₂.init
  obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.isOpen_iff.mp H₁.isOpen 0 H₁.mem
  obtain ⟨ε₂, hε₂, hb₂⟩ := Metric.isOpen_iff.mp H₂.isOpen tbar H₂.mem
  rw [Real.ball_eq_Ioo] at hb₁ hb₂
  -- the glued curve
  set η : ℝ → ℂ := fun s => if s < 0 then γ' s else if s ≤ tbar then γ s else γ₂ s with hηdef
  have hη_neg : ∀ s, s < 0 → η s = γ' s := fun s hs => by simp [hηdef, hs]
  have hη_mid : ∀ s ∈ Icc (0 : ℝ) tbar, η s = γ s := fun s hs => by
    simp [hηdef, not_lt.mpr hs.1, hs.2]
  have hη_pos : ∀ s, tbar < s → η s = γ₂ s := fun s hs => by
    have h1 : ¬ s < 0 := by linarith
    have h2 : ¬ s ≤ tbar := not_le.mpr hs
    simp [hηdef, h1, h2]
  set K : Set ℝ := Ioo (-ε₁) (tbar + ε₂) with hK
  have hloc : IsLocalSol u' univ 0 y K η := by
    refine ⟨isOpen_Ioo, ordConnected_Ioo, ⟨by linarith, by linarith⟩, ?_, fun _ _ => mem_univ _,
      ?_⟩
    · rw [hη_mid 0 ⟨le_rfl, htbar⟩, hγ0]
    intro s hs
    rcases lt_trichotomy s 0 with hs0 | hs0 | hs0
    · -- `s < 0`: `η = γ'` near `s`
      have hsJ : s ∈ J' := hb₁ ⟨by simpa using hs.1, by linarith⟩
      have hev : η =ᶠ[𝓝 s] γ' :=
        eventually_of_mem (Iio_mem_nhds hs0) fun r hr => hη_neg r hr
      rw [hη_neg s hs0]
      exact (H₁.hasDerivAt s hsJ).congr_of_eventuallyEq hev
    · -- `s = 0`: left `γ'`, right `γ`
      subst hs0
      rw [hη_mid 0 ⟨le_rfl, htbar⟩, hγ0]
      apply hasDerivAt_of_Iic_Ici
      · have hd := (H₁.hasDerivAt 0 H₁.mem).hasDerivWithinAt (s := Iic 0)
        rw [hγ'0] at hd
        refine hd.congr_of_eventuallyEq ?_ ?_
        · refine eventually_nhdsWithin_of_forall fun r hr => ?_
          rcases eq_or_lt_of_le (show r ≤ 0 from hr) with hr0 | hr0
          · rw [hr0, hη_mid 0 ⟨le_rfl, htbar⟩, hγ0, hγ'0]
          · exact hη_neg r hr0
        · rw [hη_mid 0 ⟨le_rfl, htbar⟩, hγ0, hγ'0]
      · have hd := (hγd 0).hasDerivWithinAt (s := Ici 0)
        rw [hγ0, ← heq 0 ⟨le_rfl, htbar⟩] at hd
        refine hd.congr_of_eventuallyEq ?_ (hη_mid 0 ⟨le_rfl, htbar⟩)
        exact eventually_of_mem (Icc_mem_nhdsGE hpos) fun r hr => hη_mid r hr
    rcases lt_trichotomy s tbar with hst | hst | hst
    · -- `0 < s < t̄`: `η = γ` near `s`
      have hev : η =ᶠ[𝓝 s] γ :=
        eventually_of_mem (Ioo_mem_nhds hs0 hst) fun r hr => hη_mid r ⟨hr.1.le, hr.2.le⟩
      rw [hη_mid s ⟨hs0.le, hst.le⟩, heq s ⟨hs0.le, hst.le⟩]
      exact (hγd s).congr_of_eventuallyEq hev
    · -- `s = t̄`: left `γ`, right `γ₂`
      subst hst
      rw [hη_mid s ⟨htbar, le_rfl⟩]
      apply hasDerivAt_of_Iic_Ici
      · have hd := (hγd s).hasDerivWithinAt (s := Iic s)
        rw [← heq s ⟨htbar, le_rfl⟩] at hd
        refine hd.congr_of_eventuallyEq ?_ (hη_mid s ⟨htbar, le_rfl⟩)
        exact eventually_of_mem (Ioc_mem_nhdsLE hpos) fun r hr => hη_mid r ⟨hr.1.le, hr.2⟩
      · have hd := (H₂.hasDerivAt s H₂.mem).hasDerivWithinAt (s := Ici s)
        rw [hγ₂0] at hd
        refine hd.congr_of_eventuallyEq ?_ ?_
        · refine eventually_nhdsWithin_of_forall fun r hr => ?_
          rcases eq_or_lt_of_le (show s ≤ r from hr) with hr0 | hr0
          · rw [← hr0, hη_mid s ⟨htbar, le_rfl⟩, hγ₂0]
          · exact hη_pos r hr0
        · rw [hη_mid s ⟨htbar, le_rfl⟩, hγ₂0]
    · -- `s > t̄`: `η = γ₂` near `s`
      have hsJ : s ∈ J₂ := hb₂ ⟨by linarith, hs.2⟩
      have hev : η =ᶠ[𝓝 s] γ₂ :=
        eventually_of_mem (Ioi_mem_nhds hst) fun r hr => hη_pos r hr
      rw [hη_pos s hst]
      exact (H₂.hasDerivAt s hsJ).congr_of_eventuallyEq hev
  obtain ⟨-, hEq⟩ := H₁.maximal K η hloc
  have htK : t ∈ K := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  rw [← hEq htK, hη_mid t ht]

end ClockH

end NonUniqueEuler.Smooth
