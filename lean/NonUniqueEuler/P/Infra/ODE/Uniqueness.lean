import NonUniqueEuler.Defs.Infra.ODE
import NonUniqueEuler.I.Infra.ODE.Existence
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Proof (I-ODE): uniqueness for `ψ'' = V ψ + F`

Proof of `I/Infra/ODE/Uniqueness.lean`.

The pair `Y = (ψ, ψ') : ℝ → ℂ × ℂ` solves `Y' = v ξ Y` with `v ξ (a, b) = (b, V ξ * a + F ξ)`,
which is Lipschitz in `Y` with constant `max 1 C` on a compact interval `[a, b] ⊆ s` where
`‖V‖ ≤ C` (`IsCompact.exists_bound_of_continuousOn`). Mathlib's
`ODE_solution_unique_of_mem_Icc_right` / `_left` give uniqueness forwards / backwards on
`[a, b]`; for a general point `ξ ∈ s` one applies them on `[ξ₀, ξ]` or `[ξ, ξ₀]`, contained in
`s` by `Set.OrdConnected.out`. `eqOn_sol` and `sol_restart` follow from `sol_spec`
(`I/Infra/ODE/Existence.lean`).
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace NonUniqueEuler.LinODE

variable {V F : ℝ → ℂ} {s : Set ℝ} {ψ ψ' φ φ' : ℝ → ℂ}

namespace UniquenessAux

/-- The vector field of the first-order system for `ψ'' = V ψ + F`. -/
private def field (V F : ℝ → ℂ) (t : ℝ) (y : ℂ × ℂ) : ℂ × ℂ := (y.2, V t * y.1 + F t)

private theorem field_lipschitz {t C : ℝ} (hC : ‖V t‖ ≤ C) :
    LipschitzWith (Real.toNNReal (max 1 C)) (field V F t) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  have hK : ((Real.toNNReal (max 1 C) : NNReal) : ℝ) = max 1 C :=
    Real.coe_toNNReal _ (le_trans zero_le_one (le_max_left _ _))
  rw [hK]
  simp only [field, Prod.dist_eq, dist_add_right]
  have h1 : dist y.1 z.1 ≤ max (dist y.1 z.1) (dist y.2 z.2) := le_max_left _ _
  have h2 : dist y.2 z.2 ≤ max (dist y.1 z.1) (dist y.2 z.2) := le_max_right _ _
  have hm0 : 0 ≤ max (dist y.1 z.1) (dist y.2 z.2) := le_trans dist_nonneg h1
  have hV : dist (V t * y.1) (V t * z.1) = ‖V t‖ * dist y.1 z.1 := by
    rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul]
  rw [hV]
  apply max_le
  · calc dist y.2 z.2 ≤ 1 * max (dist y.1 z.1) (dist y.2 z.2) := by rw [one_mul]; exact h2
      _ ≤ max 1 C * max (dist y.1 z.1) (dist y.2 z.2) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hm0
  · calc ‖V t‖ * dist y.1 z.1 ≤ C * max (dist y.1 z.1) (dist y.2 z.2) :=
          mul_le_mul hC h1 dist_nonneg (le_trans (norm_nonneg _) hC)
      _ ≤ max 1 C * max (dist y.1 z.1) (dist y.2 z.2) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hm0

/-- The pair `(ψ, ψ')` has derivative `field V F ξ (ψ ξ, ψ' ξ)` within `s`. -/
private theorem hasDerivWithinAt_pair (h : IsInhomSolOn V F s ψ ψ') {ξ : ℝ} (hξ : ξ ∈ s) :
    HasDerivWithinAt (fun t => (ψ t, ψ' t)) (field V F ξ (ψ ξ, ψ' ξ)) s ξ :=
  (h.hasDerivWithinAt ξ hξ).prodMk (h.hasDerivWithinAt' ξ hξ)

private theorem continuousOn_pair (h : IsInhomSolOn V F s ψ ψ') :
    ContinuousOn (fun t => (ψ t, ψ' t)) s :=
  h.continuousOn.prodMk h.continuousOn'

/-- Uniqueness on a compact interval, forwards and backwards. -/
private theorem eq_Icc {a b : ℝ} (hab : a ≤ b) (hV : ContinuousOn V (Icc a b))
    (h : IsInhomSolOn V F (Icc a b) ψ ψ') (h' : IsInhomSolOn V F (Icc a b) φ φ') :
    ((ψ a = φ a ∧ ψ' a = φ' a) → (ψ b = φ b ∧ ψ' b = φ' b)) ∧
      ((ψ b = φ b ∧ ψ' b = φ' b) → (ψ a = φ a ∧ ψ' a = φ' a)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hV
  have hLip : ∀ t ∈ Icc a b,
      LipschitzOnWith (Real.toNNReal (max 1 C)) (field V F t) univ := by
    intro t ht
    exact (field_lipschitz (F := F) (hC t ht)).lipschitzOnWith
  constructor
  · rintro ⟨e1, e2⟩
    have := ODE_solution_unique_of_mem_Icc_right (v := field V F) (s := fun _ => univ)
      (fun t ht => hLip t (Ico_subset_Icc_self ht)) (continuousOn_pair h)
      (fun t ht => (hasDerivWithinAt_pair h (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ht)) (fun _ _ => mem_univ _) (continuousOn_pair h')
      (fun t ht => (hasDerivWithinAt_pair h' (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ht)) (fun _ _ => mem_univ _) (by simp [e1, e2])
      (right_mem_Icc.2 hab)
    simpa using this
  · rintro ⟨e1, e2⟩
    have := ODE_solution_unique_of_mem_Icc_left (v := field V F) (s := fun _ => univ)
      (fun t ht => hLip t (Ioc_subset_Icc_self ht)) (continuousOn_pair h)
      (fun t ht => (hasDerivWithinAt_pair h (Ioc_subset_Icc_self ht)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE_of_mem ht)) (fun _ _ => mem_univ _) (continuousOn_pair h')
      (fun t ht => (hasDerivWithinAt_pair h' (Ioc_subset_Icc_self ht)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE_of_mem ht)) (fun _ _ => mem_univ _) (by simp [e1, e2])
      (left_mem_Icc.2 hab)
    simpa using this

end UniquenessAux

open UniquenessAux in
/-- Uniqueness on an interval on which `V` is continuous. -/
theorem IsInhomSolOn.eqOn (hs : s.OrdConnected) (hV : ContinuousOn V s)
    (h : IsInhomSolOn V F s ψ ψ') (h' : IsInhomSolOn V F s φ φ') {ξ₀ : ℝ} (hξ₀ : ξ₀ ∈ s)
    (h0 : ψ ξ₀ = φ ξ₀) (h0' : ψ' ξ₀ = φ' ξ₀) : EqOn ψ φ s ∧ EqOn ψ' φ' s := by
  have key : ∀ ξ ∈ s, ψ ξ = φ ξ ∧ ψ' ξ = φ' ξ := by
    intro ξ hξ
    rcases le_total ξ₀ ξ with hle | hle
    · have hsub : Icc ξ₀ ξ ⊆ s := hs.out hξ₀ hξ
      exact (eq_Icc hle (hV.mono hsub) (h.mono hsub) (h'.mono hsub)).1 ⟨h0, h0'⟩
    · have hsub : Icc ξ ξ₀ ⊆ s := hs.out hξ hξ₀
      exact (eq_Icc hle (hV.mono hsub) (h.mono hsub) (h'.mono hsub)).2 ⟨h0, h0'⟩
  exact ⟨fun ξ hξ => (key ξ hξ).1, fun ξ hξ => (key ξ hξ).2⟩

/-- Uniqueness on an interval on which `V` is continuous (homogeneous equation). -/
theorem IsSolOn.eqOn (hs : s.OrdConnected) (hV : ContinuousOn V s)
    (h : IsSolOn V s ψ ψ') (h' : IsSolOn V s φ φ') {ξ₀ : ℝ} (hξ₀ : ξ₀ ∈ s)
    (h0 : ψ ξ₀ = φ ξ₀) (h0' : ψ' ξ₀ = φ' ξ₀) : EqOn ψ φ s ∧ EqOn ψ' φ' s :=
  IsInhomSolOn.eqOn hs hV h.toInhom h'.toInhom hξ₀ h0 h0'

/-- A solution with zero data at one point vanishes on the whole interval. -/
theorem IsSolOn.eqOn_zero (hs : s.OrdConnected) (hV : ContinuousOn V s)
    (h : IsSolOn V s ψ ψ') {ξ₀ : ℝ} (hξ₀ : ξ₀ ∈ s) (h0 : ψ ξ₀ = 0) (h0' : ψ' ξ₀ = 0) :
    EqOn ψ 0 s ∧ EqOn ψ' 0 s :=
  IsSolOn.eqOn hs hV h IsSolOn.zero hξ₀ h0 h0'

/-- Every solution on an interval containing `ξ₀`, with data `y₀` at `ξ₀`, is the global
solution `sol V ξ₀ y₀` there. -/
theorem eqOn_sol (hV : Continuous V) (hs : s.OrdConnected) (h : IsSolOn V s ψ ψ') {ξ₀ : ℝ}
    (hξ₀ : ξ₀ ∈ s) {y₀ : ℂ × ℂ} (h0 : ψ ξ₀ = y₀.1) (h0' : ψ' ξ₀ = y₀.2) :
    ∀ ξ ∈ s, ψ ξ = (sol V ξ₀ y₀ ξ).1 ∧ ψ' ξ = (sol V ξ₀ y₀ ξ).2 := by
  obtain ⟨hsol, hsol0⟩ := sol_spec hV ξ₀ y₀
  have := IsSolOn.eqOn hs hV.continuousOn h (hsol.mono (subset_univ s)) hξ₀
    (by rw [h0, hsol0]) (by rw [h0', hsol0])
  exact fun ξ hξ => ⟨this.1 hξ, this.2 hξ⟩

/-- Restarting the global solution at another point gives the same solution. -/
theorem sol_restart (hV : Continuous V) (ξ₀ ξ₁ : ℝ) (y₀ : ℂ × ℂ) :
    sol V ξ₁ (sol V ξ₀ y₀ ξ₁) = sol V ξ₀ y₀ := by
  obtain ⟨hY, -⟩ := sol_spec hV ξ₀ y₀
  have := eqOn_sol hV ordConnected_univ hY (mem_univ ξ₁) (y₀ := sol V ξ₀ y₀ ξ₁) rfl rfl
  funext ξ
  obtain ⟨e1, e2⟩ := this ξ (mem_univ ξ)
  exact Prod.ext e1.symm e2.symm

end NonUniqueEuler.LinODE
