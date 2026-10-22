import NonUniqueEuler.Defs.Sec2.Conventions
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv

/-!
# Helpers for `I/Sec3/VelocityField`: a global `L²` gradient gives local `H¹`

Helper file of `P/Sec3/VelocityField.lean` (the remark `03_compactness.tex:243-247`).

* `memHOn_one_of_hasGradH`: if `u ∈ L²(V)` is locally integrable on the open set `V` and its
  weak gradient on the plane lies in `L²` (`Prelim.HasGradH 0 u`), then `u ∈ H¹(V)` and every
  term `‖∂^γ u‖_{L²(V)}`, `|γ| ≤ 1`, is at most `‖u‖_{L²(V)} + ‖∇u‖_{L²}`; hence
  `‖u‖_{H¹(V)} ≤ (#{|γ| ≤ 1} (‖u‖_{L²(V)} + ‖∇u‖_{L²})²)^{1/2}`.

The weak derivatives on the plane restrict to `V` (`HasWeakDerivOn.mono`), and the chosen weak
derivatives on `V` agree a.e. on `V` with them (`Sob.weakDerivOn_ae_eq`).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace NonUniqueEuler.H.VelocityField

/-- The multi-indices of order `≤ 1`. -/
theorem mem_multiIdx_one {γ : ℕ × ℕ} (hγ : γ ∈ Sob.multiIdx 1) :
    γ = (0, 0) ∨ γ = (1, 0) ∨ γ = (0, 1) := by
  rw [Sob.mem_multiIdx] at hγ
  obtain ⟨a, b⟩ := γ
  simp only at hγ
  have : (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) := by omega
  rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

theorem l2On_le_l2 {V : Set ℂ} {G : ℂ → ℂ} (hG : MemLp G 2 volume) : Sob.l2On V G ≤ Sob.l2 G :=
  ENNReal.toReal_mono hG.eLpNorm_ne_top (eLpNorm_mono_measure _ Measure.restrict_le_self)

/-- One direction of the weak gradient: restriction to `V` and the norm bound. -/
theorem weakPartialOn_dir {u : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V) (hg : Prelim.HasGradH 0 u)
    (l : Fin 2) :
    (∃ G : ℂ → ℂ, MemLp G 2 (volume.restrict V) ∧ Sob.HasWeakDerivOn V [Prelim.e2 l] u G) ∧
      Sob.l2On V (Sob.weakDerivOn V [Prelim.e2 l] u) ≤
        Sob.l2 (Sob.weakDerivOn univ [Prelim.e2 l] u) := by
  obtain ⟨G, hGH, hGw⟩ := hg.deriv l
  have hG2 : MemLp G 2 volume := (Sob.memH_iff.1 hGH).1
  have hGloc : LocallyIntegrable G volume := hG2.locallyIntegrable one_le_two
  have hGwV : Sob.HasWeakDerivOn V [Prelim.e2 l] u G := hGw.mono (subset_univ V)
  refine ⟨⟨G, hG2.restrict V, hGwV⟩, ?_⟩
  have h1 := Sob.weakDerivOn_ae_eq hV (hGloc.locallyIntegrableOn V) hGwV
  have h2 := Sob.weakDerivOn_ae_eq isOpen_univ (hGloc.locallyIntegrableOn univ) hGw
  have e1 : Sob.l2On V (Sob.weakDerivOn V [Prelim.e2 l] u) = Sob.l2On V G := by
    unfold Sob.l2On
    rw [eLpNorm_congr_ae ((ae_restrict_iff' hV.measurableSet).2 h1)]
  have e2 : Sob.l2 (Sob.weakDerivOn univ [Prelim.e2 l] u) = Sob.l2 G := by
    unfold Sob.l2
    rw [eLpNorm_congr_ae (h2.mono fun x hx => hx (mem_univ x))]
  rw [e1, e2]
  exact l2On_le_l2 hG2

theorem l2_weakPartial_le_gradL2_left (u : ℂ → ℂ) :
    Sob.l2 (Sob.weakPartial (1, 0) u) ≤ Prelim.gradL2 u := by
  unfold Prelim.gradL2
  have h := Real.abs_le_sqrt (x := Sob.l2 (Sob.weakPartial (1, 0) u))
    (y := Sob.l2 (Sob.weakPartial (1, 0) u) ^ 2 + Sob.l2 (Sob.weakPartial (0, 1) u) ^ 2)
    (le_add_of_nonneg_right (sq_nonneg _))
  rwa [abs_of_nonneg (Sob.l2_nonneg _)] at h

theorem l2_weakPartial_le_gradL2_right (u : ℂ → ℂ) :
    Sob.l2 (Sob.weakPartial (0, 1) u) ≤ Prelim.gradL2 u := by
  unfold Prelim.gradL2
  have h := Real.abs_le_sqrt (x := Sob.l2 (Sob.weakPartial (0, 1) u))
    (y := Sob.l2 (Sob.weakPartial (1, 0) u) ^ 2 + Sob.l2 (Sob.weakPartial (0, 1) u) ^ 2)
    (le_add_of_nonneg_left (sq_nonneg _))
  rwa [abs_of_nonneg (Sob.l2_nonneg _)] at h

/-- A function in `L²(V)`, locally integrable on the open set `V`, with weak gradient in `L²` on
the plane, lies in `H¹(V)`, and each term of its `H¹(V)` norm is at most
`‖u‖_{L²(V)} + ‖∇u‖_{L²}`. -/
theorem memHOn_one_of_hasGradH {u : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V)
    (hu : MemLp u 2 (volume.restrict V)) (huloc : LocallyIntegrableOn u V)
    (hg : Prelim.HasGradH 0 u) :
    Sob.MemHOn 1 V u ∧ ∀ γ ∈ Sob.multiIdx 1,
      Sob.l2On V (Sob.weakPartialOn V γ u) ≤ Sob.l2On V u + Prelim.gradL2 u := by
  have h00 : Sob.HasWeakDerivOn V (Sob.pdList (0, 0)) u u := by
    intro φ _
    simp [Sob.pdList]
  have hγ : ∀ γ ∈ Sob.multiIdx 1,
      (∃ g : ℂ → ℂ, MemLp g 2 (volume.restrict V) ∧ Sob.HasWeakDerivOn V (Sob.pdList γ) u g) ∧
        Sob.l2On V (Sob.weakPartialOn V γ u) ≤ Sob.l2On V u + Prelim.gradL2 u := by
    intro γ hγ
    rcases mem_multiIdx_one hγ with rfl | rfl | rfl
    · refine ⟨⟨u, hu, h00⟩, ?_⟩
      have h1 := Sob.weakDerivOn_ae_eq hV huloc h00
      have e : Sob.l2On V (Sob.weakPartialOn V (0, 0) u) = Sob.l2On V u := by
        unfold Sob.l2On Sob.weakPartialOn
        rw [eLpNorm_congr_ae ((ae_restrict_iff' hV.measurableSet).2 h1)]
      rw [e]
      exact le_add_of_nonneg_right (Prelim.gradL2_nonneg u)
    · obtain ⟨hex, hle⟩ := weakPartialOn_dir hV hg 0
      rw [Prelim.pdList_one_zero]
      refine ⟨hex, ?_⟩
      have : Sob.l2On V (Sob.weakPartialOn V (1, 0) u) ≤ Prelim.gradL2 u := by
        unfold Sob.weakPartialOn
        rw [Prelim.pdList_one_zero]
        refine hle.trans ?_
        have := l2_weakPartial_le_gradL2_left u
        unfold Sob.weakPartial Sob.weakPartialOn at this
        rwa [Prelim.pdList_one_zero] at this
      exact this.trans (le_add_of_nonneg_left (Sob.l2On_nonneg _ _))
    · obtain ⟨hex, hle⟩ := weakPartialOn_dir hV hg 1
      rw [Prelim.pdList_zero_one]
      refine ⟨hex, ?_⟩
      have : Sob.l2On V (Sob.weakPartialOn V (0, 1) u) ≤ Prelim.gradL2 u := by
        unfold Sob.weakPartialOn
        rw [Prelim.pdList_zero_one]
        refine hle.trans ?_
        have := l2_weakPartial_le_gradL2_right u
        unfold Sob.weakPartial Sob.weakPartialOn at this
        rwa [Prelim.pdList_zero_one] at this
      exact this.trans (le_add_of_nonneg_left (Sob.l2On_nonneg _ _))
  exact ⟨⟨hu, fun γ h => (hγ γ h).1⟩, fun γ h => (hγ γ h).2⟩

/-- The `H¹(V)` norm from termwise bounds. -/
theorem normHOn_le_of_forall_le {V : Set ℂ} {u : ℂ → ℂ} {K : ℝ}
    (h : ∀ γ ∈ Sob.multiIdx 1, Sob.l2On V (Sob.weakPartialOn V γ u) ≤ K) :
    Sob.normHOn 1 V u ≤ Real.sqrt ((Sob.multiIdx 1).card • K ^ 2) := by
  unfold Sob.normHOn
  refine Real.sqrt_le_sqrt (Finset.sum_le_card_nsmul _ _ _ fun γ hγ => ?_)
  exact pow_le_pow_left₀ (Sob.l2On_nonneg _ _) (h γ hγ) 2

end NonUniqueEuler.H.VelocityField
