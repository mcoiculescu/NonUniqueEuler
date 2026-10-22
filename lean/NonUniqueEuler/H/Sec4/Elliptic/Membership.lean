import NonUniqueEuler.H.Sec4.Elliptic.Pieces
import NonUniqueEuler.I.Infra.SobolevOneD.CompLog

/-!
# Helpers for `P/Sec4/Elliptic`: the membership `𝒢_ℓ g ∈ H^m((0,∞))`

`memH1On_of_pieces`: a function `ψ` on `(0, ∞)` which equals `A rⁿ` on `(0, ρ₋)`, `B r^{-n}`
(`n ≥ 1`) on `(ρ₊, ∞)`, and `u ∘ log` everywhere on `(0, ∞)` with `u ∈ H^m(ℝ)`, lies in
`H^m((0, ∞))`, provided `u ∘ log` has locally integrable weak derivatives on `(0, ∞)`
(`exists_secNormSq_comp_log_le`). The weak derivatives are square integrable on the three
pieces `(0, ρ₋)`, `(ρ₋/2, 2ρ₊)`, `(ρ₊, ∞)` by uniqueness of weak derivatives: they are the
classical derivatives of `A rⁿ` (bounded), the `L²` weak derivatives of `u ∘ log` on the middle
interval (`memH1On_comp_log`), and the classical derivatives `c r^{-n-j}` of `B r^{-n}`.

All proofs are complete (modulo the interface files imported).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff

namespace NonUniqueEuler.Sob.EllipticH

theorem memH1On_of_pieces {m : ℕ} {ψ u : ℝ → ℂ} {ρm ρp : ℝ} (hρm : 0 < ρm) (hρ : ρm < ρp)
    {n : ℕ} (hn : 1 ≤ n) (A B : ℂ)
    (h0 : ∀ r ∈ Ioo 0 ρm, ψ r = A * (r : ℂ) ^ n)
    (hinf : ∀ r ∈ Ioi ρp, ψ r = B * (r : ℂ) ^ (-(n : ℤ)))
    (hmid : ∀ r ∈ Ioi (0 : ℝ), ψ r = u (Real.log r))
    (hu : MemH1On m univ u)
    (hwd : ∀ j ≤ m, ∃ h : ℝ → ℂ, LocallyIntegrableOn h (Ioi 0) ∧
      HasWeakDerivOn (Ioi 0) (derivList j) (fun r => u (Real.log r)) h) :
    MemH1On m (Ioi 0) ψ := by
  have hρp : 0 < ρp := hρm.trans hρ
  have hW₁ : Ioo (0 : ℝ) ρm ⊆ Ioi 0 := fun r hr => hr.1
  have hW₂ : Ioo (ρm / 2) (2 * ρp) ⊆ Ioi 0 := fun r hr => (half_pos hρm).trans hr.1
  have hW₃ : Ioi ρp ⊆ Ioi (0 : ℝ) := fun r hr => hρp.trans hr
  have hcover : Ioi (0 : ℝ) ⊆ Ioo 0 ρm ∪ Ioo (ρm / 2) (2 * ρp) ∪ Ioi ρp := by
    intro r hr
    simp only [mem_union, mem_Ioo, mem_Ioi] at hr ⊢
    by_cases h1 : r < ρm
    · exact Or.inl (Or.inl ⟨hr, h1⟩)
    by_cases h3 : ρp < r
    · exact Or.inr h3
    rw [not_lt] at h1 h3
    exact Or.inl (Or.inr ⟨by linarith, by linarith⟩)
  have hglue : ∀ F : ℝ → ℂ, MemLp F 2 (volume.restrict (Ioo 0 ρm)) →
      MemLp F 2 (volume.restrict (Ioo (ρm / 2) (2 * ρp))) →
      MemLp F 2 (volume.restrict (Ioi ρp)) → MemLp F 2 (volume.restrict (Ioi 0)) :=
    fun F h1 h2 h3 =>
      (memLp_two_union (memLp_two_union h1 h2) h3).mono_measure
        (Measure.restrict_mono hcover le_rfl)
  -- the piece near `0`
  set F₀ : ℝ → ℂ := fun s => A * (s : ℂ) ^ n with hF₀def
  have hF₀ : ContDiff ℝ ∞ F₀ := contDiff_const.mul (Complex.ofRealCLM.contDiff.pow n)
  have hF₀c : ∀ j, Continuous (iteratedDeriv j F₀) := fun j =>
    hF₀.continuous_iteratedDeriv j (by exact_mod_cast le_top)
  have hF₀L : ∀ j, MemLp (iteratedDeriv j F₀) 2 (volume.restrict (Ioo 0 ρm)) := fun j =>
    memLp_Ioo_of_continuousOn (hF₀c j).continuousOn
  -- the piece near `∞`
  set F₁ : ℝ → ℂ := fun s => B * (s : ℂ) ^ (-(n : ℤ)) with hF₁def
  have hF₁eq : ∀ j, ∀ s ∈ Ioi ρp, iteratedDeriv j F₁ s =
      B * (∏ i ∈ Finset.range j, (((-(n : ℤ) : ℤ) : ℂ) - i)) * (s : ℂ) ^ (-(n : ℤ) - j) :=
    fun j s hs => iteratedDeriv_const_mul_zpow B (-(n : ℤ)) j (ne_of_gt (hW₃ hs))
  have hF₁L : ∀ j, MemLp (iteratedDeriv j F₁) 2 (volume.restrict (Ioi ρp)) := fun j =>
    memLp_congr_on measurableSet_Ioi (fun s hs => (hF₁eq j s hs).symm)
      (memLp_const_mul_zpow_Ioi _ (by omega) hρp)
  have hF₁c : ∀ j, ContinuousOn (iteratedDeriv j F₁) (Ioi ρp) := by
    intro j
    have hc : ContinuousOn (fun s : ℝ =>
        B * (∏ i ∈ Finset.range j, (((-(n : ℤ) : ℤ) : ℂ) - i)) * (s : ℂ) ^ (-(n : ℤ) - j))
        (Ioi ρp) := by
      refine continuousOn_const.mul ?_
      refine (Complex.continuous_ofReal.continuousOn).zpow₀ _ fun s hs => Or.inl ?_
      exact_mod_cast ne_of_gt (hW₃ hs)
    exact hc.congr fun s hs => hF₁eq j s hs
  -- the middle piece
  have hmidH := memH1On_comp_log hu (a := ρm / 2) (b := 2 * ρp) (half_pos hρm)
  refine ⟨?_, fun j hj => ?_⟩
  · refine hglue ψ ?_ ?_ ?_
    · refine memLp_congr_on measurableSet_Ioo (fun s hs => ?_) (hF₀L 0)
      rw [iteratedDeriv_zero, h0 s hs]
    · exact memLp_congr_on measurableSet_Ioo (fun s hs => (hmid s (hW₂ hs)).symm) hmidH.memLp
    · refine memLp_congr_on measurableSet_Ioi (fun s hs => ?_) (hF₁L 0)
      rw [iteratedDeriv_zero, hinf s hs]
  · obtain ⟨h, hli, hw⟩ := hwd j hj
    have hwψ : HasWeakDerivOn (Ioi 0) (derivList j) ψ h :=
      hw.congr_ae (ae_of_all _ fun x hx => (hmid x hx).symm) (ae_of_all _ fun _ _ => rfl)
    refine ⟨h, hglue h ?_ ?_ ?_, hwψ⟩
    · have hcd : ContDiffOn ℝ j F₀ (Ioo 0 ρm) := (hF₀.of_le (by exact_mod_cast le_top)).contDiffOn
      have hH := hasWeakDerivOn_of_contDiffOn isOpen_Ioo (vs := derivList j) (by simp) hcd
      rw [iterDirDeriv_derivList] at hH
      exact memLp_of_weakDeriv_piece isOpen_Ioo hW₁ hwψ hli h0 hH
        ((hF₀c j).continuousOn.locallyIntegrableOn measurableSet_Ioo) (hF₀L j)
    · obtain ⟨H, hHL, hH⟩ := hmidH.deriv j hj
      exact memLp_of_weakDeriv_piece isOpen_Ioo hW₂ hw hli (fun _ _ => rfl) hH
        (locallyIntegrableOn_Ioo_of_memLp hHL) hHL
    · have hcd : ContDiffOn ℝ j F₁ (Ioi ρp) :=
        (contDiffOn_const_mul_zpow B (-(n : ℤ))).mono hW₃
      have hH := hasWeakDerivOn_of_contDiffOn isOpen_Ioi (vs := derivList j) (by simp) hcd
      rw [iterDirDeriv_derivList] at hH
      exact memLp_of_weakDeriv_piece isOpen_Ioi hW₃ hwψ hli hinf hH
        ((hF₁c j).locallyIntegrableOn measurableSet_Ioi) (hF₁L j)

end NonUniqueEuler.Sob.EllipticH
