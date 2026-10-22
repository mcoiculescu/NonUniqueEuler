import NonUniqueEuler.Defs.Infra.ODE
import NonUniqueEuler.I.Infra.ODE.Uniqueness
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Proof of (I-ODE): explicit solutions and variation of constants

Proves the declarations of `NonUniqueEuler/I/Infra/ODE/Explicit.lean` (same names, same
statements):
* `isSolOn_cexp`: chain rule for `ξ ↦ e^{cξ}`;
* `exists_eq_exp_add_exp`: solve the `2 × 2` system for `(A, B)` at a point `ξ₀ ∈ s`, then
  uniqueness (`IsSolOn.eqOn`, `I/Infra/ODE/Uniqueness.lean`);
* `isInhomSolOn_voc`: the fundamental theorem of calculus within an interval
  (`hasDerivWithinAt_integral_of_continuousOn` below) and the product rule.
-/

noncomputable section

open Set Filter Topology

namespace NonUniqueEuler.LinODE

variable {V F : ℝ → ℂ} {s : Set ℝ} {ψ ψ' ψ₁ ψ₁' ψ₂ ψ₂' : ℝ → ℂ}

/-! ### Helpers -/

/-- Inside an interval `s`, some point `a ∈ s` with `a ≤ ξ` has `Ici a` as a neighbourhood
of `ξ` within `s`. -/
private theorem exists_Ici_mem_nhdsWithin {ξ : ℝ} (hξ : ξ ∈ s) :
    ∃ a ∈ s, a ≤ ξ ∧ Ici a ∈ 𝓝[s] ξ := by
  by_cases h : ∃ a ∈ s, a < ξ
  · obtain ⟨a, ha, hlt⟩ := h
    exact ⟨a, ha, hlt.le, mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds hlt)⟩
  · push Not at h
    exact ⟨ξ, hξ, le_rfl, mem_of_superset self_mem_nhdsWithin fun y hy => h y hy⟩

/-- Inside an interval `s`, some point `b ∈ s` with `ξ ≤ b` has `Iic b` as a neighbourhood
of `ξ` within `s`. -/
private theorem exists_Iic_mem_nhdsWithin {ξ : ℝ} (hξ : ξ ∈ s) :
    ∃ b ∈ s, ξ ≤ b ∧ Iic b ∈ 𝓝[s] ξ := by
  by_cases h : ∃ b ∈ s, ξ < b
  · obtain ⟨b, hb, hlt⟩ := h
    exact ⟨b, hb, hlt.le, mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hlt)⟩
  · push Not at h
    exact ⟨ξ, hξ, le_rfl, mem_of_superset self_mem_nhdsWithin fun y hy => h y hy⟩

/-- **FTC within an interval.** If `g` is continuous on the interval `s` and `c, ξ ∈ s`, then
`u ↦ ∫_c^u g` has derivative `g ξ` within `s` at `ξ` (one-sided at an endpoint of `s`). -/
private theorem hasDerivWithinAt_integral_of_continuousOn {g : ℝ → ℂ} (hs : s.OrdConnected)
    (hg : ContinuousOn g s) {c ξ : ℝ} (hc : c ∈ s) (hξ : ξ ∈ s) :
    HasDerivWithinAt (fun u => ∫ η in c..u, g η) (g ξ) s ξ := by
  obtain ⟨a, ha, haξ, hamem⟩ := exists_Ici_mem_nhdsWithin hξ
  obtain ⟨b, hb, hξb, hbmem⟩ := exists_Iic_mem_nhdsWithin hξ
  have hab : Icc a b ⊆ s := hs.out ha hb
  have hmem : Icc a b ∈ 𝓝[s] ξ := by
    rw [← Ici_inter_Iic]; exact inter_mem hamem hbmem
  have : Fact (ξ ∈ Icc a b) := ⟨⟨haξ, hξb⟩⟩
  have hint : IntervalIntegrable g MeasureTheory.volume c ξ :=
    (hg.mono (hs.uIcc_subset hc hξ)).intervalIntegrable
  have hmeas : StronglyMeasurableAtFilter g (𝓝[Icc a b] ξ) :=
    (hg.mono hab).stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc ξ
  have hcont : ContinuousWithinAt g (Icc a b) ξ := (hg.mono hab) ξ ⟨haξ, hξb⟩
  exact (intervalIntegral.integral_hasDerivWithinAt_right (s := Icc a b) (t := Icc a b)
    hint hmeas hcont).mono_of_mem_nhdsWithin hmem

/-! ### The interface declarations -/

/-- Where `V = c²`, `e^{cξ}` is a solution. -/
theorem isSolOn_cexp (c : ℂ) (hV : ∀ ξ ∈ s, V ξ = c ^ 2) :
    IsSolOn V s (fun ξ => Complex.exp (c * ξ)) (fun ξ => c * Complex.exp (c * ξ)) := by
  have hlin : ∀ ξ : ℝ, HasDerivAt (fun y : ℝ => c * (y : ℂ)) c ξ := fun ξ => by
    simpa using ((hasDerivAt_id ξ).ofReal_comp).const_mul c
  have hexp : ∀ ξ : ℝ,
      HasDerivAt (fun y : ℝ => Complex.exp (c * y)) (c * Complex.exp (c * ξ)) ξ := fun ξ => by
    simpa [mul_comm] using (hlin ξ).cexp
  refine ⟨fun ξ _ => (hexp ξ).hasDerivWithinAt, fun ξ hξ => ?_⟩
  have := ((hexp ξ).const_mul c).hasDerivWithinAt (s := s)
  rw [hV ξ hξ]
  exact this.congr_deriv (by ring)

/-- Where `V = c²` (`c ≠ 0`) on an interval, every solution is a combination of `e^{±cξ}`. -/
theorem exists_eq_exp_add_exp (hs : s.OrdConnected) {c : ℂ} (hc : c ≠ 0)
    (hV : ∀ ξ ∈ s, V ξ = c ^ 2) (h : IsSolOn V s ψ ψ') :
    ∃ A B : ℂ, ∀ ξ ∈ s,
      ψ ξ = A * Complex.exp (c * ξ) + B * Complex.exp (-(c * ξ)) ∧
        ψ' ξ = c * (A * Complex.exp (c * ξ) - B * Complex.exp (-(c * ξ))) := by
  rcases s.eq_empty_or_nonempty with hs0 | ⟨ξ₀, hξ₀⟩
  · exact ⟨0, 0, fun ξ hξ => by simp [hs0] at hξ⟩
  set e := Complex.exp (c * ξ₀) with he_def
  have he : e ≠ 0 := Complex.exp_ne_zero _
  set A := (ψ ξ₀ + ψ' ξ₀ / c) / 2 * e⁻¹ with hA
  set B := (ψ ξ₀ - ψ' ξ₀ / c) / 2 * e with hB
  have hV' : ∀ ξ ∈ s, V ξ = (-c) ^ 2 := fun ξ hξ => by rw [hV ξ hξ, neg_sq]
  have hφ := ((isSolOn_cexp c hV).const_mul A).add ((isSolOn_cexp (-c) hV').const_mul B)
  have hVc : ContinuousOn V s := (continuousOn_const (c := c ^ 2)).congr fun ξ hξ => hV ξ hξ
  have hneg : Complex.exp (-c * ξ₀) = e⁻¹ := by
    rw [neg_mul, Complex.exp_neg]
  have h0 : ψ ξ₀ = A * Complex.exp (c * ξ₀) + B * Complex.exp (-c * ξ₀) := by
    rw [hneg, ← he_def, hA, hB]
    field_simp
    ring
  have h0' : ψ' ξ₀ = A * (c * Complex.exp (c * ξ₀)) + B * (-c * Complex.exp (-c * ξ₀)) := by
    rw [hneg, ← he_def, hA, hB]
    field_simp
    ring
  obtain ⟨hEq, hEq'⟩ := h.eqOn hs hVc hφ hξ₀ h0 h0'
  refine ⟨A, B, fun ξ hξ => ⟨?_, ?_⟩⟩
  · rw [hEq hξ]
    simp only [neg_mul]
  · rw [hEq' hξ]
    simp only [neg_mul]
    ring

/-- **Variation of constants.** -/
theorem isInhomSolOn_voc (hs : s.OrdConnected) (h₁ : IsSolOn V s ψ₁ ψ₁')
    (h₂ : IsSolOn V s ψ₂ ψ₂') {W : ℂ} (hW : ∀ ξ ∈ s, wronskian ψ₁ ψ₁' ψ₂ ψ₂' ξ = W)
    (hW0 : W ≠ 0) (hF : ContinuousOn F s) {c d : ℝ} (hc : c ∈ s) (hd : d ∈ s) :
    IsInhomSolOn V F s (voc ψ₁ ψ₂ F W c d) (voc' ψ₁ ψ₁' ψ₂ ψ₂' F W c d) := by
  have hI₁ : ∀ ξ ∈ s, HasDerivWithinAt (fun u => ∫ η in c..u, ψ₁ η * F η)
      (ψ₁ ξ * F ξ) s ξ := fun ξ hξ =>
    hasDerivWithinAt_integral_of_continuousOn (g := fun η => ψ₁ η * F η) hs
      (h₁.continuousOn.mul hF) hc hξ
  have hI₂ : ∀ ξ ∈ s, HasDerivWithinAt (fun u => ∫ η in d..u, ψ₂ η * F η)
      (ψ₂ ξ * F ξ) s ξ := fun ξ hξ =>
    hasDerivWithinAt_integral_of_continuousOn (g := fun η => ψ₂ η * F η) hs
      (h₂.continuousOn.mul hF) hd hξ
  refine ⟨fun ξ hξ => ?_, fun ξ hξ => ?_⟩
  · have := (((h₂.hasDerivWithinAt ξ hξ).fun_mul (hI₁ ξ hξ)).fun_sub
      ((h₁.hasDerivWithinAt ξ hξ).fun_mul (hI₂ ξ hξ))).const_mul W⁻¹
    exact this.congr_deriv (by unfold voc'; ring)
  · have := (((h₂.hasDerivWithinAt' ξ hξ).fun_mul (hI₁ ξ hξ)).fun_sub
      ((h₁.hasDerivWithinAt' ξ hξ).fun_mul (hI₂ ξ hξ))).const_mul W⁻¹
    refine this.congr_deriv ?_
    have hWξ : ψ₁ ξ * ψ₂' ξ - ψ₁' ξ * ψ₂ ξ = W := hW ξ hξ
    have hinv : W⁻¹ * W = 1 := inv_mul_cancel₀ hW0
    unfold voc
    linear_combination (W⁻¹ * F ξ) * hWξ + F ξ * hinv

end NonUniqueEuler.LinODE
