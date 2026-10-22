import NonUniqueEuler.Defs.Infra.ODE
import NonUniqueEuler.I.Infra.ODE.Uniqueness
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Proof of the interface (I-ODE): the Wronskian of `ψ'' = V ψ + F`

Proves the declarations of `NonUniqueEuler/I/Infra/ODE/Wronskian.lean` (statements copied
verbatim):
* `hasDerivWithinAt_wronskian`: product rule and `ring`;
* `wronskian_sub_eq_integral`: FTC (`intervalIntegral.integral_eq_sub_of_hasDeriv_right`) on
  `uIcc ξ η ⊆ s`; at interior points `s` is a neighbourhood, so the derivative within `s` is a
  full derivative;
* `wronskian_eq`: the integrated identity with `F₁ = F₂ = 0`;
* `exists_eq_const_mul_of_wronskian_eq_zero`: choice of `c` at `ξ₀`, then uniqueness
  (`IsSolOn.eqOn`, `I/Infra/ODE/Uniqueness.lean`).
-/

noncomputable section

open Set Filter Topology

namespace NonUniqueEuler.LinODE

variable {V F₁ F₂ : ℝ → ℂ} {s : Set ℝ} {ψ₁ ψ₁' ψ₂ ψ₂' : ℝ → ℂ}

/-- The derivative of the Wronskian of two solutions of `ψ'' = V ψ + F_i`. -/
theorem hasDerivWithinAt_wronskian (h₁ : IsInhomSolOn V F₁ s ψ₁ ψ₁')
    (h₂ : IsInhomSolOn V F₂ s ψ₂ ψ₂') :
    ∀ ξ ∈ s, HasDerivWithinAt (wronskian ψ₁ ψ₁' ψ₂ ψ₂') (ψ₁ ξ * F₂ ξ - F₁ ξ * ψ₂ ξ) s ξ := by
  intro ξ hξ
  have h := ((h₁.hasDerivWithinAt ξ hξ).mul (h₂.hasDerivWithinAt' ξ hξ)).sub
    ((h₁.hasDerivWithinAt' ξ hξ).mul (h₂.hasDerivWithinAt ξ hξ))
  exact h.congr_deriv (by ring)

/-- The Wronskian of two inhomogeneous solutions is continuous on `s`. -/
private theorem continuousOn_wronskian (h₁ : IsInhomSolOn V F₁ s ψ₁ ψ₁')
    (h₂ : IsInhomSolOn V F₂ s ψ₂ ψ₂') : ContinuousOn (wronskian ψ₁ ψ₁' ψ₂ ψ₂') s :=
  fun ξ hξ => (hasDerivWithinAt_wronskian h₁ h₂ ξ hξ).continuousWithinAt

/-- The integrated Wronskian identity for inhomogeneous solutions. -/
theorem wronskian_sub_eq_integral (hs : s.OrdConnected) (hF₁ : ContinuousOn F₁ s)
    (hF₂ : ContinuousOn F₂ s) (h₁ : IsInhomSolOn V F₁ s ψ₁ ψ₁')
    (h₂ : IsInhomSolOn V F₂ s ψ₂ ψ₂') {ξ η : ℝ} (hξ : ξ ∈ s) (hη : η ∈ s) :
    wronskian ψ₁ ψ₁' ψ₂ ψ₂' η - wronskian ψ₁ ψ₁' ψ₂ ψ₂' ξ =
      ∫ ζ in ξ..η, (ψ₁ ζ * F₂ ζ - F₁ ζ * ψ₂ ζ) := by
  have hsub : uIcc ξ η ⊆ s := hs.uIcc_subset hξ hη
  have hint : ContinuousOn (fun ζ => ψ₁ ζ * F₂ ζ - F₁ ζ * ψ₂ ζ) s :=
    (h₁.continuousOn.mul hF₂).sub (hF₁.mul h₂.continuousOn)
  symm
  refine intervalIntegral.integral_eq_sub_of_hasDeriv_right
    ((continuousOn_wronskian h₁ h₂).mono hsub) (fun x hx => ?_)
    ((hint.mono hsub).intervalIntegrable)
  have hxs : x ∈ s := hsub (Ioo_subset_Icc_self hx)
  have hnhds : s ∈ 𝓝 x := Filter.mem_of_superset (Icc_mem_nhds hx.1 hx.2) hsub
  exact ((hasDerivWithinAt_wronskian h₁ h₂ x hxs).hasDerivAt hnhds).hasDerivWithinAt

/-- The Wronskian of two homogeneous solutions is constant on an interval. -/
theorem wronskian_eq (hs : s.OrdConnected) (h₁ : IsSolOn V s ψ₁ ψ₁')
    (h₂ : IsSolOn V s ψ₂ ψ₂') :
    ∀ ξ ∈ s, ∀ η ∈ s, wronskian ψ₁ ψ₁' ψ₂ ψ₂' ξ = wronskian ψ₁ ψ₁' ψ₂ ψ₂' η := by
  intro ξ hξ η hη
  have h0 : ContinuousOn (0 : ℝ → ℂ) s := continuousOn_const
  have h := wronskian_sub_eq_integral (F₁ := 0) (F₂ := 0) hs h0 h0 h₁.toInhom h₂.toInhom hξ hη
  simp only [Pi.zero_apply, mul_zero, zero_mul, sub_self, intervalIntegral.integral_zero] at h
  exact (sub_eq_zero.1 h).symm

/-- A vanishing Wronskian at one point makes two homogeneous solutions proportional on the
whole interval. -/
theorem exists_eq_const_mul_of_wronskian_eq_zero (hs : s.OrdConnected) (hV : ContinuousOn V s)
    (h₁ : IsSolOn V s ψ₁ ψ₁') (h₂ : IsSolOn V s ψ₂ ψ₂') {ξ₀ : ℝ} (hξ₀ : ξ₀ ∈ s)
    (hW : wronskian ψ₁ ψ₁' ψ₂ ψ₂' ξ₀ = 0) (hne : ψ₁ ξ₀ ≠ 0 ∨ ψ₁' ξ₀ ≠ 0) :
    ∃ c : ℂ, EqOn ψ₂ (fun ξ => c * ψ₁ ξ) s ∧ EqOn ψ₂' (fun ξ => c * ψ₁' ξ) s := by
  have hW' : ψ₁ ξ₀ * ψ₂' ξ₀ = ψ₁' ξ₀ * ψ₂ ξ₀ := sub_eq_zero.1 hW
  obtain ⟨c, hc, hc'⟩ : ∃ c : ℂ, ψ₂ ξ₀ = c * ψ₁ ξ₀ ∧ ψ₂' ξ₀ = c * ψ₁' ξ₀ := by
    rcases hne with h | h
    · refine ⟨ψ₂ ξ₀ / ψ₁ ξ₀, by field_simp, ?_⟩
      field_simp
      linear_combination hW'
    · refine ⟨ψ₂' ξ₀ / ψ₁' ξ₀, ?_, by field_simp⟩
      field_simp
      linear_combination -hW'
  exact ⟨c, h₂.eqOn hs hV (h₁.const_mul c) hξ₀ hc hc'⟩

end NonUniqueEuler.LinODE
