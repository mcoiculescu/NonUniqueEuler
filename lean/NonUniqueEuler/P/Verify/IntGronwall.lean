import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Proof: Grönwall's inequality in integral form, with a variable coefficient

Proof of `NonUniqueEuler/I/Verify/IntGronwall.lean` (manuscript: end of the proof of
Lemma A.1(2), `A_verification.tex:186-190`).

Put `g = b (c + u)`, `B(x) = ∫_α^x b`, `R(x) = c + ∫_α^x g` and `F = R e^{-B}`. On the open
interval `F' = (g - b R) e^{-B} ≤ 0` because `c + u ≤ R` (the hypothesis) and `b ≥ 0`; `F` is
continuous on `[α, β]`, hence antitone there (`antitoneOn_of_deriv_nonpos`), so
`F(x) ≤ F(α) = c`, i.e. `R(x) ≤ c e^{B(x)}`, and `c + u(x) ≤ R(x)`.
-/

open Set

namespace NonUniqueEuler

namespace AppA

/-- **Integral Grönwall inequality.** If `u ≤ ∫_α^x b (c + u)` on `[α, β]` with `b ≥ 0`
continuous and `u` continuous, then `c + u(x) ≤ c e^{∫_α^x b}` on `[α, β]`. -/
theorem int_gronwall {u b : ℝ → ℝ} {c α β : ℝ} (hu : ContinuousOn u (Icc α β))
    (hb : ContinuousOn b (Icc α β)) (hb0 : ∀ x ∈ Icc α β, 0 ≤ b x)
    (h : ∀ x ∈ Icc α β, u x ≤ ∫ t in α..x, b t * (c + u t)) :
    ∀ x ∈ Icc α β, c + u x ≤ c * Real.exp (∫ t in α..x, b t) := by
  intro x hx
  have hαβ : α ≤ β := hx.1.trans hx.2
  have huIcc : uIcc α β = Icc α β := uIcc_of_le hαβ
  set g : ℝ → ℝ := fun t => b t * (c + u t) with hg_def
  have hg : ContinuousOn g (Icc α β) := hb.mul (continuousOn_const.add hu)
  set B : ℝ → ℝ := fun y => ∫ t in α..y, b t with hB_def
  set R : ℝ → ℝ := fun y => c + ∫ t in α..y, g t with hR_def
  set F : ℝ → ℝ := fun y => R y * Real.exp (-B y) with hF_def
  -- continuity of the primitives on `[α, β]`
  have hBc : ContinuousOn B (Icc α β) := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := MeasureTheory.volume)
      (f := b) (a := α) (b := β) (by rw [huIcc]; exact hb.integrableOn_Icc)
    rwa [huIcc] at this
  have hGc : ContinuousOn (fun y => ∫ t in α..y, g t) (Icc α β) := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := MeasureTheory.volume)
      (f := g) (a := α) (b := β) (by rw [huIcc]; exact hg.integrableOn_Icc)
    rwa [huIcc] at this
  have hRc : ContinuousOn R (Icc α β) := continuousOn_const.add hGc
  have hFc : ContinuousOn F (Icc α β) := hRc.mul (hBc.neg.rexp)
  -- derivatives on the open interval
  have hderiv : ∀ y ∈ Ioo α β, HasDerivAt F ((g y - b y * R y) * Real.exp (-B y)) y := by
    intro y hy
    have hyIcc : Icc α β ∈ nhds y := Icc_mem_nhds hy.1 hy.2
    have hsub : uIcc α y ⊆ Icc α β := by
      rw [uIcc_of_le hy.1.le]; exact Icc_subset_Icc_right hy.2.le
    have hBd : HasDerivAt B (b y) y := by
      refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ ?_
      · exact (hb.mono hsub).intervalIntegrable
      · exact ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
          (hb.mono Ioo_subset_Icc_self) y hy
      · exact hb.continuousAt hyIcc
    have hGd : HasDerivAt (fun z => ∫ t in α..z, g t) (g y) y := by
      refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ ?_
      · exact (hg.mono hsub).intervalIntegrable
      · exact ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
          (hg.mono Ioo_subset_Icc_self) y hy
      · exact hg.continuousAt hyIcc
    have hRd : HasDerivAt R (g y) y := by
      exact hGd.const_add c
    have hEd : HasDerivAt (fun z => Real.exp (-B z)) (Real.exp (-B y) * (-b y)) y :=
      hBd.neg.exp
    have := hRd.mul hEd
    refine this.congr_deriv ?_
    ring
  have hFanti : AntitoneOn F (Icc α β) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc α β) hFc ?_ ?_
    · rw [interior_Icc]
      exact fun y hy => (hderiv y hy).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro y hy
      rw [(hderiv y hy).deriv]
      have hyI : y ∈ Icc α β := Ioo_subset_Icc_self hy
      have hwR : c + u y ≤ R y := by
        have := h y hyI
        simp only [hR_def, hg_def]
        linarith
      have hgR : g y - b y * R y ≤ 0 := by
        have := mul_le_mul_of_nonneg_left hwR (hb0 y hyI)
        simp only [hg_def]
        linarith
      exact mul_nonpos_of_nonpos_of_nonneg hgR (Real.exp_pos _).le
  have hαI : α ∈ Icc α β := ⟨le_rfl, hαβ⟩
  have hFx : F x ≤ F α := hFanti hαI hx hx.1
  have hFα : F α = c := by simp [hF_def, hR_def, hB_def]
  have hRx : R x ≤ c * Real.exp (B x) := by
    have hexp : Real.exp (-B x) * Real.exp (B x) = 1 := by
      rw [← Real.exp_add]; simp
    have h1 : F x * Real.exp (B x) ≤ c * Real.exp (B x) :=
      mul_le_mul_of_nonneg_right (hFα ▸ hFx) (Real.exp_pos _).le
    calc R x = F x * Real.exp (B x) := by
          simp only [hF_def]; rw [mul_assoc, hexp, mul_one]
      _ ≤ c * Real.exp (B x) := h1
  have hwx : c + u x ≤ R x := by
    have := h x hx
    simp only [hR_def, hg_def]
    linarith
  exact hwx.trans hRx

end AppA

end NonUniqueEuler
