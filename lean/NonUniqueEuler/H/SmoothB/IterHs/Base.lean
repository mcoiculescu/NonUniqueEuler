import NonUniqueEuler.H.SmoothB.IterHs.Energy
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Helper for `lem:iter-Hs`: the case `s = 1`

Helper of `P/SmoothB/IterHs.lean` (`B_global_smooth.tex:316-318`): by `lem:iterates`(i)–(ii)
and `lem:iter-lip`, `‖ω^{[j]}(t)‖_{L²} = ‖ω₀‖_{L²}` and
`‖∇ω^{[j]}(t)‖²_{L²} ≤ |B_{R(T)}| Ψ(T)² = π R(T)² Ψ(T)²` for `|t| ≤ T`, so
`‖ω^{[j]}(t)‖_{H¹} ≤ 𝓜_1(T)`.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ContDiff ENNReal Topology

namespace NonUniqueEuler.Smooth.IterHsH

open Sob

/-- `‖f‖²_{L²} = ∫⁻ ‖f‖²`. -/
theorem eLpNorm_two_sq (f : ℂ → ℂ) : eLpNorm f 2 volume ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := volume) (p := 2) two_ne_zero
  simpa using h

/-- A pointwise bound `|f₁|² + |f₂|² ≤ c²` on a disk `B_R`, outside which `f₁ = f₂ = 0`, gives
`‖f₁‖²_{L²} + ‖f₂‖²_{L²} ≤ π R² c²`. -/
theorem l2_sq_add_le {f₁ f₂ : ℂ → ℂ} (hf₁ : Continuous f₁) {R c : ℝ}
    (hR : 0 ≤ R) (hbd : ∀ x, ‖f₁ x‖ ^ 2 + ‖f₂ x‖ ^ 2 ≤ c ^ 2)
    (hout : ∀ x, x ∉ ball (0 : ℂ) R → f₁ x = 0 ∧ f₂ x = 0) :
    l2 f₁ ^ 2 + l2 f₂ ^ 2 ≤ Real.pi * R ^ 2 * c ^ 2 := by
  set E₁ := ∫⁻ x, ‖f₁ x‖ₑ ^ 2 with hE₁
  set E₂ := ∫⁻ x, ‖f₂ x‖ₑ ^ 2 with hE₂
  have h1 : l2 f₁ ^ 2 = E₁.toReal := by
    rw [l2, ← ENNReal.toReal_pow, eLpNorm_two_sq]
  have h2 : l2 f₂ ^ 2 = E₂.toReal := by
    rw [l2, ← ENNReal.toReal_pow, eLpNorm_two_sq]
  have hpt : ∀ x, ‖f₁ x‖ₑ ^ 2 + ‖f₂ x‖ₑ ^ 2 ≤
      (ball (0 : ℂ) R).indicator (fun _ => ENNReal.ofReal (c ^ 2)) x := by
    intro x
    by_cases hx : x ∈ ball (0 : ℂ) R
    · rw [indicator_of_mem hx, ← ofReal_norm, ← ofReal_norm,
        ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow (norm_nonneg _),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact ENNReal.ofReal_le_ofReal (hbd x)
    · obtain ⟨e1, e2⟩ := hout x hx
      simp [e1, e2]
  have hsum : E₁ + E₂ ≤ ENNReal.ofReal (c ^ 2) * volume (ball (0 : ℂ) R) := by
    rw [hE₁, hE₂, ← lintegral_add_left (hf₁.measurable.enorm.pow_const 2),
      ← lintegral_indicator_const measurableSet_ball]
    exact lintegral_mono hpt
  have hfin : ENNReal.ofReal (c ^ 2) * volume (ball (0 : ℂ) R) ≠ ⊤ := by
    rw [Complex.volume_ball]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ENNReal.coe_ne_top)
  have hE₁fin : E₁ ≠ ⊤ := ne_top_of_le_ne_top hfin (le_trans le_self_add hsum)
  have hE₂fin : E₂ ≠ ⊤ := ne_top_of_le_ne_top hfin (le_trans le_add_self hsum)
  rw [h1, h2, ← ENNReal.toReal_add hE₁fin hE₂fin]
  refine (ENNReal.toReal_mono hfin hsum).trans_eq ?_
  rw [Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal hR, ENNReal.coe_toReal,
    NNReal.coe_real_pi]
  ring

variable {ω₀ : ℂ → ℝ} {R₀ : ℝ}

/-- `R₀ > 0`: the support of `ω₀ ≢ 0` is a nonempty subset of `B_{R₀}`. -/
theorem R₀_pos (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) : 0 < R₀ := by
  obtain ⟨x, hx⟩ : ∃ x, ω₀ x ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hne (funext hc)
  have hmem : x ∈ ball (0 : ℂ) R₀ := h.tsupport_subset (subset_tsupport _ hx)
  exact lt_of_le_of_lt (norm_nonneg x) (by simpa using hmem)

/-- `lem:iter-Hs` for `s = 1`. -/
theorem iter_Hs_one (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) {T : ℝ} (hT : 0 < T) (j : ℕ)
    {t : ℝ} (ht : |t| ≤ T) :
    normH 1 (fun x => (iter ω₀ j t x : ℂ)) ≤ calM ω₀ R₀ 1 T := by
  set W : ℂ → ℂ := fun x => (iter ω₀ j t x : ℂ) with hW
  have hWs := contDiff_iter_sliceC h hne j t
  have hWc := hasCompactSupport_iter_sliceC h hne j t
  have hgs := contDiff_iter_slice h hne j t
  have hdg : ∀ x, DifferentiableAt ℝ (iter ω₀ j t) x := fun x => (hgs.differentiable (by simp)) x
  obtain ⟨R₀', hR₀', hR⟩ := exists_iter_support h hne
  -- the `L²` part
  have hL2 : l2 W = (eLpNorm ω₀ 2 volume).toReal := by
    rw [l2, ← iterates_eLpNorm h hne j t (p := 2) (by norm_num)]
    congr 1
    exact eLpNorm_congr_norm_ae (Eventually.of_forall fun x => by simp [hW])
  -- the gradient part
  have hU := Ustar_nonneg ω₀
  have hRT : 0 ≤ suppRadius ω₀ R₀ T := by
    have := R₀_pos h hne
    simp only [suppRadius]
    positivity
  have hgrad : l2 (partialD (1, 0) W) ^ 2 + l2 (partialD (0, 1) W) ^ 2 ≤
      Real.pi * suppRadius ω₀ R₀ T ^ 2 * Psi ω₀ T ^ 2 := by
    refine l2_sq_add_le (contDiff_partialD hWs _).continuous hRT (fun x => ?_) (fun x hx => ?_)
    · rw [norm_partialD_sq_add (hdg x)]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_iter_le h hne j ht x) 2
    · have hx' : R₀' + Ustar ω₀ * |t| < ‖x‖ := by
        have h1 : suppRadius ω₀ R₀ T ≤ ‖x‖ := by simpa using hx
        have h2 : Ustar ω₀ * |t| ≤ Ustar ω₀ * T := mul_le_mul_of_nonneg_left ht hU
        have h3 : suppRadius ω₀ R₀ T = R₀ + Ustar ω₀ * |T| := rfl
        rw [abs_of_pos hT] at h3
        linarith
      have hz := fderiv_iter_eq_zero hR j t hx'
      constructor
      · change fderiv ℝ W x 1 = 0
        rw [hW, fderiv_ofReal_apply (hdg x), hz]
        simp
      · change fderiv ℝ W x Complex.I = 0
        rw [hW, fderiv_ofReal_apply (hdg x), hz]
        simp
  -- assemble
  have hsplit : normH 1 W ^ 2 =
      l2 W ^ 2 + (l2 (partialD (1, 0) W) ^ 2 + l2 (partialD (0, 1) W) ^ 2) := by
    rw [normH_sq_eq hWs hWc]
    have hm : multiIdx 1 = {(0, 0), (1, 0), (0, 1)} := by decide
    rw [hm, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    rfl
  have hcalM : calM ω₀ R₀ 1 T = Real.sqrt ((eLpNorm ω₀ 2 volume).toReal ^ 2 +
      Real.pi * suppRadius ω₀ R₀ T ^ 2 * Psi ω₀ T ^ 2) := rfl
  rw [hcalM]
  apply Real.le_sqrt_of_sq_le
  rw [hsplit, hL2]
  linarith

end NonUniqueEuler.Smooth.IterHsH
