import NonUniqueEuler.Defs.Sec4.Evans
import NonUniqueEuler.Defs.Sec4.Extra1Sector
import NonUniqueEuler.I.Sec4.SectorSetting
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Helpers for `P/Sec4/EvansSimple/Range`: the forcing `F(ξ) = e^{2ξ}(M_λ g)(e^ξ)`

For a profile `g ∈ Y^0_ℓ` (`IsProfileL2`), with `F = S.Fres ℓ z G g` (`04_ring.tex:378`):
* `integrable_Fres`: `F ∈ L¹(ℝ)` (substitution `r = e^ξ`);
* `Fres_ae_zero`: `F = 0` a.e. off `[log ρ₋, log ρ₊]` (null sets of `(0,∞)` pull back to null
  sets under `exp`, because `log` is differentiable there);
* `integral_mul_Fres`: `∫_ℝ u F dξ = ∫_0^∞ g(r) u(log r) M_λ(r) r dr` (substitution);
* `intervalIntegral_mul_Fres_left/right/eq_integral`: the primitives `∫_c^ξ u F` vanish left of
  `c < log ρ₋` and are constant, equal to `∫_ℝ u F`, right of `d > log ρ₊`.
-/

noncomputable section

open MeasureTheory Set Filter

namespace NonUniqueEuler.EvansRangeAux

open SectorSetting

/-- `λ + iℓΩ ≠ 0` when `Re λ > 0`. -/
theorem denom_ne_zero (S : SectorSetting) {z : ℂ} (hz : 0 < z.re) (ℓ : ℤ) (G r : ℝ) :
    z + Complex.I * (ℓ : ℂ) * ((S.Omega G r : ℝ) : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

theorem denom_mul_Mres (S : SectorSetting) {z : ℂ} (hz : 0 < z.re) (ℓ : ℤ) (G r : ℝ) :
    (z + Complex.I * (ℓ : ℂ) * ((S.Omega G r : ℝ) : ℂ)) * S.Mres ℓ z G r = 1 :=
  mul_inv_cancel₀ (denom_ne_zero S hz ℓ G r)

theorem continuousOn_Mres (S : SectorSetting) (hS : S.Valid) {z : ℂ} (hz : 0 < z.re) (ℓ : ℤ)
    (G : ℝ) : ContinuousOn (S.Mres ℓ z G) (Ioi 0) := by
  have h1 : ContinuousOn (fun r : ℝ => ((S.Omega G r : ℝ) : ℂ)) (Ioi 0) :=
    Complex.continuous_ofReal.comp_continuousOn (contDiffOn_Omega S hS G).continuousOn
  have h2 : ContinuousOn (fun r : ℝ => (z + Complex.I * (ℓ : ℂ) * ((S.Omega G r : ℝ) : ℂ))⁻¹)
      (Ioi 0) :=
    (continuousOn_const.add (continuousOn_const.mul h1)).inv₀ fun r _ => denom_ne_zero S hz ℓ G r
  exact h2

/-- For `g ∈ Y^0_ℓ` (as a profile) and `F` continuous on `[ρ₋,ρ₊]`, `g F` is integrable on
`(0,∞)` (copied from `H/Sec4/EvansSimple/Basic.lean`). -/
theorem integrableOn_profile_mul (S : SectorSetting) {g : ℝ → ℂ} (hg : S.IsProfileL2 g)
    {F : ℝ → ℂ} (hF : ContinuousOn F (Icc S.ρm S.ρp)) :
    IntegrableOn (fun r => g r * F r) (Ioi 0) := by
  have hgi : IntegrableOn g (Icc S.ρm S.ρp) := hg.1.integrable one_le_two
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hF
  have h1 : IntegrableOn (fun r => g r * F r) (Icc S.ρm S.ρp) := by
    refine Integrable.mul_bdd (c := C) hgi (hF.aestronglyMeasurable measurableSet_Icc) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact hC r hr
  refine h1.of_ae_sdiff_eq_zero measurableSet_Ioi.nullMeasurableSet ?_
  have h2 := (ae_restrict_iff' measurableSet_Ioi).1 hg.2
  filter_upwards [h2] with r hr hr'
  rw [hr hr'.1 hr'.2, zero_mul]

theorem exp_image_univ : Real.exp '' univ = Ioi (0 : ℝ) := by
  rw [image_univ, Real.range_exp]

theorem ofReal_exp_two_mul (ξ : ℝ) :
    ((Real.exp (2 * ξ) : ℝ) : ℂ) = ((Real.exp ξ : ℝ) : ℂ) * ((Real.exp ξ : ℝ) : ℂ) := by
  rw [show 2 * ξ = ξ + ξ by ring, Real.exp_add, Complex.ofReal_mul]

/-- `F = e^{2ξ}(M_λ g)(e^ξ)` is integrable on `ℝ`. -/
theorem integrable_Fres (S : SectorSetting) (hS : S.Valid) {z : ℂ} (hz : 0 < z.re) (ℓ : ℕ)
    (G : ℝ) {g : ℝ → ℂ} (hg : S.IsProfileL2 g) : Integrable (S.Fres ℓ z G g) := by
  have hIcc : Icc S.ρm S.ρp ⊆ Ioi 0 := fun r hr => lt_of_lt_of_le hS.ρm_pos hr.1
  have hc : ContinuousOn (fun r : ℝ => (r : ℂ) * S.Mres ℓ z G r) (Icc S.ρm S.ρp) :=
    Complex.continuous_ofReal.continuousOn.mul ((continuousOn_Mres S hS hz ℓ G).mono hIcc)
  have h1 := integrableOn_profile_mul S hg hc
  have h2 := (integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
    (fun r => g r * ((r : ℂ) * S.Mres ℓ z G r))).1 (by rw [exp_image_univ]; exact h1)
  rw [integrableOn_univ] at h2
  refine h2.congr (Eventually.of_forall fun ξ => ?_)
  simp only [abs_of_pos (Real.exp_pos ξ), Fres, Complex.real_smul, ofReal_exp_two_mul]
  ring

/-- `F = 0` a.e. off `[log ρ₋, log ρ₊]`. -/
theorem Fres_ae_zero (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (z : ℂ) (G : ℝ) {g : ℝ → ℂ}
    (hg : S.IsProfileL2 g) :
    ∀ᵐ ξ : ℝ, ξ ∉ Icc (Real.log S.ρm) (Real.log S.ρp) → S.Fres ℓ z G g ξ = 0 := by
  have h1 := (ae_restrict_iff' measurableSet_Ioi).1 hg.2
  set N : Set ℝ := {r | ¬(r ∈ Ioi 0 → r ∉ Icc S.ρm S.ρp → g r = 0)} with hN
  have hN0 : volume N = 0 := ae_iff.1 h1
  have hNpos : N ⊆ Ioi 0 := by
    intro r hr
    by_contra h
    exact hr fun h' => absurd h' h
  have hlog : volume (Real.log '' N) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (Real.differentiableOn_log.mono fun r hr => ne_of_gt (hNpos hr)) hN0
  refine ae_iff.2 (measure_mono_null ?_ hlog)
  intro ξ hξ
  simp only [mem_ofPred_eq, not_imp] at hξ
  obtain ⟨hξI, hF⟩ := hξ
  refine ⟨Real.exp ξ, ?_, Real.log_exp ξ⟩
  simp only [hN, mem_ofPred_eq, not_imp]
  refine ⟨Real.exp_pos ξ, fun hI => hξI ⟨?_, ?_⟩, fun hg0 => hF ?_⟩
  · exact (Real.log_le_iff_le_exp hS.ρm_pos).2 hI.1
  · exact (Real.le_log_iff_exp_le (hS.ρm_pos.trans hS.ρm_lt_ρp)).2 hI.2
  · simp [Fres, hg0]

/-- `∫_ℝ u F dξ = ∫_0^∞ g(r) u(log r) M_λ(r) r dr` (substitution `r = e^ξ`). -/
theorem integral_mul_Fres (S : SectorSetting) (ℓ : ℕ) (z : ℂ) (G : ℝ) (g u : ℝ → ℂ) :
    ∫ ξ, u ξ * S.Fres ℓ z G g ξ =
      ∫ r in Ioi (0 : ℝ), g r * u (Real.log r) * S.Mres ℓ z G r * (r : ℂ) := by
  have hcv := integral_image_eq_integral_abs_deriv_smul (s := univ) (f := Real.exp)
    (f' := Real.exp) MeasurableSet.univ (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn
    (fun r : ℝ => g r * u (Real.log r) * S.Mres ℓ z G r * (r : ℂ))
  rw [exp_image_univ, Measure.restrict_univ] at hcv
  rw [hcv]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [abs_of_pos (Real.exp_pos ξ), Real.log_exp, Fres, Complex.real_smul,
    ofReal_exp_two_mul]
  ring

/-- Left of `c < log ρ₋`, the primitive `∫_c^ξ u F` vanishes. -/
theorem intervalIntegral_mul_Fres_left (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (z : ℂ)
    (G : ℝ) {g : ℝ → ℂ} (hg : S.IsProfileL2 g) (u : ℝ → ℂ) {c ξ : ℝ}
    (hc : c < Real.log S.ρm) (hξ : ξ ≤ c) :
    ∫ t in c..ξ, u t * S.Fres ℓ z G g t = 0 := by
  rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le hξ, neg_eq_zero]
  refine setIntegral_eq_zero_of_ae_eq_zero ?_
  filter_upwards [Fres_ae_zero S hS ℓ z G hg] with t ht htI
  rw [ht fun h => by linarith [h.1, htI.2], mul_zero]

/-- The primitive over `[c, d] ⊇ [log ρ₋, log ρ₊]` is the integral over `ℝ`. -/
theorem intervalIntegral_mul_Fres_eq_integral (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ)
    (z : ℂ) (G : ℝ) {g : ℝ → ℂ} (hg : S.IsProfileL2 g) (u : ℝ → ℂ) {c d : ℝ}
    (hc : c < Real.log S.ρm) (hd : Real.log S.ρp < d) (hcd : c ≤ d) :
    ∫ t in c..d, u t * S.Fres ℓ z G g t = ∫ t, u t * S.Fres ℓ z G g t := by
  rw [intervalIntegral.integral_of_le hcd]
  refine setIntegral_eq_integral_of_ae_compl_eq_zero ?_
  filter_upwards [Fres_ae_zero S hS ℓ z G hg] with t ht htI
  have hnot : t ∉ Icc (Real.log S.ρm) (Real.log S.ρp) := by
    intro h
    apply htI
    constructor <;> linarith [h.1, h.2]
  rw [ht hnot, mul_zero]

/-- Right of `d > log ρ₊`, the primitive `∫_c^ξ u F` is constant. -/
theorem intervalIntegral_mul_Fres_right (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (z : ℂ)
    (G : ℝ) {g : ℝ → ℂ} (hg : S.IsProfileL2 g) {u : ℝ → ℂ}
    (hu : ∀ a b, IntervalIntegrable (fun t => u t * S.Fres ℓ z G g t) volume a b) (c : ℝ)
    {d ξ : ℝ} (hd : Real.log S.ρp < d) (hξ : d ≤ ξ) :
    ∫ t in c..ξ, u t * S.Fres ℓ z G g t = ∫ t in c..d, u t * S.Fres ℓ z G g t := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (hu c d) (hu d ξ),
    intervalIntegral.integral_of_le hξ]
  have h0 : ∫ t in Ioc d ξ, u t * S.Fres ℓ z G g t = 0 := by
    refine setIntegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [Fres_ae_zero S hS ℓ z G hg] with t ht htI
    rw [ht fun h => by linarith [h.2, htI.1], mul_zero]
  rw [h0, add_zero]

end NonUniqueEuler.EvansRangeAux
