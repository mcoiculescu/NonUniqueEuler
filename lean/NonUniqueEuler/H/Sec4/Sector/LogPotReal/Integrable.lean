import NonUniqueEuler.Defs.Sec4.Setting
import NonUniqueEuler.Defs.Sec4.Extra1Sector
import NonUniqueEuler.Defs.Infra.Multipole
import NonUniqueEuler.I.Infra.Polar.Power
import NonUniqueEuler.I.Infra.Polar.Radial
import NonUniqueEuler.I.Infra.AngularFourier.SectorL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Helper for `I/Sec4/Sector/LogPotReal.lean`: integrability of `log|r - y| · g(|y|)e^{iℓθ}`

Helper file of `P/Sec4/Sector/LogPotReal.lean` (fully proved). Step 1 of the proof sketch of
`SectorSetting.logPotential_ofProfile_ofReal`:
* `ae_comp_norm`: an a.e. property of `ρ > 0` holds at `ρ = |y|` for a.e. `y ∈ ℂ`;
* `memLp_ofProfile`: `W = g(|y|)e^{iℓθ} ∈ L²(ℂ)` for `g ∈ Y^0_ℓ`;
* `ae_ofProfile_eq_zero`: `W = 0` a.e. outside `B_{ρ₊}`;
* `memLp_log_norm_sub`: `log|c - ·| ∈ L²(B_R)` (from `(log s)² ≤ 4(s⁻¹ + s)`);
* `integrable_log_mul_ofProfile`: `y ↦ log|c - y| W(y)` is integrable (Hölder).
-/

noncomputable section

open MeasureTheory Set Metric Real
open scoped ENNReal

namespace NonUniqueEuler.LogPotRealH

/-- An a.e. property of `ρ > 0` transfers to `ρ = ‖y‖` for a.e. `y ∈ ℂ`. -/
theorem ae_comp_norm {P : ℝ → Prop} (h : ∀ᵐ ρ ∂(volume.restrict (Ioi (0 : ℝ))), P ρ) :
    ∀ᵐ y : ℂ ∂volume, P ‖y‖ := by
  rw [ae_iff] at h ⊢
  obtain ⟨T, hsub, hT, hT0⟩ := exists_measurable_superset_of_null h
  have hm : MeasurableSet ((fun y : ℂ => ‖y‖) ⁻¹' T) := measurable_norm hT
  have hsub' : {y : ℂ | ¬P ‖y‖} ⊆ (fun y : ℂ => ‖y‖) ⁻¹' T := fun y hy => hsub hy
  refine measure_mono_null hsub' ?_
  rw [← lintegral_indicator_one hm]
  have e : ((fun y : ℂ => ‖y‖) ⁻¹' T).indicator (1 : ℂ → ℝ≥0∞) =
      fun y => T.indicator (1 : ℝ → ℝ≥0∞) ‖y‖ := by
    funext y
    by_cases hy : ‖y‖ ∈ T
    · rw [indicator_of_mem (show y ∈ (fun y : ℂ => ‖y‖) ⁻¹' T from hy), indicator_of_mem hy]
      rfl
    · rw [indicator_of_notMem (show y ∉ (fun y : ℂ => ‖y‖) ⁻¹' T from hy),
        indicator_of_notMem hy]
  rw [e, Polar.lintegral_comp_norm (measurable_one.indicator hT)]
  have h0 : ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * T.indicator (1 : ℝ → ℝ≥0∞) r = 0 := by
    rw [lintegral_congr_ae (g := fun _ => (0 : ℝ≥0∞)), lintegral_zero]
    have hae : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), r ∉ T :=
      (measure_eq_zero_iff_ae_notMem).1 hT0
    filter_upwards [hae] with r hr
    rw [indicator_of_notMem hr, mul_zero]
  rw [h0, mul_zero]

variable {S : SectorSetting} {g : ℝ → ℂ}

/-- A profile in `Y^0_ℓ` is a.e. strongly measurable on `(0, ∞)`. -/
theorem aestronglyMeasurable_profile (hg : S.IsProfileL2 g) :
    AEStronglyMeasurable g (volume.restrict (Ioi (0 : ℝ))) := by
  have h1 : AEStronglyMeasurable ((Icc S.ρm S.ρp).indicator g) volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_Icc).2 hg.1.aestronglyMeasurable
  refine h1.restrict.congr ?_
  filter_upwards [hg.2] with r hr
  by_cases hr' : r ∈ Icc S.ρm S.ρp
  · rw [indicator_of_mem hr']
  · rw [indicator_of_notMem hr', hr hr']

/-- `|g|² r` is integrable on `(0, ∞)` for a profile `g ∈ Y^0_ℓ`. -/
theorem integrableOn_profile_sq (hg : S.IsProfileL2 g) :
    IntegrableOn (fun r => ‖g r‖ ^ 2 * r) (Ioi 0) := by
  have hsq : Integrable (fun r => ‖g r‖ ^ 2) (volume.restrict (Icc S.ρm S.ρp)) :=
    (memLp_two_iff_integrable_sq_norm hg.1.aestronglyMeasurable).1 hg.1
  have hIcc : IntegrableOn (fun r => ‖g r‖ ^ 2 * r) (Icc S.ρm S.ρp) := by
    refine Integrable.mono' (hsq.mul_const (|S.ρm| + |S.ρp|)) ?_ ?_
    · exact (hg.1.aestronglyMeasurable.norm.pow 2).mul
        continuous_id.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _), Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      rcases hr with ⟨h1, h2⟩
      rcases le_total 0 r with h | h
      · rw [abs_of_nonneg h]; linarith [le_abs_self S.ρp, abs_nonneg S.ρm]
      · rw [abs_of_nonpos h]; linarith [neg_abs_le S.ρm, abs_nonneg S.ρp]
  have hind : Integrable ((Icc S.ρm S.ρp).indicator fun r => ‖g r‖ ^ 2 * r) volume :=
    (integrable_indicator_iff measurableSet_Icc).2 hIcc
  refine hind.restrict.congr ?_
  filter_upwards [hg.2] with r hr
  by_cases hr' : r ∈ Icc S.ρm S.ρp
  · rw [indicator_of_mem hr']
  · rw [indicator_of_notMem hr', hr hr', norm_zero]
    ring

/-- `W = g(|y|)e^{iℓθ} ∈ L²(ℂ)` for a profile `g ∈ Y^0_ℓ`. -/
theorem memLp_ofProfile (hg : S.IsProfileL2 g) (ℓ : ℤ) :
    MemLp (Ang.ofProfile ℓ g) 2 volume :=
  ((Ang.memLp_ofProfile_iff (aestronglyMeasurable_profile hg)).1).2
    (integrableOn_profile_sq hg)

/-- `W = g(|y|)e^{iℓθ}` vanishes a.e. outside the closed disk `B̄_{ρ₊}`. -/
theorem ae_ofProfile_eq_zero (hg : S.IsProfileL2 g) (ℓ : ℤ) :
    ∀ᵐ y : ℂ ∂volume, y ∉ closedBall (0 : ℂ) S.ρp → Ang.ofProfile ℓ g y = 0 := by
  filter_upwards [ae_comp_norm hg.2] with y hy hyB
  have hn : S.ρp < ‖y‖ := by
    rw [mem_closedBall_zero_iff, not_le] at hyB
    exact hyB
  have hnot : ‖y‖ ∉ Icc S.ρm S.ρp := fun h => absurd h.2 (not_le.2 hn)
  rw [Ang.ofProfile, hy hnot, zero_mul]

/-- `(log t)² ≤ 4t` for `t ≥ 1`. -/
theorem log_sq_le_of_one_le {t : ℝ} (ht : 1 ≤ t) : Real.log t ^ 2 ≤ 4 * t := by
  have ht0 : 0 ≤ t := by linarith
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht
  have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.2 (by linarith)
  have hlog : Real.log t = 2 * Real.log (Real.sqrt t) := by
    rw [Real.log_sqrt ht0]; ring
  have h1 : Real.log (Real.sqrt t) ≤ Real.sqrt t - 1 := Real.log_le_sub_one_of_pos hs0
  have h2 : Real.log t ≤ 2 * Real.sqrt t := by rw [hlog]; linarith
  calc Real.log t ^ 2 ≤ (2 * Real.sqrt t) ^ 2 := pow_le_pow_left₀ hlog0 h2 2
    _ = 4 * t := by rw [mul_pow, Real.sq_sqrt ht0]; norm_num

/-- `(log s)² ≤ 4(s⁻¹ + s)` for `s ≥ 0` (with `log 0 = 0`, `0⁻¹ = 0`). -/
theorem log_sq_le (s : ℝ) (hs : 0 ≤ s) : Real.log s ^ 2 ≤ 4 * (s⁻¹ + s) := by
  rcases hs.eq_or_lt with rfl | hs
  · simp
  rcases le_total 1 s with h | h
  · have := log_sq_le_of_one_le h
    have : 0 ≤ s⁻¹ := inv_nonneg.2 hs.le
    nlinarith
  · have h' : 1 ≤ s⁻¹ := one_le_inv₀ hs |>.2 h
    have := log_sq_le_of_one_le h'
    rw [Real.log_inv, neg_sq] at this
    nlinarith

/-- `‖y - c‖^s` is integrable on closed disks `B̄_R` for `s > -2`. -/
theorem integrableOn_norm_sub_rpow (c : ℂ) {s : ℝ} (hs : -2 < s) (R : ℝ) :
    IntegrableOn (fun y : ℂ => ‖y - c‖ ^ s) (closedBall 0 R) := by
  have h1 := Polar.integrableOn_ball_norm_rpow hs (R + ‖c‖ + 1)
  have h2 : Integrable ((ball (0 : ℂ) (R + ‖c‖ + 1)).indicator fun x : ℂ => ‖x‖ ^ s) :=
    (integrable_indicator_iff measurableSet_ball).2 h1
  have h3 := h2.comp_sub_right c
  refine (h3.integrableOn).congr_fun (fun y hy => ?_) measurableSet_closedBall
  have hmem : y - c ∈ ball (0 : ℂ) (R + ‖c‖ + 1) := by
    rw [mem_ball_zero_iff]
    rw [mem_closedBall_zero_iff] at hy
    calc ‖y - c‖ ≤ ‖y‖ + ‖c‖ := norm_sub_le _ _
      _ < R + ‖c‖ + 1 := by linarith
  simp only [indicator_of_mem hmem]

/-- `log|c - ·| ∈ L²(B̄_R)`. -/
theorem memLp_log_norm_sub (c : ℂ) (R : ℝ) :
    MemLp (fun y : ℂ => Real.log ‖c - y‖) 2 (volume.restrict (closedBall 0 R)) := by
  have hmeas : AEStronglyMeasurable (fun y : ℂ => Real.log ‖c - y‖)
      (volume.restrict (closedBall 0 R)) :=
    (Real.measurable_log.comp (continuous_const.sub continuous_id).norm.measurable)
      |>.aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq hmeas).2 ?_
  have hinv : IntegrableOn (fun y : ℂ => ‖y - c‖⁻¹) (closedBall 0 R) := by
    have := integrableOn_norm_sub_rpow c (s := -1) (by norm_num) R
    simpa only [Real.rpow_neg_one] using this
  have hone : IntegrableOn (fun y : ℂ => ‖y - c‖) (closedBall 0 R) := by
    have := integrableOn_norm_sub_rpow c (s := 1) (by norm_num) R
    simpa only [Real.rpow_one] using this
  refine Integrable.mono' ((hinv.add hone).const_mul 4) (hmeas.pow 2) ?_
  refine ae_of_all _ fun y => ?_
  rw [Real.norm_of_nonneg (sq_nonneg _), norm_sub_rev c y]
  exact log_sq_le _ (norm_nonneg _)

/-- `y ↦ log|c - y| · g(|y|)e^{iℓθ}` is integrable on `ℂ` for a profile `g ∈ Y^0_ℓ`. -/
theorem integrable_log_mul_ofProfile (hg : S.IsProfileL2 g) (ℓ : ℤ) (c : ℂ) :
    Integrable (fun y : ℂ => (Real.log ‖c - y‖ : ℂ) * Ang.ofProfile ℓ g y) := by
  set B := closedBall (0 : ℂ) S.ρp
  set L : ℂ → ℂ := B.indicator fun y => (Real.log ‖c - y‖ : ℂ)
  have hLB : MemLp (fun y : ℂ => (Real.log ‖c - y‖ : ℂ)) 2 (volume.restrict B) :=
    (memLp_log_norm_sub c S.ρp).ofReal
  have hL : MemLp L 2 volume := (memLp_indicator_iff_restrict measurableSet_closedBall).2 hLB
  have hW := memLp_ofProfile hg ℓ
  have hLW : Integrable (L * Ang.ofProfile ℓ g) := hL.integrable_mul hW
  refine hLW.congr ?_
  filter_upwards [ae_ofProfile_eq_zero hg ℓ] with y hy
  by_cases hyB : y ∈ B
  · simp only [Pi.mul_apply, L, indicator_of_mem hyB]
  · simp only [Pi.mul_apply, L, indicator_of_notMem hyB, hy hyB, mul_zero]

end NonUniqueEuler.LogPotRealH
