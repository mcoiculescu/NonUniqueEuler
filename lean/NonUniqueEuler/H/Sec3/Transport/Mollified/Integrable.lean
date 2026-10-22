import NonUniqueEuler.H.Sec3.Transport.Mollified.Measurable
import NonUniqueEuler.I.Sec3.CommFormula

/-!
# Helper for `P/Sec3/Transport/Mollified`: integrability (step 4)

Step 4 of the sketch in `I/Sec3/Transport/Mollified.lean`. With `μ = volume.restrict (t₀,T)`
(so that `volume.restrict ((t₀,T) × ℝ²) = μ ⊗ volume`), `U = u ⋆ ρ_ε`, `D = (div(wu)) ⋆ ρ_ε`,
`G = w·∇(u ⋆ ρ_ε)`:

* `ae_good`: for a.e. `t ∈ (t₀,T)`, `u(t) ∈ L¹` with `‖u(t)‖₁ ≤ M₁`, `u(t)w(t) ∈ L¹`,
  `w(t) ∈ L¹_loc` and `div w(t) = 0`;
* the four integrands `Υ(U) ∂_tφ`, `Υ(U) w·∇φ`, `φ Υ'(U) D`, `φ Υ'(U) G` are integrable on
  `μ ⊗ volume` (`integrable_F1` … `integrable_F4`). They are bounded by multiples of `|∂_tφ|`,
  `|w| 1_{B_R}`, `‖u(t)w(t)‖₁ 1_{B_R}`, `|w| 1_{B_R}` respectively;
* for every `x`: `U(·,x) ∈ L^∞(t₀,T)` and `D(·,x) ∈ L¹(t₀,T)` (the hypotheses of step 2);
* the mollified datum term is integrable.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace NonUniqueEuler.Weak.MollifiedH

section Integrability

variable {ρ : ℂ → ℝ} {ε T t₀ : ℝ} {w : ℝ → ℂ → ℂ} {u : ℝ → ℂ → ℝ}

/-- `∫ |g| = ‖g‖₁` (real form). -/
theorem integral_abs_eq_toReal_eLpNorm {g : ℂ → ℝ} (hg : AEStronglyMeasurable g volume) :
    ∫ y, |g y| = (eLpNorm g 1 volume).toReal := by
  rw [eLpNorm_one_eq_lintegral_enorm, ← integral_norm_eq_lintegral_enorm hg]
  simp [Real.norm_eq_abs]

theorem measure_restrict_mono_Ioo (ht₀ : 0 ≤ t₀) :
    volume.restrict (Ioo t₀ T) ≤ volume.restrict (Ioo (0 : ℝ) T) :=
  Measure.restrict_mono (Ioo_subset_Ioo_left ht₀) le_rfl

theorem prod_restrict_le (ht₀ : 0 ≤ t₀) :
    (volume.restrict (Ioo t₀ T)).prod (volume : Measure ℂ) ≤
      volume.restrict (slab T) := by
  rw [← restrict_slabFrom_eq_prod]
  exact Measure.restrict_mono (slabFrom_subset_prod ht₀) le_rfl

theorem aestronglyMeasurable_u (ht₀ : 0 ≤ t₀) (hu1 : Prelim.MemLinfLp (Ioo 0 T) univ 1 u) :
    AEStronglyMeasurable (Function.uncurry u) ((volume.restrict (Ioo t₀ T)).prod volume) :=
  hu1.aestronglyMeasurable.mono_measure (prod_restrict_le ht₀)

theorem aestronglyMeasurable_w (ht₀ : 0 ≤ t₀) (hw : IsBddH1DivFreeField (Ioo 0 T) w) :
    AEStronglyMeasurable (fun p : ℝ × ℂ => w p.1 p.2) ((volume.restrict (Ioo t₀ T)).prod volume) :=
  hw.aestronglyMeasurable.mono_measure (prod_restrict_le ht₀)

theorem aestronglyMeasurable_uw (ht₀ : 0 ≤ t₀)
    (huw : Integrable (fun p : ℝ × ℂ => u p.1 p.2 • w p.1 p.2) (volume.restrict (slab T))) :
    AEStronglyMeasurable (fun p : ℝ × ℂ => u p.1 p.2 • w p.1 p.2)
      ((volume.restrict (Ioo t₀ T)).prod volume) :=
  huw.aestronglyMeasurable.mono_measure (prod_restrict_le ht₀)

/-- `t ↦ ‖u(t)w(t)‖₁` is integrable on `(t₀,T)`. -/
theorem integrable_norm_uw (ht₀ : 0 ≤ t₀)
    (huw : Integrable (fun p : ℝ × ℂ => u p.1 p.2 • w p.1 p.2) (volume.restrict (slab T))) :
    Integrable (fun t => ∫ y, ‖u t y • w t y‖) (volume.restrict (Ioo t₀ T)) := by
  have h := huw.mono_measure (prod_restrict_le ht₀)
  exact h.integral_norm_prod_left

/-- The good times: for a.e. `t ∈ (t₀,T)`, `u(t) ∈ L¹` with `‖u(t)‖₁ ≤ M₁`, `u(t)w(t) ∈ L¹`, and
`w(t)` is locally integrable and weakly divergence free. -/
theorem ae_good (ht₀ : 0 ≤ t₀) (hw : IsBddH1DivFreeField (Ioo 0 T) w)
    (hu1 : Prelim.MemLinfLp (Ioo 0 T) univ 1 u)
    (huw : Integrable (fun p : ℝ × ℂ => u p.1 p.2 • w p.1 p.2) (volume.restrict (slab T))) :
    ∃ M₁ : ℝ, 0 ≤ M₁ ∧ ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)),
      Integrable (u t) ∧ ∫ y, |u t y| ≤ M₁ ∧ Integrable (fun y => u t y • w t y) ∧
        LocallyIntegrable (w t) volume ∧ Prelim.IsWeaklyDivFree (w t) := by
  obtain ⟨M, hM⟩ := hu1.essBounded
  have hM' := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_left ht₀) hM
  have huw' : ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)), Integrable (fun y => u t y • w t y) :=
    (huw.mono_measure (prod_restrict_le ht₀)).prod_right_ae
  have hw' := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_left ht₀)
    (ae_locallyIntegrable_divFree hw)
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  filter_upwards [hM', huw', hw'] with t ht htw htd
  rw [Measure.restrict_univ] at ht
  refine ⟨memLp_one_iff_integrable.1 ht.1, ?_, htw, htd⟩
  rw [integral_abs_eq_toReal_eLpNorm ht.1.aestronglyMeasurable]
  exact ht.2.trans (le_max_left _ _)

/-- A function on the slab that vanishes off `ℝ × B_R` and is a.e. bounded by an integrable
function on `(t₀,T) × B_R` is integrable on the slab. -/
theorem integrable_of_ball {R : ℝ} {F H : ℝ × ℂ → ℝ}
    (hF : AEStronglyMeasurable F ((volume.restrict (Ioo t₀ T)).prod volume))
    (hF0 : ∀ p : ℝ × ℂ, p.2 ∉ ball (0 : ℂ) R → F p = 0)
    (hH : IntegrableOn H (Ioo t₀ T ×ˢ ball (0 : ℂ) R))
    (hb : ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)), ∀ x, |F (t, x)| ≤ H (t, x)) :
    Integrable F ((volume.restrict (Ioo t₀ T)).prod volume) := by
  rw [← restrict_slabFrom_eq_prod]
  have h1 : IntegrableOn F (Ioo t₀ T ×ˢ ball (0 : ℂ) R) := by
    refine Integrable.mono' hH ?_ ?_
    · rw [← restrict_slabFrom_eq_prod] at hF
      exact hF.mono_measure (Measure.restrict_mono (prod_mono le_rfl (subset_univ _)) le_rfl)
    · rw [restrict_prod_eq_prod]
      have hb' : ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)), ∀ x, ‖F (t, x)‖ ≤ H (t, x) := by
        simpa only [Real.norm_eq_abs] using hb
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae hb'] with p hp
      exact hp p.2
  refine h1.of_forall_sdiff_eq_zero (measurableSet_Ioo.prod MeasurableSet.univ) ?_
  rintro p ⟨hp1, hp2⟩
  refine hF0 p fun hb2 => hp2 ⟨hp1.1, hb2⟩

/-- `‖w‖` is integrable on `(t₀,T) × B_R`. -/
theorem integrableOn_norm_w (ht₀ : 0 ≤ t₀) (hw : IsBddH1DivFreeField (Ioo 0 T) w) {R : ℝ}
    (hR : 0 < R) : IntegrableOn (fun p : ℝ × ℂ => ‖w p.1 p.2‖) (Ioo t₀ T ×ˢ ball (0 : ℂ) R) :=
  ((integrableOn_ball_of_isBddH1 hw hR).mono_set
    (prod_mono (Ioo_subset_Ioo_left ht₀) le_rfl)).norm

variable {Υ : ℝ → ℝ} {φ : ℝ × ℂ → ℝ}

/-- The integrand `Υ(U) ∂_tφ` is integrable. -/
theorem integrable_F1 (hρ : IsMollifier ρ) (hε : 0 < ε) (ht₀ : 0 ≤ t₀)
    (hw : IsBddH1DivFreeField (Ioo 0 T) w) (hu1 : Prelim.MemLinfLp (Ioo 0 T) univ 1 u)
    (huw : Integrable (fun p : ℝ × ℂ => u p.1 p.2 • w p.1 p.2) (volume.restrict (slab T)))
    (hΥ : IsRenormalization Υ) (hφ : IsTestFunction T φ) :
    Integrable (fun p : ℝ × ℂ => Υ (mollify ρ ε (u p.1) p.2) * timeDeriv φ p.1 p.2)
      ((volume.restrict (Ioo t₀ T)).prod volume) := by
  obtain ⟨M₁, hM₁, hgood⟩ := ae_good ht₀ hw hu1 huw
  obtain ⟨L, hL, hLb⟩ := exists_abs_le_of_isRenormalization hΥ
  obtain ⟨Cρ, hCρ, hCρb⟩ := exists_bound_scaled hρ hε.ne'
  have hU := aestronglyMeasurable_mollify (ε := ε) hρ (aestronglyMeasurable_u ht₀ hu1)
  have hcs : HasCompactSupport (fun p : ℝ × ℂ => timeDeriv φ p.1 p.2) := by
    refine HasCompactSupport.intro hφ.hasCompactSupport.isCompact fun p hp => ?_
    rw [timeDeriv_eq_fderiv (differentiable_of_isTestFunction hφ),
      fderiv_eq_zero_of_notMem_tsupport hp]
    simp
  have hint : Integrable (fun p : ℝ × ℂ => timeDeriv φ p.1 p.2) :=
    (continuous_timeDeriv hφ).integrable_of_hasCompactSupport hcs
  have hint' : Integrable (fun p : ℝ × ℂ => timeDeriv φ p.1 p.2)
      ((volume.restrict (Ioo t₀ T)).prod volume) := by
    rw [← restrict_slabFrom_eq_prod]
    exact hint.restrict
  refine (hint'.norm.const_mul (L * Cρ * M₁)).mono'
    (((hΥ.contDiff.continuous).comp_aestronglyMeasurable hU).mul
      (continuous_timeDeriv hφ).aestronglyMeasurable) ?_
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hgood] with p hp
  obtain ⟨hp1, hp2, -⟩ := hp
  have hUb := abs_mollify_le hp1 hCρb p.2
  rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
  have h1 : |Υ (mollify ρ ε (u p.1) p.2)| ≤ L * Cρ * M₁ :=
    calc |Υ (mollify ρ ε (u p.1) p.2)| ≤ L * |mollify ρ ε (u p.1) p.2| := hLb _
      _ ≤ L * (Cρ * M₁) := mul_le_mul_of_nonneg_left
          (hUb.trans (mul_le_mul_of_nonneg_left hp2 hCρ)) hL
      _ = L * Cρ * M₁ := by ring
  exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)

/-- The integrand `Υ(U) w·∇φ` is integrable. -/
theorem integrable_F2 (hρ : IsMollifier ρ) (hε : 0 < ε) (ht₀ : 0 ≤ t₀)
    (hw : IsBddH1DivFreeField (Ioo 0 T) w) (hu1 : Prelim.MemLinfLp (Ioo 0 T) univ 1 u)
    (huw : Integrable (fun p : ℝ × ℂ => u p.1 p.2 • w p.1 p.2) (volume.restrict (slab T)))
    (hΥ : IsRenormalization Υ) (hφ : IsTestFunction T φ) :
    Integrable (fun p : ℝ × ℂ =>
        Υ (mollify ρ ε (u p.1) p.2) * spaceDeriv φ p.1 p.2 (w p.1 p.2))
      ((volume.restrict (Ioo t₀ T)).prod volume) := by
  obtain ⟨M₁, hM₁, hgood⟩ := ae_good ht₀ hw hu1 huw
  obtain ⟨L, hL, hLb⟩ := exists_abs_le_of_isRenormalization hΥ
  obtain ⟨Cρ, hCρ, hCρb⟩ := exists_bound_scaled hρ hε.ne'
  obtain ⟨Dφ, hDφ, hDφb⟩ := exists_bound_fderiv_of_isTestFunction hφ
  obtain ⟨R, hR, b, -, hsupp⟩ := exists_ball_of_isTestFunction hφ
  have hU := aestronglyMeasurable_mollify (ε := ε) hρ (aestronglyMeasurable_u ht₀ hu1)
  have hsd : AEStronglyMeasurable (fun p : ℝ × ℂ => spaceDeriv φ p.1 p.2 (w p.1 p.2))
      ((volume.restrict (Ioo t₀ T)).prod volume) :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂
      (continuous_fderiv_slice hφ).aestronglyMeasurable (aestronglyMeasurable_w ht₀ hw)
  refine integrable_of_ball (R := R)
    (H := fun p => L * Cρ * M₁ * Dφ * ‖w p.1 p.2‖)
    (((hΥ.contDiff.continuous).comp_aestronglyMeasurable hU).mul hsd) ?_
    ((integrableOn_norm_w ht₀ hw hR).const_mul _) ?_
  · intro p hp
    have hp' : (p.1, p.2) ∉ tsupport φ := fun h => hp (hsupp _ h).2
    simp only [spaceDeriv_eq_zero_of_notMem hφ hp', mul_zero]
  · filter_upwards [hgood] with t ht x
    obtain ⟨ht1, ht2, -⟩ := ht
    have hUb := abs_mollify_le ht1 hCρb x
    rw [abs_mul]
    have h1 : |Υ (mollify ρ ε (u t) x)| ≤ L * Cρ * M₁ :=
      calc |Υ (mollify ρ ε (u t) x)| ≤ L * |mollify ρ ε (u t) x| := hLb _
        _ ≤ L * (Cρ * M₁) := mul_le_mul_of_nonneg_left
            (hUb.trans (mul_le_mul_of_nonneg_left ht2 hCρ)) hL
        _ = L * Cρ * M₁ := by ring
    calc |Υ (mollify ρ ε (u t) x)| * |spaceDeriv φ t x (w t x)|
        ≤ (L * Cρ * M₁) * (Dφ * ‖w t x‖) :=
          mul_le_mul h1 (abs_spaceDeriv_le hφ hDφb t x (w t x)) (abs_nonneg _)
            (by positivity)
      _ = L * Cρ * M₁ * Dφ * ‖w t x‖ := by ring

/-- The integrand `φ Υ'(U) D` is integrable. -/
theorem integrable_F3 (hρ : IsMollifier ρ) (hε : 0 < ε) (ht₀ : 0 ≤ t₀)
    (hw : IsBddH1DivFreeField (Ioo 0 T) w) (hu1 : Prelim.MemLinfLp (Ioo 0 T) univ 1 u)
    (huw : Integrable (fun p : ℝ × ℂ => u p.1 p.2 • w p.1 p.2) (volume.restrict (slab T)))
    (hΥ : IsRenormalization Υ) (hφ : IsTestFunction T φ) :
    Integrable (fun p : ℝ × ℂ =>
        φ p * deriv Υ (mollify ρ ε (u p.1) p.2) * mollifyDiv ρ ε u w p.1 p.2)
      ((volume.restrict (Ioo t₀ T)).prod volume) := by
  obtain ⟨M₁, hM₁, hgood⟩ := ae_good ht₀ hw hu1 huw
  obtain ⟨C', hC', hC'b⟩ := exists_abs_deriv_le_of_isRenormalization hΥ
  obtain ⟨CD, hCD, hCDb⟩ := exists_bound_fderiv_scaled hρ hε.ne'
  obtain ⟨A, hA, hAb⟩ := exists_bound_of_isTestFunction hφ
  obtain ⟨R, hR, b, -, hsupp⟩ := exists_ball_of_isTestFunction hφ
  have hU := aestronglyMeasurable_mollify (ε := ε) hρ (aestronglyMeasurable_u ht₀ hu1)
  have hD := aestronglyMeasurable_mollifyDiv (ε := ε) hρ (aestronglyMeasurable_uw ht₀ huw)
  have hN := integrable_norm_uw ht₀ huw
  have : IsFiniteMeasure (volume.restrict (ball (0 : ℂ) R)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hH : IntegrableOn (fun p : ℝ × ℂ => A * C' * CD * ∫ y, ‖u p.1 y • w p.1 y‖)
      (Ioo t₀ T ×ˢ ball (0 : ℂ) R) := by
    rw [IntegrableOn, restrict_prod_eq_prod]
    exact (hN.comp_fst (volume.restrict (ball (0 : ℂ) R))).const_mul _
  refine integrable_of_ball (R := R) ((hφ.contDiff.continuous.aestronglyMeasurable.mul
    ((continuous_deriv_of_isRenormalization hΥ).comp_aestronglyMeasurable hU)).mul hD)
    ?_ hH ?_
  · intro p hp
    have hp' : p ∉ tsupport φ := fun h => hp (hsupp _ h).2
    simp only [eq_zero_of_notMem_tsupport hp', zero_mul]
  · filter_upwards [hgood] with t ht x
    obtain ⟨-, -, ht3, -⟩ := ht
    have hDb := abs_mollifyDiv_le ht3 hCDb x
    rw [abs_mul, abs_mul]
    calc |φ (t, x)| * |deriv Υ (mollify ρ ε (u t) x)| * |mollifyDiv ρ ε u w t x|
        ≤ A * C' * (CD * ∫ y, ‖u t y • w t y‖) :=
          mul_le_mul (mul_le_mul (hAb _) (hC'b _) (abs_nonneg _) hA) hDb (abs_nonneg _)
            (mul_nonneg hA hC')
      _ = A * C' * CD * ∫ y, ‖u t y • w t y‖ := by ring

/-- The joint measurability of `G = w·∇(u ⋆ ρ_ε)`. -/
theorem aestronglyMeasurable_dotGradMollify (hρ : IsMollifier ρ) (hε : 0 < ε) (ht₀ : 0 ≤ t₀)
    (hw : IsBddH1DivFreeField (Ioo 0 T) w) (hu1 : Prelim.MemLinfLp (Ioo 0 T) univ 1 u)
    (huw : Integrable (fun p : ℝ × ℂ => u p.1 p.2 • w p.1 p.2) (volume.restrict (slab T))) :
    AEStronglyMeasurable (fun p : ℝ × ℂ => dotGradMollify ρ ε u w p.1 p.2)
      ((volume.restrict (Ioo t₀ T)).prod volume) := by
  obtain ⟨M₁, -, hgood⟩ := ae_good ht₀ hw hu1 huw
  have hA := aestronglyMeasurable_clm (ε := ε) hρ (aestronglyMeasurable_u ht₀ hu1)
  have hAw : AEStronglyMeasurable (fun p : ℝ × ℂ =>
      (∫ y, u p.1 y • fderiv ℝ (scaled ρ ε) (p.2 - y)) (w p.1 p.2))
      ((volume.restrict (Ioo t₀ T)).prod volume) :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂ hA
      (aestronglyMeasurable_w ht₀ hw)
  refine hAw.congr ?_
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hgood] with p hp
  exact (dotGradMollify_eq_clm hρ hε.ne' hp.1 p.2).symm

/-- The integrand `φ Υ'(U) G` is integrable. -/
theorem integrable_F4 (hρ : IsMollifier ρ) (hε : 0 < ε) (ht₀ : 0 ≤ t₀)
    (hw : IsBddH1DivFreeField (Ioo 0 T) w) (hu1 : Prelim.MemLinfLp (Ioo 0 T) univ 1 u)
    (huw : Integrable (fun p : ℝ × ℂ => u p.1 p.2 • w p.1 p.2) (volume.restrict (slab T)))
    (hΥ : IsRenormalization Υ) (hφ : IsTestFunction T φ) :
    Integrable (fun p : ℝ × ℂ =>
        φ p * deriv Υ (mollify ρ ε (u p.1) p.2) * dotGradMollify ρ ε u w p.1 p.2)
      ((volume.restrict (Ioo t₀ T)).prod volume) := by
  obtain ⟨M₁, hM₁, hgood⟩ := ae_good ht₀ hw hu1 huw
  obtain ⟨C', hC', hC'b⟩ := exists_abs_deriv_le_of_isRenormalization hΥ
  obtain ⟨CD, hCD, hCDb⟩ := exists_bound_fderiv_scaled hρ hε.ne'
  obtain ⟨A, hA, hAb⟩ := exists_bound_of_isTestFunction hφ
  obtain ⟨R, hR, b, -, hsupp⟩ := exists_ball_of_isTestFunction hφ
  have hU := aestronglyMeasurable_mollify (ε := ε) hρ (aestronglyMeasurable_u ht₀ hu1)
  have hG := aestronglyMeasurable_dotGradMollify hρ hε ht₀ hw hu1 huw
  refine integrable_of_ball (R := R) (H := fun p => A * C' * CD * M₁ * ‖w p.1 p.2‖)
    ((hφ.contDiff.continuous.aestronglyMeasurable.mul
      ((continuous_deriv_of_isRenormalization hΥ).comp_aestronglyMeasurable hU)).mul hG)
    ?_ ((integrableOn_norm_w ht₀ hw hR).const_mul _) ?_
  · intro p hp
    have hp' : p ∉ tsupport φ := fun h => hp (hsupp _ h).2
    simp only [eq_zero_of_notMem_tsupport hp', zero_mul]
  · filter_upwards [hgood] with t ht x
    obtain ⟨ht1, ht2, -⟩ := ht
    have hGb := abs_dotGradMollify_le (w := w) ht1 hCDb x
    have hGb' : |dotGradMollify ρ ε u w t x| ≤ CD * M₁ * ‖w t x‖ :=
      hGb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht2 hCD)
        (norm_nonneg _))
    rw [abs_mul, abs_mul]
    calc |φ (t, x)| * |deriv Υ (mollify ρ ε (u t) x)| * |dotGradMollify ρ ε u w t x|
        ≤ A * C' * (CD * M₁ * ‖w t x‖) :=
          mul_le_mul (mul_le_mul (hAb _) (hC'b _) (abs_nonneg _) hA) hGb' (abs_nonneg _)
            (mul_nonneg hA hC')
      _ = A * C' * CD * M₁ * ‖w t x‖ := by ring

/-- For every `x`, `U(·,x) = u(·) ⋆ ρ_ε (x)` is essentially bounded on `(t₀,T)`. -/
theorem memLp_top_mollify_slice (hρ : IsMollifier ρ) (hε : 0 < ε) (ht₀ : 0 ≤ t₀)
    (hw : IsBddH1DivFreeField (Ioo 0 T) w) (hu1 : Prelim.MemLinfLp (Ioo 0 T) univ 1 u)
    (huw : Integrable (fun p : ℝ × ℂ => u p.1 p.2 • w p.1 p.2) (volume.restrict (slab T)))
    (x : ℂ) : MemLp (fun s => mollify ρ ε (u s) x) ⊤ (volume.restrict (Ioo t₀ T)) := by
  obtain ⟨M₁, hM₁, hgood⟩ := ae_good ht₀ hw hu1 huw
  obtain ⟨Cρ, hCρ, hCρb⟩ := exists_bound_scaled hρ hε.ne'
  refine memLp_top_of_bound
    (aestronglyMeasurable_mollify_slice (ε := ε) hρ (aestronglyMeasurable_u ht₀ hu1) x)
    (Cρ * M₁) ?_
  filter_upwards [hgood] with t ht
  rw [Real.norm_eq_abs]
  exact (abs_mollify_le ht.1 hCρb x).trans (mul_le_mul_of_nonneg_left ht.2.1 hCρ)

/-- For every `x`, `D(·,x) = (div(wu)) ⋆ ρ_ε (·,x)` is integrable on `(t₀,T)`. -/
theorem integrable_mollifyDiv_slice (hρ : IsMollifier ρ) (hε : 0 < ε) (ht₀ : 0 ≤ t₀)
    (hw : IsBddH1DivFreeField (Ioo 0 T) w) (hu1 : Prelim.MemLinfLp (Ioo 0 T) univ 1 u)
    (huw : Integrable (fun p : ℝ × ℂ => u p.1 p.2 • w p.1 p.2) (volume.restrict (slab T)))
    (x : ℂ) : Integrable (fun s => mollifyDiv ρ ε u w s x) (volume.restrict (Ioo t₀ T)) := by
  obtain ⟨M₁, hM₁, hgood⟩ := ae_good ht₀ hw hu1 huw
  obtain ⟨CD, hCD, hCDb⟩ := exists_bound_fderiv_scaled hρ hε.ne'
  refine ((integrable_norm_uw ht₀ huw).const_mul CD).mono'
    (aestronglyMeasurable_mollifyDiv_slice (ε := ε) hρ (aestronglyMeasurable_uw ht₀ huw) x) ?_
  filter_upwards [hgood] with t ht
  rw [Real.norm_eq_abs]
  exact abs_mollifyDiv_le ht.2.2.1 hCDb x

/-- The mollified datum term `Υ(u₀ ⋆ ρ_ε) φ(t₀)` is integrable. -/
theorem integrable_datum (hρ : IsMollifier ρ) (hε : 0 < ε) {u₀ : ℂ → ℝ}
    (hu₀1 : MemLp u₀ 1 volume) (hΥ : IsRenormalization Υ) (hφ : IsTestFunction T φ)
    (t₀ : ℝ) : Integrable (fun x => Υ (mollify ρ ε u₀ x) * φ (t₀, x)) := by
  have hloc : LocallyIntegrable u₀ volume :=
    (memLp_one_iff_integrable.1 hu₀1).locallyIntegrable
  obtain ⟨hU₀, -⟩ := dotGradMollify_eq_fderiv (u := fun _ : ℝ => u₀) (t := 0)
    (w := fun _ _ => (0 : ℂ)) hρ hε hloc
  obtain ⟨hψ, hψc⟩ := slice_contDiff_hasCompactSupport hφ t₀
  exact ((hΥ.contDiff.continuous.comp hU₀.continuous).mul hψ.continuous).integrable_of_hasCompactSupport
    hψc.mul_left

end Integrability

end NonUniqueEuler.Weak.MollifiedH
