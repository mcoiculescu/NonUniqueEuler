import NonUniqueEuler.H.Sec4.Sector.GreenSol
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.MeanInequalities

/-!
# Helper for `lem:sector`(1): growth of `𝒢_ℓ g` at `0` and `∞`, and the bound on `𝒢_ℓ`

Helper file of `P/Sec4/Sector.lean` (fully proved). Manuscript `04_ring.tex:224-243`.

* `green_isBigO_zero`, `green_isBigO_atTop`: since `g` vanishes outside `[a, b]`, `𝒢_ℓ g` is a
  multiple of `rⁿ` on `(0, a]` and of `r⁻ⁿ` on `[b, ∞)`.
* `norm_green_le`: `|𝒢_ℓ g(r)| ≤ (2n)⁻¹∫_{[a,b]} ρ|g| ≤ (b/(2n)) ‖g‖_{L²(r dr)}` (the kernel is
  at most `1`, and Cauchy–Schwarz on `[a, b]`).
-/

noncomputable section

open MeasureTheory Set Filter Topology Asymptotics

namespace NonUniqueEuler.SectorH

open SectorSetting

variable {a b : ℝ} {g : ℝ → ℂ}

/-! ### Growth -/

theorem Prof.Psi_of_le (h : Prof a b g) (n : ℕ) {t : ℝ} (ht : t ≤ a) :
    Psi a b n g t = (t : ℂ) ^ n * ∫ ρ in Icc a b, ((((ρ ^ n)⁻¹ * ρ : ℝ)) : ℂ) * g ρ := by
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Icc fun ρ hρ => ?_
  have hρ0 : 0 < ρ := h.pos_of_mem hρ
  rw [ker_of_le (ht.trans hρ.1), kL, div_pow]
  push_cast
  field_simp

theorem Prof.Psi_of_ge (h : Prof a b g) (n : ℕ) {t : ℝ} (ht : b ≤ t) :
    Psi a b n g t = ((t ^ n)⁻¹ : ℂ) * ∫ ρ in Icc a b, (((ρ ^ n * ρ : ℝ)) : ℂ) * g ρ := by
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Icc fun ρ hρ => ?_
  rw [ker_of_ge (hρ.2.trans ht), kR, div_pow]
  push_cast
  ring

theorem green_isBigO_zero (h : Prof a b g) (ℓ : ℤ) :
    green ℓ g =O[𝓝[>] 0] fun r : ℝ => r ^ ℓ.natAbs := by
  set C : ℂ := -(((2 * |(ℓ : ℝ)|)⁻¹ : ℝ) : ℂ) *
    ∫ ρ in Icc a b, ((((ρ ^ ℓ.natAbs)⁻¹ * ρ : ℝ)) : ℂ) * g ρ
  refine IsBigO.of_bound ‖C‖ ?_
  filter_upwards [Ioo_mem_nhdsGT h.pos] with t ht
  rw [green_eq_Psi h ℓ t, h.Psi_of_le _ ht.2.le]
  have : -(((2 * |(ℓ : ℝ)|)⁻¹ : ℝ) : ℂ) * ((t : ℂ) ^ ℓ.natAbs *
      ∫ ρ in Icc a b, ((((ρ ^ ℓ.natAbs)⁻¹ * ρ : ℝ)) : ℂ) * g ρ) = C * (t : ℂ) ^ ℓ.natAbs := by
    simp only [C]
    ring
  rw [this, norm_mul, norm_pow, Complex.norm_real, norm_pow]

theorem green_isBigO_atTop (h : Prof a b g) (ℓ : ℤ) :
    green ℓ g =O[atTop] fun r : ℝ => r ^ (-(ℓ.natAbs : ℤ)) := by
  set C : ℂ := -(((2 * |(ℓ : ℝ)|)⁻¹ : ℝ) : ℂ) *
    ∫ ρ in Icc a b, (((ρ ^ ℓ.natAbs * ρ : ℝ)) : ℂ) * g ρ
  refine IsBigO.of_bound ‖C‖ ?_
  filter_upwards [Ici_mem_atTop b] with t ht
  rw [green_eq_Psi h ℓ t, h.Psi_of_ge _ ht]
  have : -(((2 * |(ℓ : ℝ)|)⁻¹ : ℝ) : ℂ) * (((t : ℂ) ^ ℓ.natAbs)⁻¹ *
      ∫ ρ in Icc a b, (((ρ ^ ℓ.natAbs * ρ : ℝ)) : ℂ) * g ρ) = C * ((t : ℂ) ^ ℓ.natAbs)⁻¹ := by
    simp only [C]
    ring
  rw [this, norm_mul, norm_inv, norm_pow, Complex.norm_real, zpow_neg, zpow_natCast, norm_inv,
    norm_pow]

/-! ### The bound -/

theorem Prof.setIntegral_norm_sq_mul (h : Prof a b g) :
    ∫ ρ in Ioi (0 : ℝ), ‖g ρ‖ ^ 2 * ρ = ∫ ρ in Icc a b, ‖g ρ‖ ^ 2 * ρ := by
  refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioi.nullMeasurableSet
    (fun ρ hρ => h.pos.trans_le hρ.1) ?_
  filter_upwards [h.ae_supp] with x hx hxA
  rw [hx hxA.1 hxA.2, norm_zero]
  ring

/-- Cauchy–Schwarz on `[a, b]`: `∫ ρ|g| ≤ (∫|g|²ρ)^{1/2} (∫ ρ)^{1/2}`. -/
theorem integral_mul_norm_le (h : Prof a b g) (hg2 : MemLp g 2 (volume.restrict (Icc a b))) :
    ∫ ρ in Icc a b, ρ * ‖g ρ‖ ≤
      Real.sqrt (∫ ρ in Icc a b, ‖g ρ‖ ^ 2 * ρ) * Real.sqrt (∫ ρ in Icc a b, ρ) := by
  set μ : Measure ℝ := volume.restrict (Icc a b)
  have hfin : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 measure_Icc_lt_top.ne
  have hρ0 : ∀ᵐ ρ ∂μ, 0 < ρ := ae_restrict_of_forall_mem measurableSet_Icc fun ρ hρ =>
    h.pos_of_mem hρ
  have hρb : ∀ᵐ ρ ∂μ, ρ ≤ b := ae_restrict_of_forall_mem measurableSet_Icc fun ρ hρ => hρ.2
  have hsq_meas : AEStronglyMeasurable (fun ρ : ℝ => Real.sqrt ρ) μ :=
    Real.continuous_sqrt.measurable.aestronglyMeasurable
  have hf_meas : AEStronglyMeasurable (fun ρ : ℝ => Real.sqrt ρ * ‖g ρ‖) μ :=
    hsq_meas.mul hg2.1.norm
  have hgsq : Integrable (fun ρ => ‖g ρ‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hg2.1).1 hg2
  have hint1 : Integrable (fun ρ => ‖g ρ‖ ^ 2 * ρ) μ := by
    refine hgsq.mul_bdd (c := b) measurable_id.aestronglyMeasurable ?_
    filter_upwards [hρ0, hρb] with ρ h0 hb
    rw [Real.norm_eq_abs, abs_of_pos h0]
    exact hb
  have hf : MemLp (fun ρ : ℝ => Real.sqrt ρ * ‖g ρ‖) (ENNReal.ofReal 2) μ := by
    rw [ENNReal.ofReal_ofNat, memLp_two_iff_integrable_sq hf_meas]
    refine hint1.congr ?_
    filter_upwards [hρ0] with ρ h0
    rw [mul_pow, Real.sq_sqrt h0.le]
    ring
  have hg' : MemLp (fun ρ : ℝ => Real.sqrt ρ) (ENNReal.ofReal 2) μ := by
    refine MemLp.of_bound hsq_meas (Real.sqrt b) ?_
    filter_upwards [hρ0, hρb] with ρ h0 hb
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt hb
  have key := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall fun ρ => mul_nonneg (Real.sqrt_nonneg ρ) (norm_nonneg (g ρ)))
    (Eventually.of_forall fun ρ => Real.sqrt_nonneg ρ) hf hg'
  have e1 : ∫ ρ, Real.sqrt ρ * ‖g ρ‖ * Real.sqrt ρ ∂μ = ∫ ρ, ρ * ‖g ρ‖ ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hρ0] with ρ h0
    have := Real.mul_self_sqrt h0.le
    calc Real.sqrt ρ * ‖g ρ‖ * Real.sqrt ρ = (Real.sqrt ρ * Real.sqrt ρ) * ‖g ρ‖ := by ring
      _ = ρ * ‖g ρ‖ := by rw [this]
  have e2 : ∫ ρ, (Real.sqrt ρ * ‖g ρ‖) ^ (2 : ℝ) ∂μ = ∫ ρ, ‖g ρ‖ ^ 2 * ρ ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hρ0] with ρ h0
    rw [Real.rpow_two, mul_pow, Real.sq_sqrt h0.le]
    ring
  have e3 : ∫ ρ, (Real.sqrt ρ) ^ (2 : ℝ) ∂μ = ∫ ρ, ρ ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hρ0] with ρ h0
    rw [Real.rpow_two, Real.sq_sqrt h0.le]
  rw [e1, e2, e3] at key
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact key

theorem norm_green_le (h : Prof a b g) (hg2 : MemLp g 2 (volume.restrict (Icc a b))) {ℓ : ℤ}
    (hℓ : ℓ ≠ 0) {r : ℝ} (hr : 0 ≤ r) :
    ‖green ℓ g r‖ ≤ b / (2 * |(ℓ : ℝ)|) *
      Real.sqrt (∫ ρ in Ioi (0 : ℝ), ‖g ρ‖ ^ 2 * ρ) := by
  have hl : 0 < |(ℓ : ℝ)| := abs_pos.2 (by exact_mod_cast hℓ)
  have hb : 0 < b := h.pos.trans_le h.le
  rw [green_eq_Psi h ℓ r, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity), h.setIntegral_norm_sq_mul]
  have h1 : ‖Psi a b ℓ.natAbs g r‖ ≤ ∫ ρ in Icc a b, ρ * ‖g ρ‖ := by
    refine (norm_integral_le_integral_norm _).trans ?_
    refine setIntegral_mono_on (h.integrable_ker _ hr).norm ?_ measurableSet_Icc fun ρ hρ => ?_
    · exact h.int.norm.bdd_mul (c := b) measurable_id.aestronglyMeasurable
        (ae_restrict_of_forall_mem measurableSet_Icc fun ρ hρ => by
          rw [Real.norm_eq_abs, abs_of_pos (h.pos_of_mem hρ)]; exact hρ.2)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (abs_ker_le hr (h.pos_of_mem hρ)) (norm_nonneg _)
  have h2 := integral_mul_norm_le h hg2
  have h3 : Real.sqrt (∫ ρ in Icc a b, ρ) ≤ b := by
    rw [Real.sqrt_le_left hb.le]
    have : ∫ ρ in Icc a b, ρ ≤ ∫ ρ in Icc a b, b := by
      refine setIntegral_mono_on ?_ ?_ measurableSet_Icc fun ρ hρ => hρ.2
      · exact (continuous_id.integrableOn_Icc)
      · exact (continuous_const.integrableOn_Icc)
    refine this.trans ?_
    rw [setIntegral_const, Real.volume_real_Icc_of_le h.le, smul_eq_mul]
    nlinarith [h.pos, h.le]
  have hsq0 : 0 ≤ Real.sqrt (∫ ρ in Icc a b, ‖g ρ‖ ^ 2 * ρ) := Real.sqrt_nonneg _
  calc (2 * |(ℓ : ℝ)|)⁻¹ * ‖Psi a b ℓ.natAbs g r‖
      ≤ (2 * |(ℓ : ℝ)|)⁻¹ * (Real.sqrt (∫ ρ in Icc a b, ‖g ρ‖ ^ 2 * ρ) * b) := by
        gcongr
        exact h1.trans (h2.trans (mul_le_mul_of_nonneg_left h3 hsq0))
    _ = b / (2 * |(ℓ : ℝ)|) * Real.sqrt (∫ ρ in Icc a b, ‖g ρ‖ ^ 2 * ρ) := by
        field_simp

end NonUniqueEuler.SectorH
