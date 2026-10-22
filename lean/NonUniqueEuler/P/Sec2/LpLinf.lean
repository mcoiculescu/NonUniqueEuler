import NonUniqueEuler.Defs.Sec2.BiotSavart
import NonUniqueEuler.I.Sec2.BSBasic
import NonUniqueEuler.I.Infra.Polar.Power
import NonUniqueEuler.I.Infra.ConvMinkowski.Young
import NonUniqueEuler.I.Infra.ConvMinkowski.Measurable

/-!
# Proof: `lem:LpLinf`, the `L^∞` bound of the velocity of an `L¹ ∩ L^p` vorticity, `p > 2`

Proof of `I/Sec2/LpLinf.lean` (`02_prelim.tex:386-406`). Write `q = p' = p.conjExponent`, so
`1 < q < 2`. For `R > 0` split the kernel as `K = 1_{B_R} K + 1_{B_R^c} K`. Then
* `‖1_{B_R} K‖_{L^q} = (2π)⁻¹ (2π R^{2-q}/(2-q))^{1/q} = (2π)⁻¹ c_p R^{2/q-1}`
  (`lem:BS-basic`(a) and `Polar.lintegral_ball_norm_rpow` with exponent `-q > -2`);
* `‖1_{B_R^c} K‖_{L^∞} ≤ (2πR)⁻¹`;
* Hölder in the split form `Conv.convAbs_le_of_split_holder` gives
  `(|K| ∗ |g|)(x) ≤ (2π)⁻¹ c_p R^{2/q-1} ‖g‖_p + (2πR)⁻¹ ‖g‖₁` for every `x`.
With `R = (‖g‖₁/‖g‖_p)^{q/2}` both terms equal `(2π)⁻¹ ‖g‖₁^{1-q/2} ‖g‖_p^{q/2}` (times `c_p`, resp.
`1`). If `‖g‖₁ = 0` or `‖g‖_p = 0` then `g = 0` a.e., both norms vanish and the bound with `R = 1`
is `0`. Absolute convergence: `Conv.integrable_conv_of_convAbs_ne_top`; the pointwise velocity
bound: `Conv.enorm_velocity_le`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace NonUniqueEuler.BS

/-! ### Helpers -/

/-- `‖K_BS(z)‖ = (2π‖z‖)⁻¹` for every `z` (both sides vanish at `z = 0`). -/
private theorem norm_kernel_eq (z : ℂ) :
    ‖biotSavartKernel z‖ = (2 * Real.pi * ‖z‖)⁻¹ := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [biotSavartKernel]
  · exact norm_biotSavartKernel_eq hz

private theorem measurable_kernel : Measurable biotSavartKernel := by
  unfold biotSavartKernel
  fun_prop

/-- `1 < p' < 2` for `p > 2`. -/
private theorem conjExponent_bounds {p : ℝ} (hp : 2 < p) :
    1 < p.conjExponent ∧ p.conjExponent < 2 := by
  have hp1 : 0 < p - 1 := by linarith
  refine ⟨?_, ?_⟩
  · rw [Real.conjExponent, lt_div_iff₀ hp1]
    linarith
  · rw [Real.conjExponent, div_lt_iff₀ hp1]
    linarith

/-- The real identity behind `‖1_{B_R} K‖_{L^q}` (with `a = 2π`):
`(a^{-q} · a R^{-q+2}/(-q+2))^{1/q} = a⁻¹ (a/(2-q))^{1/q} R^{2/q-1}`. -/
private theorem near_norm_identity {a q R : ℝ} (ha : 0 < a) (hq0 : 0 < q) (hq2 : q < 2)
    (hR : 0 < R) :
    (a ^ (-q) * (a * R ^ (-q + 2) / (-q + 2))) ^ (1 / q) =
      a⁻¹ * (a / (2 - q)) ^ (1 / q) * R ^ (2 / q - 1) := by
  have h2q : 0 < 2 - q := by linarith
  have e1 : a * R ^ (-q + 2) / (-q + 2) = a / (2 - q) * R ^ (2 - q) := by
    rw [show -q + 2 = 2 - q by ring]
    ring
  have hA : 0 ≤ a ^ (-q) := by positivity
  have hB : 0 ≤ a / (2 - q) := by positivity
  have hC : 0 ≤ R ^ (2 - q) := by positivity
  rw [e1, Real.mul_rpow hA (mul_nonneg hB hC), Real.mul_rpow hB hC, ← Real.rpow_mul ha.le,
    ← Real.rpow_mul hR.le]
  have e2 : -q * (1 / q) = -1 := by field_simp
  have e3 : (2 - q) * (1 / q) = 2 / q - 1 := by field_simp
  rw [e2, e3, Real.rpow_neg_one]
  ring

/-- `c_p ≥ 0` for `p > 2`. -/
private theorem cLpLinf_nonneg {p : ℝ} (hp : 2 < p) : 0 ≤ cLpLinf p := by
  have h2 : 0 < 2 - p.conjExponent := by linarith [(conjExponent_bounds hp).2]
  have h3 : 0 ≤ 2 * Real.pi / (2 - p.conjExponent) := by positivity
  exact Real.rpow_nonneg h3 _

/-- The near part `1_{B_R} K` of the kernel at radius `R`. -/
private def kNear (R : ℝ) : ℂ → ℂ := (ball (0 : ℂ) R).indicator biotSavartKernel

/-- The far part `1_{B_R^c} K` of the kernel at radius `R`. -/
private def kFar (R : ℝ) : ℂ → ℂ := (ball (0 : ℂ) R)ᶜ.indicator biotSavartKernel

private theorem norm_le_kNear_add_kFar (R : ℝ) (z : ℂ) :
    ‖biotSavartKernel z‖ ≤ ‖kNear R z‖ + ‖kFar R z‖ := by
  rw [← indicator_self_add_compl_apply (ball (0 : ℂ) R) biotSavartKernel z]
  exact norm_add_le _ _

/-- `‖1_{B_R} K(z)‖ₑ^q = 1_{B_R}(z) (2π)^{-q} ‖z‖^{-q}` for `q > 0`. -/
private theorem enorm_kNear_rpow {q : ℝ} (hq : 0 < q) (R : ℝ) (z : ℂ) :
    ‖kNear R z‖ₑ ^ q =
      (ball (0 : ℂ) R).indicator
        (fun z => ENNReal.ofReal ((2 * Real.pi) ^ (-q)) * ENNReal.ofReal (‖z‖ ^ (-q))) z := by
  have hpi : 0 < 2 * Real.pi := by positivity
  by_cases hz : z ∈ ball (0 : ℂ) R
  · rw [indicator_of_mem hz, kNear, indicator_of_mem hz, ← ofReal_norm, norm_kernel_eq,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) hq.le, ← ENNReal.ofReal_mul (by positivity),
      Real.inv_rpow (by positivity), Real.mul_rpow hpi.le (norm_nonneg _),
      Real.rpow_neg hpi.le, Real.rpow_neg (norm_nonneg _), mul_inv]
  · rw [indicator_of_notMem hz, kNear, indicator_of_notMem hz, enorm_zero,
      ENNReal.zero_rpow_of_pos hq]

/-- `‖1_{B_R} K‖_{L^{p'}} = (2π)⁻¹ c_p R^{2/p'-1}` for `p > 2`, `R > 0`. -/
private theorem eLpNorm_kNear {p : ℝ} (hp : 2 < p) {R : ℝ} (hR : 0 < R) :
    eLpNorm (kNear R) (ENNReal.ofReal p.conjExponent) volume =
      ENNReal.ofReal ((2 * Real.pi)⁻¹ * cLpLinf p * R ^ (2 / p.conjExponent - 1)) := by
  obtain ⟨hq1, hq2⟩ := conjExponent_bounds hp
  set q := p.conjExponent with hqdef
  have hq0 : 0 < q := by linarith
  have hpi : 0 < 2 * Real.pi := by positivity
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hq0) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hq0.le]
  simp_rw [enorm_kNear_rpow hq0 R]
  rw [lintegral_indicator measurableSet_ball, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    Polar.lintegral_ball_norm_rpow (by linarith) hR.le, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_rpow_of_nonneg ?_ (by positivity), near_norm_identity hpi hq0 hq2 hR, cLpLinf]
  have : 0 < -q + 2 := by linarith
  positivity

/-- `‖1_{B_R^c} K‖_{L^∞} ≤ (2πR)⁻¹` for `R > 0`. -/
private theorem eLpNorm_kFar_le {R : ℝ} (hR : 0 < R) :
    eLpNorm (kFar R) ⊤ volume ≤ ENNReal.ofReal ((2 * Real.pi * R)⁻¹) := by
  rw [eLpNorm_exponent_top]
  refine eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall fun z => ?_)
  have hpi : 0 < 2 * Real.pi := by positivity
  by_cases hz : z ∈ (ball (0 : ℂ) R)ᶜ
  · rw [kFar, indicator_of_mem hz, norm_kernel_eq]
    have hzR : R ≤ ‖z‖ := by simpa [mem_ball_zero_iff] using hz
    exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left hzR hpi.le)
  · rw [kFar, indicator_of_notMem hz, norm_zero]
    positivity

/-- The split bound at radius `R`:
`(|K| ∗ |g|)(x) ≤ (2π)⁻¹ c_p R^{2/p'-1} ‖g‖_p + (2πR)⁻¹ ‖g‖₁`. -/
private theorem convAbs_le_split {p : ℝ} (hp : 2 < p) {g : ℂ → ℝ} (hg1 : MemLp g 1 volume)
    (hgp : MemLp g (ENNReal.ofReal p) volume) {R : ℝ} (hR : 0 < R) (x : ℂ) :
    Conv.convAbs biotSavartKernel g x ≤ ENNReal.ofReal
      ((2 * Real.pi)⁻¹ * cLpLinf p * R ^ (2 / p.conjExponent - 1) *
          (eLpNorm g (ENNReal.ofReal p) volume).toReal +
        (2 * Real.pi * R)⁻¹ * (eLpNorm g 1 volume).toReal) := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have hp1 : 1 < p := by linarith
  have hpq : (ENNReal.ofReal p.conjExponent).HolderConjugate (ENNReal.ofReal p) :=
    (Real.HolderConjugate.conjExponent hp1).symm.ennrealOfReal
  have hK₁ : AEStronglyMeasurable (kNear R) volume :=
    (measurable_kernel.indicator measurableSet_ball).aestronglyMeasurable
  have hK₂ : AEStronglyMeasurable (kFar R) volume :=
    (measurable_kernel.indicator measurableSet_ball.compl).aestronglyMeasurable
  have hmain := Conv.convAbs_le_of_split_holder hK₁ hK₂ (norm_le_kNear_add_kFar R)
    hg1.aestronglyMeasurable hpq x
  rw [eLpNorm_kNear hp hR, ← ENNReal.ofReal_toReal hgp.2.ne,
    ← ENNReal.ofReal_toReal hg1.2.ne] at hmain
  have hc : 0 ≤ cLpLinf p := cLpLinf_nonneg hp
  have hX : 0 ≤ (2 * Real.pi)⁻¹ * cLpLinf p * R ^ (2 / p.conjExponent - 1) := by positivity
  have hY : 0 ≤ (2 * Real.pi * R)⁻¹ := by positivity
  calc Conv.convAbs biotSavartKernel g x
      ≤ _ := hmain
    _ ≤ ENNReal.ofReal ((2 * Real.pi)⁻¹ * cLpLinf p * R ^ (2 / p.conjExponent - 1)) *
          ENNReal.ofReal (eLpNorm g (ENNReal.ofReal p) volume).toReal +
        ENNReal.ofReal ((2 * Real.pi * R)⁻¹) * ENNReal.ofReal (eLpNorm g 1 volume).toReal := by
      gcongr
      exact eLpNorm_kFar_le hR
    _ = _ := by
      rw [← ENNReal.ofReal_mul hX, ← ENNReal.ofReal_mul hY,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]

/-- The optimization identity: with `R = (A/B)^{q/2}`,
`(2π)⁻¹ c R^{2/q-1} B + (2πR)⁻¹ A = (1 + c)/(2π) A^{1-q/2} B^{q/2}`. -/
private theorem optimize_identity {q A B c : ℝ} (hq : 0 < q) (hA : 0 < A) (hB : 0 < B) :
    (2 * Real.pi)⁻¹ * c * ((A / B) ^ (q / 2)) ^ (2 / q - 1) * B +
        (2 * Real.pi * (A / B) ^ (q / 2))⁻¹ * A =
      (1 + c) / (2 * Real.pi) * A ^ (1 - q / 2) * B ^ (q / 2) := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have hAB : 0 < A / B := div_pos hA hB
  have e1 : ((A / B) ^ (q / 2)) ^ (2 / q - 1) = (A / B) / (A ^ (q / 2) / B ^ (q / 2)) := by
    rw [← Real.rpow_mul hAB.le, show q / 2 * (2 / q - 1) = 1 - q / 2 by field_simp,
      Real.rpow_sub hAB, Real.rpow_one, Real.div_rpow hA.le hB.le]
  have e2 : (A / B) ^ (q / 2) = A ^ (q / 2) / B ^ (q / 2) := Real.div_rpow hA.le hB.le _
  have e3 : A ^ (1 - q / 2) = A / A ^ (q / 2) := by
    rw [Real.rpow_sub hA, Real.rpow_one]
  have ha : 0 < A ^ (q / 2) := Real.rpow_pos_of_pos hA _
  have hb : 0 < B ^ (q / 2) := Real.rpow_pos_of_pos hB _
  rw [e1, e2, e3]
  field_simp
  ring

/-! ### The lemma -/

/-- `lem:LpLinf`: for `2 < p < ∞` and `g ∈ L¹ ∩ L^p`, at every `x` the majorant satisfies
`(|K| ∗ |g|)(x) ≤ (1 + c_p)/(2π) ‖g‖₁^{1-p'/2} ‖g‖_p^{p'/2}`, the integral defining `K ∗ g(x)`
converges absolutely, and `|K ∗ g(x)|` obeys the same bound. -/
theorem velocity_bound_L1_Lp {p : ℝ} (hp : 2 < p) {g : ℂ → ℝ} (hg1 : MemLp g 1 volume)
    (hgp : MemLp g (ENNReal.ofReal p) volume) (x : ℂ) :
    Conv.convAbs biotSavartKernel g x ≤ ENNReal.ofReal
        ((1 + cLpLinf p) / (2 * Real.pi) * (eLpNorm g 1 volume).toReal ^ (1 - p.conjExponent / 2) *
          (eLpNorm g (ENNReal.ofReal p) volume).toReal ^ (p.conjExponent / 2)) ∧
      Integrable (fun y => biotSavartKernel (x - y) * (g y : ℂ)) volume ∧
      ‖velocity g x‖ ≤
        (1 + cLpLinf p) / (2 * Real.pi) * (eLpNorm g 1 volume).toReal ^ (1 - p.conjExponent / 2) *
          (eLpNorm g (ENNReal.ofReal p) volume).toReal ^ (p.conjExponent / 2) := by
  obtain ⟨hq1, hq2⟩ := conjExponent_bounds hp
  have hpi : 0 < 2 * Real.pi := by positivity
  have hc : 0 ≤ cLpLinf p := cLpLinf_nonneg hp
  set A := (eLpNorm g 1 volume).toReal with hAdef
  set B := (eLpNorm g (ENNReal.ofReal p) volume).toReal with hBdef
  set q := p.conjExponent with hqdef
  have hA0 : 0 ≤ A := ENNReal.toReal_nonneg
  have hB0 : 0 ≤ B := ENNReal.toReal_nonneg
  have hbound0 : 0 ≤ (1 + cLpLinf p) / (2 * Real.pi) * A ^ (1 - q / 2) * B ^ (q / 2) := by
    have := Real.rpow_nonneg hA0 (1 - q / 2)
    have := Real.rpow_nonneg hB0 (q / 2)
    positivity
  have h1 : Conv.convAbs biotSavartKernel g x ≤
      ENNReal.ofReal ((1 + cLpLinf p) / (2 * Real.pi) * A ^ (1 - q / 2) * B ^ (q / 2)) := by
    by_cases hAB : A = 0 ∨ B = 0
    · -- `g = 0` a.e., so both norms vanish
      have hg0 : g =ᵐ[volume] 0 := by
        rcases hAB with h | h
        · rw [hAdef, ENNReal.toReal_eq_zero_iff] at h
          rcases h with h | h
          · exact (eLpNorm_eq_zero_iff hg1.aestronglyMeasurable one_ne_zero).1 h
          · exact absurd h hg1.2.ne
        · rw [hBdef, ENNReal.toReal_eq_zero_iff] at h
          rcases h with h | h
          · exact (eLpNorm_eq_zero_iff hg1.aestronglyMeasurable
              (by simp; linarith)).1 h
          · exact absurd h hgp.2.ne
      have hA' : A = 0 := by
        rw [hAdef, eLpNorm_congr_ae hg0, eLpNorm_zero, ENNReal.toReal_zero]
      have hB' : B = 0 := by
        rw [hBdef, eLpNorm_congr_ae hg0, eLpNorm_zero, ENNReal.toReal_zero]
      refine (convAbs_le_split hp hg1 hgp one_pos x).trans ?_
      rw [← hAdef, ← hBdef, hA', hB']
      simp
    · push Not at hAB
      have hA : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hAB.1)
      have hB : 0 < B := lt_of_le_of_ne hB0 (Ne.symm hAB.2)
      have hR : 0 < (A / B) ^ (q / 2) := Real.rpow_pos_of_pos (div_pos hA hB) _
      refine (convAbs_le_split hp hg1 hgp hR x).trans (le_of_eq ?_)
      rw [← hAdef, ← hBdef, ← hqdef, optimize_identity (by linarith) hA hB]
  have hK : AEStronglyMeasurable biotSavartKernel volume := measurable_kernel.aestronglyMeasurable
  refine ⟨h1, ?_, ?_⟩
  · exact Conv.integrable_conv_of_convAbs_ne_top hK hg1.aestronglyMeasurable
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1)
  · have h2 := (Conv.enorm_velocity_le g x).trans h1
    rw [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff hbound0] at h2
    exact h2

/-- `lem:LpLinf`, `L^∞` form: `‖K ∗ g‖_{L^∞} ≤ (1 + c_p)/(2π) ‖g‖₁^{1-p'/2} ‖g‖_p^{p'/2}`. -/
theorem eLpNorm_velocity_top_le_L1_Lp {p : ℝ} (hp : 2 < p) {g : ℂ → ℝ} (hg1 : MemLp g 1 volume)
    (hgp : MemLp g (ENNReal.ofReal p) volume) :
    eLpNorm (velocity g) ⊤ volume ≤ ENNReal.ofReal
        ((1 + cLpLinf p) / (2 * Real.pi) * (eLpNorm g 1 volume).toReal ^ (1 - p.conjExponent / 2) *
          (eLpNorm g (ENNReal.ofReal p) volume).toReal ^ (p.conjExponent / 2)) := by
  rw [eLpNorm_exponent_top]
  exact eLpNormEssSup_le_of_ae_bound
    (Filter.Eventually.of_forall fun x => (velocity_bound_L1_Lp hp hg1 hgp x).2.2)

end NonUniqueEuler.BS
