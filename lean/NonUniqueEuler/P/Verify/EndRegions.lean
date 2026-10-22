import NonUniqueEuler.Defs.Verify.Profile
import NonUniqueEuler.I.Verify.ProfileBasic
import NonUniqueEuler.I.Verify.ProfileOmega
import NonUniqueEuler.I.Verify.Comparison
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Proof: Lemma A.1 (`lem:end-regions`)

Proof of the interface `NonUniqueEuler/I/Verify/EndRegions.lean` (same declarations, same
statements). Manuscript: `A_verification.tex:131-191`, Equation `(eq:xayb)` (`:34-41`).

**Deviation (a variant of restructuring T3).** For `w = AB` we use the exact
identity `w' = A'B + AB' = (2/d) A B (Ā - B̄)` (from `A' = (2/d)AĀ`, `B' = -(2/d)BB̄`), so
`|w'| ≤ (2/d) w ≤ (2/d) min(A, B)` because `Ā, B̄ ∈ [0, 1]`. With `|ϖ'| ≤ |χ'| w + |w'|` this
gives `∫_{ξL}^{ξa} |ϖ'| ≤ A(ξa) + e^{2x_a} ≤ 2e^{2x_a}` (and `≤ 2e^{2y_b}` on the right), which
is stronger than the manuscript's `(9/4)e^{2x_a}` (constant `5/(2d)` replaced by `2/d`). The
integrals are computed by one application of the fundamental theorem of calculus to the
antiderivative `A(ξa) χ + e^{2(ξ-a₀)/d}` (resp. `-B(ξb) χ - e^{-2ξ/d}`). The integrals over the
half lines reduce to `[ξL, ξa]` and `[ξb, ξR]` since `ϖ' = 0` outside `[ξL, ξR]`.
-/

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace NonUniqueEuler

namespace AppA

open RingData

/-! ### Numerics -/

/-- Equation `(eq:xayb)`, first half: `-25 < x_a < -25 + 4·10^{-15}`. -/
theorem xa_bounds : -25 < xa ∧ xa < -25 + 4 / 10 ^ 15 := by
  constructor <;> norm_num [xa, ξa, a₀, d]

/-- Equation `(eq:xayb)`, second half: `-25 < y_b < -25 + 10^{-15}`. -/
theorem yb_bounds : -25 < yb ∧ yb < -25 + 1 / 10 ^ 15 := by
  constructor <;> norm_num [yb, ξb, d]

private theorem exp_small_lt : Real.exp (8 / 10 ^ 15) < 4 / 3 := by
  have h := Real.exp_bound_div_one_sub_of_interval' (x := 8 / 10 ^ 15) (by norm_num)
    (by norm_num)
  refine h.trans ?_
  norm_num

private theorem const_lt_of_lt {x : ℝ} (hx : x < -25 + 4 / 10 ^ 15) :
    9 / 4 * Real.exp (2 * x) < 3 * Real.exp (-50) := by
  have h1 : Real.exp (2 * x) < Real.exp (-50) * Real.exp (8 / 10 ^ 15) := by
    rw [← Real.exp_add]
    exact Real.exp_lt_exp.2 (by linarith)
  have h2 := exp_small_lt
  have h3 := Real.exp_pos (-50)
  nlinarith

/-- **Lemma A.1(1)**, the numerical bounds: both constants are `< 3e^{-50}`. -/
theorem endRegion_const_lt :
    9 / 4 * Real.exp (2 * xa) < 3 * Real.exp (-50) ∧
      9 / 4 * Real.exp (2 * yb) < 3 * Real.exp (-50) :=
  ⟨const_lt_of_lt xa_bounds.2, const_lt_of_lt (by linarith [yb_bounds.2])⟩

private theorem ξL_le_ξa : ξL ≤ ξa := by norm_num [ξL, ξa]
private theorem ξb_le_ξR : ξb ≤ ξR := by norm_num [ξb, ξR]
private theorem ξa_le_ξR : ξa ≤ ξR := by norm_num [ξa, ξR]
private theorem ξL_le_ξb : ξL ≤ ξb := by norm_num [ξL, ξb]
private theorem d_pos : 0 < d := by norm_num [d]

/-! ### The functions `A`, `B`, `w = AB` -/

private theorem profA_nonneg (ξ : ℝ) : 0 ≤ profA ξ := (H_pos _).le
private theorem profB_nonneg (ξ : ℝ) : 0 ≤ profB ξ := (H_pos _).le
private theorem profAbar_nonneg (ξ : ℝ) : 0 ≤ profAbar ξ := (H_pos _).le
private theorem profBbar_nonneg (ξ : ℝ) : 0 ≤ profBbar ξ := (H_pos _).le
private theorem profA_le_one (ξ : ℝ) : profA ξ ≤ 1 := H_le_one _
private theorem profB_le_one (ξ : ℝ) : profB ξ ≤ 1 := H_le_one _
private theorem profAbar_le_one (ξ : ℝ) : profAbar ξ ≤ 1 := H_le_one _
private theorem profBbar_le_one (ξ : ℝ) : profBbar ξ ≤ 1 := H_le_one _

private theorem profW_nonneg (ξ : ℝ) : 0 ≤ profW ξ :=
  mul_nonneg (profA_nonneg ξ) (profB_nonneg ξ)

private theorem profW_le_profA (ξ : ℝ) : profW ξ ≤ profA ξ := by
  have := mul_le_mul_of_nonneg_left (profB_le_one ξ) (profA_nonneg ξ)
  simpa [profW] using this

private theorem profW_le_profB (ξ : ℝ) : profW ξ ≤ profB ξ := by
  have := mul_le_mul_of_nonneg_right (profA_le_one ξ) (profB_nonneg ξ)
  simpa [profW] using this

/-- `w' = A'B + AB'`. -/
private theorem hasDerivAt_profW (ξ : ℝ) :
    HasDerivAt profW ((2 / d) * (profA ξ * profAbar ξ) * profB ξ +
      profA ξ * (-(2 / d) * (profB ξ * profBbar ξ))) ξ :=
  (hasDerivAt_profA ξ).mul (hasDerivAt_profB ξ)

/-- `|w'| ≤ (2/d) w`, from `w' = (2/d) A B (Ā - B̄)`. -/
private theorem abs_deriv_profW_le (ξ : ℝ) : |deriv profW ξ| ≤ 2 / d * profW ξ := by
  rw [(hasDerivAt_profW ξ).deriv]
  have hd := d_pos
  have heq : (2 / d) * (profA ξ * profAbar ξ) * profB ξ +
      profA ξ * (-(2 / d) * (profB ξ * profBbar ξ)) =
      (2 / d * profW ξ) * (profAbar ξ - profBbar ξ) := by
    simp only [profW]; ring
  rw [heq, abs_mul, abs_of_nonneg (by positivity [profW_nonneg ξ])]
  have h1 : |profAbar ξ - profBbar ξ| ≤ 1 := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [profAbar_nonneg ξ, profBbar_nonneg ξ, profAbar_le_one ξ,
      profBbar_le_one ξ]
  have h2 : 0 ≤ 2 / d * profW ξ := by have := profW_nonneg ξ; positivity
  nlinarith

/-! ### The cutoff -/

private theorem chi_differentiable {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) :
    Differentiable ℝ χ :=
  hχ.contDiff.differentiable (by simp)

private theorem chi_eq_zero_of_lt {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {ξ : ℝ}
    (hξ : ξ ∉ Icc ξL ξR) : χ ξ = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hξ (hχ.tsupport_subset h))

private theorem chi_ξL {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) : χ ξL = 0 := by
  have hc : IsClosed {x : ℝ | χ x = 0} :=
    isClosed_eq (chi_differentiable hχ).continuous continuous_const
  have hsub : Iio ξL ⊆ {x : ℝ | χ x = 0} := fun x hx =>
    chi_eq_zero_of_lt hχ (fun h => absurd h.1 (not_le.2 hx))
  have := hc.closure_subset_iff.2 hsub
  rw [closure_Iio] at this
  exact this (mem_Iic.2 le_rfl)

private theorem chi_ξR {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) : χ ξR = 0 := by
  have hc : IsClosed {x : ℝ | χ x = 0} :=
    isClosed_eq (chi_differentiable hχ).continuous continuous_const
  have hsub : Ioi ξR ⊆ {x : ℝ | χ x = 0} := fun x hx =>
    chi_eq_zero_of_lt hχ (fun h => absurd h.2 (not_le.2 hx))
  have := hc.closure_subset_iff.2 hsub
  rw [closure_Ioi] at this
  exact this (mem_Ici.2 le_rfl)

private theorem deriv_chi_nonneg {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {ξ : ℝ}
    (hξ : ξ ≤ ξa) : 0 ≤ deriv χ ξ := by
  have hd : HasDerivWithinAt χ (deriv χ ξ) (Iic ξa) ξ :=
    ((chi_differentiable hχ) ξ).hasDerivAt.hasDerivWithinAt
  refine hd.nonneg_of_monotoneOn ?_ hχ.monotoneOn
  rw [accPt_principal_iff_nhdsWithin]
  refine NeBot.mono (inferInstance : (𝓝[<] ξ).NeBot) (nhdsWithin_mono _ ?_)
  intro x hx
  exact ⟨le_trans (le_of_lt hx) hξ, ne_of_lt hx⟩

private theorem deriv_chi_nonpos {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {ξ : ℝ}
    (hξ : ξb ≤ ξ) : deriv χ ξ ≤ 0 := by
  have hd : HasDerivWithinAt χ (deriv χ ξ) (Ici ξb) ξ :=
    ((chi_differentiable hχ) ξ).hasDerivAt.hasDerivWithinAt
  refine hd.nonpos_of_antitoneOn ?_ hχ.antitoneOn
  rw [accPt_principal_iff_nhdsWithin]
  refine NeBot.mono (inferInstance : (𝓝[>] ξ).NeBot) (nhdsWithin_mono _ ?_)
  intro x hx
  exact ⟨le_trans hξ (le_of_lt hx), ne_of_gt hx⟩

/-! ### The profile `ϖ = χ w` -/

private theorem prof_eq_fun (χ : ℝ → ℝ) : prof χ = fun ξ => χ ξ * profW ξ :=
  funext (prof_eq_mul_profW χ)

private theorem deriv_prof_eq {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (ξ : ℝ) :
    deriv (prof χ) ξ = deriv χ ξ * profW ξ + χ ξ * deriv profW ξ := by
  rw [prof_eq_fun]
  exact (((chi_differentiable hχ) ξ).hasDerivAt.mul
    (hasDerivAt_profW ξ).differentiableAt.hasDerivAt).deriv

/-- `|ϖ'| ≤ |χ'| w + (2/d) w`. -/
private theorem abs_deriv_prof_le {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (ξ : ℝ) :
    |deriv (prof χ) ξ| ≤ |deriv χ ξ| * profW ξ + 2 / d * profW ξ := by
  rw [deriv_prof_eq hχ]
  have hχ0 := (hχ.mem_Icc ξ).1
  have hχ1 := (hχ.mem_Icc ξ).2
  have hw := profW_nonneg ξ
  have h1 : |deriv χ ξ * profW ξ| = |deriv χ ξ| * profW ξ := by
    rw [abs_mul, abs_of_nonneg hw]
  have h2 : |χ ξ * deriv profW ξ| ≤ 2 / d * profW ξ := by
    rw [abs_mul, abs_of_nonneg hχ0]
    have := abs_deriv_profW_le ξ
    have h3 : 0 ≤ |deriv profW ξ| := abs_nonneg _
    nlinarith
  calc |deriv χ ξ * profW ξ + χ ξ * deriv profW ξ|
      ≤ |deriv χ ξ * profW ξ| + |χ ξ * deriv profW ξ| := abs_add_le _ _
    _ ≤ |deriv χ ξ| * profW ξ + 2 / d * profW ξ := by rw [h1]; linarith

private theorem continuous_deriv_prof {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) :
    Continuous (deriv (prof χ)) :=
  (contDiff_prof hχ).continuous_deriv (by simp)

private theorem continuous_deriv_chi {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) :
    Continuous (deriv χ) :=
  hχ.contDiff.continuous_deriv (by simp)

/-- `ϖ'` is integrable (continuous with compact support). -/
theorem integrable_deriv_prof {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) :
    Integrable (fun ξ => |deriv (prof χ) ξ|) := by
  refine (continuous_deriv_prof hχ).abs.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (K := Icc ξL ξR) isCompact_Icc (fun x hx => ?_)
  simp [deriv_prof_eq_zero_of_not_mem hχ hx]

/-! ### The interval integrals -/

private theorem intervalTV_left_le {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) :
    ∫ ξ in ξL..ξa, |deriv (prof χ) ξ| ≤ 2 * Real.exp (2 * xa) := by
  have hd := d_pos
  have hgc : Continuous
      (fun ξ => profA ξa * deriv χ ξ + 2 / d * Real.exp (2 * ((ξ - a₀) / d))) :=
    (continuous_const.mul (continuous_deriv_chi hχ)).add
      (continuous_const.mul (Real.continuous_exp.comp (by fun_prop)))
  have hFd : ∀ ξ, HasDerivAt (fun ξ => profA ξa * χ ξ + Real.exp (2 * ((ξ - a₀) / d)))
      (profA ξa * deriv χ ξ + 2 / d * Real.exp (2 * ((ξ - a₀) / d))) ξ := by
    intro ξ
    have h1 := ((chi_differentiable hχ) ξ).hasDerivAt.const_mul (profA ξa)
    have h2 : HasDerivAt (fun ξ => Real.exp (2 * ((ξ - a₀) / d)))
        (Real.exp (2 * ((ξ - a₀) / d)) * (2 * (1 / d))) ξ :=
      ((((hasDerivAt_id ξ).sub_const a₀).div_const d).const_mul 2).exp
    exact (h1.add h2).congr_deriv (by ring)
  have hmono : ∫ ξ in ξL..ξa, |deriv (prof χ) ξ| ≤
      ∫ ξ in ξL..ξa, (profA ξa * deriv χ ξ + 2 / d * Real.exp (2 * ((ξ - a₀) / d))) := by
    refine intervalIntegral.integral_mono_on ξL_le_ξa
      ((continuous_deriv_prof hχ).abs.intervalIntegrable _ _) (hgc.intervalIntegrable _ _) ?_
    intro ξ hξ
    have hb := abs_deriv_prof_le hχ ξ
    have hχ' := deriv_chi_nonneg hχ hξ.2
    have hwA : profW ξ ≤ profA ξa :=
      (profW_le_profA ξ).trans (strictMono_profA.monotone hξ.2)
    have hwe : profW ξ ≤ Real.exp (2 * ((ξ - a₀) / d)) :=
      (profW_le_profA ξ).trans (H_le_exp _)
    rw [abs_of_nonneg hχ'] at hb
    have e1 : deriv χ ξ * profW ξ ≤ profA ξa * deriv χ ξ := by nlinarith
    have e2 : 2 / d * profW ξ ≤ 2 / d * Real.exp (2 * ((ξ - a₀) / d)) :=
      mul_le_mul_of_nonneg_left hwe (by positivity)
    linarith
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun ξ _ => hFd ξ)
    (hgc.intervalIntegrable _ _)] at hmono
  simp only [hχ.eq_one ξa ⟨le_rfl, by norm_num [ξa, ξb]⟩, chi_ξL hχ] at hmono
  have h1 : profA ξa ≤ Real.exp (2 * xa) := H_le_exp _
  have h2 : (ξa - a₀) / d = xa := rfl
  have h3 := Real.exp_pos (2 * ((ξL - a₀) / d))
  rw [h2] at hmono
  linarith

private theorem intervalTV_right_le {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) :
    ∫ ξ in ξb..ξR, |deriv (prof χ) ξ| ≤ 2 * Real.exp (2 * yb) := by
  have hd := d_pos
  have hgc : Continuous
      (fun ξ => profB ξb * (-deriv χ ξ) + 2 / d * Real.exp (2 * (-ξ / d))) :=
    (continuous_const.mul (continuous_deriv_chi hχ).neg).add
      (continuous_const.mul (Real.continuous_exp.comp (by fun_prop)))
  have hFd : ∀ ξ, HasDerivAt (fun ξ => -(profB ξb * χ ξ) - Real.exp (2 * (-ξ / d)))
      (profB ξb * (-deriv χ ξ) + 2 / d * Real.exp (2 * (-ξ / d))) ξ := by
    intro ξ
    have h1 := ((chi_differentiable hχ) ξ).hasDerivAt.const_mul (profB ξb)
    have h2 : HasDerivAt (fun ξ => Real.exp (2 * (-ξ / d)))
        (Real.exp (2 * (-ξ / d)) * (2 * (-1 / d))) ξ :=
      ((((hasDerivAt_id ξ).neg).div_const d).const_mul 2).exp
    exact (h1.neg.sub h2).congr_deriv (by ring)
  have hmono : ∫ ξ in ξb..ξR, |deriv (prof χ) ξ| ≤
      ∫ ξ in ξb..ξR, (profB ξb * (-deriv χ ξ) + 2 / d * Real.exp (2 * (-ξ / d))) := by
    refine intervalIntegral.integral_mono_on ξb_le_ξR
      ((continuous_deriv_prof hχ).abs.intervalIntegrable _ _) (hgc.intervalIntegrable _ _) ?_
    intro ξ hξ
    have hb := abs_deriv_prof_le hχ ξ
    have hχ' := deriv_chi_nonpos hχ hξ.1
    have hwB : profW ξ ≤ profB ξb :=
      (profW_le_profB ξ).trans (strictAnti_profB.antitone hξ.1)
    have hwe : profW ξ ≤ Real.exp (2 * (-ξ / d)) :=
      (profW_le_profB ξ).trans (H_le_exp _)
    rw [abs_of_nonpos hχ'] at hb
    have e1 : -deriv χ ξ * profW ξ ≤ profB ξb * (-deriv χ ξ) := by nlinarith
    have e2 : 2 / d * profW ξ ≤ 2 / d * Real.exp (2 * (-ξ / d)) :=
      mul_le_mul_of_nonneg_left hwe (by positivity)
    linarith
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun ξ _ => hFd ξ)
    (hgc.intervalIntegrable _ _)] at hmono
  simp only [hχ.eq_one ξb ⟨by norm_num [ξa, ξb], le_rfl⟩, chi_ξR hχ] at hmono
  have h1 : profB ξb ≤ Real.exp (2 * yb) := H_le_exp _
  have h2 : -ξb / d = yb := rfl
  have h3 := Real.exp_pos (2 * (-ξR / d))
  rw [h2] at hmono
  linarith

/-! ### Half lines to intervals -/

private theorem setIntegral_Iic_eq {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) :
    ∫ ξ in Iic ξa, |deriv (prof χ) ξ| = ∫ ξ in ξL..ξa, |deriv (prof χ) ξ| := by
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Iic
    (Icc_subset_Iic_self : Icc ξL ξa ⊆ Iic ξa), integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le ξL_le_ξa]
  intro x hx
  have hx' : x ∉ Icc ξL ξR := by
    intro h
    exact hx.2 ⟨h.1, hx.1⟩
  simp [deriv_prof_eq_zero_of_not_mem hχ hx']

private theorem setIntegral_Ici_eq {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) :
    ∫ ξ in Ici ξb, |deriv (prof χ) ξ| = ∫ ξ in ξb..ξR, |deriv (prof χ) ξ| := by
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ici
    (Icc_subset_Ici_self : Icc ξb ξR ⊆ Ici ξb), integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le ξb_le_ξR]
  intro x hx
  have hx' : x ∉ Icc ξL ξR := by
    intro h
    exact hx.2 ⟨hx.1, h.2⟩
  simp [deriv_prof_eq_zero_of_not_mem hχ hx']

/-! ### Lemma A.1(1) -/

/-- **Lemma A.1(1)**, left end region. -/
theorem endRegion_left_TV {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) :
    ∫ ξ in Iic ξa, |deriv (prof χ) ξ| ≤ 9 / 4 * Real.exp (2 * xa) := by
  rw [setIntegral_Iic_eq hχ]
  have := intervalTV_left_le hχ
  have := Real.exp_pos (2 * xa)
  linarith

/-- **Lemma A.1(1)**, right end region. -/
theorem endRegion_right_TV {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) :
    ∫ ξ in Ici ξb, |deriv (prof χ) ξ| ≤ 9 / 4 * Real.exp (2 * yb) := by
  rw [setIntegral_Ici_eq hχ]
  have := intervalTV_right_le hχ
  have := Real.exp_pos (2 * yb)
  linarith

/-- Lemma A.1(1) on the bounded end region `[ξL, ξa]`, in the form used by (2). -/
theorem endRegion_left_TV_interval {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) :
    ∫ ξ in ξL..ξa, |deriv (prof χ) ξ| ≤ 3 * Real.exp (-50) := by
  rw [← setIntegral_Iic_eq hχ]
  exact (endRegion_left_TV hχ).trans endRegion_const_lt.1.le

/-- Lemma A.1(1) on the bounded end region `[ξb, ξR]`, in the form used by (2). -/
theorem endRegion_right_TV_interval {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) :
    ∫ ξ in ξb..ξR, |deriv (prof χ) ξ| ≤ 3 * Real.exp (-50) := by
  rw [← setIntegral_Ici_eq hχ]
  exact (endRegion_right_TV hχ).trans endRegion_const_lt.2.le

/-! ### Lemma A.1(2) -/

/-- **Lemma A.1(2)**: the comparison estimate on the two end regions, for every solution pair
of the Evans system on `[ξL, ξR]`. -/
theorem endRegion_comparison {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    {z : ℂ} (hz : 0 < z.re) {G : ℝ} {ψ ψ' : ℝ → ℂ} (hsol : IsEvansSolution χ ℓ z G ψ ψ')
    {α β : ℝ} (hαβ : (α = ξL ∧ β = ξa) ∨ (α = ξb ∧ β = ξR)) :
    ∀ ξ ∈ Icc α β,
      wnorm ℓ (ψ ξ - cmpSol ℓ α (ψ α) (ψ' α) ξ) (ψ' ξ - cmpSol' ℓ α (ψ α) (ψ' α) ξ) ≤
        Real.exp (ℓ * (ξ - α)) * wnorm ℓ (ψ α) (ψ' α) * (Real.exp (epsEnd z) - 1) := by
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hαβ' : Icc α β ⊆ Icc ξL ξR ∧ α ≤ β ∧
      ∫ t in α..β, |deriv (prof χ) t| ≤ 3 * Real.exp (-50) := by
    rcases hαβ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨Icc_subset_Icc le_rfl ξa_le_ξR, ξL_le_ξa, endRegion_left_TV_interval hχ⟩
    · exact ⟨Icc_subset_Icc ξL_le_ξb le_rfl, ξb_le_ξR, endRegion_right_TV_interval hχ⟩
  obtain ⟨hsub, hle, hTV⟩ := hαβ'
  have hδc : Continuous (evansDelta χ ℓ z G) := (contDiff_evansDelta hχ ℓ hz G).continuous
  have hpc : Continuous (fun t => |deriv (prof χ) t|) := (continuous_deriv_prof hχ).abs
  refine comparison_estimate (ℓ := (ℓ : ℝ)) hℓ0 (δ := evansDelta χ ℓ z G) ?_ ?_
    hδc.continuousOn ?_
  · intro ξ hξ
    exact (hsol.hasDerivWithinAt ξ (hsub hξ)).mono hsub
  · intro ξ hξ
    have h := (hsol.hasDerivWithinAt' ξ (hsub hξ)).mono hsub
    rw [riccatiCoeff_eq_add_evansDelta] at h
    exact_mod_cast h
  · calc ∫ t in α..β, ‖evansDelta χ ℓ z G t‖ / ℓ
        ≤ ∫ t in α..β, |deriv (prof χ) t| / z.re := by
          refine intervalIntegral.integral_mono_on hle ?_ ?_
            (fun t _ => norm_evansDelta_div_le ℓ hz G t)
          · exact (hδc.norm.div_const _).intervalIntegrable _ _
          · exact (hpc.div_const _).intervalIntegrable _ _
      _ = (∫ t in α..β, |deriv (prof χ) t|) / z.re := intervalIntegral.integral_div _ _
      _ ≤ 3 * Real.exp (-50) / z.re := div_le_div_of_nonneg_right hTV hz.le
      _ = epsEnd z := rfl

end AppA

end NonUniqueEuler
