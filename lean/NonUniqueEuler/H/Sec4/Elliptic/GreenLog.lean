import NonUniqueEuler.Defs.Sec4.Setting
import NonUniqueEuler.Defs.Infra.SobolevOneD
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Helpers for `P/Sec4/Elliptic`: the Green operator in the log variable

Manuscript `04_ring.tex:875-878`: with `x = log r`, `(min/max)^{|ℓ|} = e^{-|ℓ||x-y|}` and
`ρ dρ = e^{2y} dy`, so `𝒢_ℓ g (e^x) = yukawa ℓ (e^{2·} g(e^·)) (x)`.

* `integral_Ioi_eq_exp`: `∫_{(0,∞)} G = ∫_ℝ e^x G(e^x) dx` (any `G`; the same substitution as
  `LogVarH.integral_Ioi_eq` of `H/Infra/SobolevOneD/LogVariable/Change.lean`);
* `green_eq_yukawa_log`: `𝒢_ℓ g (r) = yukawa ℓ f (log r)` for `r > 0`, `f = e^{2x} g(e^x)`;
* `green_eq_of_lt`, `green_eq_of_gt`: for `g` vanishing outside `[ρ₋, ρ₊]`,
  `𝒢_ℓ g = A rⁿ` on `(0, ρ₋)` and `𝒢_ℓ g = B r^{-n}` on `(ρ₊, ∞)`, `n = |ℓ|`;
* `ae_comp_exp`: an a.e. property on `(0, ∞)` holds a.e. along `x ↦ e^x`;
* `iteratedDeriv_expTwo`: `∂^i e^{2x} = 2^i e^{2x}`.

All proofs are complete.
-/

noncomputable section

open MeasureTheory Set Filter

namespace NonUniqueEuler.Sob.EllipticH

/-- `∫_{(0,∞)} G = ∫_ℝ e^x G(e^x) dx`, for any `G` (substitution `r = e^x`). -/
theorem integral_Ioi_eq_exp (G : ℝ → ℂ) :
    ∫ r in Ioi 0, G r = ∫ x, Real.exp x • G (Real.exp x) := by
  rw [← Real.range_exp, ← image_univ,
    integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn G,
    Measure.restrict_univ]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [abs_of_pos (Real.exp_pos x)]

/-- `(min(e^x, e^y)/max(e^x, e^y))^n = e^{-n|x-y|}`. -/
theorem kernel_exp (n : ℕ) (x y : ℝ) :
    (min (Real.exp x) (Real.exp y) / max (Real.exp x) (Real.exp y)) ^ n =
      Real.exp (-(n : ℝ) * |x - y|) := by
  rcases le_total x y with h | h
  · rw [min_eq_left (Real.exp_le_exp.2 h), max_eq_right (Real.exp_le_exp.2 h), ← Real.exp_sub,
      ← Real.exp_nat_mul, abs_of_nonpos (by linarith)]
    congr 1
    ring
  · rw [min_eq_right (Real.exp_le_exp.2 h), max_eq_left (Real.exp_le_exp.2 h), ← Real.exp_sub,
      ← Real.exp_nat_mul, abs_of_nonneg (by linarith)]
    congr 1
    ring

/-- The kernel of `𝒢_ℓ` at `r > 0` in the log variable. -/
theorem kernel_log (ℓ : ℤ) {r : ℝ} (hr : 0 < r) (y : ℝ) :
    (min r (Real.exp y) / max r (Real.exp y)) ^ ℓ.natAbs =
      Real.exp (-|(ℓ : ℝ)| * |Real.log r - y|) := by
  have h := kernel_exp ℓ.natAbs (Real.log r) y
  rw [Real.exp_log hr] at h
  rw [h]
  congr 3
  rw [Nat.cast_natAbs, Int.cast_abs]

/-- `𝒢_ℓ g (r) = yukawa ℓ (e^{2·} g(e^·)) (log r)` for `r > 0` (`04_ring.tex:875-878`). -/
theorem green_eq_yukawa_log (ℓ : ℤ) (g : ℝ → ℂ) {r : ℝ} (hr : 0 < r) :
    SectorSetting.green ℓ g r =
      yukawa ℓ (fun x => ((Real.exp (2 * x) : ℝ) : ℂ) * g (Real.exp x)) (Real.log r) := by
  unfold SectorSetting.green yukawa
  congr 1
  rw [integral_Ioi_eq_exp]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only
  rw [kernel_log ℓ hr y, Complex.real_smul,
    show 2 * y = y + y by ring, Real.exp_add]
  push_cast
  ring

/-- For `g` vanishing a.e. outside `[ρ₋, ρ₊]`: `𝒢_ℓ g (r) = A rⁿ` for `0 < r < ρ₋`. -/
theorem green_eq_of_lt {ℓ : ℤ} {g : ℝ → ℂ} {ρm ρp : ℝ}
    (hsupp : ∀ᵐ ρ ∂(volume.restrict (Ioi (0 : ℝ))), ρ ∉ Icc ρm ρp → g ρ = 0) {r : ℝ}
    (hr : r < ρm) :
    SectorSetting.green ℓ g r =
      (-((((2 * |(ℓ : ℝ)|)⁻¹ : ℝ)) : ℂ) *
        ∫ ρ in Ioi (0 : ℝ), ((ρ : ℂ) ^ ℓ.natAbs)⁻¹ * g ρ * (ρ : ℂ)) * (r : ℂ) ^ ℓ.natAbs := by
  unfold SectorSetting.green
  rw [mul_assoc]
  congr 1
  rw [← integral_mul_const]
  refine integral_congr_ae ?_
  filter_upwards [hsupp] with ρ hρ
  by_cases hI : ρ ∈ Icc ρm ρp
  · have hrρ : r < ρ := hr.trans_le hI.1
    rw [min_eq_left hrρ.le, max_eq_right hrρ.le]
    push_cast
    rw [div_pow]
    ring
  · simp [hρ hI]

/-- For `g` vanishing a.e. outside `[ρ₋, ρ₊]`: `𝒢_ℓ g (r) = B r^{-n}` for `r > ρ₊`. -/
theorem green_eq_of_gt {ℓ : ℤ} {g : ℝ → ℂ} {ρm ρp : ℝ}
    (hsupp : ∀ᵐ ρ ∂(volume.restrict (Ioi (0 : ℝ))), ρ ∉ Icc ρm ρp → g ρ = 0) {r : ℝ}
    (hr : ρp < r) :
    SectorSetting.green ℓ g r =
      (-((((2 * |(ℓ : ℝ)|)⁻¹ : ℝ)) : ℂ) *
        ∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ ℓ.natAbs * g ρ * (ρ : ℂ)) *
          (r : ℂ) ^ (-(ℓ.natAbs : ℤ)) := by
  unfold SectorSetting.green
  rw [mul_assoc]
  congr 1
  rw [← integral_mul_const]
  refine integral_congr_ae ?_
  filter_upwards [hsupp] with ρ hρ
  by_cases hI : ρ ∈ Icc ρm ρp
  · have hρr : ρ < r := hI.2.trans_lt hr
    rw [min_eq_right hρr.le, max_eq_left hρr.le, zpow_neg, zpow_natCast]
    push_cast
    ring
  · simp [hρ hI]

/-- An a.e. property on `(0, ∞)` holds a.e. along `x ↦ e^x`. -/
theorem ae_comp_exp {P : ℝ → Prop} (h : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), P r) :
    ∀ᵐ x : ℝ, P (Real.exp x) := by
  obtain ⟨T, hNT, hTm, hT0⟩ := exists_measurable_superset_of_null (ae_iff.1 h)
  have hchange := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
    (T.indicator 1)
  rw [image_univ, Real.range_exp, Measure.restrict_univ, lintegral_indicator_one hTm, hT0]
    at hchange
  have hmeas : Measurable fun x : ℝ =>
      ENNReal.ofReal |Real.exp x| * T.indicator (1 : ℝ → ENNReal) (Real.exp x) :=
    (ENNReal.measurable_ofReal.comp Real.continuous_exp.abs.measurable).mul
      ((measurable_one.indicator hTm).comp Real.measurable_exp)
  have hz := (lintegral_eq_zero_iff hmeas).1 hchange.symm
  filter_upwards [hz] with x hx
  by_contra hPx
  have hxT : Real.exp x ∈ T := hNT hPx
  simp only [Pi.zero_apply, indicator_of_mem hxT, Pi.one_apply, mul_one,
    ENNReal.ofReal_eq_zero] at hx
  exact absurd hx (not_le.2 (abs_pos.2 (Real.exp_pos x).ne'))

/-- The weight `e^{2x}`, complex valued. -/
def expTwo (x : ℝ) : ℂ := ((Real.exp (2 * x) : ℝ) : ℂ)

theorem hasDerivAt_expTwo (x : ℝ) : HasDerivAt expTwo (2 * expTwo x) x := by
  have h := ((Real.hasDerivAt_exp (2 * x)).comp x ((hasDerivAt_id x).const_mul 2)).ofReal_comp
  refine h.congr_deriv ?_
  simp only [expTwo]
  push_cast
  ring

theorem contDiff_expTwo {n : WithTop ℕ∞} : ContDiff ℝ n expTwo :=
  Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))

/-- `∂^i e^{2x} = 2^i e^{2x}`. -/
theorem iteratedDeriv_expTwo (i : ℕ) :
    iteratedDeriv i expTwo = fun x => (2 : ℂ) ^ i * expTwo x := by
  induction i with
  | zero => funext x; simp
  | succ i ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [((hasDerivAt_expTwo x).const_mul ((2 : ℂ) ^ i)).deriv, pow_succ]
    ring

/-- `|∂^i e^{2x}| ≤ 2^k ρ₊²` for `i ≤ k` and `x ≤ log ρ₊`. -/
theorem norm_iteratedDeriv_expTwo_le {k i : ℕ} (hi : i ≤ k) {ρp x : ℝ} (hρp : 0 < ρp)
    (hx : x ≤ Real.log ρp) : ‖iteratedDeriv i expTwo x‖ ≤ 2 ^ k * ρp ^ 2 := by
  rw [iteratedDeriv_expTwo, norm_mul, norm_pow]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  have he : ‖expTwo x‖ = Real.exp x ^ 2 := by
    simp only [expTwo, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h2, he]
  have hex : Real.exp x ≤ ρp := by
    calc Real.exp x ≤ Real.exp (Real.log ρp) := Real.exp_le_exp.2 hx
      _ = ρp := Real.exp_log hρp
  gcongr
  norm_num

end NonUniqueEuler.Sob.EllipticH
