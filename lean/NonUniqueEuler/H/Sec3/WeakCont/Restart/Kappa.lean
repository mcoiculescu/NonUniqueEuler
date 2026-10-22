import NonUniqueEuler.Defs.Sec3.Transport
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Helpers for `P/Sec3/WeakCont/Restart.lean`: the shifted steps `ϰ_h(t) = ϰ((t - t₀)/h)`

Manuscript: proof of `lem:weak-cont`(c) (`03_compactness.tex:209-225`). For `h > 0` the shifted
step `ϰ_h(t) = ϰ((t - t₀)/h)` is smooth, vanishes for `t ≤ t₀`, equals `1` for `t ≥ t₀ + h`, its
derivative is continuous, nonnegative, vanishes off `[t₀, t₀ + h]` and has integral `1` over
`(0, T)` when `0 ≤ t₀` and `t₀ + h ≤ T`. For `φ ∈ 𝒟_T` the product `ϰ_h φ` is in `𝒟_T`, and
`transportIntegrand u w (ϰ_h φ) = ϰ_h' u φ + ϰ_h · transportIntegrand u w φ`.

All lemmas are fully proved.
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler.Weak.WeakCont.Restart

variable {t₀ h : ℝ}

theorem contDiff_kappaShift (t₀ h : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => kappa ((t - t₀) / h)) :=
  contDiff_kappa.comp ((contDiff_id.sub contDiff_const).div_const h)

theorem differentiable_kappaShift (t₀ h : ℝ) :
    Differentiable ℝ (fun t : ℝ => kappa ((t - t₀) / h)) :=
  (contDiff_kappaShift t₀ h).differentiable (by simp)

theorem continuous_kappaShift (t₀ h : ℝ) : Continuous (fun t : ℝ => kappa ((t - t₀) / h)) :=
  (differentiable_kappaShift t₀ h).continuous

theorem continuous_deriv_kappaShift (t₀ h : ℝ) :
    Continuous (deriv (fun t : ℝ => kappa ((t - t₀) / h))) :=
  (contDiff_kappaShift t₀ h).continuous_deriv (by exact_mod_cast le_top)

theorem kappaShift_eq_zero (hh : 0 < h) {t : ℝ} (ht : t ≤ t₀) : kappa ((t - t₀) / h) = 0 :=
  kappa_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hh.le)

theorem kappaShift_eq_one (hh : 0 < h) {t : ℝ} (ht : t₀ + h ≤ t) : kappa ((t - t₀) / h) = 1 :=
  kappa_of_one_le (by rw [le_div_iff₀ hh]; linarith)

theorem abs_kappaShift_le_one (t₀ h t : ℝ) : |kappa ((t - t₀) / h)| ≤ 1 := by
  rw [abs_of_nonneg (kappa_nonneg _)]
  exact kappa_le_one _

theorem monotone_kappaShift (hh : 0 < h) : Monotone (fun t : ℝ => kappa ((t - t₀) / h)) :=
  fun a b hab => monotone_kappa (div_le_div_of_nonneg_right (by linarith) hh.le)

theorem deriv_kappaShift_nonneg (hh : 0 < h) (t : ℝ) :
    0 ≤ deriv (fun t : ℝ => kappa ((t - t₀) / h)) t :=
  (monotone_kappaShift hh).deriv_nonneg

theorem deriv_kappaShift_eq_zero_of_lt (hh : 0 < h) {t : ℝ} (ht : t < t₀) :
    deriv (fun t : ℝ => kappa ((t - t₀) / h)) t = 0 := by
  have hev : (fun t : ℝ => kappa ((t - t₀) / h)) =ᶠ[nhds t] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact kappaShift_eq_zero hh (le_of_lt hs)
  rw [hev.deriv_eq, deriv_const]

theorem deriv_kappaShift_eq_zero_of_gt (hh : 0 < h) {t : ℝ} (ht : t₀ + h < t) :
    deriv (fun t : ℝ => kappa ((t - t₀) / h)) t = 0 := by
  have hev : (fun t : ℝ => kappa ((t - t₀) / h)) =ᶠ[nhds t] fun _ => (1 : ℝ) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact kappaShift_eq_one hh (le_of_lt hs)
  rw [hev.deriv_eq, deriv_const]

/-- `∫_0^T ϰ_h' = ϰ_h(T) - ϰ_h(0) = 1` for `0 ≤ t₀` and `t₀ + h ≤ T`. -/
theorem integral_deriv_kappaShift (hh : 0 < h) {T : ℝ} (ht₀ : 0 ≤ t₀) (hT : t₀ + h ≤ T) :
    ∫ t in Ioo 0 T, deriv (fun t : ℝ => kappa ((t - t₀) / h)) t = 1 := by
  have h0T : (0 : ℝ) ≤ T := by linarith
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le h0T,
    intervalIntegral.integral_deriv_eq_sub (fun x _ => differentiable_kappaShift t₀ h x)
      ((continuous_deriv_kappaShift t₀ h).intervalIntegrable 0 T),
    kappaShift_eq_one hh hT, kappaShift_eq_zero hh ht₀]
  norm_num

/-- `ϰ_h φ ∈ 𝒟_T` for `φ ∈ 𝒟_T`. -/
theorem isTestFunction_kappaShift_mul {T : ℝ} {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ)
    (t₀ h : ℝ) : IsTestFunction T (fun p : ℝ × ℂ => kappa ((p.1 - t₀) / h) * φ p) where
  contDiff := ((contDiff_kappaShift t₀ h).comp contDiff_fst).mul hφ.contDiff
  hasCompactSupport :=
    hφ.hasCompactSupport.mul_left (f := fun p : ℝ × ℂ => kappa ((p.1 - t₀) / h))
  support_lt p hp := hφ.support_lt p (tsupport_mul_subset_right hp)

/-- `transportIntegrand u w (ϰ_h φ) = ϰ_h' u φ + ϰ_h · transportIntegrand u w φ`. -/
theorem transportIntegrand_kappaShift_mul (u : ℝ → ℂ → ℝ) (w : ℝ → ℂ → ℂ) {φ : ℝ × ℂ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (t₀ h t : ℝ) (x : ℂ) :
    transportIntegrand u w (fun p : ℝ × ℂ => kappa ((p.1 - t₀) / h) * φ p) (t, x) =
      deriv (fun t : ℝ => kappa ((t - t₀) / h)) t * (u t x * φ (t, x)) +
        kappa ((t - t₀) / h) * transportIntegrand u w φ (t, x) := by
  have hφd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hdt : DifferentiableAt ℝ (fun s : ℝ => φ (s, x)) t :=
    (hφd (t, x)).comp t (differentiableAt_id.prodMk (differentiableAt_const x))
  have hdx : DifferentiableAt ℝ (fun y : ℂ => φ (t, y)) x :=
    (hφd (t, x)).comp x ((differentiableAt_const t).prodMk differentiableAt_id)
  have htime : timeDeriv (fun p : ℝ × ℂ => kappa ((p.1 - t₀) / h) * φ p) t x =
      deriv (fun t : ℝ => kappa ((t - t₀) / h)) t * φ (t, x) +
        kappa ((t - t₀) / h) * timeDeriv φ t x := by
    simp only [timeDeriv]
    exact deriv_mul (differentiable_kappaShift t₀ h t) hdt
  have hspace : ∀ v : ℂ, spaceDeriv (fun p : ℝ × ℂ => kappa ((p.1 - t₀) / h) * φ p) t x v =
      kappa ((t - t₀) / h) * spaceDeriv φ t x v := by
    intro v
    simp only [spaceDeriv]
    rw [fderiv_const_mul hdx]
    rfl
  simp only [transportIntegrand]
  rw [htime, hspace]
  ring

end NonUniqueEuler.Weak.WeakCont.Restart
