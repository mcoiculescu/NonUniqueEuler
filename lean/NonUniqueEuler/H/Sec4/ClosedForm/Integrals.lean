import NonUniqueEuler.H.Sec4.ClosedForm.SechIntegral
import NonUniqueEuler.H.Sec4.ClosedForm.Sign
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Integral

/-!
# Helper for `lem:closed-form`: the integrals of the bounding functions

Manuscript `04_ring.tex:805-827`.
* `integral_kA`: `∫_ℝ e^{2ℓ(ξ-ξc)} (2/d) A Ā dξ = e^{ℓa₀} Θ_ℓ` (substitution `ξ = a₀ + dx`);
* `integral_kB`: `∫_ℝ e^{-2ℓ(ξ-ξc)} (2/d) B B̄ dξ = e^{ℓa₀} Θ_ℓ` (substitution `ξ = -dx`);
  both from the `sech²` integral (`integral_exp_mul_dH`, with `β = 2ℓd ∈ (0, 2)`), and the
  integrability of the two functions (their integrals are nonzero);
* `integral_deriv_chi_left`, `integral_deriv_chi_right`: `∫_{ξL-1}^{ξc} χ' = 1` and
  `∫_{ξc}^{ξR+1} (-χ') = 1` (`χ(ξc) = 1`, `χ = 0` off `[ξL, ξR]`).
-/

noncomputable section

open MeasureTheory Set Real

namespace NonUniqueEuler

namespace ClosedFormAux

open RingData AppA

/-- `Θ_ℓ > 0` for `1 ≤ ℓ`, `ℓd < 1`. -/
theorem Θ_pos {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hd : (ℓ : ℝ) * d < 1) : 0 < Θ ℓ := by
  have hd0 := d_pos
  have hl : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have h1 : 0 < π * ℓ * d := by positivity
  have h2 : π * ℓ * d < π := by
    have := Real.pi_pos
    calc π * ℓ * d = π * (ℓ * d) := by ring
      _ < π * 1 := by gcongr
      _ = π := mul_one _
  exact div_pos h1 (Real.sin_pos_of_pos_of_lt_pi h1 h2)

/-- The rescaled kernel `G(x) = e^{ℓa₀} d⁻¹ e^{2ℓdx} 2H(x)H(-x)`. -/
def kerG (ℓ : ℕ) (x : ℝ) : ℝ :=
  Real.exp (ℓ * a₀) * (1 / d) * (Real.exp ((2 * ℓ * d) * x) * (2 * (H x * H (-x))))

theorem integral_kerG {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hd : (ℓ : ℝ) * d < 1) :
    |d| • ∫ x, kerG ℓ x = Real.exp (ℓ * a₀) * Θ ℓ := by
  have hd0 := d_pos
  have hl : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hβ0 : 0 < 2 * ℓ * d := by positivity
  have hβ2 : 2 * ℓ * d < 2 := by linarith
  simp only [kerG]
  rw [integral_const_mul, integral_exp_mul_dH hβ0 hβ2, smul_eq_mul, abs_of_pos hd0,
    show π * (2 * ℓ * d / 2) = π * ℓ * d by ring, Θ]
  field_simp

/-- `kA(ξ) = e^{2ℓ(ξ-ξc)} (2/d) A(ξ) Ā(ξ)`. -/
def kA (ℓ : ℕ) (ξ : ℝ) : ℝ := Real.exp (2 * ℓ * (ξ - ξc)) * ((2 / d) * (profA ξ * profAbar ξ))

/-- `kB(ξ) = e^{-2ℓ(ξ-ξc)} (2/d) B(ξ) B̄(ξ)`. -/
def kB (ℓ : ℕ) (ξ : ℝ) : ℝ :=
  Real.exp (-(2 * ℓ * (ξ - ξc))) * ((2 / d) * (profB ξ * profBbar ξ))

theorem kA_nonneg (ℓ : ℕ) (ξ : ℝ) : 0 ≤ kA ℓ ξ := by
  have := d_pos
  have := profA_pos ξ
  have := profAbar_pos ξ
  simp only [kA]
  positivity

theorem kB_nonneg (ℓ : ℕ) (ξ : ℝ) : 0 ≤ kB ℓ ξ := by
  have := d_pos
  have := profB_pos ξ
  have := profBbar_pos ξ
  simp only [kB]
  positivity

theorem kA_eq (ℓ : ℕ) (ξ : ℝ) : kA ℓ ξ = kerG ℓ ((ξ - a₀) / d) := by
  have hd0 := d_pos.ne'
  simp only [kA, kerG, profA, profAbar, ξc]
  rw [show (a₀ - ξ) / d = -((ξ - a₀) / d) by ring]
  have : Real.exp (2 * ℓ * (ξ - a₀ / 2)) =
      Real.exp (ℓ * a₀) * Real.exp (2 * ℓ * d * ((ξ - a₀) / d)) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [this]
  field_simp

theorem kB_eq (ℓ : ℕ) (ξ : ℝ) : kB ℓ ξ = kerG ℓ ((-ξ) / d) := by
  have hd0 := d_pos.ne'
  simp only [kB, kerG, profB, profBbar, ξc]
  rw [show -((-ξ) / d) = ξ / d by ring, show (-ξ) / d = -ξ / d by ring]
  have : Real.exp (-(2 * ℓ * (ξ - a₀ / 2))) =
      Real.exp (ℓ * a₀) * Real.exp (2 * ℓ * d * (-ξ / d)) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [this]
  field_simp

/-- `∫_ℝ e^{2ℓ(ξ-ξc)} (2/d) A Ā dξ = e^{ℓa₀} Θ_ℓ` (`04_ring.tex:810-814`). -/
theorem integral_kA {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hd : (ℓ : ℝ) * d < 1) :
    ∫ ξ, kA ℓ ξ = Real.exp (ℓ * a₀) * Θ ℓ := by
  calc ∫ ξ, kA ℓ ξ = ∫ ξ, (fun y => kerG ℓ (y / d)) (ξ - a₀) := by
        congr 1
        funext ξ
        exact kA_eq ℓ ξ
    _ = ∫ y, kerG ℓ (y / d) := integral_sub_right_eq_self (fun y => kerG ℓ (y / d)) a₀
    _ = |d| • ∫ x, kerG ℓ x := Measure.integral_comp_div (kerG ℓ) d
    _ = Real.exp (ℓ * a₀) * Θ ℓ := integral_kerG hℓ hd

/-- `∫_ℝ e^{-2ℓ(ξ-ξc)} (2/d) B B̄ dξ = e^{ℓa₀} Θ_ℓ` (`04_ring.tex:823-827`). -/
theorem integral_kB {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hd : (ℓ : ℝ) * d < 1) :
    ∫ ξ, kB ℓ ξ = Real.exp (ℓ * a₀) * Θ ℓ := by
  calc ∫ ξ, kB ℓ ξ = ∫ ξ, (fun y => kerG ℓ (y / d)) (-ξ) := by
        congr 1
        funext ξ
        exact kB_eq ℓ ξ
    _ = ∫ y, kerG ℓ (y / d) := integral_neg_eq_self (fun y => kerG ℓ (y / d)) volume
    _ = |d| • ∫ x, kerG ℓ x := Measure.integral_comp_div (kerG ℓ) d
    _ = Real.exp (ℓ * a₀) * Θ ℓ := integral_kerG hℓ hd

theorem integrable_kA {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hd : (ℓ : ℝ) * d < 1) : Integrable (kA ℓ) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_kA hℓ hd]
  exact (mul_pos (Real.exp_pos _) (Θ_pos hℓ hd)).ne'

theorem integrable_kB {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hd : (ℓ : ℝ) * d < 1) : Integrable (kB ℓ) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_kB hℓ hd]
  exact (mul_pos (Real.exp_pos _) (Θ_pos hℓ hd)).ne'

/-! ### The cutoff integrals -/

variable {χ : ℝ → ℝ}

theorem chi_eq_zero_of_not_mem (hχ : IsAdmissibleCutoff χ) {ξ : ℝ} (h : ξ ∉ Icc ξL ξR) :
    χ ξ = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h' => h (hχ.tsupport_subset h'))

theorem chi_c (hχ : IsAdmissibleCutoff χ) : χ ξc = 1 :=
  hχ.eq_one ξc ⟨ξa_lt_ξc.le, ξc_lt_ξb.le⟩

theorem continuous_deriv_chi (hχ : IsAdmissibleCutoff χ) : Continuous (deriv χ) :=
  hχ.contDiff.continuous_deriv (by simp)

/-- `∫_{[ξL-1, ξc]} χ' = χ(ξc) - χ(ξL-1) = 1`. -/
theorem integral_deriv_chi_left (hχ : IsAdmissibleCutoff χ) :
    ∫ ξ in Icc (ξL - 1) ξc, deriv χ ξ = 1 := by
  have hle : ξL - 1 ≤ ξc := by
    have := ξL_lt_ξc
    simp only [ξc]
    linarith
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle,
    intervalIntegral.integral_deriv_eq_sub
      (fun x _ => (hχ.contDiff.differentiable (by simp)) x)
      ((continuous_deriv_chi hχ).intervalIntegrable _ _),
    chi_c hχ, chi_eq_zero_of_not_mem hχ (fun h => by linarith [h.1])]
  ring

/-- `∫_{[ξc, ξR+1]} (-χ') = χ(ξc) - χ(ξR+1) = 1`. -/
theorem integral_deriv_chi_right (hχ : IsAdmissibleCutoff χ) :
    ∫ ξ in Icc ξc (ξR + 1), -deriv χ ξ = 1 := by
  have hle : ξc ≤ ξR + 1 := by
    have := ξc_lt_ξR
    simp only [ξc]
    linarith
  rw [integral_neg, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle,
    intervalIntegral.integral_deriv_eq_sub
      (fun x _ => (hχ.contDiff.differentiable (by simp)) x)
      ((continuous_deriv_chi hχ).intervalIntegrable _ _),
    chi_c hχ, chi_eq_zero_of_not_mem hχ (fun h => by linarith [h.2])]
  ring

end ClosedFormAux

end NonUniqueEuler
