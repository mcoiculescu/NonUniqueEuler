import NonUniqueEuler.H.Sec4.Adjoint.Basic
import NonUniqueEuler.H.Sec4.Adjoint.Green
import NonUniqueEuler.I.Sec4.Sector
import NonUniqueEuler.I.Infra.Polar.Power
import NonUniqueEuler.I.Infra.Polar.Radial
import NonUniqueEuler.Defs.Sec2.Multipole
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Helper for `lem:adjoint`(3): the stream function of `g_* e^{iℓθ}` off `supp ω̄'`

Helper of `P/Sec4/Adjoint.lean` (`04_ring.tex:620-629`).
* The sector function `f = g_*e^{iℓθ}` is continuous with compact support, so its log potential
  `(2π)⁻¹ log|·| * f` is continuous (`continuous_logPotential`, Mathlib's convolution with the
  locally integrable `log|·|`).
* By `lem:sector`(1) (`green_eq_logPotential`) the log potential is a.e. `(𝒢_ℓ g_*)e^{iℓθ}`; both
  are continuous on `ℂ \ {0}`, so they agree there; at `0` by continuity.
* `𝒢_ℓ g_*` off `[r₁,r₂]` (`green_eq_exterior`, `green_eq_interior`), evaluated at `r₁`, `r₂`
  with `𝒢_ℓ g_* = ψ_*(log r)`, gives `pin_*`, `pout_*`.
* `pout_*`, `pin_*` are the multipole coefficients of `f` (polar coordinates,
  `Polar.integral_comp_norm`).
-/

noncomputable section

open MeasureTheory Set Filter Topology ComplexConjugate Metric
open scoped ContDiff

namespace NonUniqueEuler.AdjointAux

open SectorSetting

theorem continuousOn_angPhase (ℓ : ℤ) : ContinuousOn (Ang.angPhase ℓ) {0}ᶜ := by
  intro x hx
  have hx0 : x ≠ 0 := hx
  have hn : ((‖x‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hx0
  have h1 : ContinuousAt (fun y : ℂ => y / ((‖y‖ : ℝ) : ℂ)) x :=
    continuousAt_id.div (Complex.continuous_ofReal.comp continuous_norm).continuousAt hn
  have h2 : x / ((‖x‖ : ℝ) : ℂ) ≠ 0 := div_ne_zero hx0 hn
  exact (h1.zpow₀ ℓ (Or.inl h2)).continuousWithinAt

theorem continuousOn_ofProfile {h : ℝ → ℂ} (hc : ContinuousOn h (Ioi 0)) (ℓ : ℤ) :
    ContinuousOn (Ang.ofProfile ℓ h) {0}ᶜ := by
  have h1 : ContinuousOn (fun y : ℂ => h ‖y‖) {0}ᶜ :=
    hc.comp continuous_norm.continuousOn fun y hy => norm_pos_iff.2 hy
  exact h1.mul (continuousOn_angPhase ℓ)

theorem continuous_ofProfile_of_supp {h : ℝ → ℂ} {a b : ℝ} (ha : 0 < a)
    (hc : ContinuousOn h (Ioi 0)) (hz : ∀ r : ℝ, 0 < r → r ∉ Icc a b → h r = 0) (h0 : h 0 = 0)
    (ℓ : ℤ) : Continuous (Ang.ofProfile ℓ h) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : ‖x‖ < a
  · have hev : Ang.ofProfile ℓ h =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
      have hy' : h ‖y‖ = 0 := by
        rcases eq_or_lt_of_le (norm_nonneg y) with h' | h'
        · rw [← h', h0]
        · exact hz _ h' fun hm => absurd hm.1 (not_le.2 hy)
      simp [Ang.ofProfile, hy']
    exact continuousAt_const.congr hev.symm
  · have hx0 : x ≠ 0 := by
      intro h'
      rw [h', norm_zero] at hx
      exact hx ha
    exact (continuousOn_ofProfile hc ℓ).continuousAt (isOpen_compl_singleton.mem_nhds hx0)

theorem hasCompactSupport_ofProfile_of_supp {h : ℝ → ℂ} {a b : ℝ} (hb : 0 ≤ b)
    (hz : ∀ r : ℝ, 0 < r → r ∉ Icc a b → h r = 0) (ℓ : ℤ) :
    HasCompactSupport (Ang.ofProfile ℓ h) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) b) fun x hx => ?_
  have hxb : b < ‖x‖ := by
    simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hx
  have h1 : h ‖x‖ = 0 := hz _ (lt_of_le_of_lt hb hxb) fun hm => absurd hm.2 (not_le.2 hxb)
  simp [Ang.ofProfile, h1]

/-- The log potential of a continuous compactly supported function is continuous. -/
theorem continuous_logPotential {f : ℂ → ℂ} (hf : Continuous f) (hcs : HasCompactSupport f) :
    Continuous (Multipole.logPotential f) := by
  let L : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℝ
  have hconv : Continuous (convolution (fun t : ℂ => Real.log ‖t‖) f L volume) :=
    hcs.continuous_convolution_right L Polar.locallyIntegrable_log_norm hf
  have heq : Multipole.logPotential f =
      fun x => (2 * Real.pi : ℂ)⁻¹ * convolution (fun t : ℂ => Real.log ‖t‖) f L volume x := by
    funext x
    rw [Multipole.logPotential, convolution_eq_swap]
    congr 2
  rw [heq]
  exact continuous_const.mul hconv

theorem angPhase_zero (ℓ : ℕ) (hℓ : 1 ≤ ℓ) : Ang.angPhase ℓ 0 = 0 := by
  simp only [Ang.angPhase, zero_div, zpow_natCast]
  exact zero_pow (by omega)

/-- `pout_* = pout_ℓ[g_* e^{iℓθ}]` (polar coordinates). -/
theorem poutStar_eq_pout (S : SectorSetting) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (z : ℂ) (G : ℝ) :
    S.poutStar ℓ z G = BS.pout ℓ (Ang.ofProfile ℓ (S.gStar ℓ z G)) := by
  have hpt : ∀ y : ℂ, Ang.ofProfile ℓ (S.gStar ℓ z G) y * conj y ^ ℓ =
      S.gStar ℓ z G ‖y‖ * ((‖y‖ : ℝ) : ℂ) ^ ℓ := by
    intro y
    by_cases hy : y = 0
    · subst hy
      simp [Ang.ofProfile, angPhase_zero ℓ hℓ, zero_pow (show ℓ ≠ 0 by omega)]
    · have hn : ((‖y‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hy
      simp only [Ang.ofProfile, Ang.angPhase, zpow_natCast]
      rw [mul_assoc, ← mul_pow]
      congr 2
      rw [div_mul_eq_mul_div, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      field_simp
  have hπ : (2 * Real.pi : ℂ) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  rw [BS.pout]
  simp_rw [hpt]
  rw [Polar.integral_comp_norm (fun r : ℝ => S.gStar ℓ z G r * (r : ℂ) ^ ℓ), Complex.real_smul]
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ hπ, one_mul, poutStar]
  congr 1
  funext r
  rw [Complex.real_smul, pow_succ]
  ring

/-- `pin_* = pin_ℓ[g_* e^{iℓθ}]` (polar coordinates). -/
theorem pinStar_eq_pin (S : SectorSetting) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (z : ℂ) (G : ℝ) :
    S.pinStar ℓ z G = BS.pin ℓ (Ang.ofProfile ℓ (S.gStar ℓ z G)) := by
  have hpt : ∀ y : ℂ, Ang.ofProfile ℓ (S.gStar ℓ z G) y * (y ^ ℓ)⁻¹ =
      S.gStar ℓ z G ‖y‖ * (((‖y‖ : ℝ) : ℂ) ^ ℓ)⁻¹ := by
    intro y
    by_cases hy : y = 0
    · subst hy
      simp [Ang.ofProfile, angPhase_zero ℓ hℓ, zero_pow (show ℓ ≠ 0 by omega)]
    · have hn : ((‖y‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hy
      simp only [Ang.ofProfile, Ang.angPhase, zpow_natCast]
      rw [div_pow]
      field_simp
  have hπ : (2 * Real.pi : ℂ) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  rw [BS.pin]
  simp_rw [hpt]
  rw [Polar.integral_comp_norm (fun r : ℝ => S.gStar ℓ z G r * ((r : ℂ) ^ ℓ)⁻¹),
    Complex.real_smul]
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ hπ, one_mul, pinStar]
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (mem_Ioi.1 hr))
  rw [Complex.real_smul, zpow_sub₀ hr0, zpow_one, zpow_natCast]
  ring

end NonUniqueEuler.AdjointAux
