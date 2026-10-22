import NonUniqueEuler.Defs.Sec4.Setting
import NonUniqueEuler.Defs.Sec4.Extra1Sector
import NonUniqueEuler.Defs.Infra.Multipole
import NonUniqueEuler.I.Infra.Polar.Fubini
import NonUniqueEuler.I.Infra.Multipole.CircleKernel
import NonUniqueEuler.H.Sec4.Sector.LogPotReal.Integrable

/-!
# Proof: the logarithmic potential of `g(|y|)e^{iℓθ}` at a point `r > 0` of the real axis

Proof of `I/Sec4/Sector/LogPotReal.lean` (`lem:sector`(1), `04_ring.tex:206-208`, proof
`:244-256`). Following the interface's proof sketch (a deviation in the proof only: polar
coordinates and the explicit circle integral replace the Liouville/density argument):
1. `y ↦ log|r - y| W(y)` is integrable (`LogPotRealH.integrable_log_mul_ofProfile`, Hölder);
2. polar coordinates (`Polar.integral_eq_integral_Ioi_intervalIntegral`);
3. the inner circle integral for `ρ ≠ r`
   (`Multipole.intervalIntegral_log_norm_sub_circleMap_mul_exp`), then the constants
   `(2π)⁻¹ · (-(π/|ℓ|)) = -(2|ℓ|)⁻¹`.
-/

noncomputable section

open MeasureTheory Set Real

namespace NonUniqueEuler

namespace LogPotRealH

/-- `e^{iℓθ}` at `ρe^{iθ}`, `ρ > 0`. -/
theorem angPhase_circleMap (ℓ : ℤ) {ρ : ℝ} (hρ : 0 < ρ) (θ : ℝ) :
    Ang.angPhase ℓ (circleMap 0 ρ θ) = Complex.exp ((ℓ : ℂ) * θ * Complex.I) := by
  have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  rw [Ang.angPhase, norm_circleMap_zero, abs_of_pos hρ, circleMap, zero_add,
    mul_div_cancel_left₀ _ hρ', mul_assoc, Complex.exp_int_mul]

/-- The polar integrand: for `ρ > 0`, `ρ ≠ r`, `ℓ ≠ 0`,
`ρ ∫₀^{2π} log|r - ρe^{iθ}| g(ρ)e^{iℓθ} dθ = -(π/|ℓ|) tⁿ g(ρ) ρ`. -/
theorem smul_intervalIntegral_eq {ℓ : ℤ} (hℓ : ℓ ≠ 0) (g : ℝ → ℂ) {r ρ : ℝ} (hr : 0 < r)
    (hρ : 0 < ρ) (hρr : ρ ≠ r) :
    ρ • ∫ θ in (0 : ℝ)..2 * π, (Real.log ‖(r : ℂ) - circleMap 0 ρ θ‖ : ℂ) *
        Ang.ofProfile ℓ g (circleMap 0 ρ θ) =
      -((π : ℂ) / (ℓ.natAbs : ℂ)) *
        ((((min r ρ / max r ρ) ^ ℓ.natAbs : ℝ) : ℂ) * g ρ * (ρ : ℂ)) := by
  have hpt : ∀ θ : ℝ, (Real.log ‖(r : ℂ) - circleMap 0 ρ θ‖ : ℂ) *
      Ang.ofProfile ℓ g (circleMap 0 ρ θ) =
      g ρ * ((Real.log ‖(r : ℂ) - circleMap 0 ρ θ‖ : ℂ) *
        Complex.exp ((ℓ : ℂ) * θ * Complex.I)) := by
    intro θ
    rw [Ang.ofProfile, norm_circleMap_zero, abs_of_pos hρ, angPhase_circleMap ℓ hρ θ]
    ring
  rw [intervalIntegral.integral_congr (fun θ _ => hpt θ), intervalIntegral.integral_const_mul,
    Multipole.intervalIntegral_log_norm_sub_circleMap_mul_exp hr hρ (Ne.symm hρr) hℓ,
    Complex.real_smul]
  push_cast
  ring

/-- `(2π)⁻¹ · (-(π/|ℓ|)) = -(2|ℓ|)⁻¹` for `ℓ ≠ 0`. -/
theorem const_eq {ℓ : ℤ} (hℓ : ℓ ≠ 0) :
    (2 * π : ℂ)⁻¹ * -((π : ℂ) / (ℓ.natAbs : ℂ)) = -((((2 * |(ℓ : ℝ)|)⁻¹ : ℝ)) : ℂ) := by
  have hab : |(ℓ : ℝ)| = (ℓ.natAbs : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
  have hn : (ℓ.natAbs : ℂ) ≠ 0 := by exact_mod_cast Int.natAbs_ne_zero.2 hℓ
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [hab]
  push_cast
  field_simp

end LogPotRealH

namespace SectorSetting

/-- `Δ⁻¹(g(|y|)e^{iℓθ})` at the point `r > 0` of the real axis is `𝒢_ℓ g(r)`, for `ℓ ≠ 0` and every
profile `g ∈ Y^0_ℓ`. -/
theorem logPotential_ofProfile_ofReal (S : SectorSetting) (hS : S.Valid) {ℓ : ℤ} (hℓ : ℓ ≠ 0)
    {g : ℝ → ℂ} (hg : S.IsProfileL2 g) {r : ℝ} (hr : 0 < r) :
    Multipole.logPotential (Ang.ofProfile ℓ g) (r : ℂ) = green ℓ g r := by
  have hf := LogPotRealH.integrable_log_mul_ofProfile hg ℓ (r : ℂ)
  have hne : ∀ᵐ ρ : ℝ ∂volume, ρ ≠ r := by
    filter_upwards [(Set.countable_singleton r).ae_notMem volume] with ρ hρ
    exact hρ
  rw [Multipole.logPotential, Polar.integral_eq_integral_Ioi_intervalIntegral hf,
    setIntegral_congr_ae measurableSet_Ioi (hne.mono fun ρ hρr hρ =>
      LogPotRealH.smul_intervalIntegral_eq hℓ g hr hρ hρr),
    integral_const_mul, ← mul_assoc, LogPotRealH.const_eq hℓ, green]

end SectorSetting

end NonUniqueEuler
