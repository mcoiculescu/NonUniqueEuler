import NonUniqueEuler.H.Infra.AngularFourier.NormEquiv.ProfileDeriv.Angular
import NonUniqueEuler.Defs.Infra.AngularFourier
import NonUniqueEuler.I.Infra.Polar.Fubini
import NonUniqueEuler.I.Infra.Polar.Radial

/-!
# Helpers for `P/Infra/AngularFourier/NormEquiv/ProfileDeriv`: sector integrals in polar form

For a profile `f` with `r f(r)` integrable on `(0,∞)` and `ψ` continuous with compact support:
`∫_ℂ f(|x|) e^{imθ} ψ(x) dx = ∫₀^∞ r f(r) (∫₀^{2π} e^{imθ} ψ(r e^{iθ}) dθ) dr`
(`ofProfile_polar`), from Fubini in polar coordinates
(`Polar.integral_eq_integral_Ioi_intervalIntegral`) and `angPhase m (r e^{iθ}) = e^{imθ}`
(`angPhase_circleMap`). Integrability: `f(|·|)` is integrable (`Polar.integrable_comp_norm_iff`)
and `e^{imθ} ψ` is bounded and a.e. strongly measurable (continuous off `0`).
-/

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff

namespace NonUniqueEuler.Ang.NEProfileDerivAux

theorem angPhase_circleMap (m : ℤ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    angPhase m (circleMap 0 r θ) = eA m θ := by
  have hn : ‖circleMap 0 r θ‖ = r := by rw [norm_circleMap_zero, abs_of_pos hr]
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hu : circleMap 0 r θ / ((‖circleMap 0 r θ‖ : ℝ) : ℂ) =
      Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [hn, circleMap_zero, mul_div_cancel_left₀ _ hr']
  rw [angPhase, hu, ← Complex.exp_int_mul, eA]
  congr 1
  ring

theorem continuousAt_angPhase (m : ℤ) {x : ℂ} (hx : x ≠ 0) : ContinuousAt (angPhase m) x := by
  have hn : ((‖x‖ : ℝ) : ℂ) ≠ 0 := by simpa using hx
  have h1 : ContinuousAt (fun y : ℂ => y / ((‖y‖ : ℝ) : ℂ)) x :=
    continuousAt_id.div (Complex.continuous_ofReal.comp continuous_norm).continuousAt hn
  exact h1.zpow₀ m (Or.inl (div_ne_zero hx hn))

theorem aestronglyMeasurable_angPhase_mul (m : ℤ) {ψ : ℂ → ℂ} (hψ : Continuous ψ) :
    AEStronglyMeasurable (fun x => angPhase m x * ψ x) volume := by
  have hc : ContinuousOn (fun x => angPhase m x * ψ x) {0}ᶜ := fun x hx =>
    ((continuousAt_angPhase m hx).mul hψ.continuousAt).continuousWithinAt
  have := hc.aestronglyMeasurable (μ := volume) (measurableSet_singleton 0).compl
  rwa [restrict_compl_singleton] at this

/-- Sector integrals in polar coordinates. -/
theorem ofProfile_polar {f : ℝ → ℂ} (hf : IntegrableOn (fun r : ℝ => (r : ℂ) * f r) (Ioi 0))
    (m : ℤ) {ψ : ℂ → ℂ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Integrable (fun x => ofProfile m f x * ψ x) ∧
      ∫ x, ofProfile m f x * ψ x = ∫ r in Ioi (0 : ℝ), (r : ℂ) * (f r * angCoef (eA m) ψ r) := by
  have hf' : Integrable (fun x : ℂ => f ‖x‖) := by
    refine Polar.integrable_comp_norm_iff.2 ?_
    simpa only [Complex.real_smul] using hf
  obtain ⟨C, hC⟩ := hψc.exists_bound_of_continuous hψ
  have hbd : ∀ᵐ x : ℂ, ‖angPhase m x * ψ x‖ ≤ C := by
    filter_upwards [(volume : Measure ℂ).ae_ne 0] with x hx
    rw [norm_mul, norm_angPhase hx m, one_mul]
    exact hC x
  have hint : Integrable (fun x => ofProfile m f x * ψ x) := by
    have h := hf'.mul_bdd (aestronglyMeasurable_angPhase_mul m hψ) hbd
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp only [ofProfile]
    ring
  refine ⟨hint, ?_⟩
  rw [Polar.integral_eq_integral_Ioi_intervalIntegral hint]
  refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
  have hr0 : (0 : ℝ) < r := hr
  have hn : ∀ θ : ℝ, ‖circleMap 0 r θ‖ = r := fun θ => by
    rw [norm_circleMap_zero, abs_of_pos hr0]
  simp only [ofProfile, hn, angPhase_circleMap m hr0, Complex.real_smul]
  congr 1
  rw [angCoef, ← intervalIntegral.integral_const_mul]
  congr 1
  funext θ
  ring

end NonUniqueEuler.Ang.NEProfileDerivAux
