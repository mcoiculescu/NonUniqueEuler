import NonUniqueEuler.Defs.Sec4.Eigendata
import NonUniqueEuler.I.Infra.Polar.Fubini
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Helper for `lem:running`: `ℓ_*(G)` on functions only sees the a.e. class

Helper of `P/Sec5/Running.lean`.

* `RunningAux.angularSector_congr_ae`: a.e. equal functions on `ℂ` have a.e. equal angular
  sectors on `(0, ∞)` (Tonelli in polar coordinates applied to the indicator of a measurable null
  set containing `{g ≠ g'}`). The proof is the one of `ProfileL2Aux.angularSector_congr_ae` in
  `P/Infra/AngularFourier/Derivatives/ProfileL2.lean`, copied because a `P` file
  cannot be imported.
* `RunningAux.ellFn_congr_ae`: hence `Eig.ellFn χ G f = Eig.ellFn χ G g` for `f =ᵐ g`.
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace NonUniqueEuler.OneRing.RunningAux

/-- The polar parametrisation `(r, θ) ↦ r e^{iθ}` is continuous. -/
theorem continuous_polarParam :
    Continuous fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I) := by
  fun_prop

/-- a.e. equal functions on `ℂ` have a.e. equal angular sectors on `(0, ∞)`. -/
theorem angularSector_congr_ae {g g' : ℂ → ℂ} (h : g =ᵐ[volume] g') (ℓ : ℤ) :
    Polar.angularSector g ℓ =ᵐ[volume.restrict (Ioi 0)] Polar.angularSector g' ℓ := by
  have h0 : volume {x | ¬ g x = g' x} = 0 := ae_iff.1 h
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null h0
  have hmeasN : Measurable (N.indicator (1 : ℂ → ℝ≥0∞)) := measurable_one.indicator hNm
  have hT := Polar.lintegral_eq_lintegral_Ioi_circle hmeasN
  rw [lintegral_indicator_one hNm, hN0] at hT
  have hFm : Measurable fun p : ℝ × ℝ => N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 p.1 p.2) := by
    refine hmeasN.comp ?_
    have : (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) =
        fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I) := by
      funext p; simp [circleMap]
    rw [this]
    exact continuous_polarParam.measurable
  have hGm : Measurable fun r : ℝ => ENNReal.ofReal r *
      ∫⁻ θ in Ioc (0 : ℝ) (2 * π), N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 r θ) :=
    ENNReal.measurable_ofReal.mul (hFm.lintegral_prod_right' (ν := volume.restrict (Ioc 0 (2 * π))))
  have hae := (lintegral_eq_zero_iff hGm).1 hT.symm
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioi] with r hr hrpos
  have hrpos' : (0 : ℝ) < r := hrpos
  have hr' : ∫⁻ θ in Ioc (0 : ℝ) (2 * π), N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 r θ) = 0 := by
    have hr2 : ENNReal.ofReal r *
        ∫⁻ θ in Ioc (0 : ℝ) (2 * π), N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 r θ) = 0 := hr
    rcases mul_eq_zero.1 hr2 with h1 | h1
    · exact absurd h1 (ENNReal.ofReal_pos.2 hrpos').ne'
    · exact h1
  have hθm : Measurable fun θ : ℝ => N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 r θ) :=
    hFm.comp (measurable_const.prodMk measurable_id)
  have hθ := (lintegral_eq_zero_iff hθm).1 hr'
  unfold Polar.angularSector
  congr 1
  rw [intervalIntegral.integral_of_le (by positivity), intervalIntegral.integral_of_le (by positivity)]
  refine integral_congr_ae ?_
  filter_upwards [hθ] with θ hθ'
  have hnot : circleMap 0 r θ ∉ N := by
    intro hmem
    have : N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 r θ) = 1 := indicator_of_mem hmem _
    simp [this] at hθ'
  have hcm : circleMap 0 r θ = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    simp [circleMap]
  rw [hcm] at hnot
  have heq : g ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
      g' ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
    by_contra hne
    exact hnot (hNsub hne)
  simp only [heq]

/-- `ℓ_*(G)` on functions (`Eig.ellFn`) only depends on the a.e. class of the function. -/
theorem ellFn_congr_ae (χ : ℝ → ℝ) (G : ℝ) {f g : ℂ → ℂ} (hfg : f =ᵐ[volume] g) :
    Eig.ellFn χ G f = Eig.ellFn χ G g := by
  have hs := angularSector_congr_ae hfg 3
  unfold Eig.ellFn SectorSetting.ellStar
  congr 2
  refine integral_congr_ae ?_
  filter_upwards [hs] with r hr
  rw [hr]

end NonUniqueEuler.OneRing.RunningAux
