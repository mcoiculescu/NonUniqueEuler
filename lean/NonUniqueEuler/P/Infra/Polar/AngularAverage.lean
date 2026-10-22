import NonUniqueEuler.Defs.Infra.Polar
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Proof: angular averages and angular sectors (I-POLAR)

Proof of `NonUniqueEuler/I/Infra/Polar/AngularAverage.lean` (same declarations, same
statements). Manuscript: `lem:hollow` (`02_prelim.tex:413-414`, the rotation form of the angular
average) and the angular sectors (`02_prelim.tex:27-33`).

Method. All measure-theoretic statements are reduced to one fact
(`AngularAverageAux.measurePreserving_rotProd`): with the normalized angle measure
`P = (2π)⁻¹ dφ` on `(0, 2π]` (a probability measure), the map `(x, φ) ↦ rot φ x` is measure
preserving from `volume ⊗ P` to `volume`. Then
* `angAvg g x = ∫ g (rot φ x) dP(φ)` (`AngularAverageAux.angAvg_eq_integral`);
* a null set of `ℂ` pulls back to a null set of `ℂ × ℝ`, so for a.e. `x`, `P`-a.e. `φ` avoids
  it (`AngularAverageAux.ae_ae_rot`);
* Fubini/Tonelli on `volume ⊗ P` plus the measure-preserving change of variables give the
  `L¹` statements and the `L^p` contraction (Jensen for the probability measure `P`).
-/

noncomputable section

open MeasureTheory Set Metric Real
open scoped ENNReal

namespace NonUniqueEuler.Polar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The rotation form of the angular average (`02_prelim.tex:413-414`). -/
theorem angAvg_eq_intervalIntegral_rot (g : ℂ → E) (x : ℂ) :
    angAvg g x = (2 * π)⁻¹ • ∫ φ in (0 : ℝ)..2 * π, g (rot φ x) := by
  rw [angAvg, Real.circleAverage_eq_integral_add (Complex.arg x)]
  congr 2
  funext φ
  congr 1
  simp only [circleMap, rot, zero_add, Complex.ofReal_add, add_mul, Complex.exp_add]
  conv_rhs => rw [← Complex.norm_mul_exp_arg_mul_I x]
  ring

theorem angAvg_of_isRadialPointwise {g : ℂ → ℝ} (hg : IsRadialPointwise g) : angAvg g = g := by
  funext x
  rw [angAvg_eq_intervalIntegral_rot]
  simp only [hg _ x, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

namespace AngularAverageAux

/-- The normalized angle measure `(2π)⁻¹ dφ` on `(0, 2π]`. -/
def angleMeasure : Measure ℝ :=
  (ENNReal.ofReal (2 * π))⁻¹ • volume.restrict (Ioc 0 (2 * π))

/-- `angleMeasure` is a probability measure. A theorem, used as a `local instance` only
(no global instances in proof files). -/
theorem isProbabilityMeasure_angleMeasure : IsProbabilityMeasure angleMeasure := by
  constructor
  simp only [angleMeasure, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, Real.volume_Ioc, sub_zero, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by simp [pi_pos]) ENNReal.ofReal_ne_top

attribute [local instance] isProbabilityMeasure_angleMeasure

theorem continuous_rotProd : Continuous (fun p : ℂ × ℝ => rot p.2 p.1) := by
  unfold rot
  fun_prop

/-- The key fact: `(x, φ) ↦ rot φ x` is measure preserving from `volume ⊗ P` to `volume`. -/
theorem measurePreserving_rotProd :
    MeasurePreserving (fun p : ℂ × ℝ => rot p.2 p.1) (volume.prod angleMeasure) volume := by
  refine ⟨continuous_rotProd.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply continuous_rotProd.measurable hs,
    Measure.prod_apply_symm (continuous_rotProd.measurable hs)]
  have h : ∀ y : ℝ,
      volume ((fun x : ℂ => (x, y)) ⁻¹' ((fun p : ℂ × ℝ => rot p.2 p.1) ⁻¹' s)) = volume s :=
    fun y => (measurePreserving_rot y).measure_preimage hs.nullMeasurableSet
  refine (lintegral_congr h).trans ?_
  simp

/-- The angular average as an integral against the probability measure `P`. -/
theorem angAvg_eq_integral (g : ℂ → E) (x : ℂ) :
    angAvg g x = ∫ φ, g (rot φ x) ∂angleMeasure := by
  rw [angAvg_eq_intervalIntegral_rot, intervalIntegral.integral_of_le (by positivity),
    angleMeasure, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (by positivity)]

theorem angAvg_eq_fun (g : ℂ → E) :
    angAvg g = fun x => ∫ φ, g (rot φ x) ∂angleMeasure :=
  funext (angAvg_eq_integral g)

/-- A property holding a.e. on `ℂ` holds, for a.e. `x`, at `rot φ x` for `P`-a.e. `φ`. -/
theorem ae_ae_rot {q : ℂ → Prop} (h : ∀ᵐ y : ℂ, q y) :
    ∀ᵐ x : ℂ, ∀ᵐ φ ∂angleMeasure, q (rot φ x) :=
  Measure.ae_ae_of_ae_prod (measurePreserving_rotProd.quasiMeasurePreserving.ae h)

theorem angAvg_ae_eq_of_ae_eq {g g' : ℂ → E} (h : g =ᵐ[volume] g') :
    angAvg g =ᵐ[volume] angAvg g' := by
  filter_upwards [ae_ae_rot h] with x hx
  rw [angAvg_eq_integral, angAvg_eq_integral]
  exact integral_congr_ae hx

omit [CompleteSpace E] in
theorem integral_comp_rotProd {g : ℂ → E} (hg : AEStronglyMeasurable g volume) :
    ∫ z, g (rot z.2 z.1) ∂(volume.prod angleMeasure) = ∫ y, g y := by
  have hm : AEStronglyMeasurable g
      (Measure.map (fun p : ℂ × ℝ => rot p.2 p.1) (volume.prod angleMeasure)) := by
    rw [measurePreserving_rotProd.map_eq]; exact hg
  have := integral_map measurePreserving_rotProd.measurable.aemeasurable hm
  rw [measurePreserving_rotProd.map_eq] at this
  exact this.symm

theorem lintegral_comp_rotProd {f : ℂ → ℝ≥0∞} (hf : AEMeasurable f volume) :
    ∫⁻ z, f (rot z.2 z.1) ∂(volume.prod angleMeasure) = ∫⁻ y, f y := by
  have hm : AEMeasurable f
      (Measure.map (fun p : ℂ × ℝ => rot p.2 p.1) (volume.prod angleMeasure)) := by
    rw [measurePreserving_rotProd.map_eq]; exact hf
  have := lintegral_map' hm measurePreserving_rotProd.measurable.aemeasurable
  rw [measurePreserving_rotProd.map_eq] at this
  exact this.symm

omit [CompleteSpace E] in
/-- Jensen's inequality `‖∫ f‖^p ≤ ∫ ‖f‖^p` for a probability measure, `1 ≤ p < ∞`. -/
theorem enorm_integral_rpow_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → E} (hf : AEStronglyMeasurable f μ) {p : ℝ≥0∞}
    (hp1 : 1 ≤ p) (hp : p ≠ ∞) :
    ‖∫ a, f a ∂μ‖ₑ ^ p.toReal ≤ ∫⁻ a, ‖f a‖ₑ ^ p.toReal ∂μ := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have h1 : ‖∫ a, f a ∂μ‖ₑ ≤ eLpNorm f p μ :=
    calc ‖∫ a, f a ∂μ‖ₑ ≤ ∫⁻ a, ‖f a‖ₑ ∂μ := enorm_integral_le_lintegral_enorm f
    _ = eLpNorm f 1 μ := eLpNorm_one_eq_lintegral_enorm.symm
    _ ≤ eLpNorm f p μ := eLpNorm_le_eLpNorm_of_exponent_le hp1 hf
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp] at h1
  calc ‖∫ a, f a ∂μ‖ₑ ^ p.toReal
      ≤ ((∫⁻ a, ‖f a‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal)) ^ p.toReal :=
        ENNReal.rpow_le_rpow h1 hq.le
    _ = ∫⁻ a, ‖f a‖ₑ ^ p.toReal ∂μ := by rw [one_div, ENNReal.rpow_inv_rpow hq.ne']

end AngularAverageAux

attribute [local instance] AngularAverageAux.isProbabilityMeasure_angleMeasure

open AngularAverageAux

/-- An (a.e.) radial measurable function is a.e. equal to its angular average, which is
pointwise radial (`isRadialPointwise_angAvg`). -/
theorem ae_eq_angAvg_of_isRadial {g : ℂ → ℝ} (hg : IsRadial g)
    (hgm : AEStronglyMeasurable g volume) : g =ᵐ[volume] angAvg g := by
  set g' := hgm.mk g
  have hg'm : StronglyMeasurable g' := hgm.stronglyMeasurable_mk
  have hgg' : g =ᵐ[volume] g' := hgm.ae_eq_mk
  have hrad : ∀ θ : ℝ, ∀ᵐ x : ℂ, g' (rot θ x) = g' x := by
    intro θ
    have h1 : ∀ᵐ x : ℂ, g (rot θ x) = g' (rot θ x) :=
      (measurePreserving_rot θ).quasiMeasurePreserving.ae hgg'
    filter_upwards [h1, hg θ, hgg'] with x h1x h2x h3x
    rw [← h1x, h2x, h3x]
  have hmeas : MeasurableSet {z : ℂ × ℝ | g' (rot z.2 z.1) = g' z.1} :=
    measurableSet_eq_fun (hg'm.measurable.comp continuous_rotProd.measurable)
      (hg'm.measurable.comp measurable_fst)
  have hswap : ∀ᵐ x : ℂ, ∀ᵐ φ ∂angleMeasure, g' (rot φ x) = g' x :=
    (Measure.ae_ae_comm (p := fun x φ => g' (rot φ x) = g' x) hmeas).2 (ae_of_all _ hrad)
  filter_upwards [hswap, ae_ae_rot hgg', hgg'] with x h1 h2 h3
  rw [angAvg_eq_integral]
  have : (fun φ => g (rot φ x)) =ᵐ[angleMeasure] fun _ => g x := by
    filter_upwards [h1, h2] with φ hφ1 hφ2
    rw [hφ2, hφ1, h3]
  rw [integral_congr_ae this]
  simp

theorem aestronglyMeasurable_angAvg {g : ℂ → E} (hg : AEStronglyMeasurable g volume) :
    AEStronglyMeasurable (angAvg g) volume := by
  rw [angAvg_eq_fun]
  exact (hg.comp_measurePreserving measurePreserving_rotProd).integral_prod_right'

theorem integrable_angAvg {g : ℂ → E} (hg : Integrable g) : Integrable (angAvg g) := by
  rw [angAvg_eq_fun]
  exact (measurePreserving_rotProd.integrable_comp_of_integrable hg).integral_prod_left

theorem integral_angAvg {g : ℂ → E} (hg : Integrable g) : ∫ x, angAvg g x = ∫ x, g x := by
  have hF := measurePreserving_rotProd.integrable_comp_of_integrable hg
  calc ∫ x, angAvg g x = ∫ x, ∫ φ, g (rot φ x) ∂angleMeasure := by
        simp_rw [angAvg_eq_integral]
    _ = ∫ z, g (rot z.2 z.1) ∂(volume.prod angleMeasure) := (integral_prod _ hF).symm
    _ = ∫ y, g y := integral_comp_rotProd hg.aestronglyMeasurable

/-- The angular average is a contraction on every `L^p`, `1 ≤ p ≤ ∞`. -/
theorem eLpNorm_angAvg_le {g : ℂ → E} (hg : AEStronglyMeasurable g volume) {p : ℝ≥0∞}
    (hp : 1 ≤ p) : eLpNorm (angAvg g) p volume ≤ eLpNorm g p volume := by
  by_cases hp_top : p = ∞
  · subst hp_top
    rw [eLpNorm_exponent_top, eLpNorm_exponent_top]
    refine eLpNormEssSup_le_of_ae_enorm_bound ?_
    filter_upwards [ae_ae_rot (ae_le_eLpNormEssSup (f := g) (μ := volume))] with x hx
    rw [angAvg_eq_integral]
    calc ‖∫ φ, g (rot φ x) ∂angleMeasure‖ₑ ≤ ∫⁻ φ, ‖g (rot φ x)‖ₑ ∂angleMeasure :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ _, eLpNormEssSup g volume ∂angleMeasure := lintegral_mono_ae hx
      _ = eLpNormEssSup g volume := by simp
  · have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top]
    refine ENNReal.rpow_le_rpow ?_ (by positivity)
    have hF := hg.comp_measurePreserving measurePreserving_rotProd
    have hFm : AEMeasurable (fun z : ℂ × ℝ => ‖g (rot z.2 z.1)‖ₑ ^ p.toReal)
        (volume.prod angleMeasure) :=
      hF.enorm.pow_const _
    calc ∫⁻ x, ‖angAvg g x‖ₑ ^ p.toReal
        ≤ ∫⁻ x, ∫⁻ φ, ‖g (rot φ x)‖ₑ ^ p.toReal ∂angleMeasure := by
          refine lintegral_mono_ae ?_
          filter_upwards [hF.prodMk_left] with x hx
          rw [angAvg_eq_integral]
          exact enorm_integral_rpow_le hx hp hp_top
      _ = ∫⁻ z, ‖g (rot z.2 z.1)‖ₑ ^ p.toReal ∂(volume.prod angleMeasure) :=
          (lintegral_prod _ hFm).symm
      _ = ∫⁻ y, ‖g y‖ₑ ^ p.toReal := lintegral_comp_rotProd (hg.enorm.pow_const _)

/-- If `g = 0` a.e. on `{y | ‖y‖ ∈ A}`, then `angAvg g = 0` a.e. there. -/
theorem ae_angAvg_eq_zero_of_ae {g : ℂ → E} {A : Set ℝ} (hA : MeasurableSet A)
    (hg : ∀ᵐ y : ℂ, ‖y‖ ∈ A → g y = 0) : ∀ᵐ x : ℂ, ‖x‖ ∈ A → angAvg g x = 0 := by
  filter_upwards [ae_ae_rot hg] with x hx hxA
  rw [angAvg_eq_integral]
  have : (fun φ => g (rot φ x)) =ᵐ[angleMeasure] fun _ => 0 := by
    filter_upwards [hx] with φ hφ
    exact hφ (by rwa [norm_rot])
  rw [integral_congr_ae this, integral_zero]

/-- The angular sector `0` is the circle average. -/
theorem angularSector_zero (g : ℂ → ℂ) (r : ℝ) :
    angularSector g 0 r = Real.circleAverage g 0 r := by
  simp only [angularSector, Real.circleAverage, circleMap, zero_add, Int.cast_zero, zero_mul,
    neg_zero, Complex.exp_zero, mul_one, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_mul, Complex.ofReal_ofNat]

/-- A rotation-invariant function has no angular sectors `ℓ ≠ 0`. -/
theorem angularSector_eq_zero_of_rot_invariant {g : ℂ → ℂ} (hg : ∀ θ x, g (rot θ x) = g x)
    {ℓ : ℤ} (hℓ : ℓ ≠ 0) (r : ℝ) : angularSector g ℓ r = 0 := by
  have h1 : ∀ θ : ℝ, g ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = g r := by
    intro θ
    rw [← hg θ (r : ℂ)]
    simp only [rot, mul_comm]
  have hc : (-(ℓ : ℂ) * Complex.I) ≠ 0 := by
    simp [hℓ, Complex.I_ne_zero]
  have h2 : ∫ θ in (0 : ℝ)..2 * π, Complex.exp (-((ℓ : ℂ) * θ * Complex.I)) = 0 := by
    have hrw : ∀ θ : ℝ, -((ℓ : ℂ) * θ * Complex.I) = (-(ℓ : ℂ) * Complex.I) * θ :=
      fun θ => by ring
    simp only [hrw]
    rw [integral_exp_mul_complex hc]
    have h3 : Complex.exp (-(ℓ : ℂ) * Complex.I * ((2 * π : ℝ) : ℂ)) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I (-ℓ)]
      congr 1
      push_cast
      ring
    rw [h3]
    simp
  simp only [angularSector, h1]
  rw [intervalIntegral.integral_const_mul, h2, mul_zero, mul_zero]

end NonUniqueEuler.Polar
