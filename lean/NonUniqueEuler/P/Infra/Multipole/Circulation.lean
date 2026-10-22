import NonUniqueEuler.Defs.Infra.Multipole
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Proof: circulation and flux of Biot–Savart fields through circles (I-MULT, R11)

Proof of `NonUniqueEuler/I/Infra/Multipole/Circulation.lean` (same declarations, same
statements). Manuscript: `05_single_ring.tex:165-176` (proof of `lem:reduction`(1)), restructured
through the complex form of the Biot–Savart law (restructuring R11: no general winding numbers).

* Point vortex: `conj (K (z - y)) = (2πi)⁻¹ (z - y)⁻¹` (`conj_biotSavartKernel`); inside the
  circle, `circleIntegral.integral_sub_inv_of_mem_ball`; outside, Cauchy–Goursat
  (`Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable`).
* Real forms: the circle integrand `ż · conj u` with `ż = i r e^{iθ}` has real part
  `r (u·e_θ)` and imaginary part `r (u·e_r)` (`deriv_circleMap_smul_conj`), so a real value of
  the circle integral gives the circulation and a vanishing flux (`real_forms_of_circle`).
* Vorticity: Fubini (`intervalIntegral_integral_swap`) for
  `(θ, y) ↦ ż(θ) conj (K (r e^{iθ} - y)) ω(y)`, dominated by `r (2πδ)⁻¹ |ω(y)|` because
  `|r e^{iθ} - y| ≥ δ` where `ω(y) ≠ 0`; then the point-vortex formula for a.e. `y`.
-/

noncomputable section

open MeasureTheory Set Metric Real ComplexConjugate

namespace NonUniqueEuler.Multipole

/-! ### Helpers -/

/-- The point-vortex circle integrand in closed form. -/
private lemma conj_biotSavartKernel_sub_eq (z y : ℂ) :
    conj (biotSavartKernel (z - y)) = (2 * π * Complex.I)⁻¹ * (z - y)⁻¹ := by
  rw [conj_biotSavartKernel, mul_inv]

/-- `‖K z‖ = (2π‖z‖)⁻¹`. -/
private lemma norm_biotSavartKernel_eq (z : ℂ) :
    ‖biotSavartKernel z‖ = (2 * π * ‖z‖)⁻¹ := by
  rw [← Complex.norm_conj, conj_biotSavartKernel, norm_inv, norm_mul, norm_mul, norm_mul,
    Complex.norm_I, Complex.norm_real, Complex.norm_two, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, mul_one]

/-- Real and imaginary parts of the circle integrand `ż · conj u`, `ż = i r e^{iθ}`. -/
private lemma deriv_circleMap_smul_conj (r θ : ℝ) (u : ℂ) :
    deriv (circleMap 0 r) θ • conj u =
      ((r * inner ℝ u (Complex.I * Complex.exp (θ * Complex.I)) : ℝ) : ℂ) +
      ((r * inner ℝ u (Complex.exp (θ * Complex.I)) : ℝ) : ℂ) * Complex.I := by
  rw [deriv_circleMap, circleMap_zero, smul_eq_mul, Complex.inner, Complex.inner]
  generalize Complex.exp (θ * Complex.I) = e
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re,
      Complex.conj_im] <;> ring

/-- A real value `c` of a circle integral `∫ ż · conj u` gives the circulation `c` and a
vanishing flux of `u`. -/
private lemma real_forms_of_circle {r : ℝ} (hr : 0 < r) (u : ℝ → ℂ) (c : ℝ)
    (hint : IntervalIntegrable (fun θ => deriv (circleMap 0 r) θ • conj (u θ)) volume 0
      (2 * π))
    (h : ∫ θ in (0 : ℝ)..2 * π, deriv (circleMap 0 r) θ • conj (u θ) = (c : ℂ)) :
    r * ∫ θ in (0 : ℝ)..2 * π, inner ℝ (u θ) (Complex.I * Complex.exp (θ * Complex.I)) = c ∧
      ∫ θ in (0 : ℝ)..2 * π, inner ℝ (u θ) (Complex.exp (θ * Complex.I)) = 0 := by
  have hre : ∀ θ : ℝ, (deriv (circleMap 0 r) θ • conj (u θ)).re =
      r * inner ℝ (u θ) (Complex.I * Complex.exp (θ * Complex.I)) := by
    intro θ
    rw [deriv_circleMap_smul_conj]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im, neg_zero,
      add_zero]
  have him : ∀ θ : ℝ, (deriv (circleMap 0 r) θ • conj (u θ)).im =
      r * inner ℝ (u θ) (Complex.exp (θ * Complex.I)) := by
    intro θ
    rw [deriv_circleMap_smul_conj]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re, zero_add]
  have h1 := intervalIntegral.intervalIntegral_re hint
  have h2 := intervalIntegral.intervalIntegral_im hint
  simp only [RCLike.re_to_complex, RCLike.im_to_complex, hre, him, h] at h1 h2
  rw [intervalIntegral.integral_const_mul] at h1 h2
  refine ⟨by simpa using h1, ?_⟩
  simp only [Complex.ofReal_im] at h2
  exact (mul_eq_zero.mp h2).resolve_left hr.ne'

/-- The point-vortex circle integrand is integrable. -/
private lemma circleIntegrable_conj_biotSavartKernel_sub {r : ℝ} (hr : 0 < r) {y : ℂ}
    (hy : ‖y‖ ≠ r) : CircleIntegrable (fun z => conj (biotSavartKernel (z - y))) 0 r := by
  simp_rw [conj_biotSavartKernel_sub_eq]
  refine ContinuousOn.circleIntegrable hr.le ?_
  refine continuousOn_const.mul (ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) ?_)
  intro z hz
  rw [mem_sphere, dist_zero_right] at hz
  intro h
  have hzy : z = y := sub_eq_zero.mp h
  exact hy (hzy ▸ hz)

/-! ### Point vortex -/

/-- `∮_{C(0,r)} conj (K(z - y)) dz = [|y| < r]` for `|y| ≠ r`. -/
theorem circleIntegral_conj_biotSavartKernel_sub {r : ℝ} (hr : 0 < r) {y : ℂ}
    (hy : ‖y‖ ≠ r) :
    (∮ z in C(0, r), conj (biotSavartKernel (z - y))) = if ‖y‖ < r then 1 else 0 := by
  simp_rw [conj_biotSavartKernel_sub_eq]
  rw [circleIntegral.integral_const_mul]
  have hpi : (2 * π * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  split_ifs with h
  · rw [circleIntegral.integral_sub_inv_of_mem_ball (by simpa using h)]
    exact inv_mul_cancel₀ hpi
  · have hlt : r < ‖y‖ := lt_of_le_of_ne (not_lt.mp h) (Ne.symm hy)
    have hne : ∀ z ∈ closedBall (0 : ℂ) r, z - y ≠ 0 := by
      intro z hz h0
      rw [mem_closedBall, dist_zero_right, sub_eq_zero.mp h0] at hz
      linarith
    rw [Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le countable_empty,
      mul_zero]
    · exact ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) hne
    · intro z hz
      exact ((differentiableAt_id.sub_const y).inv (hne z (ball_subset_closedBall hz.1)))

/-- The flux of a point vortex through a circle not containing it on its boundary is `0`. -/
theorem integral_inner_biotSavartKernel_radial {r : ℝ} (hr : 0 < r) {y : ℂ} (hy : ‖y‖ ≠ r) :
    ∫ θ in (0 : ℝ)..2 * π,
      inner ℝ (biotSavartKernel (circleMap 0 r θ - y)) (Complex.exp (θ * Complex.I)) = 0 := by
  have h := circleIntegral_conj_biotSavartKernel_sub hr hy
  rw [circleIntegral] at h
  refine (real_forms_of_circle hr (fun θ => biotSavartKernel (circleMap 0 r θ - y))
    (if ‖y‖ < r then 1 else 0) (circleIntegrable_conj_biotSavartKernel_sub hr hy).out ?_).2
  rw [h]
  split_ifs <;> simp

/-- The circulation of a point vortex around `C_r` is `1` if it lies inside, `0` outside. -/
theorem integral_inner_biotSavartKernel_tangential {r : ℝ} (hr : 0 < r) {y : ℂ}
    (hy : ‖y‖ ≠ r) :
    r * ∫ θ in (0 : ℝ)..2 * π,
      inner ℝ (biotSavartKernel (circleMap 0 r θ - y))
        (Complex.I * Complex.exp (θ * Complex.I)) = if ‖y‖ < r then 1 else 0 := by
  have h := circleIntegral_conj_biotSavartKernel_sub hr hy
  rw [circleIntegral] at h
  refine (real_forms_of_circle hr (fun θ => biotSavartKernel (circleMap 0 r θ - y))
    (if ‖y‖ < r then 1 else 0) (circleIntegrable_conj_biotSavartKernel_sub hr hy).out ?_).1
  rw [h]
  split_ifs <;> simp

/-! ### Vorticity: the Fubini argument -/

/-- `ż(θ) conj (K ⋆ ω)(r e^{iθ}) = ∫ ż(θ) conj (K (r e^{iθ} - y)) ω(y) dy` (no hypothesis). -/
private lemma deriv_smul_conj_velocity (ω : ℂ → ℝ) (r θ : ℝ) :
    deriv (circleMap 0 r) θ • conj (velocity ω (circleMap 0 r θ)) =
      ∫ y, deriv (circleMap 0 r) θ *
        (conj (biotSavartKernel (circleMap 0 r θ - y)) * (ω y : ℂ)) := by
  rw [velocity, ← integral_conj, smul_eq_mul, ← integral_const_mul]
  congr 1
  funext y
  rw [map_mul, Complex.conj_ofReal]

/-- Distance from the circle `C_r` to a point `y` with `‖y‖ ∉ (r - δ, r + δ)`. -/
private lemma le_norm_circleMap_sub {r δ : ℝ} (hr : 0 < r) {y : ℂ}
    (hy : ¬ ‖y‖ ∈ Ioo (r - δ) (r + δ)) (θ : ℝ) : δ ≤ ‖circleMap 0 r θ - y‖ := by
  rw [mem_Ioo, not_and_or, not_lt, not_lt] at hy
  have h := abs_norm_sub_norm_le (circleMap 0 r θ) y
  rw [norm_circleMap_zero, abs_of_pos hr] at h
  rcases hy with hy | hy
  · exact le_trans (by linarith) ((le_abs_self _).trans h)
  · exact le_trans (by linarith) ((neg_le_abs _).trans h)

/-- The Fubini integrand is integrable on `(0, 2π] × ℂ`. -/
private lemma integrable_circIntegrand {ω : ℂ → ℝ} (hω : Integrable ω) {r δ : ℝ} (hr : 0 < r)
    (hδ : 0 < δ) (hsupp : ∀ᵐ y, ‖y‖ ∈ Ioo (r - δ) (r + δ) → ω y = 0) :
    Integrable (Function.uncurry fun θ y => deriv (circleMap 0 r) θ *
        (conj (biotSavartKernel (circleMap 0 r θ - y)) * (ω y : ℂ)))
      ((volume.restrict (uIoc (0 : ℝ) (2 * π))).prod volume) := by
  have : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) (2 * π))) :=
    isFiniteMeasure_restrict.2
      ((measure_mono uIoc_subset_uIcc).trans_lt isCompact_uIcc.measure_lt_top).ne
  have hg : Integrable (fun p : ℝ × ℂ => r * (2 * π * δ)⁻¹ * ‖ω p.2‖)
      ((volume.restrict (uIoc (0 : ℝ) (2 * π))).prod volume) :=
    (integrable_const (r * (2 * π * δ)⁻¹)).mul_prod hω.norm
  refine hg.mono' ?_ ?_
  · have h1 : Measurable fun p : ℝ × ℂ => deriv (circleMap 0 r) p.1 *
        conj (biotSavartKernel (circleMap 0 r p.1 - p.2)) := by
      simp_rw [deriv_circleMap, conj_biotSavartKernel]
      fun_prop
    have h2 : AEStronglyMeasurable (fun p : ℝ × ℂ => (ω p.2 : ℂ))
        ((volume.restrict (uIoc (0 : ℝ) (2 * π))).prod volume) :=
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hω.aestronglyMeasurable).comp_snd
    refine (h1.aestronglyMeasurable.mul h2).congr ?_
    filter_upwards with p
    simp only [Function.uncurry, Pi.mul_apply, mul_assoc]
  · filter_upwards [(Measure.quasiMeasurePreserving_snd).ae hsupp] with p hp
    by_cases h0 : ω p.2 = 0
    · simp [Function.uncurry, h0]
    · have hdist := le_norm_circleMap_sub hr (fun h => h0 (hp h)) p.1
      have hK : ‖biotSavartKernel (circleMap 0 r p.1 - p.2)‖ ≤ (2 * π * δ)⁻¹ := by
        rw [norm_biotSavartKernel_eq]
        gcongr
      simp only [Function.uncurry, norm_mul, Complex.norm_conj, deriv_circleMap,
        norm_circleMap_zero, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
        mul_one]
      rw [mul_assoc]
      gcongr

/-- The circle integrand of `conj (K ⋆ ω)` is integrable, and its integral is `∫_{B_r} ω`. -/
private lemma velocity_circle_aux {ω : ℂ → ℝ} (hω : Integrable ω) {r δ : ℝ} (hr : 0 < r)
    (hδ : 0 < δ) (hsupp : ∀ᵐ y, ‖y‖ ∈ Ioo (r - δ) (r + δ) → ω y = 0) :
    IntervalIntegrable (fun θ => deriv (circleMap 0 r) θ • conj (velocity ω (circleMap 0 r θ)))
        volume 0 (2 * π) ∧
      ∫ θ in (0 : ℝ)..2 * π, deriv (circleMap 0 r) θ • conj (velocity ω (circleMap 0 r θ)) =
        ((∫ y in ball (0 : ℂ) r, ω y : ℝ) : ℂ) := by
  have hint := integrable_circIntegrand hω hr hδ hsupp
  simp_rw [deriv_smul_conj_velocity]
  refine ⟨?_, ?_⟩
  · rw [intervalIntegrable_iff]
    exact hint.integral_prod_left
  · rw [intervalIntegral_integral_swap hint]
    have hpt : ∀ᵐ y, (∫ θ in (0 : ℝ)..2 * π, deriv (circleMap 0 r) θ *
        (conj (biotSavartKernel (circleMap 0 r θ - y)) * (ω y : ℂ))) =
        (((ball (0 : ℂ) r).indicator ω y : ℝ) : ℂ) := by
      filter_upwards [hsupp] with y hy
      by_cases h0 : ω y = 0
      · simp [h0, indicator]
      · have hyr : ‖y‖ ≠ r := fun h => h0 (hy (by rw [h]; constructor <;> linarith))
        have hc := circleIntegral_conj_biotSavartKernel_sub hr hyr
        rw [circleIntegral] at hc
        simp only [smul_eq_mul] at hc
        simp_rw [← mul_assoc]
        rw [intervalIntegral.integral_mul_const, hc]
        simp only [indicator, mem_ball, dist_zero_right]
        split_ifs <;> simp
    rw [integral_congr_ae hpt, integral_complex_ofReal, integral_indicator measurableSet_ball]

/-- Complex circulation of `K ⋆ ω` around `C_r`, for `ω` vanishing near `C_r`. -/
theorem circleIntegral_conj_velocity {ω : ℂ → ℝ} (hω : Integrable ω) {r δ : ℝ} (hr : 0 < r)
    (hδ : 0 < δ) (hsupp : ∀ᵐ y, ‖y‖ ∈ Ioo (r - δ) (r + δ) → ω y = 0) :
    (∮ z in C(0, r), conj (velocity ω z)) = ((∫ y in ball (0 : ℂ) r, ω y : ℝ) : ℂ) := by
  rw [circleIntegral]
  exact (velocity_circle_aux hω hr hδ hsupp).2

/-- The flux of `K ⋆ ω` through `C_r` vanishes, for `ω` vanishing near `C_r`. -/
theorem integral_inner_velocity_radial {ω : ℂ → ℝ} (hω : Integrable ω) {r δ : ℝ} (hr : 0 < r)
    (hδ : 0 < δ) (hsupp : ∀ᵐ y, ‖y‖ ∈ Ioo (r - δ) (r + δ) → ω y = 0) :
    ∫ θ in (0 : ℝ)..2 * π,
      inner ℝ (velocity ω (circleMap 0 r θ)) (Complex.exp (θ * Complex.I)) = 0 :=
  (real_forms_of_circle hr (fun θ => velocity ω (circleMap 0 r θ)) _
    (velocity_circle_aux hω hr hδ hsupp).1 (velocity_circle_aux hω hr hδ hsupp).2).2

/-- The circulation of `K ⋆ ω` around `C_r` is `∫_{B_r} ω`, for `ω` vanishing near `C_r`. -/
theorem integral_inner_velocity_tangential {ω : ℂ → ℝ} (hω : Integrable ω) {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (hsupp : ∀ᵐ y, ‖y‖ ∈ Ioo (r - δ) (r + δ) → ω y = 0) :
    r * ∫ θ in (0 : ℝ)..2 * π,
      inner ℝ (velocity ω (circleMap 0 r θ)) (Complex.I * Complex.exp (θ * Complex.I)) =
      ∫ y in ball (0 : ℂ) r, ω y :=
  (real_forms_of_circle hr (fun θ => velocity ω (circleMap 0 r θ)) _
    (velocity_circle_aux hω hr hδ hsupp).1 (velocity_circle_aux hω hr hδ hsupp).2).1

end NonUniqueEuler.Multipole
