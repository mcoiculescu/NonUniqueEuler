import NonUniqueEuler.Defs.Sec5.Config
import NonUniqueEuler.Defs.Sec2.Multipole
import NonUniqueEuler.I.Infra.Multipole.StreamFunction
import NonUniqueEuler.I.Infra.Multipole.LogPotential
import NonUniqueEuler.I.Infra.Polar.RadialDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Proof: the exterior sector-`m` profile of the radial velocity `(K_BS * ν)·e_r`

Proof of `I/Sec8/Coupling/RadialSector.lean` (`08_kick.tex:66-86`, proof of `lem:coupling`(1)).

1. `ψ = logPotentialReal ν` is smooth on `U = {|z| > ρ}` and `Dψ(z)v = ⟨-i(K*ν)(z), v⟩` there
   (`I/Infra/Multipole/StreamFunction.lean`); hence `(K*ν)·e_r = -|z|⁻¹ Dψ(z)(iz)`
   (`RadialSectorAux.radComp_eq_neg_inner`).
2. On the circle `|z| = r`, `θ ↦ ψ(re^{iθ})` has derivative `Dψ(re^{iθ})(i re^{iθ})`
   (`Polar.hasDerivAt_angular`); integration by parts against `e^{-imθ}` on `[0, 2π]`
   (`RadialSectorAux.integral_deriv_mul_exp`) gives `sector_m(∂_θψ) = i m · sector_m(ψ)`.
3. `sector_m(ψ)(r) = -(2m)⁻¹ pout_m[ν] r^{-m}` (`Multipole.angularSector_logPotential_exterior_pos`).
4. Combine.
-/

noncomputable section

open MeasureTheory Set Metric Real ComplexConjugate

namespace NonUniqueEuler

namespace Kick

namespace RadialSectorAux

/-- The radial component as an inner product with the angular direction:
`h·e_r = -|z|⁻¹ ⟨-i h(z), i z⟩`. -/
theorem radComp_eq_neg_inner (h : ℂ → ℂ) (z : ℂ) :
    OneRing.radComp h z =
      -‖z‖⁻¹ * inner ℝ (-(Complex.I * h z)) (Complex.I * z) := by
  rw [OneRing.radComp, Complex.inner, ← Complex.ofReal_inv]
  simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
  rw [show h z * ((((‖z‖)⁻¹ : ℝ) : ℂ) * conj z) = (((‖z‖)⁻¹ : ℝ) : ℂ) * (h z * conj z) by ring,
    Complex.re_ofReal_mul]
  have : Complex.I * z * -(-Complex.I * conj (h z)) = -(z * conj (h z)) := by
    rw [neg_mul, neg_neg, mul_mul_mul_comm, Complex.I_mul_I]; ring
  rw [this, Complex.neg_re]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- Integration by parts on `[0, 2π]` for a `2π`-periodic `C¹` function against `e^{-iℓθ}`:
`∫₀^{2π} f'(θ) e^{-iℓθ} dθ = iℓ ∫₀^{2π} f(θ) e^{-iℓθ} dθ`. -/
theorem integral_deriv_mul_exp {f f' : ℝ → ℝ} (hf : ∀ θ, HasDerivAt f (f' θ) θ)
    (hf' : Continuous f') (hper : f (2 * π) = f 0) (ℓ : ℤ) :
    ∫ θ in (0 : ℝ)..2 * π, (f' θ : ℂ) * Complex.exp (-((ℓ : ℂ) * θ * Complex.I)) =
      (ℓ : ℂ) * Complex.I *
        ∫ θ in (0 : ℝ)..2 * π, (f θ : ℂ) * Complex.exp (-((ℓ : ℂ) * θ * Complex.I)) := by
  set e : ℝ → ℂ := fun θ => Complex.exp (-((ℓ : ℂ) * θ * Complex.I)) with he
  have hv : ∀ θ : ℝ, HasDerivAt e (e θ * (-((ℓ : ℂ) * Complex.I))) θ := by
    intro θ
    have h1 : HasDerivAt (fun s : ℝ => -((ℓ : ℂ) * s * Complex.I)) (-((ℓ : ℂ) * Complex.I)) θ := by
      have h0 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 θ := by
        simpa only [id, Complex.ofReal_one] using (hasDerivAt_id θ).ofReal_comp
      have h2 := h0.const_mul (-((ℓ : ℂ) * Complex.I))
      rw [mul_one] at h2
      have hfun : (fun s : ℝ => -((ℓ : ℂ) * s * Complex.I)) =
          fun s : ℝ => -((ℓ : ℂ) * Complex.I) * s := by
        funext s; ring
      rw [hfun]
      exact h2
    exact h1.cexp
  have hu : ∀ θ : ℝ, HasDerivAt (fun s : ℝ => (f s : ℂ)) (f' θ : ℂ) θ :=
    fun θ => (hf θ).ofReal_comp
  have hec : Continuous e := by
    simp only [he]; fun_prop
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 2 * π)
    (fun θ _ => hu θ) (fun θ _ => hv θ)
    ((Complex.continuous_ofReal.comp hf').intervalIntegrable _ _)
    ((hec.mul continuous_const).intervalIntegrable _ _)
  have he0 : e 0 = 1 := by simp [he]
  have he2 : e (2 * π) = 1 := by
    simp only [he]
    rw [show -((ℓ : ℂ) * ((2 * π : ℝ) : ℂ) * Complex.I) = ((-ℓ : ℤ) : ℂ) * (2 * π * Complex.I) by
      push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [he0, he2, hper] at hibp
  have hL : ∫ θ in (0 : ℝ)..2 * π, (f θ : ℂ) * (e θ * -((ℓ : ℂ) * Complex.I)) =
      -((ℓ : ℂ) * Complex.I) * ∫ θ in (0 : ℝ)..2 * π, (f θ : ℂ) * e θ := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext θ; ring
  rw [hL] at hibp
  show ∫ θ in (0 : ℝ)..2 * π, (f' θ : ℂ) * e θ = _
  linear_combination hibp

end RadialSectorAux

open RadialSectorAux in
/-- **The exterior sector-`m` profile of `(K_BS * ν)·e_r`** (`08_kick.tex:66-86`): for a real
smooth `ν` vanishing outside `B_ρ`, `m ≥ 1` and `r > ρ`, the angular sector `m` of the radial
velocity is `(i/2) pout_m[ν] r^{-m-1}`. -/
theorem angularSector_radComp_velocity {ν : ℂ → ℝ}
    (hν : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν) {ρ : ℝ} (hρ : 0 < ρ)
    (hsupp : ∀ y : ℂ, ρ ≤ ‖y‖ → ν y = 0) {m : ℕ} (hm : 1 ≤ m) {r : ℝ} (hr : ρ < r) :
    Polar.angularSector (fun y => ((OneRing.radComp (velocity ν) y : ℝ) : ℂ)) m r =
      Complex.I / 2 * BS.pout m (fun y => ((ν y : ℝ) : ℂ)) * (r : ℂ) ^ (-(m : ℤ) - 1) := by
  set V := velocity ν with hV
  set ψ := Multipole.logPotentialReal ν with hψ
  have hr0 : 0 < r := hρ.trans hr
  -- `ν` is integrable (continuous with compact support)
  have hcs : HasCompactSupport ν :=
    HasCompactSupport.intro (isCompact_closedBall 0 ρ) fun y hy => hsupp y (by
      simp only [mem_closedBall, dist_zero_right, not_le] at hy
      exact hy.le)
  have hint : Integrable ν := hν.continuous.integrable_of_hasCompactSupport hcs
  -- the exterior `U = {ρ < |z|}`
  set U : Set ℂ := {z | ρ < ‖z‖} with hUdef
  have hU : IsOpen U := isOpen_lt continuous_const continuous_norm
  have hsep : ∀ z ∈ U, ∃ δ > 0, ∀ᵐ w, w ∈ ball z δ → ν w = 0 := by
    intro z hz
    refine ⟨‖z‖ - ρ, sub_pos.mpr hz, Filter.Eventually.of_forall fun w hw => hsupp w ?_⟩
    rw [mem_ball, dist_eq_norm] at hw
    have := norm_sub_norm_le z w
    rw [norm_sub_rev] at hw
    linarith
  have hR : ∀ᵐ y, ρ < ‖y‖ → ν y = 0 := Filter.Eventually.of_forall fun y hy => hsupp y hy.le
  have hsmooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ U :=
    Multipole.contDiffOn_logPotentialReal hint hU hsep
  have hderiv : ∀ z ∈ U, ∀ v, fderiv ℝ ψ z v = inner ℝ (-(Complex.I * V z)) v := by
    intro z hz v
    obtain ⟨δ, hδ, hδ'⟩ := hsep z hz
    exact Multipole.fderiv_logPotentialReal hint hU hsep hz
      (Multipole.integrable_log_norm_sub_mul_of_vanishing_outside hint hR hδ hδ') v
  have hdiff : ∀ z ∈ U, DifferentiableAt ℝ ψ z := fun z hz =>
    (hsmooth.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hz)
  -- the circle of radius `r`
  have hrot : ∀ θ : ℝ, (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) = rot θ (r : ℂ) :=
    fun θ => mul_comm _ _
  have hnorm : ∀ θ : ℝ, ‖rot θ (r : ℂ)‖ = r := fun θ => by
    rw [Polar.norm_rot, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
  have hcirc : ∀ θ : ℝ, rot θ (r : ℂ) ∈ U := fun θ => by
    show ρ < ‖rot θ (r : ℂ)‖
    rw [hnorm]; exact hr
  set f : ℝ → ℝ := fun θ => ψ (rot θ (r : ℂ)) with hfdef
  set f' : ℝ → ℝ := fun θ => fderiv ℝ ψ (rot θ (r : ℂ)) (Complex.I * rot θ (r : ℂ)) with hf'def
  have hf : ∀ θ, HasDerivAt f (f' θ) θ := fun θ => Polar.hasDerivAt_angular (hdiff _ (hcirc θ))
  have hrotc : Continuous fun θ : ℝ => rot θ (r : ℂ) := by
    simp only [rot]; fun_prop
  have hf'c : Continuous f' := by
    have h1 : ContinuousOn (fderiv ℝ ψ) U := hsmooth.continuousOn_fderiv_of_isOpen hU (by simp)
    have h2 : Continuous fun θ => fderiv ℝ ψ (rot θ (r : ℂ)) := h1.comp_continuous hrotc hcirc
    exact h2.clm_apply (continuous_const.mul hrotc)
  have hper : f (2 * π) = f 0 := by
    simp only [hfdef, rot]
    congr 2
    rw [Complex.ofReal_zero, zero_mul, Complex.exp_zero]
    push_cast
    exact Complex.exp_two_pi_mul_I
  -- the integrand: `(K*ν)·e_r = -r⁻¹ ∂_θψ` on the circle
  have hpt : ∀ θ : ℝ, ((OneRing.radComp V ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) : ℝ) : ℂ)
      = -(r : ℂ)⁻¹ * (f' θ : ℂ) := by
    intro θ
    rw [hrot, radComp_eq_neg_inner, hnorm, ← hderiv _ (hcirc θ)]
    push_cast
    ring
  -- the sector of `ψ`
  have hψsec : Polar.angularSector (fun y => (ψ y : ℂ)) m r =
      -((2 * (m : ℂ))⁻¹ * BS.pout m (fun y => ((ν y : ℝ) : ℂ)) / (r : ℂ) ^ m) := by
    have hfun : (fun y => (ψ y : ℂ)) = Multipole.logPotential (fun y => ((ν y : ℝ) : ℂ)) := by
      funext y; rw [Multipole.logPotential_ofReal]
    rw [hfun, BS.pout_eq_conjMoment]
    exact Multipole.angularSector_logPotential_exterior_pos (hint.ofReal) hρ.le
      (Filter.Eventually.of_forall fun y hy => by simp [hsupp y hy.le]) hm hr
  -- integration by parts
  have hibp := integral_deriv_mul_exp hf hf'c hper (m : ℤ)
  have hS : Polar.angularSector (fun y => (ψ y : ℂ)) m r =
      (2 * π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π,
        (f θ : ℂ) * Complex.exp (-(((m : ℤ) : ℂ) * θ * Complex.I)) := by
    simp only [Polar.angularSector, hfdef, hrot]
  have hL : Polar.angularSector (fun y => ((OneRing.radComp V y : ℝ) : ℂ)) m r =
      (2 * π : ℂ)⁻¹ * (-(r : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π,
        (f' θ : ℂ) * Complex.exp (-(((m : ℤ) : ℂ) * θ * Complex.I))) := by
    simp only [Polar.angularSector, hpt]
    congr 1
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext θ; ring
  set S := ∫ θ in (0 : ℝ)..2 * π, (f θ : ℂ) * Complex.exp (-(((m : ℤ) : ℂ) * θ * Complex.I))
    with hSdef
  set P := BS.pout m (fun y => ((ν y : ℝ) : ℂ)) with hPdef
  have key : (2 * π : ℂ)⁻¹ * S = -((2 * (m : ℂ))⁻¹ * P / (r : ℂ) ^ m) := hS.symm.trans hψsec
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hm)
  have hzpow : (r : ℂ) ^ (-(m : ℤ) - 1) = ((r : ℂ) ^ m)⁻¹ * (r : ℂ)⁻¹ := by
    rw [show -(m : ℤ) - 1 = -((m : ℤ) + 1) by ring, zpow_neg, zpow_add_one₀ hr', zpow_natCast,
      mul_inv]
  rw [hL, hibp, hzpow]
  calc (2 * π : ℂ)⁻¹ * (-(r : ℂ)⁻¹ * (((m : ℤ) : ℂ) * Complex.I * S))
      = -(r : ℂ)⁻¹ * (m : ℂ) * Complex.I * ((2 * π : ℂ)⁻¹ * S) := by push_cast; ring
    _ = -(r : ℂ)⁻¹ * (m : ℂ) * Complex.I * -((2 * (m : ℂ))⁻¹ * P / (r : ℂ) ^ m) := by rw [key]
    _ = Complex.I / 2 * P * (((r : ℂ) ^ m)⁻¹ * (r : ℂ)⁻¹) := by
      field_simp

end Kick

end NonUniqueEuler
