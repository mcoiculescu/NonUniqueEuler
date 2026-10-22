import NonUniqueEuler.Defs.Sec4.Evans
import NonUniqueEuler.I.Infra.Polar.RadialDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Helper for `lem:adjoint`(4): the sector-`ℓ` part of `-h·∇ω̄` for the multipole field `h`

Helper of `P/Sec4/Adjoint.lean` (`04_ring.tex:640-644`). Write `c = -m/(2ℓ)`. Then
* the stream function is `2 Re(c̄ x^{-ℓ})` (`multipoleStream_eq`; `r^{-ℓ}e^{iℓθ} = conj(x)^{-ℓ}`);
* its gradient is computed from the complex derivative of `c̄ x^{-ℓ}`, and
  `h = ∇^⊥ψ = 2i conj(F')` with `F' = c̄(-ℓ)x^{-ℓ-1}` (`multipoleField_eq`);
* `∇ω̄ = ω̄'(r) x/|x|` (radial), so `Dω̄(x)h(x) = (ω̄'/r) i((m/2) conj(x^{-ℓ}) - (m̄/2)x^{-ℓ})`
  (`fderiv_om_field`);
* in polar coordinates `x = re^{iθ}` this is `(ω̄'/r) r^{-ℓ} i((m/2)e^{iℓθ} - (m̄/2)e^{-iℓθ})`,
  whose sector-`ℓ` coefficient is `(i/2) m r^{-ℓ-1} ω̄'`; so the sector-`ℓ` profile of `-h·∇ω̄`
  is `m b(r)` (`angularSector_forcing`).
-/

noncomputable section

open MeasureTheory Set Filter Topology ComplexConjugate
open scoped ContDiff

namespace NonUniqueEuler.AdjointAux

open SectorSetting

/-- `ω̄(x) = ω̄(|x|)` for a radial `ω̄`. -/
theorem om_eq_omR (S : SectorSetting) (hS : S.Valid) (x : ℂ) : S.om x = S.omR ‖x‖ := by
  have h := hS.radial (Complex.arg x) ((‖x‖ : ℝ) : ℂ)
  have hx : rot (Complex.arg x) ((‖x‖ : ℝ) : ℂ) = x := by
    rw [rot, mul_comm]
    exact Complex.norm_mul_exp_arg_mul_I x
  rw [hx] at h
  rw [h]
  rfl

theorem hasDerivAt_omR (S : SectorSetting) (hS : S.Valid) (r : ℝ) :
    HasDerivAt S.omR (S.dom r) r := by
  have hom : Differentiable ℝ S.om := hS.contDiff.differentiable (by simp)
  have h : DifferentiableAt ℝ S.omR r :=
    (hom (r : ℂ)).comp r Complex.ofRealCLM.differentiableAt
  exact h.hasDerivAt

/-- `Dω̄(x)v = (ω̄'(|x|)/|x|) Re(v x̄)` for `x ≠ 0`. -/
theorem fderiv_om_apply (S : SectorSetting) (hS : S.Valid) {x : ℂ} (hx : x ≠ 0) (v : ℂ) :
    fderiv ℝ S.om x v = S.dom ‖x‖ / ‖x‖ * (v * conj x).re := by
  have hfun : S.om = fun y => S.omR ‖y‖ := funext (om_eq_omR S hS)
  have h := Polar.hasFDerivAt_comp_norm hx (hasDerivAt_omR S hS ‖x‖)
  rw [hfun, h.fderiv]
  simp [innerSL_apply_apply, Complex.inner]

/-- The derivative `F'(x) = c̄(-ℓ)x^{-ℓ-1}` of `F(x) = c̄ x^{-ℓ}`, `c = -m/(2ℓ)`. -/
def dF (ℓ : ℕ) (m x : ℂ) : ℂ :=
  conj (-(m / (2 * (ℓ : ℂ)))) * (((-(ℓ : ℤ) : ℤ) : ℂ) * x ^ (-(ℓ : ℤ) - 1))

theorem zero_zpow_neg (ℓ : ℕ) (hℓ : 1 ≤ ℓ) : (0 : ℂ) ^ (-(ℓ : ℤ)) = 0 := by
  rw [zpow_neg, zpow_natCast, zero_pow (by omega), inv_zero]

/-- `-(m/2ℓ) r^{-ℓ}e^{iℓθ} + c.c. = 2 Re(c̄ x^{-ℓ})`. -/
theorem multipoleStream_eq (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (m : ℂ) :
    multipoleStream ℓ m = fun x => 2 * (conj (-(m / (2 * (ℓ : ℂ)))) * x ^ (-(ℓ : ℤ))).re := by
  funext x
  simp only [multipoleStream]
  congr 1
  by_cases hx : x = 0
  · subst hx
    simp [zero_zpow_neg ℓ hℓ]
  · rw [← Complex.conj_re]
    congr 1
    have hn : ((‖x‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hx
    have hmc : x * conj x = ((‖x‖ : ℝ) : ℂ) * ((‖x‖ : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    simp only [Ang.angPhase, zpow_neg, zpow_natCast, map_mul, map_inv₀, map_pow, map_div₀,
      Complex.conj_ofReal]
    congr 1
    have hcx : conj x ≠ 0 := (map_ne_zero _).2 hx
    calc (((‖x‖ : ℝ) : ℂ) ^ ℓ)⁻¹ * (conj x / ((‖x‖ : ℝ) : ℂ)) ^ ℓ
        = (conj x / (((‖x‖ : ℝ) : ℂ) * ((‖x‖ : ℝ) : ℂ))) ^ ℓ := by ring
      _ = (conj x / (x * conj x)) ^ ℓ := by rw [hmc]
      _ = (x ^ ℓ)⁻¹ := by
        rw [← inv_pow]
        congr 1
        field_simp

theorem fderiv_multipoleStream_apply (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (m : ℂ) {x : ℂ} (hx : x ≠ 0)
    (v : ℂ) : fderiv ℝ (multipoleStream ℓ m) x v = 2 * (v * dF ℓ m x).re := by
  have hF : HasDerivAt (fun y : ℂ => conj (-(m / (2 * (ℓ : ℂ)))) * y ^ (-(ℓ : ℤ))) (dF ℓ m x) x :=
    (hasDerivAt_zpow (-(ℓ : ℤ)) x (Or.inl hx)).const_mul _
  have hR := (Complex.reCLM.hasFDerivAt.comp x (hF.hasFDerivAt.restrictScalars ℝ)).const_mul
    (2 : ℝ)
  have h2 : HasFDerivAt (fun y : ℂ => 2 * (conj (-(m / (2 * (ℓ : ℂ)))) * y ^ (-(ℓ : ℤ))).re) _ x :=
    hR
  rw [multipoleStream_eq ℓ hℓ m, h2.fderiv]
  simp

/-- `h = ∇^⊥ψ = 2i conj(F'(x))` for `x ≠ 0`. -/
theorem multipoleField_eq (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (m : ℂ) {x : ℂ} (hx : x ≠ 0) :
    multipoleField ℓ m x = 2 * Complex.I * conj (dF ℓ m x) := by
  simp only [multipoleField, perpGrad]
  rw [fderiv_multipoleStream_apply ℓ hℓ m hx 1, fderiv_multipoleStream_apply ℓ hℓ m hx Complex.I]
  apply Complex.ext <;> simp

/-- `Dω̄(x)h(x) = (ω̄'(r)/r) i((m/2) conj(x^{-ℓ}) - (m̄/2) x^{-ℓ})` for `x ≠ 0`. -/
theorem fderiv_om_field (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (m : ℂ)
    {x : ℂ} (hx : x ≠ 0) :
    ((fderiv ℝ S.om x (multipoleField ℓ m x) : ℝ) : ℂ) =
      ((S.dom ‖x‖ / ‖x‖ : ℝ) : ℂ) * (Complex.I * (m / 2 * conj (x ^ (-(ℓ : ℤ))) -
        conj m / 2 * x ^ (-(ℓ : ℤ)))) := by
  have hℓC : (ℓ : ℂ) ≠ 0 := by exact_mod_cast (show ℓ ≠ 0 by omega)
  have hq : x ^ (-(ℓ : ℤ) - 1) * x = x ^ (-(ℓ : ℤ)) := by
    rw [zpow_sub_one₀ hx, mul_assoc, inv_mul_cancel₀ hx, mul_one]
  have hdx : dF ℓ m x * x = conj m / 2 * x ^ (-(ℓ : ℤ)) := by
    simp only [dF, map_neg, map_div₀, map_mul, map_ofNat, Complex.conj_natCast]
    rw [mul_assoc, mul_assoc, hq]
    push_cast
    field_simp
  have hw : multipoleField ℓ m x * conj x = Complex.I * m * conj (x ^ (-(ℓ : ℤ))) := by
    rw [multipoleField_eq ℓ hℓ m hx, mul_assoc, ← map_mul, hdx]
    simp only [map_mul, map_div₀, map_ofNat, Complex.conj_conj]
    ring
  rw [fderiv_om_apply S hS hx, hw]
  push_cast
  rw [Complex.re_eq_add_conj]
  simp only [map_mul, Complex.conj_I, Complex.conj_conj]
  ring

/-- The integrand of the sector-`ℓ` coefficient of `-h·∇ω̄` at `x = re^{iθ}`. -/
theorem forcing_integrand (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (m : ℂ)
    {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    -((fderiv ℝ S.om ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
          (multipoleField ℓ m ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) : ℝ) : ℂ) *
        Complex.exp (-((((ℓ : ℤ) : ℂ)) * θ * Complex.I)) =
      -((S.dom r / r : ℝ) : ℂ) * Complex.I * ((r : ℂ) ^ ℓ)⁻¹ * (m / 2) +
        ((S.dom r / r : ℝ) : ℂ) * Complex.I * ((r : ℂ) ^ ℓ)⁻¹ * (conj m / 2) *
          Complex.exp ((-(2 * (ℓ : ℂ)) * Complex.I) * θ) := by
  set e : ℂ := Complex.exp ((θ : ℂ) * Complex.I) with he_def
  have he : ‖e‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have he0 : e ≠ 0 := Complex.exp_ne_zero _
  have hconj : conj e = e⁻¹ := by
    rw [he_def, ← Complex.exp_conj, ← Complex.exp_neg]
    congr 1
    simp [Complex.conj_ofReal]
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hx : (r : ℂ) * e ≠ 0 := mul_ne_zero hr0 he0
  have hxn : ‖(r : ℂ) * e‖ = r := by
    rw [norm_mul, he, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  rw [fderiv_om_field S hS ℓ hℓ m hx, hxn]
  have hq : ((r : ℂ) * e) ^ (-(ℓ : ℤ)) = ((r : ℂ) ^ ℓ)⁻¹ * (e ^ ℓ)⁻¹ := by
    rw [mul_zpow, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
  have hcq : conj (((r : ℂ) * e) ^ (-(ℓ : ℤ))) = ((r : ℂ) ^ ℓ)⁻¹ * e ^ ℓ := by
    rw [hq, map_mul, map_inv₀, map_inv₀, map_pow, map_pow, Complex.conj_ofReal, hconj, inv_pow,
      inv_inv]
  have hexp1 : Complex.exp (-((((ℓ : ℤ) : ℂ)) * θ * Complex.I)) = (e ^ ℓ)⁻¹ := by
    rw [Complex.exp_neg, Int.cast_natCast, mul_assoc, Complex.exp_nat_mul]
  have hexp2 : Complex.exp ((-(2 * (ℓ : ℂ)) * Complex.I) * θ) = ((e ^ ℓ)⁻¹) ^ 2 := by
    rw [← inv_pow, ← pow_mul, he_def, ← Complex.exp_neg, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hcq, hq, hexp1, hexp2]
  have hel : e ^ ℓ ≠ 0 := pow_ne_zero _ he0
  have hrl : (r : ℂ) ^ ℓ ≠ 0 := pow_ne_zero _ hr0
  field_simp
  ring

/-- `lem:adjoint`(4): the sector-`ℓ` profile of `-h·∇ω̄` is `m b(r)` (`r > 0`). -/
theorem angularSector_forcing (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (m : ℂ)
    {r : ℝ} (hr : 0 < r) :
    Polar.angularSector (fun x => -((fderiv ℝ S.om x (multipoleField ℓ m x) : ℝ) : ℂ)) ℓ r =
      m * S.bfun ℓ r := by
  set A : ℂ := -((S.dom r / r : ℝ) : ℂ) * Complex.I * ((r : ℂ) ^ ℓ)⁻¹ * (m / 2) with hA
  set B : ℂ := ((S.dom r / r : ℝ) : ℂ) * Complex.I * ((r : ℂ) ^ ℓ)⁻¹ * (conj m / 2) with hB
  set c : ℂ := -(2 * (ℓ : ℂ)) * Complex.I with hc
  have hℓC : (ℓ : ℂ) ≠ 0 := by exact_mod_cast (show ℓ ≠ 0 by omega)
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact mul_ne_zero (neg_ne_zero.2 (mul_ne_zero two_ne_zero hℓC)) Complex.I_ne_zero
  simp only [Polar.angularSector]
  rw [intervalIntegral.integral_congr (g := fun θ : ℝ => A + B * Complex.exp (c * θ))
    (fun θ _ => forcing_integrand S hS ℓ hℓ m hr θ)]
  have hcont : Continuous fun θ : ℝ => B * Complex.exp (c * θ) := by fun_prop
  rw [intervalIntegral.integral_add intervalIntegrable_const (hcont.intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    integral_exp_mul_complex hc0]
  have he1 : Complex.exp (c * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
    have : c * ((2 * Real.pi : ℝ) : ℂ) = ((-(2 * (ℓ : ℤ)) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      rw [hc]
      push_cast
      ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  have he0 : Complex.exp (c * ((0 : ℝ) : ℂ)) = 1 := by simp
  rw [he1, he0, sub_self, zero_div, mul_zero, add_zero, sub_zero, Complex.real_smul]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [hA, bfun, zpow_sub_one₀ hr0, zpow_neg, zpow_natCast]
  push_cast
  field_simp

end NonUniqueEuler.AdjointAux
