import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.I.Infra.Sobolev.Smooth
import NonUniqueEuler.I.Infra.Polar.RadialDeriv
import NonUniqueEuler.H.Sec8.Coupling.Bridge

/-!
# Helper for `lem:coupling`(1): `ℓ_*(G)(-h·∇Φ) = p_3 β(G)` from the sector-`3` profile of `h·e_r`

Helper of `P/Sec8/Coupling.lean` (fully proved, modulo the interface files it imports).
Manuscript `08_kick.tex:86-110`: "Since `Φ` is radial, `h·∇Φ = Φ'(r) h·e_r`, and `Φ'` vanishes
outside `[a,1]`. Hence the sector-`3` profile of `-h·∇Φ` is `-(i/2)p_3r^{-4}Φ'(r) = p_3 b(r)` …
`ℓ_*(G_k)(w) = n_*(G_k)ℓ_*(w_3)` depends linearly on the sector-`3` profile `w_3` of `w` only, and
`β(G_k) = ℓ_*(G_k)(b e^{3iθ}) = n_*(G_k)ℓ_*(b)`."

* `ringPhi_eq_omR`, `hasFDerivAt_ringPhi`: `Φ(x) = Φ(|x|)` and `DΦ(x) = (Φ'(|x|)/|x|)⟨x, ·⟩`;
* `forcing_ae_eq`: `-h·∇Φ = -Φ'(|x|) (h·e_r)` a.e. (the weak partials of `Φ` are classical a.e.);
* `angularSector_neg_radial_mul`, `angularSector_ofProfile`: two pointwise sector computations;
* `ellFn_forcing`: if the sector-`3` profile of `h·e_r` is `(i/2)p r^{-4}` on `[a/4,3]`, then
  `ℓ_*(G)(-h·∇Φ) = p β(G)`.
-/

noncomputable section

open MeasureTheory Set Real Filter
open scoped ContDiff

namespace NonUniqueEuler.CouplingAux

open Sect Sob RingData OneRing

/-- `Φ(x) = Φ(|x|)` (`Φ` radial). -/
theorem ringPhi_eq_omR {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (x : ℂ) :
    ringPhi χ x = (ringPhiSetting χ).omR ‖x‖ := by
  have hrad := (ringPhiSetting_valid hχ).radial
  have h := hrad (Complex.arg x) ((‖x‖ : ℝ) : ℂ)
  have hx : rot (Complex.arg x) ((‖x‖ : ℝ) : ℂ) = x := by
    simp only [rot]
    rw [mul_comm]
    exact Complex.norm_mul_exp_arg_mul_I x
  rw [hx] at h
  exact h

/-- The derivative of the radial ring `Φ` at `x ≠ 0`: `DΦ(x) = (Φ'(|x|)/|x|)⟨x, ·⟩`. -/
theorem hasFDerivAt_ringPhi {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {x : ℂ} (hx : x ≠ 0) :
    HasFDerivAt (ringPhi χ)
      (((ringPhiSetting χ).dom ‖x‖ / ‖x‖) • innerSL ℝ x) x := by
  have hv := ringPhiSetting_valid hχ
  have hsm : ContDiff ℝ ∞ (ringPhiSetting χ).om := hv.contDiff
  have hR : Differentiable ℝ (ringPhiSetting χ).omR := by
    have : (ringPhiSetting χ).omR = (ringPhiSetting χ).om ∘ Complex.ofRealCLM := rfl
    rw [this]
    exact (hsm.differentiable (by simp)).comp Complex.ofRealCLM.differentiable
  have hd : HasDerivAt (ringPhiSetting χ).omR ((ringPhiSetting χ).dom ‖x‖) ‖x‖ :=
    (hR ‖x‖).hasDerivAt
  have h := Polar.hasFDerivAt_comp_norm hx hd
  have heq : (fun y : ℂ => (ringPhiSetting χ).omR ‖y‖) = ringPhi χ := by
    funext y; exact (ringPhi_eq_omR hχ y).symm
  rwa [heq] at h

/-- The complexified derivative of a differentiable real function. -/
theorem fderiv_ofReal_apply' {φ : ℂ → ℝ} {x : ℂ} (hφ : DifferentiableAt ℝ φ x) (v : ℂ) :
    fderiv ℝ (fun y => ((φ y : ℝ) : ℂ)) x v = ((fderiv ℝ φ x v : ℝ) : ℂ) := by
  have h := (Complex.ofRealCLM.hasFDerivAt (x := φ x)).comp x hφ.hasFDerivAt
  rw [show (fun y => ((φ y : ℝ) : ℂ)) = Complex.ofRealCLM ∘ φ from rfl, h.fderiv]
  rfl

/-- The radial component `h·e_r = |x|⁻¹ (Re h x₁ + Im h x₂)`. -/
theorem radComp_eq (h : ℂ → ℂ) (x : ℂ) :
    radComp h x = ‖x‖⁻¹ * ((h x).re * x.re + (h x).im * x.im) := by
  have hc : (starRingEnd ℂ) (((‖x‖ : ℝ) : ℂ)⁻¹ * x) = ((‖x‖⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ) x := by
    rw [map_mul, map_inv₀, Complex.conj_ofReal, Complex.ofReal_inv]
  simp only [radComp, hc, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im]
  ring

/-- **The forcing in classical form**: `-h·∇Φ = -Φ'(|x|)(h·e_r)` almost everywhere. -/
theorem forcing_ae_eq {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (h : ℂ → ℂ) :
    (fun x => -Eig.hGradPhi χ h x) =ᵐ[volume]
      fun x => -(((ringPhiSetting χ).dom ‖x‖ * radComp h x : ℝ) : ℂ) := by
  obtain ⟨hsmooth, hcpt, -⟩ := ringFacts_of_admissible hχ
  have hC : ContDiff ℝ ∞ (PhiC χ) := Complex.ofRealCLM.contDiff.comp hsmooth
  have hcC : HasCompactSupport (PhiC χ) := hcpt.comp_left Complex.ofReal_zero
  have hW := (memH_of_contDiff_hasCompactSupport hC hcC 1).2.1
  have hdiff : ∀ x, DifferentiableAt ℝ (ringPhi χ) x := fun x =>
    (hsmooth.differentiable (by simp)) x
  have h10 : (1, 0) ∈ multiIdx 1 := by decide
  have h01 : (0, 1) ∈ multiIdx 1 := by decide
  filter_upwards [hW (1, 0) h10, hW (0, 1) h01, (volume : Measure ℂ).ae_ne 0] with x hx1 hx2 hx0
  have e1 : weakPartial (1, 0) (PhiC χ) x = ((fderiv ℝ (ringPhi χ) x (1 : ℂ) : ℝ) : ℂ) := by
    rw [hx1]
    show fderiv ℝ (fun y => ((ringPhi χ y : ℝ) : ℂ)) x (1 : ℂ) = _
    exact fderiv_ofReal_apply' (hdiff x) 1
  have e2 : weakPartial (0, 1) (PhiC χ) x = ((fderiv ℝ (ringPhi χ) x Complex.I : ℝ) : ℂ) := by
    rw [hx2]
    show fderiv ℝ (fun y => ((ringPhi χ y : ℝ) : ℂ)) x Complex.I = _
    exact fderiv_ofReal_apply' (hdiff x) Complex.I
  have hF := (hasFDerivAt_ringPhi hχ hx0).fderiv
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx0
  rw [← hGrad_PhiC]
  simp only [hGrad, Sob.dotGrad]
  rw [e1, e2, hF, radComp_eq]
  simp only [_root_.smul_apply, innerSL_apply_apply, smul_eq_mul,
    Complex.inner, Complex.one_re, Complex.I_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.one_im, Complex.I_im]
  push_cast
  field_simp
  ring

/-- On the circle `|x| = r`, a radial factor comes out of the angular sector. -/
theorem angularSector_neg_radial_mul (f₀ : ℝ → ℝ) (g : ℂ → ℝ) (ℓ : ℤ) {r : ℝ} (hr : 0 ≤ r) :
    Polar.angularSector (fun x => -((f₀ ‖x‖ * g x : ℝ) : ℂ)) ℓ r =
      -(f₀ r : ℂ) * Polar.angularSector (fun x => ((g x : ℝ) : ℂ)) ℓ r := by
  unfold Polar.angularSector
  have hn : ∀ θ : ℝ, ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = r := by
    intro θ
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr]
  have hpt : ∀ θ : ℝ,
      -((f₀ ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ *
          g ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) : ℝ) : ℂ) *
        Complex.exp (-((ℓ : ℂ) * θ * Complex.I)) =
      -(f₀ r : ℂ) * (((g ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) : ℝ) : ℂ) *
        Complex.exp (-((ℓ : ℂ) * θ * Complex.I))) := by
    intro θ
    rw [hn]
    push_cast
    ring
  simp_rw [hpt, intervalIntegral.integral_const_mul]
  ring

/-- The angular sector `ℓ` of the sector function `b(|x|)e^{iℓθ}` is `b` (for `r > 0`). -/
theorem angularSector_ofProfile (ℓ : ℤ) (b : ℝ → ℂ) {r : ℝ} (hr : 0 < r) :
    Polar.angularSector (Ang.ofProfile ℓ b) ℓ r = b r := by
  unfold Polar.angularSector Ang.ofProfile Ang.angPhase
  have hn : ∀ θ : ℝ, ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = r := by
    intro θ
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr]
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  have hpt : ∀ θ : ℝ,
      b ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ *
          (((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) /
            ((‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ : ℝ) : ℂ)) ^ ℓ *
        Complex.exp (-((ℓ : ℂ) * θ * Complex.I)) = b r := by
    intro θ
    rw [hn, mul_div_cancel_left₀ _ hr0, ← Complex.exp_int_mul, mul_assoc, ← Complex.exp_add]
    have : (ℓ : ℂ) * ((θ : ℂ) * Complex.I) + -((ℓ : ℂ) * θ * Complex.I) = 0 := by ring
    rw [this, Complex.exp_zero, mul_one]
  simp_rw [hpt]
  rw [intervalIntegral.integral_const]
  have hπ : (2 * π : ℂ) ≠ 0 := by
    have := Real.pi_pos
    exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  simp only [sub_zero, Complex.real_smul]
  push_cast
  field_simp

/-- `ℓ_*` on profiles only sees the profile on `(0, ∞)`. -/
theorem ellStar_congr (S : SectorSetting) (ℓ : ℕ) (z : ℂ) (G : ℝ) {g g' : ℝ → ℂ}
    (h : ∀ r ∈ Ioi (0 : ℝ), g r = g' r) : S.ellStar ℓ z G g = S.ellStar ℓ z G g' := by
  unfold SectorSetting.ellStar
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi fun r hr => by rw [h r hr]

/-- `ℓ_*` on profiles is homogeneous. -/
theorem ellStar_const_mul (S : SectorSetting) (ℓ : ℕ) (z : ℂ) (G : ℝ) (p : ℂ) (g : ℝ → ℂ) :
    S.ellStar ℓ z G (fun r => p * g r) = p * S.ellStar ℓ z G g := by
  unfold SectorSetting.ellStar
  simp only [mul_assoc]
  rw [integral_const_mul]
  ring

/-- `[a,1] ⊆ [a/4,3]`. -/
theorem Icc_a_one_subset : Icc a 1 ⊆ Icc (a / 4) 3 := by
  have ha : 0 < a := Real.exp_pos _
  intro r hr
  exact ⟨by linarith [hr.1], by linarith [hr.2]⟩

/-- **`ℓ_*(G)(-h·∇Φ) = p β(G)`** (`08_kick.tex:86-110`) if the sector-`3` profile of `h·e_r` is
`(i/2) p r^{-4}` on `[a/4,3]`. -/
theorem ellFn_forcing {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (G : ℝ) {h : ℂ → ℂ} {p : ℂ}
    (hprof : ∀ r ∈ Icc (a / 4) 3,
      Polar.angularSector (fun y => ((radComp h y : ℝ) : ℂ)) 3 r =
        Complex.I / 2 * p * (r : ℂ) ^ (-4 : ℤ)) :
    Eig.ellFn χ G (fun x => -Eig.hGradPhi χ h x) = p * Eig.beta χ G := by
  have hv := ringPhiSetting_valid hχ
  rw [ellFn_congr_ae χ G (forcing_ae_eq hχ h)]
  -- the sector-`3` profile of the classical forcing is `p b(r)` on `(0, ∞)`
  have hsec : ∀ r ∈ Ioi (0 : ℝ),
      Polar.angularSector (fun x => -(((ringPhiSetting χ).dom ‖x‖ * radComp h x : ℝ) : ℂ)) 3 r =
        p * Eig.bprof χ r := by
    intro r hr
    have hr0 : (0 : ℝ) < r := hr
    rw [angularSector_neg_radial_mul _ _ _ hr0.le]
    simp only [Eig.bprof, SectorSetting.bfun]
    by_cases hmem : r ∈ Icc (a / 4) 3
    · rw [hprof r hmem]
      norm_num
      ring
    · have hd : (ringPhiSetting χ).dom r = 0 :=
        hv.dom_eq_zero r hr0 fun h' => hmem (Icc_a_one_subset h')
      rw [hd]
      simp
  have hsecb : ∀ r ∈ Ioi (0 : ℝ),
      Polar.angularSector (Ang.ofProfile 3 (Eig.bprof χ)) 3 r = Eig.bprof χ r :=
    fun r hr => angularSector_ofProfile 3 _ hr
  unfold Eig.beta Eig.ellFn
  rw [ellStar_congr _ _ _ _ hsec, ellStar_const_mul, ellStar_congr _ _ _ _ hsecb]
  ring

end NonUniqueEuler.CouplingAux
