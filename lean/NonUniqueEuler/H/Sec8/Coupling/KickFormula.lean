import NonUniqueEuler.Defs.Sec8.Kick
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Helper for `lem:coupling`(2): the variation-of-constants formula in kick time

Helper of `P/Sec8/Coupling.lean` (fully proved; elementary real analysis). Manuscript
`08_kick.tex:121-138`: "The substitution `v = (τ_K' - τ₀)/μ` gives
`c^in(τ_K) = β_k∫_{τ₀}^{τ_K} e^{ζ₀(τ_K-τ_K')} q_{k+1}(τ_K') dτ_K'`. Since `q_{k+1}` is continuous,
`c^in ∈ C¹([τ₀,T_pin])`, `c^in(τ₀) = 0`, and differentiation gives `eq:kick`."

* `coef_hasDerivWithinAt_Icc`: for `q` continuous on `[a,b]`, `c = Kick.coef ζ β a q` satisfies
  `c' = ζc + βq` on `[a,b]` (derivatives within `[a,b]`; FTC for the continuous extension
  `q ∘ projIcc`);
* `coef_eq_of_running`: the running-coefficient form
  `e^{λu} ∫₀ᵘ e^{-λv} μβ Q(v) dv`, `u = (τ_K - τ₀)/μ`, `Q(v) = q(μv + τ₀)`, equals
  `Kick.coef (λ/μ) β τ₀ q τ_K` (substitution `s = μv + τ₀`).
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler.CouplingAux

/-- **`c' = ζc + βq` on `[a,b]`** for `c = Kick.coef ζ β a q` and `q` continuous on `[a,b]`
(derivative within `[a,b]`, one-sided at the end points). -/
theorem coef_hasDerivWithinAt_Icc {ζ β : ℂ} {a b : ℝ} {q : ℝ → ℂ}
    (hq : ContinuousOn q (Icc a b)) {τ : ℝ} (hτ : τ ∈ Icc a b) :
    HasDerivWithinAt (Kick.coef ζ β a q) (ζ * Kick.coef ζ β a q τ + β * q τ) (Icc a b) τ := by
  have hab : a ≤ b := hτ.1.trans hτ.2
  set qe : ℝ → ℂ := fun s => q (projIcc a b hab s) with hqe
  have hqec : Continuous qe :=
    hq.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      (fun s => (projIcc a b hab s).2)
  have hqe_eq : ∀ s ∈ Icc a b, qe s = q s := fun s hs => by
    simp only [hqe, projIcc_of_mem hab hs]
  set g : ℝ → ℂ := fun s => Complex.exp (-(ζ * s)) * qe s with hg
  have hgc : Continuous g :=
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal).neg).mul hqec
  have hF : HasDerivAt (fun u => ∫ s in a..u, g s) (g τ) τ :=
    (hgc.integral_hasStrictDerivAt a τ).hasDerivAt
  have hE : HasDerivAt (fun u : ℝ => Complex.exp (ζ * u)) (Complex.exp (ζ * τ) * (ζ * 1)) τ :=
    ((hasDerivAt_id τ).ofReal_comp.const_mul ζ).cexp
  set c' : ℝ → ℂ := fun u => Complex.exp (ζ * u) * (β * ∫ s in a..u, g s) with hc'def
  have hc' : HasDerivAt c' (Complex.exp (ζ * τ) * (ζ * 1) * (β * ∫ s in a..τ, g s) +
      Complex.exp (ζ * τ) * (β * g τ)) τ :=
    hE.mul (hF.const_mul β)
  have heq : ∀ u ∈ Icc a b, Kick.coef ζ β a q u = c' u := by
    intro u hu
    simp only [Kick.coef, Kick.amp, hc'def]
    congr 2
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hu.1] at hs
    simp only [hg, hqe_eq s ⟨hs.1, hs.2.trans hu.2⟩]
  refine (hc'.hasDerivWithinAt.congr heq (heq τ hτ)).congr_deriv ?_
  rw [heq τ hτ]
  simp only [hc'def, hg]
  rw [hqe_eq τ hτ]
  have he : Complex.exp (ζ * τ) * Complex.exp (-(ζ * τ)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  linear_combination (β * q τ) * he

/-- **The running coefficient in kick time** (`08_kick.tex:128-135`): with `u = (τ_K - τ₀)/μ`
and `Q(v) = q(μv + τ₀)`, `e^{λu}∫₀ᵘ e^{-λv} μβQ(v) dv = Kick.coef (λ/μ) β τ₀ q τ_K`. -/
theorem coef_eq_of_running {lam : ℂ} {μ τ₀ τK : ℝ} (hμ : 0 < μ) (β : ℂ) {Q qk : ℝ → ℂ}
    (hQ : ∀ v, Q v = qk (μ * v + τ₀)) :
    Complex.exp (lam * (((τK - τ₀) / μ : ℝ) : ℂ)) *
        ∫ v in (0 : ℝ)..(τK - τ₀) / μ, Complex.exp (-(lam * v)) * ((μ : ℂ) * β * Q v) =
      Kick.coef (lam / μ) β τ₀ qk τK := by
  have hμ0 : (μ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hμ.ne'
  have hpt : ∀ v : ℝ, Complex.exp (-(lam * v)) * ((μ : ℂ) * β * Q v) =
      ((μ : ℂ) * β * Complex.exp (lam / μ * τ₀)) *
        (Complex.exp (-(lam / μ * ((μ * v + τ₀ : ℝ) : ℂ))) * qk (μ * v + τ₀)) := by
    intro v
    rw [hQ v]
    have : Complex.exp (-(lam * v)) = Complex.exp (lam / μ * τ₀) *
        Complex.exp (-(lam / μ * ((μ * v + τ₀ : ℝ) : ℂ))) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      field_simp
      ring
    rw [this]
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul]
  have hcv := intervalIntegral.integral_comp_mul_add
    (fun s : ℝ => Complex.exp (-(lam / μ * (s : ℂ))) * qk s) hμ.ne' τ₀
    (a := (0 : ℝ)) (b := (τK - τ₀) / μ)
  rw [hcv]
  have hb : μ * ((τK - τ₀) / μ) + τ₀ = τK := by field_simp; ring
  rw [mul_zero, zero_add, hb]
  simp only [Kick.coef, Kick.amp]
  rw [Complex.real_smul]
  have he : Complex.exp (lam * (((τK - τ₀) / μ : ℝ) : ℂ)) * Complex.exp (lam / μ * τ₀) =
      Complex.exp (lam / μ * τK) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  rw [← he]
  push_cast
  field_simp

end NonUniqueEuler.CouplingAux
