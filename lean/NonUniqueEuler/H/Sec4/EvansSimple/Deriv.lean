import NonUniqueEuler.Defs.Sec4.Evans
import NonUniqueEuler.I.Sec4.Sector
import NonUniqueEuler.I.Sec4.SectorSetting
import NonUniqueEuler.I.Sec4.EvansBasic
import NonUniqueEuler.I.Infra.ODE.Holo
import NonUniqueEuler.I.Infra.ODE.Wronskian
import NonUniqueEuler.I.Infra.ODE.Uniqueness
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Helper for `thm:evans-simple`: the two expressions of `J`, and part (1)

Helper of `P/Sec4/EvansSimple.lean` (fully proved). Namespace `NonUniqueEuler.EvansSimpleAux`.
Manuscript `04_ring.tex:455-457` (the two expressions of `J`) and `:479-497` (part (1)).

* `J_eq_integral`: `J = iℓ ∫_ℝ f_ξ ψ_*² / (λ_* + iℓΩ(e^ξ))² dξ` (`r = e^ξ`, `r dr = e^{2ξ} dξ`,
  `e^{2ξ} g_* = iℓ f_ξ M_* ψ_*`; the substitution holds without integrability assumptions);
* `fxi_eq_zero`: `f_ξ = 0` outside `[ξ₁, ξ₂]`;
* `hasDerivAt_Vric`: `∂_λ V_ℓ = -iℓ f_ξ M²`;
* `evans_deriv_identity`: part (1), `ψ_*(ξ₂) ≠ 0` and
  `e^{ℓ(ξ₂-ξ₁)} ψ_*(ξ₂) ∂_λ E_ℓ(λ_*) = -J` (the variational equation of `ψ̇ = ∂_λψ`,
  `I/Infra/ODE/Holo.lean`, and the integrated Wronskian identity of `ψ_*` and `ψ̇` on
  `[ξ₁, ξ₂]`, `I/Infra/ODE/Wronskian.lean`).
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace NonUniqueEuler.EvansSimpleAux

open SectorSetting

/-- `λ + iℓΩ ≠ 0` for `Re λ > 0` (`ℕ`-indexed form). -/
theorem denom_ne_zero' (S : SectorSetting) {z : ℂ} (hz : 0 < z.re) (ℓ : ℕ) (G r : ℝ) :
    z + Complex.I * (ℓ : ℂ) * ((S.Omega G r : ℝ) : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

/-- **The two expressions of `J`** (`04_ring.tex:455-457`, `r = e^ξ`). -/
theorem J_eq_integral (S : SectorSetting) (ℓ : ℕ) (z : ℂ) (G : ℝ) :
    S.J ℓ z G = Complex.I * (ℓ : ℂ) *
      ∫ ξ : ℝ, ((S.fxi ξ : ℝ) : ℂ) * S.psi ℓ z G ξ ^ 2 /
        (z + Complex.I * (ℓ : ℂ) * ((S.Omega G (Real.exp ξ) : ℝ) : ℂ)) ^ 2 := by
  have himg : Real.exp '' univ = Ioi (0 : ℝ) := by rw [image_univ, Real.range_exp]
  have hcv := integral_image_eq_integral_abs_deriv_smul (s := univ) (f := Real.exp)
    (f' := Real.exp) MeasurableSet.univ (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn
    (fun r : ℝ => S.gStar ℓ z G r * S.psi ℓ z G (Real.log r) * S.Mres ℓ z G r * (r : ℂ))
  rw [himg, Measure.restrict_univ] at hcv
  rw [J, hcv, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [abs_of_pos (Real.exp_pos ξ), Real.log_exp, gStar, kcoef, Mres, fxi,
    Int.cast_natCast, Complex.real_smul]
  have hex : ((Real.exp ξ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.exp_pos ξ).ne'
  push_cast
  field_simp

/-- `f_ξ = 0` outside `[ξ₁, ξ₂]`. -/
theorem fxi_eq_zero (S : SectorSetting) (hS : S.Valid) {ξ : ℝ} (hξ : ξ ∉ Icc S.ξ₁ S.ξ₂) :
    S.fxi ξ = 0 := by
  have hnot : Real.exp ξ ∉ Icc S.r₁ S.r₂ := by
    rintro ⟨h1, h2⟩
    apply hξ
    refine ⟨?_, ?_⟩
    · rw [ξ₁, Real.log_le_iff_le_exp hS.r₁_pos]
      exact h1
    · rw [ξ₂, Real.le_log_iff_exp_le hS.r₂_pos]
      exact h2
  rw [fxi, hS.dom_eq_zero _ (Real.exp_pos ξ) hnot, mul_zero]

/-- `f_ξ` is continuous. -/
theorem continuous_fxi (S : SectorSetting) (hS : S.Valid) : Continuous S.fxi := by
  have hom : ContDiff ℝ ∞ S.omR := hS.contDiff.comp Complex.ofRealCLM.contDiff
  have hdom : Continuous S.dom := hom.continuous_deriv (by simp)
  exact Real.continuous_exp.mul (hdom.comp Real.continuous_exp)

/-- `∂_λ V_ℓ(ξ;λ) = -iℓ f_ξ(ξ) / (λ + iℓΩ(e^ξ))²`. -/
theorem hasDerivAt_Vric (S : SectorSetting) (ℓ : ℕ) {z : ℂ} (hz : 0 < z.re) (G ξ : ℝ) :
    HasDerivAt (fun w => S.Vric ℓ w G ξ)
      (-(Complex.I * (ℓ : ℂ) * ((S.fxi ξ : ℝ) : ℂ)) /
        (z + Complex.I * (ℓ : ℂ) * ((S.Omega G (Real.exp ξ) : ℝ) : ℂ)) ^ 2) z := by
  have hd : HasDerivAt (fun w : ℂ => w + Complex.I * (ℓ : ℂ) * ((S.Omega G (Real.exp ξ) : ℝ) : ℂ))
      1 z := (hasDerivAt_id z).add_const _
  have h := ((hd.inv (denom_ne_zero' S hz ℓ G (Real.exp ξ))).const_mul
    (Complex.I * (ℓ : ℂ) * ((S.fxi ξ : ℝ) : ℂ))).const_add ((ℓ : ℂ) ^ 2)
  refine (h.congr_deriv ?_).congr_of_eventuallyEq ?_
  · ring
  · exact Eventually.of_forall fun w => by simp only [Vric, div_eq_mul_inv, Pi.inv_apply]

/-- **`thm:evans-simple`(1)** (`04_ring.tex:479-497`). -/
theorem evans_deriv_identity (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (z : ℂ)
    (hz : 0 < z.re) (G : ℝ) (hE : S.evans ℓ z G = 0) :
    S.psi ℓ z G S.ξ₂ ≠ 0 ∧
      ((Real.exp (ℓ * (S.ξ₂ - S.ξ₁)) : ℝ) : ℂ) * S.psi ℓ z G S.ξ₂ *
          deriv (fun w => S.evans ℓ w G) z = -S.J ℓ z G := by
  obtain ⟨hsol, hψ₁, hdψ₁, hψsmooth, -, -⟩ := psi_spec S hS ℓ hℓ z hz G
  obtain ⟨-, hVsmooth, hVd, hVc, -⟩ := sector_riccati S hS ℓ hℓ G
  have hVcz : Continuous (S.Vric ℓ z G) := (hVsmooth z hz).continuous
  -- `E = 0` gives `ψ_*'(ξ₂) = -ℓ ψ_*(ξ₂)`
  have hexp0 : ((Real.exp (-(ℓ : ℝ) * (S.ξ₂ - S.ξ₁)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne'
  have hd₂ : S.dpsi ℓ z G S.ξ₂ = -(ℓ : ℂ) * S.psi ℓ z G S.ξ₂ := by
    rw [evans_def] at hE
    have := (mul_eq_zero.1 hE).resolve_left hexp0
    linear_combination this
  refine ⟨?_, ?_⟩
  · -- `ψ_*(ξ₂) = 0` would force `ψ_* ≡ 0`
    intro h0
    have h0' : S.dpsi ℓ z G S.ξ₂ = 0 := by rw [hd₂, h0, mul_zero]
    have hzero := LinODE.IsSolOn.eqOn_zero ordConnected_univ hVcz.continuousOn hsol
      (mem_univ S.ξ₂) h0 h0'
    have := hzero.1 (mem_univ S.ξ₁)
    rw [hψ₁] at this
    exact one_ne_zero this
  · -- the variational equation of `ψ̇ = ∂_λ ψ`
    set U : Set ℂ := {w : ℂ | 0 < w.re} with hUdef
    have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
    have hzU : z ∈ U := hz
    have hvar := LinODE.isInhomSolOn_deriv_sol (V := fun ξ w => S.Vric ℓ w G ξ) hU hVc
      (fun ξ => hVd ξ) S.ξ₁ (1, (ℓ : ℂ)) hzU
    set ψd : ℝ → ℂ := fun ξ => deriv (fun w => S.psi ℓ w G ξ) z with hψd
    set ψd' : ℝ → ℂ := fun ξ => deriv (fun w => S.dpsi ℓ w G ξ) z with hψd'
    set dV : ℝ → ℂ := fun ξ => deriv (fun w => S.Vric ℓ w G ξ) z with hdV
    have hvar' : LinODE.IsInhomSolOn (S.Vric ℓ z G) (fun ξ => dV ξ * S.psi ℓ z G ξ) univ ψd ψd' :=
      hvar.1
    have hψd₁ : ψd S.ξ₁ = 0 := hvar.2.1
    have hψd'₁ : ψd' S.ξ₁ = 0 := hvar.2.2
    have hdVeq : ∀ ξ, dV ξ = -(Complex.I * (ℓ : ℂ) * ((S.fxi ξ : ℝ) : ℂ)) /
        (z + Complex.I * (ℓ : ℂ) * ((S.Omega G (Real.exp ξ) : ℝ) : ℂ)) ^ 2 :=
      fun ξ => (hasDerivAt_Vric S ℓ hz G ξ).deriv
    -- continuity of the forcing
    have hΩc : Continuous fun ξ : ℝ => ((S.Omega G (Real.exp ξ) : ℝ) : ℂ) := by
      have h1 : ContinuousOn (S.Omega G) (Ioi 0) := (contDiffOn_Omega S hS G).continuousOn
      exact Complex.continuous_ofReal.comp
        (h1.comp_continuous Real.continuous_exp fun ξ => Real.exp_pos ξ)
    have hdVc : Continuous dV := by
      rw [show dV = fun ξ => -(Complex.I * (ℓ : ℂ) * ((S.fxi ξ : ℝ) : ℂ)) /
          (z + Complex.I * (ℓ : ℂ) * ((S.Omega G (Real.exp ξ) : ℝ) : ℂ)) ^ 2 from
        funext hdVeq]
      exact Continuous.div
        (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_fxi S hS))).neg
        ((continuous_const.add (continuous_const.mul hΩc)).pow 2)
        fun ξ => pow_ne_zero 2 (denom_ne_zero' S hz ℓ G _)
    have hF₂ : ContinuousOn (fun ξ => dV ξ * S.psi ℓ z G ξ) univ :=
      (hdVc.mul hψsmooth.continuous).continuousOn
    have hW := LinODE.wronskian_sub_eq_integral ordConnected_univ
      (continuous_zero.continuousOn : ContinuousOn (0 : ℝ → ℂ) univ) hF₂
      hsol.toInhom hvar' (mem_univ S.ξ₁) (mem_univ S.ξ₂)
    simp only [LinODE.wronskian, hψd₁, hψd'₁, hψ₁, hdψ₁, mul_zero, sub_zero, Pi.zero_apply,
      zero_mul] at hW
    -- the derivative of `E`
    obtain ⟨hhol, -, -, -, -, -⟩ := evans_basic_holo S hS ℓ hℓ G
    have hdψ : DifferentiableAt ℂ (fun w => S.psi ℓ w G S.ξ₂) z :=
      ((hhol S.ξ₂).1 z hzU).differentiableAt (hU.mem_nhds hzU)
    have hddψ : DifferentiableAt ℂ (fun w => S.dpsi ℓ w G S.ξ₂) z :=
      ((hhol S.ξ₂).2.1 z hzU).differentiableAt (hU.mem_nhds hzU)
    have hEd : deriv (fun w => S.evans ℓ w G) z =
        ((Real.exp (-(ℓ : ℝ) * (S.ξ₂ - S.ξ₁)) : ℝ) : ℂ) * (ψd' S.ξ₂ + (ℓ : ℂ) * ψd S.ξ₂) := by
      have h := ((hddψ.hasDerivAt.add (hdψ.hasDerivAt.const_mul (ℓ : ℂ))).const_mul
        ((Real.exp (-(ℓ : ℝ) * (S.ξ₂ - S.ξ₁)) : ℝ) : ℂ)).deriv
      exact h
    -- the integral over `[ξ₁, ξ₂]` is the integral over `ℝ`
    have hle := hS.ξ₁_le_ξ₂
    have hint : ∫ ζ in S.ξ₁..S.ξ₂, S.psi ℓ z G ζ * (dV ζ * S.psi ℓ z G ζ) =
        -(Complex.I * (ℓ : ℂ) * ∫ ξ : ℝ, ((S.fxi ξ : ℝ) : ℂ) * S.psi ℓ z G ξ ^ 2 /
          (z + Complex.I * (ℓ : ℂ) * ((S.Omega G (Real.exp ξ) : ℝ) : ℂ)) ^ 2) := by
      rw [intervalIntegral.integral_of_le hle, ← integral_Icc_eq_integral_Ioc,
        setIntegral_eq_integral_of_forall_compl_eq_zero, ← integral_const_mul, ← integral_neg]
      · refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
        simp only [hdVeq]
        ring
      · intro ξ hξ
        simp only [hdVeq, fxi_eq_zero S hS hξ]
        simp
    have hexpmul : ((Real.exp (ℓ * (S.ξ₂ - S.ξ₁)) : ℝ) : ℂ) *
        ((Real.exp (-(ℓ : ℝ) * (S.ξ₂ - S.ξ₁)) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]
      simp
    rw [J_eq_integral, ← hint, ← hW, hEd, hd₂]
    linear_combination (S.psi ℓ z G S.ξ₂ * (ψd' S.ξ₂ + (ℓ : ℂ) * ψd S.ξ₂)) * hexpmul

end NonUniqueEuler.EvansSimpleAux
