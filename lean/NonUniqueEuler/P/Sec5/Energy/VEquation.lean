import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Sec5.ReductionEq
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.H.Sec5.Energy.VEquation.Basic

/-!
# Proof of `I/Sec5/Energy/VEquation.lean`: the equation of `v = w - w_app`

Step 1 of the proof of `lem:energy` (`05_single_ring.tex:318-331`). Same declaration, statement
copied verbatim.

Proof (the manuscript's subtraction argument, at a point). Fix `τ ∈ [0,t]`. By
`lem:reduction`(3) (`reduction_eq`) `w = w(τ) ∈ X^1`, and `w_app(τ) ∈ X^{s+1} ⊆ X^1`; `Φ` is smooth
with compact support (`ringPhiSetting_valid`), so `Φ ∈ H^1` with classical weak derivatives
(`VEqH.memH_PhiC`). For a.e. `x`:
* the weak derivatives are additive at `x` (`VEqH.weakPartial_sub_ae`, `VEqH.weakPartial_add_ae`),
  and those of `Φ` are the classical ones;
* the Biot–Savart integrals of `Re w, Im w, Re w_app, Im w_app` converge absolutely at `x`
  (`BS.ae_integrable_biotSavart_of_L1`; the four functions are in `L¹`, `VEqH.memLp_one_re_im`),
  so `K_BS * v = K_BS * w - K_BS * w_app` at `x` (`VEqH.velocityRe_sub_apply`,
  `VEqH.velocityIm_sub_apply`) and the coupling term of `L(G)` is
  `-DΦ(x)((K_BS * Re f)(x)) - i DΦ(x)((K_BS * Im f)(x))` for `f = w, w_app`
  (`VEqH.integral_coupling_eq`).
At such a point both sides are explicit expressions in the same finitely many numbers; with
`K_BS * Im w = 0` (`w` is real, `BS.velocityIm_ofReal`) and `U₁∂₁Φ + U₂∂₂Φ = DΦ(x)U`
(`VEqH.dotGradPhi_eq`), the identity is a ring identity: the transport part `-Ω ∂_θ v` is
`-(Ω x^⊥)·∇v`, the coupling part is `B(v, Φ)`, and
`B(w,w) - B(w_app,w_app) = B(w,v) + B(v,w_app)` with `B(w,v) = -(K_BS * w)·∇v`.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ContDiff

namespace NonUniqueEuler

namespace OneRing

open RingData

/-- **The equation of `v = w - w_app`** (proof of `lem:energy`, `05_single_ring.tex:318-331`):
for `τ ∈ [0,t]`, a.e. on `ℝ²`,
`L(G)w + B(w,w) - h·∇w - h·∇Φ - w_app' = -U·∇v + B(v, Φ + w_app) - R_app` with
`U = Ω(|x|;G)x^⊥ + h + K_BS*w` and `v = w - w_app`. -/
theorem energy_vEquation (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) {s : ℕ} {c : RingConfig}
    {t : ℝ} (hc : c.Hyp t) (hsupp : c.RingSupportedIn t annN) {wapp wapp' : ℝ → ℂ → ℂ}
    (happ : PathC (s + 1) t wapp) :
    ∀ τ ∈ Icc (0 : ℝ) t,
      ringRHS χ c.G (c.h τ) (c.w χ τ) - wapp' τ =ᵐ[volume]
        -Sob.dotGrad (omegaField χ c.G + c.h τ + BS.velocityRe (c.w χ τ)) (c.w χ τ - wapp τ) +
          Bfn (c.w χ τ - wapp τ) (PhiC χ + wapp τ) - Rapp χ c.G c.h wapp wapp' τ := by
  intro τ hτ
  obtain ⟨-, hpert⟩ := reduction_eq χ hχ hc hsupp
  have hwX : Lin.MemXFn 1 (c.w χ τ) := (hpert 1).1.1 τ hτ
  have haX : Lin.MemXFn (s + 1) (wapp τ) := happ.1 τ hτ
  have hw : Sob.MemH 1 (c.w χ τ) := hwX.1
  have ha : Sob.MemH 1 (wapp τ) := haX.1.mono_order (by omega)
  have hS := ringPhiSetting_valid hχ
  have hΦs : ContDiff ℝ ∞ (ringPhi χ) := hS.contDiff
  have hΦc : HasCompactSupport (ringPhi χ) := hS.hasCompactSupport
  have hΦd : Differentiable ℝ (ringPhi χ) := hΦs.differentiable (by simp)
  obtain ⟨hΦ, hΦp⟩ := VEqH.memH_PhiC hΦs hΦc 1
  have h10 : ((1 : ℕ), (0 : ℕ)) ∈ Sob.multiIdx 1 := Sob.mem_multiIdx.2 (by norm_num)
  have h01 : ((0 : ℕ), (1 : ℕ)) ∈ Sob.multiIdx 1 := Sob.mem_multiIdx.2 (by norm_num)
  have hvIm : BS.velocityIm (c.w χ τ) = 0 :=
    BS.velocityIm_ofReal (fun x => c.ringPart τ x - ringPhi χ x)
  obtain ⟨hwre, hwim⟩ := VEqH.memLp_one_re_im hwX
  obtain ⟨hare, haim⟩ := VEqH.memLp_one_re_im haX
  filter_upwards [VEqH.weakPartial_sub_ae hw ha h10, VEqH.weakPartial_sub_ae hw ha h01,
    VEqH.weakPartial_add_ae hΦ ha h10, VEqH.weakPartial_add_ae hΦ ha h01, hΦp _ h10, hΦp _ h01,
    BS.ae_integrable_biotSavart_of_L1 hwre, BS.ae_integrable_biotSavart_of_L1 hwim,
    BS.ae_integrable_biotSavart_of_L1 hare, BS.ae_integrable_biotSavart_of_L1 haim]
    with x hv1 hv2 hq1 hq2 hp1 hp2 iwr iwi iar iai
  -- the coupling terms at `x`
  have hcw : (ringPhiSetting χ).couplingFn (c.w χ τ) x =
      -(((fderiv ℝ (ringPhi χ) x (BS.velocityRe (c.w χ τ) x) : ℝ) : ℂ) +
        Complex.I * ((fderiv ℝ (ringPhi χ) x (BS.velocityIm (c.w χ τ) x) : ℝ) : ℂ)) := by
    simp only [SectorSetting.couplingFn, ringPhiSetting_om]
    rw [VEqH.integral_coupling_eq _ iwr iwi]
  have hca : (ringPhiSetting χ).couplingFn (wapp τ) x =
      -(((fderiv ℝ (ringPhi χ) x (BS.velocityRe (wapp τ) x) : ℝ) : ℂ) +
        Complex.I * ((fderiv ℝ (ringPhi χ) x (BS.velocityIm (wapp τ) x) : ℝ) : ℂ)) := by
    simp only [SectorSetting.couplingFn, ringPhiSetting_om]
    rw [VEqH.integral_coupling_eq _ iar iai]
  -- `U₁∂₁Φ + U₂∂₂Φ = DΦ(x)U` for the two velocities of `v`
  have hΦ1 := VEqH.dotGradPhi_eq hΦd x (BS.velocityRe (c.w χ τ) x - BS.velocityRe (wapp τ) x)
  have hΦ2 := VEqH.dotGradPhi_eq hΦd x (0 - BS.velocityIm (wapp τ) x)
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, ringRHS, Rapp, Lin.Lfn,
    SectorSetting.linFn, SectorSetting.transportPartFn, Ang.thetaDeriv, Bfn, bsGrad, hGrad,
    Sob.dotGrad, omegaField, Lin.Omega]
  rw [hv1, hv2, hq1, hq2, VEqH.velocityRe_sub_apply iwr iar,
    VEqH.velocityIm_sub_apply iwi iai, hcw, hca, hvIm]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply, hp1, hp2, map_zero, map_sub, map_neg,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re,
    Complex.neg_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.zero_re, Complex.zero_im, Complex.ofReal_add,
    Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_zero, mul_zero,
    zero_mul, one_mul, sub_zero, zero_sub, add_zero, zero_add] at hΦ1 hΦ2 ⊢
  linear_combination hΦ1 + Complex.I * hΦ2

end OneRing

end NonUniqueEuler
