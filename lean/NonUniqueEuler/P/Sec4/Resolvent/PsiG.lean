import NonUniqueEuler.Defs.Sec4.Evans
import NonUniqueEuler.Defs.Sec4.Extra1Sector
import NonUniqueEuler.I.Sec4.EvansBasic
import NonUniqueEuler.I.Sec4.Sector
import NonUniqueEuler.H.Sec4.Resolvent.PsiG.Fres
import NonUniqueEuler.H.Sec4.Resolvent.PsiG.VoC

/-!
# Proof: the Wronskian formula `ψ_g` solves the boundary value problem `eq:bvp`
(sub-step of `lem:resolvent`(1))

Proof of `I/Sec4/Resolvent/PsiG.lean` (`04_ring.tex:412-422`). Following the proof sketch of the
interface file:
1. `F = S.Fres ℓ z G g` is integrable and vanishes a.e. off `[c, d] = [log ρ₋, log ρ₊]`
   (`H/Sec4/Resolvent/PsiG/Fres.lean`), so `∫_{Iic ξ} ψ F = ∫_c^ξ ψ F` and
   `∫_{Ioi ξ} ψ F = ∫_ℝ ψ F - ∫_c^ξ ψ F`: `W ψ_g = ψ_L C_R + Φ`, `Φ = ψ_R A_L - ψ_L A_R`.
2. Variation of constants with an `L¹` forcing (`H/Sec4/Resolvent/PsiG/VoC.lean`):
   `Φ' = ψ_R' A_L - ψ_L' A_R =: D` (continuous) and `D(b) - D(a) = ∫_a^b (V_ℓΦ + W F)`.
3. `φ' = W⁻¹(ψ_L' C_R + D)`; the integrated equation follows from `ψ_L'' = V_ℓψ_L`.
4. Growth: on `ξ ≤ c` the integral over `Iic ξ` vanishes and `ψ_L = e^{ℓξ}` (`c < ξ₁`); on
   `ξ ≥ d` the integral over `Ioi ξ` vanishes and `ψ_R = e^{-ℓξ}` (`ξ₂ < d`).
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler

namespace SectorSetting

/-- Proof of `lem:resolvent`(1) (`04_ring.tex:412-422`): if `E_ℓ(λ;G) ≠ 0` and `g ∈ Y^0_ℓ`, the
Wronskian formula `ψ_g` is `C¹` and solves `ψ_g'' = V_ℓψ_g + F` (`F = S.Fres ℓ z G g`) in
integrated form, with `ψ_g = A e^{ℓξ}` for `ξ ≤ log ρ₋` and `ψ_g = B e^{-ℓξ}` for
`ξ ≥ log ρ₊`. -/
theorem psiG_spec (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (z : ℂ)
    (hz : 0 < z.re) (G : ℝ) (hE : S.evans ℓ z G ≠ 0) {g : ℝ → ℂ} (hg : S.IsProfileL2 g) :
    ∃ φ' : ℝ → ℂ,
      (∀ ξ : ℝ, HasDerivAt (S.psiG ℓ z G g) (φ' ξ) ξ) ∧ Continuous φ' ∧
      (∀ a b : ℝ, φ' b - φ' a =
        ∫ t in a..b, (S.Vric ℓ z G t * S.psiG ℓ z G g t + S.Fres ℓ z G g t)) ∧
      (∃ A : ℂ, ∀ ξ : ℝ, ξ ≤ Real.log S.ρm →
        S.psiG ℓ z G g ξ = A * ((Real.exp (ℓ * ξ) : ℝ) : ℂ)) ∧
      (∃ B : ℂ, ∀ ξ : ℝ, Real.log S.ρp ≤ ξ →
        S.psiG ℓ z G g ξ = B * ((Real.exp (-(ℓ * ξ)) : ℝ) : ℂ)) := by
  -- the homogeneous solutions `ψ_L`, `ψ_R` and the Wronskian
  obtain ⟨hpsi, -, -, -, -, -⟩ := psi_spec S hS ℓ hℓ z hz G
  obtain ⟨hpsiR, -, -, hright⟩ := psiR_spec S hS ℓ hℓ z hz G
  obtain ⟨hleft, hwr⟩ := wronskian_eq_neg_evans S hS ℓ hℓ z hz G
  have hV : Continuous (S.Vric ℓ z G) := ((sector_riccati S hS ℓ hℓ G).2.1 z hz).continuous
  have hLsol : LinODE.IsSolOn (S.Vric ℓ z G) univ (S.psiL ℓ z G) (S.dpsiL ℓ z G) :=
    hpsi.const_mul ((Real.exp (ℓ * S.ξ₁) : ℝ) : ℂ)
  obtain ⟨hL, hL'⟩ := LinODE.isSolOn_univ_iff.1 hLsol
  obtain ⟨hR, hR'⟩ := LinODE.isSolOn_univ_iff.1 hpsiR
  have cL : Continuous (S.psiL ℓ z G) :=
    continuous_iff_continuousAt.2 fun t => (hL t).continuousAt
  have cR : Continuous (S.psiR ℓ z G) :=
    continuous_iff_continuousAt.2 fun t => (hR t).continuousAt
  have cL' : Continuous (S.dpsiL ℓ z G) :=
    continuous_iff_continuousAt.2 fun t => (hL' t).continuousAt
  have hWne : S.wr ℓ z G ≠ 0 := by
    rw [wr, hwr]
    exact neg_ne_zero.2 hE
  have hW : ∀ t, S.psiL ℓ z G t * S.dpsiR ℓ z G t - S.dpsiL ℓ z G t * S.psiR ℓ z G t =
      S.wr ℓ z G := by
    intro t
    have h : S.wrFn ℓ z G t = S.wr ℓ z G := by rw [wr, hwr, hwr]
    simpa [wrFn, LinODE.wronskian] using h
  -- the forcing
  have hFii : ∀ a b : ℝ, IntervalIntegrable (S.Fres ℓ z G g) volume a b := fun _ _ =>
    (PsiGAux.integrable_Fres S hS ℓ hz G hg).intervalIntegrable
  have hsupp := PsiGAux.Fres_ae_eq_zero S hS ℓ z G hg
  have hφF : ∀ φ : ℝ → ℂ, Continuous φ → Integrable (fun t => φ t * S.Fres ℓ z G g t) :=
    fun φ hφ => PsiGAux.integrable_mul_Fres S hS ℓ hz G hg hφ
  -- the half-line integrals
  have hvanL : ∀ (φ : ℝ → ℂ) (ξ : ℝ), ξ ≤ Real.log S.ρm →
      ∫ t in Iic ξ, φ t * S.Fres ℓ z G g t = 0 := by
    intro φ ξ hξ
    rw [integral_Iic_eq_integral_Iio]
    refine setIntegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [hsupp] with t ht htmem
    rw [ht fun h => lt_irrefl t ((mem_Iio.1 htmem).trans_le (hξ.trans h.1)), mul_zero]
  have hvanR : ∀ (φ : ℝ → ℂ) (ξ : ℝ), Real.log S.ρp ≤ ξ →
      ∫ t in Ioi ξ, φ t * S.Fres ℓ z G g t = 0 := by
    intro φ ξ hξ
    refine setIntegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [hsupp] with t ht htmem
    rw [ht fun h => lt_irrefl t ((h.2.trans hξ).trans_lt (mem_Ioi.1 htmem)), mul_zero]
  have hIoi : ∀ (φ : ℝ → ℂ), Continuous φ → ∀ ξ : ℝ,
      ∫ t in Ioi ξ, φ t * S.Fres ℓ z G g t =
        (∫ t, φ t * S.Fres ℓ z G g t) - ∫ t in Iic ξ, φ t * S.Fres ℓ z G g t := by
    intro φ hφ ξ
    have h := integral_add_compl (measurableSet_Iic (a := ξ)) (hφF φ hφ)
    rw [compl_Iic] at h
    rw [← h]
    ring
  have hIic' : ∀ (φ : ℝ → ℂ), Continuous φ → ∀ ξ : ℝ,
      ∫ t in Iic ξ, φ t * S.Fres ℓ z G g t =
        (∫ t, φ t * S.Fres ℓ z G g t) - ∫ t in Ioi ξ, φ t * S.Fres ℓ z G g t := by
    intro φ hφ ξ
    rw [hIoi φ hφ ξ]
    ring
  have hIic : ∀ (φ : ℝ → ℂ), Continuous φ → ∀ ξ : ℝ,
      ∫ t in Iic ξ, φ t * S.Fres ℓ z G g t =
        ∫ t in Real.log S.ρm..ξ, φ t * S.Fres ℓ z G g t := by
    intro φ hφ ξ
    have h := intervalIntegral.integral_Iic_sub_Iic (a := Real.log S.ρm) (b := ξ)
      (hφF φ hφ).integrableOn (hφF φ hφ).integrableOn
    rwa [hvanL φ (Real.log S.ρm) le_rfl, sub_zero] at h
  -- step 1: `W ψ_g = ψ_L C_R + Φ`
  set CR : ℂ := ∫ t, S.psiR ℓ z G t * S.Fres ℓ z G g t with hCR
  set CL : ℂ := ∫ t, S.psiL ℓ z G t * S.Fres ℓ z G g t with hCL
  have hform : ∀ ξ : ℝ, S.psiG ℓ z G g ξ = (S.wr ℓ z G)⁻¹ * (S.psiL ℓ z G ξ * CR +
      (S.psiR ℓ z G ξ * (∫ t in Real.log S.ρm..ξ, S.psiL ℓ z G t * S.Fres ℓ z G g t) -
        S.psiL ℓ z G ξ * ∫ t in Real.log S.ρm..ξ, S.psiR ℓ z G t * S.Fres ℓ z G g t)) := by
    intro ξ
    rw [psiG, hIoi _ cR ξ, hIic _ cL ξ, hIic _ cR ξ]
    ring
  -- step 2: variation of constants
  obtain ⟨hΦd, hDc, hDint⟩ := PsiGAux.voc_integrated (Real.log S.ρm) hV hL hL' hR hR' hW hFii
  refine ⟨fun ξ => (S.wr ℓ z G)⁻¹ * (S.dpsiL ℓ z G ξ * CR +
      (S.dpsiR ℓ z G ξ * (∫ t in Real.log S.ρm..ξ, S.psiL ℓ z G t * S.Fres ℓ z G g t) -
        S.dpsiL ℓ z G ξ * ∫ t in Real.log S.ρm..ξ, S.psiR ℓ z G t * S.Fres ℓ z G g t)),
    fun ξ => ?_, continuous_const.mul ((cL'.mul continuous_const).add hDc), fun a b => ?_,
    ⟨(S.wr ℓ z G)⁻¹ * CR, fun ξ hξ => ?_⟩, ⟨(S.wr ℓ z G)⁻¹ * CL, fun ξ hξ => ?_⟩⟩
  · -- the derivative
    have hfun : S.psiG ℓ z G g = fun ξ => (S.wr ℓ z G)⁻¹ * (S.psiL ℓ z G ξ * CR +
        (S.psiR ℓ z G ξ * (∫ t in Real.log S.ρm..ξ, S.psiL ℓ z G t * S.Fres ℓ z G g t) -
          S.psiL ℓ z G ξ * ∫ t in Real.log S.ρm..ξ, S.psiR ℓ z G t * S.Fres ℓ z G g t)) :=
      funext hform
    rw [hfun]
    exact (((hL ξ).mul_const CR).add (hΦd ξ)).const_mul _
  · -- step 3: the integrated equation
    have hL'int : S.dpsiL ℓ z G b - S.dpsiL ℓ z G a =
        ∫ t in a..b, S.Vric ℓ z G t * S.psiL ℓ z G t :=
      (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hL' x)
        ((hV.mul cL).intervalIntegrable a b)).symm
    have hWW := inv_mul_cancel₀ hWne
    have hcongr : ∫ t in a..b, (S.Vric ℓ z G t * S.psiG ℓ z G g t + S.Fres ℓ z G g t) =
        ∫ t in a..b, ((S.wr ℓ z G)⁻¹ * CR * (S.Vric ℓ z G t * S.psiL ℓ z G t) +
          (S.wr ℓ z G)⁻¹ * (S.Vric ℓ z G t *
            (S.psiR ℓ z G t * (∫ s in Real.log S.ρm..t, S.psiL ℓ z G s * S.Fres ℓ z G g s) -
              S.psiL ℓ z G t * ∫ s in Real.log S.ρm..t, S.psiR ℓ z G s * S.Fres ℓ z G g s) +
            S.wr ℓ z G * S.Fres ℓ z G g t)) := by
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [hform t]
      linear_combination (-(S.Fres ℓ z G g t)) * hWW
    have i1 : IntervalIntegrable (fun t => S.Vric ℓ z G t * S.psiL ℓ z G t) volume a b :=
      (hV.mul cL).intervalIntegrable a b
    have cAL : Continuous fun t => ∫ s in Real.log S.ρm..t, S.psiL ℓ z G s * S.Fres ℓ z G g s :=
      intervalIntegral.continuous_primitive (fun a b => (hFii a b).continuousOn_mul cL.continuousOn) _
    have cAR : Continuous fun t => ∫ s in Real.log S.ρm..t, S.psiR ℓ z G s * S.Fres ℓ z G g s :=
      intervalIntegral.continuous_primitive (fun a b => (hFii a b).continuousOn_mul cR.continuousOn) _
    have i2 : IntervalIntegrable (fun t => S.Vric ℓ z G t *
        (S.psiR ℓ z G t * (∫ s in Real.log S.ρm..t, S.psiL ℓ z G s * S.Fres ℓ z G g s) -
          S.psiL ℓ z G t * ∫ s in Real.log S.ρm..t, S.psiR ℓ z G s * S.Fres ℓ z G g s) +
        S.wr ℓ z G * S.Fres ℓ z G g t) volume a b :=
      ((hV.mul ((cR.mul cAL).sub (cL.mul cAR))).intervalIntegrable a b).add
        ((hFii a b).const_mul _)
    rw [hcongr, intervalIntegral.integral_add (i1.const_mul _) (i2.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, ← hL'int,
      ← hDint a b]
    ring
  · -- step 4: the left half-line
    have hξ1 : ξ ≤ S.ξ₁ := hξ.trans (Real.log_lt_log hS.ρm_pos hS.ρm_lt_r₁).le
    rw [psiG, hvanL (S.psiL ℓ z G) ξ hξ, hIoi (S.psiR ℓ z G) cR ξ, hvanL (S.psiR ℓ z G) ξ hξ,
      hleft ξ hξ1]
    ring
  · -- step 4: the right half-line
    have hξ2 : S.ξ₂ ≤ ξ := (Real.log_lt_log hS.r₂_pos hS.r₂_lt_ρp).le.trans hξ
    rw [psiG, hvanR (S.psiR ℓ z G) ξ hξ, hIic' (S.psiL ℓ z G) cL ξ, hvanR (S.psiL ℓ z G) ξ hξ,
      (hright ξ hξ2).1]
    ring

end SectorSetting

end NonUniqueEuler
