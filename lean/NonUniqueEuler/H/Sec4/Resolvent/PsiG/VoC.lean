import NonUniqueEuler.I.Infra.ODE.WeakIBP
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Helpers for `P/Sec4/Resolvent/PsiG`: variation of constants with an `L¹` forcing

Steps 2-3 of the proof of `psiG_spec` (proof of `lem:resolvent`(1), `04_ring.tex:412-422`:
"differentiating the formula for `ψ_g`, the terms from the variable limits cancel, and
`ψ_g'' = V_ℓψ_g + W⁻¹(ψ_Lψ_R' - ψ_L'ψ_R)F`"), for an abstract pair of classical solutions
`ψ_L, ψ_R` of `ψ'' = Vψ` with constant Wronskian `W`, and a forcing `F` that is only locally
integrable. With `A_L(ξ) = ∫_c^ξ ψ_L F`, `A_R(ξ) = ∫_c^ξ ψ_R F`, the function
`Φ = ψ_R A_L - ψ_L A_R` is differentiable with the continuous derivative
`D = ψ_R' A_L - ψ_L' A_R`, and `D(b) - D(a) = ∫_a^b (VΦ + W F)`.

Since `A_L`, `A_R` are only absolutely continuous, the product rule is replaced by the integration
by parts `LinODE.integral_mul_eq_of_integrated` (`I/Infra/ODE/WeakIBP.lean`), applied with
`v = ψ_R, ψ_L` (first derivative) and `v = ψ_R', ψ_L'` (second derivative).
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler.PsiGAux

/-- Integration by parts against the primitive `U(t) = ∫_c^t H` of a locally integrable `H`, for a
classical `C¹` function `v` on `ℝ`. -/
theorem ibp_primitive {H v v' : ℝ → ℂ} (c a b : ℝ)
    (hH : ∀ a b : ℝ, IntervalIntegrable H volume a b)
    (hv : ∀ t, HasDerivAt v (v' t) t) (hv' : Continuous v') :
    ∫ t in a..b, v t * H t =
      v b * (∫ s in c..b, H s) - v a * (∫ s in c..a, H s) -
        ∫ t in a..b, v' t * ∫ s in c..t, H s :=
  LinODE.integral_mul_eq_of_integrated (U := fun t => ∫ s in c..t, H s) (hH a b)
    (fun t _ => (intervalIntegral.integral_add_adjacent_intervals (hH c a) (hH a t)).symm)
    (fun t _ => hv t) hv'.continuousOn

/-- Variation of constants with a locally integrable forcing: with `A_L = ∫_c^· ψ_L F`,
`A_R = ∫_c^· ψ_R F`, `Φ = ψ_R A_L - ψ_L A_R` has the continuous derivative
`D = ψ_R' A_L - ψ_L' A_R`, and `D(b) - D(a) = ∫_a^b (VΦ + W F)`. -/
theorem voc_integrated {V L L' R R' F : ℝ → ℂ} {W : ℂ} (c : ℝ) (hV : Continuous V)
    (hL : ∀ t, HasDerivAt L (L' t) t) (hL' : ∀ t, HasDerivAt L' (V t * L t) t)
    (hR : ∀ t, HasDerivAt R (R' t) t) (hR' : ∀ t, HasDerivAt R' (V t * R t) t)
    (hW : ∀ t, L t * R' t - L' t * R t = W)
    (hF : ∀ a b : ℝ, IntervalIntegrable F volume a b) :
    (∀ ξ, HasDerivAt
        (fun ξ => R ξ * (∫ t in c..ξ, L t * F t) - L ξ * ∫ t in c..ξ, R t * F t)
        (R' ξ * (∫ t in c..ξ, L t * F t) - L' ξ * ∫ t in c..ξ, R t * F t) ξ) ∧
      Continuous (fun ξ => R' ξ * (∫ t in c..ξ, L t * F t) - L' ξ * ∫ t in c..ξ, R t * F t) ∧
      ∀ a b : ℝ,
        (R' b * (∫ t in c..b, L t * F t) - L' b * ∫ t in c..b, R t * F t) -
            (R' a * (∫ t in c..a, L t * F t) - L' a * ∫ t in c..a, R t * F t) =
          ∫ t in a..b,
            (V t * (R t * (∫ s in c..t, L s * F s) - L t * ∫ s in c..t, R s * F s) +
              W * F t) := by
  -- continuity of the coefficients
  have cL : Continuous L := continuous_iff_continuousAt.2 fun t => (hL t).continuousAt
  have cR : Continuous R := continuous_iff_continuousAt.2 fun t => (hR t).continuousAt
  have cL' : Continuous L' := continuous_iff_continuousAt.2 fun t => (hL' t).continuousAt
  have cR' : Continuous R' := continuous_iff_continuousAt.2 fun t => (hR' t).continuousAt
  -- the forcings `ψ_L F`, `ψ_R F` and the primitives
  have iLF : ∀ a b : ℝ, IntervalIntegrable (fun t => L t * F t) volume a b :=
    fun a b => (hF a b).continuousOn_mul cL.continuousOn
  have iRF : ∀ a b : ℝ, IntervalIntegrable (fun t => R t * F t) volume a b :=
    fun a b => (hF a b).continuousOn_mul cR.continuousOn
  set AL : ℝ → ℂ := fun ξ => ∫ t in c..ξ, L t * F t with hAL
  set AR : ℝ → ℂ := fun ξ => ∫ t in c..ξ, R t * F t with hAR
  have cAL : Continuous AL := intervalIntegral.continuous_primitive iLF c
  have cAR : Continuous AR := intervalIntegral.continuous_primitive iRF c
  set D : ℝ → ℂ := fun ξ => R' ξ * AL ξ - L' ξ * AR ξ with hD
  have cD : Continuous D := (cR'.mul cAL).sub (cL'.mul cAR)
  -- first derivative: `Φ(b) - Φ(a) = ∫_a^b D`
  have hΦ : ∀ a b : ℝ, (R b * AL b - L b * AR b) - (R a * AL a - L a * AR a) =
      ∫ t in a..b, D t := by
    intro a b
    have h1 := ibp_primitive c a b iLF hR cR'
    have h2 := ibp_primitive c a b iRF hL cL'
    have h12 : ∫ t in a..b, R t * (L t * F t) = ∫ t in a..b, L t * (R t * F t) := by
      refine intervalIntegral.integral_congr fun t _ => ?_
      ring
    have hsplit : ∫ t in a..b, D t =
        (∫ t in a..b, R' t * AL t) - ∫ t in a..b, L' t * AR t :=
      intervalIntegral.integral_sub ((cR'.mul cAL).intervalIntegrable a b)
        ((cL'.mul cAR).intervalIntegrable a b)
    rw [hsplit]
    simp only [hAL, hAR] at h1 h2 ⊢
    linear_combination h2 - h1 + h12
  refine ⟨fun ξ => ?_, cD, fun a b => ?_⟩
  · -- `Φ = Φ(0) + ∫_0^· D` and the fundamental theorem of calculus
    have hfun : (fun ξ => R ξ * AL ξ - L ξ * AR ξ) =
        fun x => (R 0 * AL 0 - L 0 * AR 0) + ∫ t in (0 : ℝ)..x, D t := by
      funext x
      rw [← hΦ 0 x]
      ring
    have := ((cD.integral_hasStrictDerivAt 0 ξ).hasDerivAt).const_add
      (R 0 * AL 0 - L 0 * AR 0)
    rw [← hfun] at this
    exact this
  · -- second derivative
    have h3 := ibp_primitive c a b iLF hR' (hV.mul cR)
    have h4 := ibp_primitive c a b iRF hL' (hV.mul cL)
    have iR'LF : IntervalIntegrable (fun t => R' t * (L t * F t)) volume a b :=
      (iLF a b).continuousOn_mul cR'.continuousOn
    have iL'RF : IntervalIntegrable (fun t => L' t * (R t * F t)) volume a b :=
      (iRF a b).continuousOn_mul cL'.continuousOn
    have iVRAL : IntervalIntegrable (fun t => V t * R t * AL t) volume a b :=
      ((hV.mul cR).mul cAL).intervalIntegrable a b
    have iVLAR : IntervalIntegrable (fun t => V t * L t * AR t) volume a b :=
      ((hV.mul cL).mul cAR).intervalIntegrable a b
    have hcongr : ∫ t in a..b, (V t * (R t * AL t - L t * AR t) + W * F t) =
        ∫ t in a..b, ((V t * R t * AL t - V t * L t * AR t) +
          (R' t * (L t * F t) - L' t * (R t * F t))) := by
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [← hW t]
      ring
    have hsplit : ∫ t in a..b, ((V t * R t * AL t - V t * L t * AR t) +
          (R' t * (L t * F t) - L' t * (R t * F t))) =
        ((∫ t in a..b, V t * R t * AL t) - ∫ t in a..b, V t * L t * AR t) +
          ((∫ t in a..b, R' t * (L t * F t)) - ∫ t in a..b, L' t * (R t * F t)) := by
      rw [intervalIntegral.integral_add (iVRAL.sub iVLAR) (iR'LF.sub iL'RF),
        intervalIntegral.integral_sub iVRAL iVLAR, intervalIntegral.integral_sub iR'LF iL'RF]
    show D b - D a = ∫ t in a..b, (V t * (R t * AL t - L t * AR t) + W * F t)
    rw [hcongr, hsplit]
    simp only [hD, hAL, hAR] at h3 h4 ⊢
    linear_combination h4 - h3

end NonUniqueEuler.PsiGAux
