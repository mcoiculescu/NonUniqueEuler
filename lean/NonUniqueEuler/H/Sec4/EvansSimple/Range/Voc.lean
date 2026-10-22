import NonUniqueEuler.Defs.Infra.ODE
import NonUniqueEuler.I.Infra.ODE.WeakIBP
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Helpers for `P/Sec4/EvansSimple/Range`: variation of constants with `L¹_loc` forcing

`voc_integrated`: if `u, v` are classical solutions of `ψ'' = Vψ` on `ℝ` (`V` continuous) with
Wronskian `u v' - u' v ≡ 1`, and `F` is interval integrable on every interval, then
`φ = v ∫_c^ξ uF - u ∫_c^ξ vF` is `C¹` with `φ' = v' ∫_c^ξ uF - u' ∫_c^ξ vF`, and
`φ'(b) - φ'(a) = ∫_a^b (Vφ + F)` (the integrated form of `φ'' = Vφ + F`).

This is the variation of constants formula of the proof of `thm:evans-simple`(3)
(`04_ring.tex:540-546`), in the integrated form needed for a forcing `F` that is only `L¹`
(as in `I/Sec4/Resolvent/PsiG.lean`). The proof uses integration by parts against an
indefinite integral (`I/Infra/ODE/WeakIBP.lean`) twice.
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler.EvansRangeAux

open LinODE

theorem primitive_eq {H : ℝ → ℂ} (hH : ∀ a b, IntervalIntegrable H volume a b) (c a t : ℝ) :
    (∫ s in c..t, H s) = (∫ s in c..a, H s) + ∫ s in a..t, H s :=
  (intervalIntegral.integral_add_adjacent_intervals (hH c a) (hH a t)).symm

/-- Integration by parts against the primitive `∫_c^t H`. -/
theorem ibp_primitive {H w w' : ℝ → ℂ} (hH : ∀ a b, IntervalIntegrable H volume a b)
    (hw : ∀ t, HasDerivAt w (w' t) t) (hw' : Continuous w') (c a b : ℝ) :
    ∫ t in a..b, w t * H t = w b * (∫ s in c..b, H s) - w a * (∫ s in c..a, H s) -
      ∫ t in a..b, w' t * ∫ s in c..t, H s :=
  LinODE.integral_mul_eq_of_integrated (hH a b) (fun t _ => primitive_eq hH c a t)
    (fun t _ => hw t) hw'.continuousOn

/-- **Variation of constants in integrated form.** -/
theorem voc_integrated {V u u' v v' F : ℝ → ℂ} (hV : Continuous V)
    (hu : IsSolOn V univ u u') (hv : IsSolOn V univ v v')
    (hW : ∀ ξ, u ξ * v' ξ - u' ξ * v ξ = 1)
    (hF : ∀ a b, IntervalIntegrable F volume a b) (c : ℝ) :
    (∀ ξ, HasDerivAt (fun ξ => v ξ * (∫ t in c..ξ, u t * F t) - u ξ * ∫ t in c..ξ, v t * F t)
        (v' ξ * (∫ t in c..ξ, u t * F t) - u' ξ * ∫ t in c..ξ, v t * F t) ξ) ∧
      Continuous (fun ξ => v' ξ * (∫ t in c..ξ, u t * F t) - u' ξ * ∫ t in c..ξ, v t * F t) ∧
      ∀ a b : ℝ, (v' b * (∫ t in c..b, u t * F t) - u' b * ∫ t in c..b, v t * F t) -
          (v' a * (∫ t in c..a, u t * F t) - u' a * ∫ t in c..a, v t * F t) =
        ∫ t in a..b,
          (V t * (v t * (∫ s in c..t, u s * F s) - u t * ∫ s in c..t, v s * F s) + F t) := by
  obtain ⟨hu1, hu2⟩ := isSolOn_univ_iff.1 hu
  obtain ⟨hv1, hv2⟩ := isSolOn_univ_iff.1 hv
  have huc : Continuous u := continuous_iff_continuousAt.2 fun ξ => (hu1 ξ).continuousAt
  have hu'c : Continuous u' := continuous_iff_continuousAt.2 fun ξ => (hu2 ξ).continuousAt
  have hvc : Continuous v := continuous_iff_continuousAt.2 fun ξ => (hv1 ξ).continuousAt
  have hv'c : Continuous v' := continuous_iff_continuousAt.2 fun ξ => (hv2 ξ).continuousAt
  have hUF : ∀ a b, IntervalIntegrable (fun t => u t * F t) volume a b :=
    fun a b => (hF a b).continuousOn_mul huc.continuousOn
  have hVF : ∀ a b, IntervalIntegrable (fun t => v t * F t) volume a b :=
    fun a b => (hF a b).continuousOn_mul hvc.continuousOn
  set Au : ℝ → ℂ := fun ξ => ∫ t in c..ξ, u t * F t with hAu
  set Av : ℝ → ℂ := fun ξ => ∫ t in c..ξ, v t * F t with hAv
  have hAuc : Continuous Au := intervalIntegral.continuous_primitive hUF c
  have hAvc : Continuous Av := intervalIntegral.continuous_primitive hVF c
  have hφ'c : Continuous fun ξ => v' ξ * Au ξ - u' ξ * Av ξ :=
    (hv'c.mul hAuc).sub (hu'c.mul hAvc)
  -- step 1: `φ(b) - φ(a) = ∫_a^b φ'`
  have step1 : ∀ a b : ℝ, (v b * Au b - u b * Av b) - (v a * Au a - u a * Av a) =
      ∫ t in a..b, (v' t * Au t - u' t * Av t) := by
    intro a b
    have i1 := ibp_primitive hUF hv1 hv'c c a b
    have i2 := ibp_primitive hVF hu1 hu'c c a b
    have heq : (∫ t in a..b, v t * (u t * F t)) = ∫ t in a..b, u t * (v t * F t) := by
      refine intervalIntegral.integral_congr fun t _ => ?_
      ring
    have hsub : (∫ t in a..b, (v' t * Au t - u' t * Av t)) =
        (∫ t in a..b, v' t * Au t) - ∫ t in a..b, u' t * Av t :=
      intervalIntegral.integral_sub ((hv'c.mul hAuc).intervalIntegrable a b)
        ((hu'c.mul hAvc).intervalIntegrable a b)
    rw [hsub]
    simp only [hAu, hAv] at i1 i2 ⊢
    linear_combination i2 - i1 + heq
  refine ⟨fun ξ => ?_, hφ'c, fun a b => ?_⟩
  · have hfun : (fun ξ => v ξ * Au ξ - u ξ * Av ξ) =
        fun ξ => (v c * Au c - u c * Av c) + ∫ t in c..ξ, (v' t * Au t - u' t * Av t) := by
      funext ξ
      rw [← step1 c ξ]
      ring
    change HasDerivAt (fun ξ => v ξ * Au ξ - u ξ * Av ξ) (v' ξ * Au ξ - u' ξ * Av ξ) ξ
    rw [hfun]
    exact ((hφ'c.integral_hasStrictDerivAt c ξ).hasDerivAt).const_add _
  · -- step 2: `φ'(b) - φ'(a) = ∫_a^b (Vφ + F)`
    have hVvc : Continuous fun t => V t * v t := hV.mul hvc
    have hVuc : Continuous fun t => V t * u t := hV.mul huc
    have j1 := ibp_primitive hUF hv2 hVvc c a b
    have j2 := ibp_primitive hVF hu2 hVuc c a b
    have hi1 : IntervalIntegrable (fun t => v' t * (u t * F t)) volume a b :=
      (hUF a b).continuousOn_mul hv'c.continuousOn
    have hi2 : IntervalIntegrable (fun t => u' t * (v t * F t)) volume a b :=
      (hVF a b).continuousOn_mul hu'c.continuousOn
    have hF' : (∫ t in a..b, F t) =
        (∫ t in a..b, v' t * (u t * F t)) - ∫ t in a..b, u' t * (v t * F t) := by
      rw [← intervalIntegral.integral_sub hi1 hi2]
      refine intervalIntegral.integral_congr fun t _ => ?_
      have := hW t
      linear_combination (-(F t)) * this
    have hVφ : (∫ t in a..b, V t * (v t * Au t - u t * Av t)) =
        (∫ t in a..b, V t * v t * Au t) - ∫ t in a..b, V t * u t * Av t := by
      have k1 : IntervalIntegrable (fun t => V t * v t * Au t) volume a b :=
        (hVvc.mul hAuc).intervalIntegrable a b
      have k2 : IntervalIntegrable (fun t => V t * u t * Av t) volume a b :=
        (hVuc.mul hAvc).intervalIntegrable a b
      rw [← intervalIntegral.integral_sub k1 k2]
      refine intervalIntegral.integral_congr fun t _ => ?_
      ring
    have hsplit : (∫ t in a..b, (V t * (v t * Au t - u t * Av t) + F t)) =
        (∫ t in a..b, V t * (v t * Au t - u t * Av t)) + ∫ t in a..b, F t :=
      intervalIntegral.integral_add
        ((hV.mul ((hvc.mul hAuc).sub (huc.mul hAvc))).intervalIntegrable a b) (hF a b)
    change (v' b * Au b - u' b * Av b) - (v' a * Au a - u' a * Av a) =
      ∫ t in a..b, (V t * (v t * Au t - u t * Av t) + F t)
    rw [hsplit, hVφ, hF']
    simp only [hAu, hAv] at j1 j2 ⊢
    linear_combination j2 - j1

end NonUniqueEuler.EvansRangeAux
