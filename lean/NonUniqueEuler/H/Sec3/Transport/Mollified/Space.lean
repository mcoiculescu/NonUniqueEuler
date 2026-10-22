import NonUniqueEuler.H.Sec3.Transport.Mollified.Basic
import NonUniqueEuler.I.Infra.Sobolev.DivFreeC1
import NonUniqueEuler.I.Sec3.CommFormula
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Helper for `P/Sec3/Transport/Mollified`: the space part (step 3)

Step 3 of the sketch in `I/Sec3/Transport/Mollified.lean` (`03_compactness.tex:505-508`): for a
weakly divergence-free `v ∈ L¹_loc`, `f ∈ C¹` and `ψ ∈ C¹_c`,
`∫ f v·∇ψ = -∫ ψ v·∇f` (`integral_mul_fderiv_eq_neg`), from the `C¹_c` form of
`div v = 0` (`I/Infra/Sobolev/DivFreeC1.lean`) applied to `ψ f` and the product rule. With
`f = Υ(u(t) ⋆ ρ_ε)` and `ψ = φ(t,·)` this gives, for a.e. `t`,
`∫ Υ(u_ε(t)) w(t)·∇φ(t) = -∫ φ(t) Υ'(u_ε(t)) w(t)·∇u_ε(t)` (`integral_renorm_spaceDeriv`),
where `w·∇u_ε = dotGradMollify` (`dotGradMollify_eq_fderiv`, `I/Sec3/CommFormula.lean`).
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace NonUniqueEuler.Weak.MollifiedH

/-- `x ↦ L(x)(v(x))` is integrable for `L` continuous with compact support and `v ∈ L¹_loc`. -/
theorem integrable_clm_apply_of_hasCompactSupport {L : ℂ → ℂ →L[ℝ] ℝ} (hL : Continuous L)
    (hLc : HasCompactSupport L) {v : ℂ → ℂ} (hv : LocallyIntegrable v volume) :
    Integrable (fun x => L x (v x)) := by
  have hn : Integrable (fun x => ‖L x‖ • v x) :=
    hv.integrable_smul_left_of_hasCompactSupport hL.norm hLc.norm
  refine hn.norm.mono' ?_ (ae_of_all _ fun x => ?_)
  · exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂
      hL.aestronglyMeasurable hv.aestronglyMeasurable
  · rw [norm_smul, norm_norm]
    exact (L x).le_opNorm _

/-- Integration by parts against a weakly divergence-free field: `∫ f v·∇ψ = -∫ ψ v·∇f` for
`f ∈ C¹`, `ψ ∈ C¹_c` (`03_compactness.tex:505-508`). -/
theorem integral_mul_fderiv_eq_neg {v : ℂ → ℂ} (hdiv : Prelim.IsWeaklyDivFree v)
    (hv : LocallyIntegrable v volume) {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) {ψ : ℂ → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, f x * fderiv ℝ ψ x (v x) = -∫ x, ψ x * fderiv ℝ f x (v x) := by
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hψd : Differentiable ℝ ψ := hψ.differentiable one_ne_zero
  have ha : Integrable (fun x => (f x • fderiv ℝ ψ x) (v x)) :=
    integrable_clm_apply_of_hasCompactSupport
      (hf.continuous.smul (hψ.continuous_fderiv one_ne_zero)) (hψc.fderiv (𝕜 := ℝ)).smul_left hv
  have hb : Integrable (fun x => (ψ x • fderiv ℝ f x) (v x)) :=
    integrable_clm_apply_of_hasCompactSupport
      (hψ.continuous.smul (hf.continuous_fderiv one_ne_zero)) hψc.smul_right hv
  obtain ⟨-, h0⟩ := hdiv.integral_fderiv_eq_zero_of_contDiff_one hv (hψ.mul hf)
    hψc.mul_right
  have hsplit : ∀ x, fderiv ℝ (fun y => ψ y * f y) x (v x) =
      (ψ x • fderiv ℝ f x) (v x) + (f x • fderiv ℝ ψ x) (v x) := by
    intro x
    rw [fderiv_fun_mul (hψd x) (hfd x)]
    rfl
  simp_rw [hsplit] at h0
  rw [integral_add hb ha] at h0
  have e1 : ∫ x, f x * fderiv ℝ ψ x (v x) = ∫ x, (f x • fderiv ℝ ψ x) (v x) := by
    congr 1
  have e2 : ∫ x, ψ x * fderiv ℝ f x (v x) = ∫ x, (ψ x • fderiv ℝ f x) (v x) := by
    congr 1
  rw [e1, e2]
  linarith

/-- Step 3 at a fixed time: `∫ Υ(u_ε(t)) w(t)·∇φ(t) = -∫ φ(t) Υ'(u_ε(t)) w(t)·∇u_ε(t)`, for
`u(t), w(t) ∈ L¹_loc` with `div w(t) = 0`. -/
theorem integral_renorm_spaceDeriv {ρ : ℂ → ℝ} (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    {T : ℝ} {u : ℝ → ℂ → ℝ} {w : ℝ → ℂ → ℂ} {t : ℝ} (hu : LocallyIntegrable (u t) volume)
    (hw : LocallyIntegrable (w t) volume) (hdiv : Prelim.IsWeaklyDivFree (w t))
    {Υ : ℝ → ℝ} (hΥ : IsRenormalization Υ) {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) :
    ∫ x, Υ (mollify ρ ε (u t) x) * spaceDeriv φ t x (w t x) =
      -∫ x, φ (t, x) * deriv Υ (mollify ρ ε (u t) x) * dotGradMollify ρ ε u w t x := by
  obtain ⟨hU, hG⟩ := dotGradMollify_eq_fderiv (w := w) hρ hε hu
  have hU1 : ContDiff ℝ 1 (mollify ρ ε (u t)) := hU.of_le (by exact_mod_cast le_top)
  have hUd : Differentiable ℝ (mollify ρ ε (u t)) := hU1.differentiable one_ne_zero
  have hΥd : Differentiable ℝ Υ := hΥ.contDiff.differentiable one_ne_zero
  obtain ⟨hψ, hψc⟩ := slice_contDiff_hasCompactSupport hφ t
  have h := integral_mul_fderiv_eq_neg (f := fun y => Υ (mollify ρ ε (u t) y)) hdiv hw
    (hΥ.contDiff.comp hU1)
    (hψ.of_le (by exact_mod_cast le_top)) hψc
  have hchain : ∀ x, fderiv ℝ (fun y => Υ (mollify ρ ε (u t) y)) x (w t x) =
      deriv Υ (mollify ρ ε (u t) x) * dotGradMollify ρ ε u w t x := by
    intro x
    have hd : HasFDerivAt (fun y => Υ (mollify ρ ε (u t) y))
        (deriv Υ (mollify ρ ε (u t) x) • fderiv ℝ (mollify ρ ε (u t)) x) x :=
      (hΥd _).hasDerivAt.comp_hasFDerivAt x (hUd x).hasFDerivAt
    rw [hd.fderiv, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, hG x]
  have e : ∀ x, φ (t, x) * fderiv ℝ (fun y => Υ (mollify ρ ε (u t) y)) x (w t x) =
      φ (t, x) * deriv Υ (mollify ρ ε (u t) x) * dotGradMollify ρ ε u w t x := by
    intro x
    rw [hchain x, mul_assoc]
  rw [show (fun x => φ (t, x) * deriv Υ (mollify ρ ε (u t) x) * dotGradMollify ρ ε u w t x) =
      fun x => φ (t, x) * fderiv ℝ (fun y => Υ (mollify ρ ε (u t) y)) x (w t x) from
    funext fun x => (e x).symm]
  exact h

end NonUniqueEuler.Weak.MollifiedH
