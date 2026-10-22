import NonUniqueEuler.I.SmoothB.Smooth
import NonUniqueEuler.Defs.Infra.Polar
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Proof: thm:smooth (6) (rotational symmetry is preserved)

Proof of `I/SmoothB/SmoothRot.lean` (`thm:smooth`(6), `02_prelim.tex:586-587`; proof
`B_global_smooth.tex:533-545`, restructuring R16: from the uniqueness (5)).

Let `ω = sol ω₀` and `ω_θ(t, x) = ω(t, O_θ x)` (the manuscript writes `O_θ⁻¹`; both are the same
argument since `O_θ⁻¹ = O_{-θ}` is again a rotation).
* `RotAux.velocity_rot_comp`: `(K * g)(O_θ x) = O_θ (K * (g ∘ O_θ))(x)` (`K(O_θ z) = O_θ K(z)`
  and the substitution `y = O_θ z`, `rot` preserves `volume`). So the velocity of `ω_θ(t)` at `x`
  is `O_θ⁻¹ v(t, O_θ x)`.
* `RotAux.isC1SolOn_rot`: `ω_θ` is a `C¹` solution on `ℝ` with datum `ω₀ ∘ O_θ = ω₀` in the sense
  of (5): `C^∞` by composition, the chain rule gives
  `∂_t ω_θ + v_θ·∇ω_θ = (∂_t ω + v·∇ω)(t, O_θ x) = 0`, and `supp ω_θ(t) = O_θ⁻¹ supp ω(t)` lies
  in the same disk `B_{R(t)}`.
* `smooth_rot`: (5) (`smooth_unique` with `I = ℝ`) gives `ω_θ = ω`.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler.Smooth

namespace RotAux

/-- `K(O_θ z) = O_θ K(z)`. -/
theorem biotSavartKernel_rot (θ : ℝ) (z : ℂ) :
    biotSavartKernel (rot θ z) = rot θ (biotSavartKernel z) := by
  simp only [biotSavartKernel, Polar.norm_rot]
  simp only [rot]
  ring

theorem measurableEmbedding_rot (θ : ℝ) : MeasurableEmbedding (rot θ) := by
  rw [Polar.rot_eq_rotation]
  exact (rotation (Circle.exp θ)).toHomeomorph.measurableEmbedding

/-- Rotation covariance of the Biot–Savart law: `(K * g)(O_θ x) = O_θ (K * (g ∘ O_θ))(x)` for
every `g` and `x` (substitution `y = O_θ z`). -/
theorem velocity_rot_comp (g : ℂ → ℝ) (θ : ℝ) (x : ℂ) :
    velocity g (rot θ x) = rot θ (velocity (fun y => g (rot θ y)) x) := by
  unfold velocity
  rw [← (Polar.measurePreserving_rot θ).integral_comp (measurableEmbedding_rot θ)]
  have hsub : ∀ z, rot θ x - rot θ z = rot θ (x - z) := fun z => by simp [rot, mul_sub]
  simp_rw [hsub, biotSavartKernel_rot]
  rw [show rot θ (∫ y, biotSavartKernel (x - y) * (g (rot θ y) : ℂ)) =
      Complex.exp ((θ : ℂ) * Complex.I) * ∫ y, biotSavartKernel (x - y) * (g (rot θ y) : ℂ)
      from rfl, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [rot]
  ring

/-- The derivative of a differentiable space–time function `(t, x) ↦ ω(t, x)` in the direction
`(1, w)` is `∂_t ω(t, x) + ∇ω(t, x)·w`. -/
theorem fderiv_uncurry_one_apply' {ω : ℝ → ℂ → ℝ} {t : ℝ} {x : ℂ}
    (hd : DifferentiableAt ℝ (Function.uncurry ω) (t, x)) (w : ℂ) :
    fderiv ℝ (Function.uncurry ω) (t, x) (1, w) =
      deriv (fun s => ω s x) t + fderiv ℝ (ω t) x w := by
  set D := fderiv ℝ (Function.uncurry ω) (t, x) with hD
  have hf : HasFDerivAt (Function.uncurry ω) D (t, x) := hd.hasFDerivAt
  have ht : HasDerivAt (fun s => ω s x) (D (1, 0)) t := by
    have h1 : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : ℂ)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
    exact HasFDerivAt.comp_hasDerivAt (x := t) hf h1
  have hx : HasFDerivAt (ω t) (D.comp (ContinuousLinearMap.inr ℝ ℝ ℂ)) x := by
    exact HasFDerivAt.comp (x := x) hf (hasFDerivAt_prodMk_right (𝕜 := ℝ) t x)
  rw [ht.deriv, hx.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    ← map_add, Prod.mk_add_mk, add_zero, zero_add]

/-- The space–time change of variables `(t, x) ↦ (t, O_θ x)`. -/
def rotST (θ : ℝ) (p : ℝ × ℂ) : ℝ × ℂ := (p.1, rot θ p.2)

/-- Its (constant) derivative. -/
def rotSTL (θ : ℝ) : ℝ × ℂ →L[ℝ] ℝ × ℂ :=
  (ContinuousLinearMap.fst ℝ ℝ ℂ).prod
    (Complex.exp ((θ : ℂ) * Complex.I) • ContinuousLinearMap.snd ℝ ℝ ℂ)

theorem hasFDerivAt_rotST (θ : ℝ) (p : ℝ × ℂ) : HasFDerivAt (rotST θ) (rotSTL θ) p := by
  have h2 : HasFDerivAt (fun q : ℝ × ℂ => Complex.exp ((θ : ℂ) * Complex.I) * q.2)
      (Complex.exp ((θ : ℂ) * Complex.I) • ContinuousLinearMap.snd ℝ ℝ ℂ) p :=
    (hasFDerivAt_snd).const_mul _
  exact (hasFDerivAt_fst).prodMk h2

theorem rotSTL_apply (θ : ℝ) (s : ℝ) (w : ℂ) : rotSTL θ (s, w) = (s, rot θ w) := by
  simp [rotSTL, rot]

theorem contDiff_rotST (θ : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (rotST θ) :=
  contDiff_fst.prodMk (contDiff_const.mul contDiff_snd)

theorem continuous_rot (θ : ℝ) : Continuous (rot θ) :=
  continuous_const.mul continuous_id

/-- `ω_θ(t, x) = ω(t, O_θ x)` is a `C¹` solution on `ℝ` in the sense of thm:smooth(5), with datum
`ω₀ ∘ O_θ`, whenever `ω` has properties (1)–(3). -/
theorem isC1SolOn_rot {ω₀ : ℂ → ℝ} {R₀ : ℝ} {ω : ℝ → ℂ → ℝ} (hω : IsSmoothSol ω₀ R₀ ω)
    (θ : ℝ) : IsC1SolOn univ (fun x => ω₀ (rot θ x)) (fun t x => ω t (rot θ x)) := by
  have hC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry ω) := hω.contDiff
  have hcomp : Function.uncurry (fun t x => ω t (rot θ x)) =
      Function.uncurry ω ∘ rotST θ := rfl
  have hC1 : ContDiff ℝ 1 (Function.uncurry ω) := hC.of_le (by exact_mod_cast le_top)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hcomp]
    exact ((hC.comp (contDiff_rotST θ)).of_le (by exact_mod_cast le_top)).contDiffOn
  · funext x
    simp only [hω.init]
  · intro t _ x
    rw [univ_prod_univ, fderivWithin_univ, hcomp]
    have hD : HasFDerivAt (Function.uncurry ω ∘ rotST θ)
        ((fderiv ℝ (Function.uncurry ω) (t, rot θ x)).comp (rotSTL θ)) (t, x) :=
      HasFDerivAt.comp (x := (t, x))
        (hC1.differentiable one_ne_zero (rotST θ (t, x))).hasFDerivAt (hasFDerivAt_rotST θ _)
    rw [hD.fderiv, ContinuousLinearMap.comp_apply, rotSTL_apply,
      ← velocity_rot_comp (ω t) θ x,
      fderiv_uncurry_one_apply' (hC1.differentiable one_ne_zero _)]
    exact hω.transport t (rot θ x)
  · intro a b _
    refine ⟨suppRadius ω₀ R₀ (max |a| |b|), fun t ht => ?_⟩
    have hball : tsupport (ω t) ⊆ ball 0 (suppRadius ω₀ R₀ (max |a| |b|)) := by
      refine (hω.tsupport_subset t).trans (ball_subset_ball (suppRadius_mono_abs ω₀ R₀ ?_))
      rw [abs_of_nonneg (le_max_of_le_left (abs_nonneg a))]
      rcases le_total 0 t with h0 | h0
      · rw [abs_of_nonneg h0]
        exact (ht.2.trans (le_abs_self b)).trans (le_max_right _ _)
      · rw [abs_of_nonpos h0]
        have : -t ≤ -a := neg_le_neg ht.1
        exact (this.trans (neg_le_abs a)).trans (le_max_left _ _)
    intro x hx
    have hx' : rot θ x ∈ tsupport (ω t) :=
      tsupport_comp_subset_preimage (ω t) (continuous_rot θ) hx
    have := hball hx'
    rw [mem_ball_zero_iff, Polar.norm_rot] at this
    exact mem_ball_zero_iff.mpr this

end RotAux

variable {ω₀ : ℂ → ℝ} {R₀ : ℝ}

/-- thm:smooth (6): if `ω₀ ∘ O_θ = ω₀` for a rotation `O_θ ∈ SO(2)`, then `ω(t) ∘ O_θ = ω(t)` for
every `t ∈ ℝ`. -/
theorem smooth_rot (h : IsSmoothDatum ω₀ R₀) {θ : ℝ} (hθ : ∀ x : ℂ, ω₀ (rot θ x) = ω₀ x)
    (t : ℝ) (x : ℂ) :
    sol ω₀ t (rot θ x) = sol ω₀ t x := by
  have hsol := RotAux.isC1SolOn_rot (sol_isSmoothSol h) θ
  have hd : (fun x => ω₀ (rot θ x)) = ω₀ := funext hθ
  rw [hd] at hsol
  have := smooth_unique h ordConnected_univ (mem_univ 0) hsol t (mem_univ t)
  exact congrFun this x

end NonUniqueEuler.Smooth
