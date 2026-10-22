import NonUniqueEuler.Defs.SmoothB.Iteration
import NonUniqueEuler.I.Sec2.BSSmooth
import NonUniqueEuler.I.Infra.BSParam.ContDiff
import NonUniqueEuler.H.SmoothB.IterLimit.Bootstrap.Good
import NonUniqueEuler.H.SmoothB.IterLimit.Bootstrap.Partial

/-!
# Proof: `prop:iter-limit`, step 5 — space–time smoothness by bootstrapping the equation

Proof of `I/SmoothB/IterLimit/Bootstrap.lean` (`B_global_smooth.tex:449-472`).

Write `φ_t = ω(t)` viewed as complex valued, `F_γ(t, x) = ∂_x^γ φ_t(x)`, `v = K_BS ∗ ω`. We show by
induction on `n` that `Good n (ofRealST ω)`: every `F_γ` is `C^n` on `ℝ × ℝ²`
(`Good` is defined in `H/SmoothB/IterLimit/Bootstrap/Good.lean`).
* `n = 0`: the hypothesis `hcont`.
* `Good n (ofRealST ω) ⇒ Good n v` (`good_velocity`): `∂^γ v(t) = K_BS ∗ Re F_γ(t)`
  (`BS.partialD_velocity_of_smooth`), and `Re F_γ` is `C^n` with locally bounded supports, so
  `BS.contDiff_velocityField_of_slabSupport` applies.
* `Good n (ofRealST ω) ⇒ Good n (v · ∇ω)` (`good_transport`):
  `v · ∇ω = Re v ∂₁φ + Im v ∂₂φ`, and `Good` is closed under sums, products, real-linear maps and
  spatial derivatives.
* `Good n ⇒ Good (n+1)` (`good_succ`): `∂_t F_γ = -∂^γ(v · ∇ω)` (hypothesis `heq`) and
  `∂_l F_γ = F_{e_l + γ}` are `C^n`, so `F_γ` is `C^{n+1}` (`contDiff_succ_of_partials`).
Finally `F_0 = ω` (as complex values) is `C^n` for all `n`.

**Deviation.** The manuscript's classes `𝒞^l(T)` and Schwarz's theorem are replaced by the
`C^{n+1}`-from-partials criterion (as planned in the interface docstring).
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler.Smooth

namespace BootstrapAux

open Sob

variable {ω : ℝ → ℂ → ℝ}

/-- `x ↦ (Re x : ℂ)` as a real-linear map. -/
def reC : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.reCLM

/-- `x ↦ (Im x : ℂ)` as a real-linear map. -/
def imC : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.imCLM

theorem reC_apply (z : ℂ) : reC z = (z.re : ℂ) := rfl

theorem imC_apply (z : ℂ) : imC z = (z.im : ℂ) := rfl

theorem hasCompactSupport_slice
    (hsupp : ∀ T : ℝ, ∃ ρ : ℝ, ∀ t ∈ Icc (-T) T, ∀ x : ℂ, ρ < ‖x‖ → ω t x = 0) (t : ℝ) :
    HasCompactSupport (ω t) := by
  obtain ⟨ρ, hρ⟩ := hsupp |t|
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) ρ) fun x hx => ?_
  refine hρ t ⟨neg_abs_le t, le_abs_self t⟩ x ?_
  simpa [Metric.mem_closedBall, not_le] using hx

theorem spaceD_ofRealST_eq_zero
    (hsupp : ∀ T : ℝ, ∃ ρ : ℝ, ∀ t ∈ Icc (-T) T, ∀ x : ℂ, ρ < ‖x‖ → ω t x = 0) (γ : ℕ × ℕ) :
    ∀ T : ℝ, ∃ ρ : ℝ, ∀ t ∈ Icc (-T) T, ∀ x : ℂ, ρ < ‖x‖ → spaceD γ (ofRealST ω) t x = 0 := by
  intro T
  obtain ⟨ρ, hρ⟩ := hsupp T
  refine ⟨ρ, fun t ht x hx => ?_⟩
  exact iterDirDeriv_eq_zero_of_isOpen (U := {y : ℂ | ρ < ‖y‖})
    (isOpen_lt continuous_const continuous_norm)
    (fun y hy => by simp [ofRealST, hρ t ht y hy]) _ x hx

theorem good_zero (hsm : ∀ t, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ω t))
    (hcont : ∀ γ : ℕ × ℕ, Continuous (fun p : ℝ × ℂ => spaceD γ (ofRealST ω) p.1 p.2)) :
    Good 0 (ofRealST ω) where
  smooth t := Complex.ofRealCLM.contDiff.comp (hsm t)
  cont γ := by
    rw [Nat.cast_zero, contDiff_zero]
    exact hcont γ

theorem good_velocity {n : ℕ} (hsm : ∀ t, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ω t))
    (hsupp : ∀ T : ℝ, ∃ ρ : ℝ, ∀ t ∈ Icc (-T) T, ∀ x : ℂ, ρ < ‖x‖ → ω t x = 0)
    (h : Good n (ofRealST ω)) : Good n (velocityField ω) where
  smooth t := (BS.contDiff_velocity_of_smooth (hsm t) (hasCompactSupport_slice hsupp t)).1
  cont γ := by
    set G : ℝ → ℂ → ℝ := fun t x => (spaceD γ (ofRealST ω) t x).re with hG
    have hGc : ContDiff ℝ ((n : ℕ∞) : WithTop ℕ∞) (Function.uncurry G) :=
      Complex.reCLM.contDiff.comp (h.cont γ)
    have hGs : ∀ T : ℝ, ∃ ρ : ℝ, ∀ t ∈ Icc (-T) T, ∀ x : ℂ, ρ < ‖x‖ → G t x = 0 := by
      intro T
      obtain ⟨ρ, hρ⟩ := spaceD_ofRealST_eq_zero hsupp γ T
      exact ⟨ρ, fun t ht x hx => by simp [hG, hρ t ht x hx]⟩
    have hv := BS.contDiff_velocityField_of_slabSupport hGc hGs
    have he : (fun p : ℝ × ℂ => spaceD γ (velocityField ω) p.1 p.2) =
        Function.uncurry (velocityField G) := by
      funext p
      show Sob.partialD γ (velocity (ω p.1)) p.2 = velocity (G p.1) p.2
      rw [BS.partialD_velocity_of_smooth (hsm p.1) (hasCompactSupport_slice hsupp p.1) γ]
      rfl
    rw [he]
    exact hv

/-- `v · ∇ω = Re v ∂₁ω + Im v ∂₂ω`. -/
theorem transport_eq (hsm : ∀ t, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ω t)) :
    (fun s y => ((fderiv ℝ (ω s) y (velocityField ω s y) : ℝ) : ℂ)) =
      fun s y => reC (velocityField ω s y) * Sob.partialD (1, 0) (ofRealST ω s) y +
        imC (velocityField ω s y) * Sob.partialD (0, 1) (ofRealST ω s) y := by
  funext s y
  have hd : DifferentiableAt ℝ (ω s) y := (hsm s).differentiable (by simp) y
  have h1 : Sob.partialD (1, 0) (ofRealST ω s) y = ((fderiv ℝ (ω s) y 1 : ℝ) : ℂ) :=
    fderiv_ofReal_apply hd 1
  have h2 : Sob.partialD (0, 1) (ofRealST ω s) y = ((fderiv ℝ (ω s) y Complex.I : ℝ) : ℂ) :=
    fderiv_ofReal_apply hd Complex.I
  rw [h1, h2, reC_apply, imC_apply, clm_apply_eq_re_im' (fderiv ℝ (ω s) y)]
  simp only [smul_eq_mul, Complex.ofReal_add, Complex.ofReal_mul]

theorem good_transport {n : ℕ} (hsm : ∀ t, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ω t))
    (hsupp : ∀ T : ℝ, ∃ ρ : ℝ, ∀ t ∈ Icc (-T) T, ∀ x : ℂ, ρ < ‖x‖ → ω t x = 0)
    (h : Good n (ofRealST ω)) :
    Good n (fun s y => ((fderiv ℝ (ω s) y (velocityField ω s y) : ℝ) : ℂ)) := by
  rw [transport_eq hsm]
  have hv := good_velocity hsm hsupp h
  exact ((hv.clm reC).mul (h.partialD (1, 0))).add ((hv.clm imC).mul (h.partialD (0, 1)))

theorem good_succ {n : ℕ} (hsm : ∀ t, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ω t))
    (hsupp : ∀ T : ℝ, ∃ ρ : ℝ, ∀ t ∈ Icc (-T) T, ∀ x : ℂ, ρ < ‖x‖ → ω t x = 0)
    (heq : ∀ (γ : ℕ × ℕ) (t : ℝ) (x : ℂ), HasDerivAt (fun s => spaceD γ (ofRealST ω) s x)
      (-(spaceD γ (fun s y => ((fderiv ℝ (ω s) y (velocityField ω s y) : ℝ) : ℂ)) t x)) t)
    (h : Good n (ofRealST ω)) : Good (n + 1) (ofRealST ω) where
  smooth := h.smooth
  cont γ := by
    have hT := good_transport hsm hsupp h
    have hF : ∀ δ : ℕ × ℕ, ContDiff ℝ n
        (fun p : ℝ × ℂ => Sob.partialD δ (spaceD γ (ofRealST ω) p.1) p.2) := by
      intro δ
      have he : (fun p : ℝ × ℂ => Sob.partialD δ (spaceD γ (ofRealST ω) p.1) p.2) =
          fun p => spaceD (δ + γ) (ofRealST ω) p.1 p.2 := by
        funext p
        exact congrFun (partialD_partialD (h.smooth p.1) δ γ) p.2
      rw [he]
      exact h.cont (δ + γ)
    exact contDiff_succ_of_partials (F := spaceD γ (ofRealST ω))
      (Ft := fun p => -(spaceD γ (fun s y => ((fderiv ℝ (ω s) y (velocityField ω s y) : ℝ) : ℂ))
        p.1 p.2))
      (fun p => heq γ p.1 p.2) (fun t => differentiable_partialD (h.smooth t) γ)
      (hT.cont γ).neg (hF (1, 0)) (hF (0, 1))

end BootstrapAux

open BootstrapAux in
/-- `prop:iter-limit`, step 5 (`B_global_smooth.tex:449-472`): a function whose spatial
derivatives are jointly continuous, with locally bounded supports, satisfying
`∂_t ∂_x^γ ω = -∂_x^γ(v · ∇ω)` for all `γ` (`v = K_BS ∗ ω`), is `C^∞` on `ℝ × ℝ²`. -/
theorem contDiff_uncurry_of_transport {ω : ℝ → ℂ → ℝ}
    (hsm : ∀ t, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ω t))
    (hcont : ∀ γ : ℕ × ℕ, Continuous (fun p : ℝ × ℂ => spaceD γ (ofRealST ω) p.1 p.2))
    (hsupp : ∀ T : ℝ, ∃ ρ : ℝ, ∀ t ∈ Icc (-T) T, ∀ x : ℂ, ρ < ‖x‖ → ω t x = 0)
    (heq : ∀ (γ : ℕ × ℕ) (t : ℝ) (x : ℂ), HasDerivAt (fun s => spaceD γ (ofRealST ω) s x)
      (-(spaceD γ (fun s y => ((fderiv ℝ (ω s) y (velocityField ω s y) : ℝ) : ℂ)) t x)) t) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry ω) := by
  have hall : ∀ n : ℕ, Good n (ofRealST ω) := by
    intro n
    induction n with
    | zero => exact good_zero hsm hcont
    | succ n ih => exact good_succ hsm hsupp heq ih
  have hC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℂ => (ω p.1 p.2 : ℂ)) :=
    contDiff_infty.2 fun n => (hall n).cont (0, 0)
  have he : (fun p : ℝ × ℂ => Complex.reCLM ((ω p.1 p.2 : ℂ))) = Function.uncurry ω := by
    funext p
    simp [Function.uncurry]
  rw [← he]
  exact Complex.reCLM.contDiff.comp hC

end NonUniqueEuler.Smooth
