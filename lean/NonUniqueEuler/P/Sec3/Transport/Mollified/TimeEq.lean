import NonUniqueEuler.Defs.Sec3.Transport
import NonUniqueEuler.Defs.Sec3.Commutator
import NonUniqueEuler.Defs.Sec2.Spaces
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Proof: the time equation of `u ⋆ ρ_ε (·, x)` (step 1 of the mollified identity)

Proof of `I/Sec3/Transport/Mollified/TimeEq.lean` (`03_compactness.tex:494-500`).

We test `(te)` with `ψ(s,y) = α(s) ρ_ε(x - y)` (a test function by `isTestFunction_mul`). Then
`∂_s ψ = α' ρ_ε(x - ·)` and `w·∇_y ψ = -α Dρ_ε(x - ·) w`, so the inner integrand of `(te)` is
`α'(s) u(s,y) ρ_ε(x-y) - α(s) u(s,y) Dρ_ε(x-y) w(s,y)`. For a.e. `s ∈ (t₀,T)` both terms are
integrable in `y` (`u(s) ∈ L¹`, `u(s)w(s) ∈ L¹` by Fubini, and `ρ_ε`, `Dρ_ε` are bounded), so the
inner integral is `α'(s) U(s) - α(s) D(s)`. The datum term is `α(t₀) (u₀ ⋆ ρ_ε)(x)`.

Helper lemmas are in the namespace `NonUniqueEuler.Weak.MollifiedTimeEqH`.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler.Weak

namespace MollifiedTimeEqH

variable {ρ : ℂ → ℝ}

/-! ### The kernel `ρ_ε` and its reflection `y ↦ ρ_ε(x - y)` -/

theorem contDiff_scaled (hρ : IsMollifier ρ) (ε : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (scaled ρ ε) :=
  contDiff_const.mul (hρ.contDiff.comp (contDiff_const.mul contDiff_id))

theorem hasCompactSupport_scaled (hρ : IsMollifier ρ) {ε : ℝ} (hε : ε ≠ 0) :
    HasCompactSupport (scaled ρ ε) := by
  have hε' : ((ε : ℂ)⁻¹) ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.2 hε)
  have hc : HasCompactSupport (fun x : ℂ => ρ ((ε : ℂ)⁻¹ * x)) :=
    hρ.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft₀ _ hε')
  exact hc.mul_left

theorem differentiable_scaled (hρ : IsMollifier ρ) (ε : ℝ) : Differentiable ℝ (scaled ρ ε) :=
  (contDiff_scaled hρ ε).differentiable (by simp)

/-- `ρ_ε` is bounded. -/
theorem exists_bound_scaled (hρ : IsMollifier ρ) {ε : ℝ} (hε : ε ≠ 0) :
    ∃ C : ℝ, ∀ z, ‖scaled ρ ε z‖ ≤ C :=
  (contDiff_scaled hρ ε).continuous.bounded_above_of_compact_support
    (hasCompactSupport_scaled hρ hε)

/-- `Dρ_ε` is bounded. -/
theorem exists_bound_fderiv_scaled (hρ : IsMollifier ρ) {ε : ℝ} (hε : ε ≠ 0) :
    ∃ C : ℝ, ∀ z, ‖fderiv ℝ (scaled ρ ε) z‖ ≤ C :=
  ((contDiff_scaled hρ ε).continuous_fderiv (by simp)).bounded_above_of_compact_support
    ((hasCompactSupport_scaled hρ hε).fderiv (𝕜 := ℝ))

theorem continuous_fderiv_scaled (hρ : IsMollifier ρ) (ε : ℝ) :
    Continuous (fderiv ℝ (scaled ρ ε)) :=
  (contDiff_scaled hρ ε).continuous_fderiv (by simp)

/-- The reflected kernel `y ↦ ρ_ε(x - y)` is `C^∞`. -/
theorem contDiff_reflect (hρ : IsMollifier ρ) (ε : ℝ) (x : ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℂ => scaled ρ ε (x - y)) :=
  (contDiff_scaled hρ ε).comp (contDiff_const.sub contDiff_id)

/-- The reflected kernel `y ↦ ρ_ε(x - y)` has compact support. -/
theorem hasCompactSupport_reflect (hρ : IsMollifier ρ) {ε : ℝ} (hε : ε ≠ 0) (x : ℂ) :
    HasCompactSupport (fun y : ℂ => scaled ρ ε (x - y)) := by
  have h := (hasCompactSupport_scaled hρ hε).comp_homeomorph (Homeomorph.subLeft x)
  exact h

/-- `D_y [ρ_ε(x - y)] v = -Dρ_ε(x - y) v`. -/
theorem fderiv_reflect_apply (hρ : IsMollifier ρ) (ε : ℝ) (x y v : ℂ) :
    fderiv ℝ (fun y : ℂ => scaled ρ ε (x - y)) y v = -fderiv ℝ (scaled ρ ε) (x - y) v := by
  have h1 : HasFDerivAt (fun y : ℂ => x - y) (-ContinuousLinearMap.id ℝ ℂ) y :=
    (hasFDerivAt_id y).const_sub x
  have h2 : HasFDerivAt (scaled ρ ε) (fderiv ℝ (scaled ρ ε) (x - y)) (x - y) :=
    (differentiable_scaled hρ ε (x - y)).hasFDerivAt
  have h3 : HasFDerivAt (fun y : ℂ => scaled ρ ε (x - y))
      ((fderiv ℝ (scaled ρ ε) (x - y)).comp (-ContinuousLinearMap.id ℝ ℂ)) y := h2.comp y h1
  rw [h3.fderiv]
  simp

/-! ### Derivatives of the test function `α(s) ρ_ε(x - y)` -/

theorem timeDeriv_mul {α : ℝ → ℝ} (hα : Differentiable ℝ α) (k : ℂ → ℝ) (s : ℝ) (y : ℂ) :
    timeDeriv (fun p : ℝ × ℂ => α p.1 * k p.2) s y = deriv α s * k y := by
  show deriv (fun s' : ℝ => α s' * k y) s = deriv α s * k y
  exact deriv_mul_const (hα s) (k y)

theorem spaceDeriv_mul (α : ℝ → ℝ) {k : ℂ → ℝ} (hk : Differentiable ℝ k) (s : ℝ) (y v : ℂ) :
    spaceDeriv (fun p : ℝ × ℂ => α p.1 * k p.2) s y v = α s * fderiv ℝ k y v := by
  show fderiv ℝ (fun y' : ℂ => α s * k y') y v = α s * fderiv ℝ k y v
  rw [fderiv_const_mul (hk y) (α s)]
  rfl

/-- The integrand of `(te)` for `ψ(s,y) = α(s) ρ_ε(x - y)`. -/
theorem transportIntegrand_eq (hρ : IsMollifier ρ) (ε : ℝ) {α : ℝ → ℝ}
    (hα : Differentiable ℝ α) (u : ℝ → ℂ → ℝ) (w : ℝ → ℂ → ℂ) (x : ℂ) (s : ℝ) (y : ℂ) :
    transportIntegrand u w (fun p : ℝ × ℂ => α p.1 * scaled ρ ε (x - p.2)) (s, y) =
      deriv α s * (u s y * scaled ρ ε (x - y)) -
        α s * (u s y * fderiv ℝ (scaled ρ ε) (x - y) (w s y)) := by
  have hk : Differentiable ℝ (fun y : ℂ => scaled ρ ε (x - y)) :=
    (contDiff_reflect hρ ε x).differentiable (by simp)
  have ht := timeDeriv_mul hα (fun y : ℂ => scaled ρ ε (x - y)) s y
  have hs := spaceDeriv_mul α hk s y (w s y)
  simp only [transportIntegrand]
  rw [ht, hs, fderiv_reflect_apply hρ ε x y (w s y)]
  ring

/-! ### Integrability of the slices -/

/-- For a.e. `s ∈ (t₀,T)`, `u(s) ∈ L¹` and `u(s) w(s) ∈ L¹`. -/
theorem ae_integrable_slices {T t₀ : ℝ} (ht₀ : 0 ≤ t₀) {w : ℝ → ℂ → ℂ} {u : ℝ → ℂ → ℝ}
    (hu1 : Prelim.MemLinfLp (Ioo 0 T) univ 1 u)
    (huw : Integrable (fun p : ℝ × ℂ => u p.1 p.2 • w p.1 p.2) (volume.restrict (slab T))) :
    ∀ᵐ s ∂(volume.restrict (Ioo t₀ T)),
      Integrable (u s) ∧ Integrable (fun y => u s y • w s y) := by
  obtain ⟨M, hM⟩ := hu1.essBounded
  have hprod : volume.restrict (slab T) =
      (volume.restrict (Ioo (0 : ℝ) T)).prod (volume : Measure ℂ) := by
    rw [slab, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  rw [hprod] at huw
  have h2 := huw.prod_right_ae
  have h0 : ∀ᵐ s ∂(volume.restrict (Ioo (0 : ℝ) T)),
      Integrable (u s) ∧ Integrable (fun y => u s y • w s y) := by
    filter_upwards [hM, h2] with s hs hs2
    refine ⟨?_, hs2⟩
    have h := hs.1
    rw [Measure.restrict_univ] at h
    exact memLp_one_iff_integrable.1 h
  exact ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_left ht₀) h0

/-- `y ↦ u(y) ρ_ε(x - y)` is integrable for `u ∈ L¹`. -/
theorem integrable_mul_reflect (hρ : IsMollifier ρ) {ε : ℝ} (hε : ε ≠ 0) (x : ℂ) {g : ℂ → ℝ}
    (hg : Integrable g) : Integrable (fun y => g y * scaled ρ ε (x - y)) := by
  obtain ⟨C, hC⟩ := exists_bound_scaled hρ hε
  exact hg.mul_bdd (contDiff_reflect hρ ε x).continuous.aestronglyMeasurable
    (ae_of_all _ fun y => hC (x - y))

/-- `y ↦ u(y) Dρ_ε(x - y) w(y)` is integrable for `u w ∈ L¹`. -/
theorem integrable_mul_fderiv_reflect (hρ : IsMollifier ρ) {ε : ℝ} (hε : ε ≠ 0) (x : ℂ)
    {g : ℂ → ℝ} {v : ℂ → ℂ} (hgv : Integrable (fun y => g y • v y)) :
    Integrable (fun y => g y * fderiv ℝ (scaled ρ ε) (x - y) (v y)) := by
  obtain ⟨C, hC⟩ := exists_bound_fderiv_scaled hρ hε
  have heq : (fun y => g y * fderiv ℝ (scaled ρ ε) (x - y) (v y)) =
      fun y => fderiv ℝ (scaled ρ ε) (x - y) (g y • v y) := by
    funext y
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
  rw [heq]
  have hL : Continuous (fun y : ℂ => fderiv ℝ (scaled ρ ε) (x - y)) :=
    (continuous_fderiv_scaled hρ ε).comp (continuous_const.sub continuous_id)
  have hmeas : AEStronglyMeasurable (fun y => fderiv ℝ (scaled ρ ε) (x - y) (g y • v y)) volume :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂
      hL.aestronglyMeasurable hgv.aestronglyMeasurable
  refine (hgv.norm.const_mul C).mono' hmeas (ae_of_all _ fun y => ?_)
  refine ((fderiv ℝ (scaled ρ ε) (x - y)).le_opNorm _).trans ?_
  exact mul_le_mul_of_nonneg_right (hC (x - y)) (norm_nonneg _)

end MollifiedTimeEqH

open MollifiedTimeEqH in
/-- Step 1 of the mollified identity (`03_compactness.tex:494-500`): at every `x`, the
mollification `U(s) = u(s) ⋆ ρ_ε (x)` satisfies `∂_s U = -(div(wu)) ⋆ ρ_ε (·,x)` on `[t₀,T)`
weakly, with datum `u₀ ⋆ ρ_ε (x)`:
`∫_{t₀}^T (α' U - α (div(wu)) ⋆ ρ_ε (·,x)) + α(t₀) (u₀ ⋆ ρ_ε)(x) = 0` for every
`α ∈ C_c^∞((-∞,T))`. -/
theorem mollify_timeEq {ρ : ℂ → ℝ} (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    {T t₀ : ℝ} (ht₀ : t₀ ∈ Ico 0 T) {w : ℝ → ℂ → ℂ} {u : ℝ → ℂ → ℝ} {u₀ : ℂ → ℝ}
    (hu1 : Prelim.MemLinfLp (Ioo 0 T) univ 1 u)
    (huw : Integrable (fun p : ℝ × ℂ => u p.1 p.2 • w p.1 p.2) (volume.restrict (slab T)))
    (hte : SolvesTE t₀ T u w u₀) (x : ℂ) {α : ℝ → ℝ} (hα : IsTimeTestFn T α) :
    (∫ s in Ioo t₀ T, (deriv α s * mollify ρ ε (u s) x - α s * mollifyDiv ρ ε u w s x)) +
      α t₀ * mollify ρ ε u₀ x = 0 := by
  have hε0 : ε ≠ 0 := hε.ne'
  have hαd : Differentiable ℝ α := hα.contDiff.differentiable (by simp)
  set ψ : ℝ × ℂ → ℝ := fun p => α p.1 * scaled ρ ε (x - p.2) with hψdef
  have hψ : IsTestFunction T ψ :=
    isTestFunction_mul hα (contDiff_reflect hρ ε x) (hasCompactSupport_reflect hρ hε0 x)
  have hid := hte.identity ψ hψ
  -- the datum term
  have hdatum : ∫ y : ℂ, u₀ y * ψ (t₀, y) = α t₀ * mollify ρ ε u₀ x := by
    have : (fun y : ℂ => u₀ y * ψ (t₀, y)) =
        fun y => α t₀ * (u₀ y * scaled ρ ε (x - y)) := by
      funext y
      simp only [hψdef]
      ring
    rw [this, integral_const_mul]
    rfl
  -- the inner integrals agree for a.e. `s`
  have hinner : ∀ᵐ s ∂(volume.restrict (Ioo t₀ T)),
      ∫ y : ℂ, transportIntegrand u w ψ (s, y) =
        deriv α s * mollify ρ ε (u s) x - α s * mollifyDiv ρ ε u w s x := by
    filter_upwards [ae_integrable_slices ht₀.1 hu1 huw] with s hs
    have hA := integrable_mul_reflect hρ hε0 x hs.1
    have hB := integrable_mul_fderiv_reflect hρ hε0 x hs.2
    have hpt : (fun y : ℂ => transportIntegrand u w ψ (s, y)) =
        fun y => deriv α s * (u s y * scaled ρ ε (x - y)) -
          α s * (u s y * fderiv ℝ (scaled ρ ε) (x - y) (w s y)) := by
      funext y
      exact transportIntegrand_eq hρ ε hαd u w x s y
    rw [hpt, integral_sub (hA.const_mul _) (hB.const_mul _), integral_const_mul,
      integral_const_mul]
    rfl
  have houter : (∫ s in Ioo t₀ T, ∫ y : ℂ, transportIntegrand u w ψ (s, y)) =
      ∫ s in Ioo t₀ T, (deriv α s * mollify ρ ε (u s) x - α s * mollifyDiv ρ ε u w s x) :=
    integral_congr_ae hinner
  rw [← houter, ← hdatum]
  exact hid

end NonUniqueEuler.Weak
