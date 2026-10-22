import NonUniqueEuler.I.SmoothB.IterLip
import NonUniqueEuler.H.SmoothB.IterCauchy.Basic
import NonUniqueEuler.H.SmoothB.IterCauchy.Calculus

/-!
# Helper for `lem:iter-cauchy`: the energy step

`B_global_smooth.tex:362-375`. For `j = k + 1 ≥ 1`, `δ = ω^{[j+1]} - ω^{[j]}` satisfies
`∂_t δ + v^{[j]}·∇δ = -(K ∗ (ω^{[j]} - ω^{[j-1]}))·∇ω^{[j]}`; multiplying by `δ` and integrating,
the transport term vanishes and

* `hasDerivAt_iterErr_sq`: `d/dt e_{j+1}² = -2 ∫ δ (v^{[j]} - v^{[j-1]})·∇ω^{[j]}`;
* `abs_integral_le`: `|∫ δ (v^{[j]} - v^{[j-1]})·∇ω^{[j]}| ≤ Ψ(T) e_{j+1}(t) · 2R(T) e_j(t)` for
  `|t| ≤ T` (`∇ω^{[j]}(t)` vanishes outside `B_R`, is bounded by `Ψ`, and `lem:BS-basic`(c)
  with `ρ = R`);
* `iterErr_sq_deriv_bound`: hence `|d/dt e_{j+1}²| ≤ 4RΨ e_j e_{j+1}`.

Fully proved (from the interfaces).
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace NonUniqueEuler.Smooth.IterCauchyAux

variable {ω₀ : ℂ → ℝ} {R₀ : ℝ}

/-- The energy identity: `d/dt e_{k+2}² = -2 ∫ δ (v^{[k+1]} - v^{[k]})·∇ω^{[k+1]}` with
`δ = ω^{[k+2]} - ω^{[k+1]}` (`B_global_smooth.tex:364-370`). -/
theorem hasDerivAt_iterErr_sq (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (k : ℕ) (t : ℝ) :
    HasDerivAt (fun τ => iterErr ω₀ (k + 2) τ ^ 2)
      (-2 * ∫ x, (iter ω₀ (k + 2) t x - iter ω₀ (k + 1) t x) *
        fderiv ℝ (iter ω₀ (k + 1) t) x (iterVel ω₀ (k + 1) t x - iterVel ω₀ k t x)) t := by
  set δ : ℝ → ℂ → ℝ := fun τ x => iter ω₀ (k + 2) τ x - iter ω₀ (k + 1) τ x with hδ_def
  have hδc : ContDiff ℝ 1 (Function.uncurry δ) :=
    (iter_contDiff h hne (k + 2)).sub (iter_contDiff h hne (k + 1))
  have hδsupp : ∀ T : ℝ, ∃ ρ : ℝ, ∀ τ ∈ Icc (-T) T, ∀ x : ℂ, ρ < ‖x‖ → δ τ x = 0 := by
    intro T
    refine ⟨suppRadius ω₀ R₀ T, fun τ hτ x hx => ?_⟩
    have hτ' : |τ| ≤ T := abs_le.2 hτ
    simp only [hδ_def, iter_eq_zero h hne _ hτ' hx.le, sub_zero]
  have hD := hasDerivAt_integral_sq hδc hδsupp t
  have hfun : (fun τ => iterErr ω₀ (k + 2) τ ^ 2) = fun τ => ∫ x, δ τ x ^ 2 := by
    funext τ
    have hm : MemLp (iter ω₀ (k + 2) τ - iter ω₀ (k + 1) τ) 2 volume :=
      (iter_memLp h hne (k + 2) τ 2).sub (iter_memLp h hne (k + 1) τ 2)
    rw [iterErr_succ, toReal_eLpNorm_two_sq hm]
    rfl
  rw [hfun]
  convert hD using 1
  -- the slices
  have hsl : ∀ j, ContDiff ℝ 1 (iter ω₀ j t) := fun j => iter_slice_contDiff h hne j t
  have hsld : ∀ j x, DifferentiableAt ℝ (iter ω₀ j t) x := fun j x =>
    ((hsl j).differentiable one_ne_zero) x
  have hδt : ContDiff ℝ 1 (δ t) := (hsl (k + 2)).sub (hsl (k + 1))
  have hδtc : HasCompactSupport (δ t) := iter_sub_hasCompactSupport h hne (k + 2) (k + 1) t
  have hdiffj : ∀ j x, DifferentiableAt ℝ (fun τ => iter ω₀ j τ x) t := fun j x =>
    (hasDerivAt_time (iter_contDiff h hne j) t x).differentiableAt
  -- the time derivative of `δ`
  have hdt : ∀ x, deriv (fun τ => δ τ x) t =
      -(fderiv ℝ (δ t) x (iterVel ω₀ (k + 1) t x)) -
        fderiv ℝ (iter ω₀ (k + 1) t) x (iterVel ω₀ (k + 1) t x - iterVel ω₀ k t x) := by
    intro x
    have e1 : deriv (fun τ => δ τ x) t =
        deriv (fun τ => iter ω₀ (k + 2) τ x) t - deriv (fun τ => iter ω₀ (k + 1) τ x) t :=
      deriv_sub (hdiffj (k + 2) x) (hdiffj (k + 1) x)
    have tr2 : deriv (fun τ => iter ω₀ (k + 2) τ x) t +
        fderiv ℝ (iter ω₀ (k + 2) t) x (iterVel ω₀ (k + 1) t x) = 0 :=
      (iterates_flow h hne (k + 1)).2.2.2.2 t x
    have tr1 : deriv (fun τ => iter ω₀ (k + 1) τ x) t +
        fderiv ℝ (iter ω₀ (k + 1) t) x (iterVel ω₀ k t x) = 0 :=
      (iterates_flow h hne k).2.2.2.2 t x
    have e2 : fderiv ℝ (δ t) x (iterVel ω₀ (k + 1) t x) =
        fderiv ℝ (iter ω₀ (k + 2) t) x (iterVel ω₀ (k + 1) t x) -
          fderiv ℝ (iter ω₀ (k + 1) t) x (iterVel ω₀ (k + 1) t x) := by
      have := fderiv_sub (hsld (k + 2) x) (hsld (k + 1) x)
      rw [show δ t = iter ω₀ (k + 2) t - iter ω₀ (k + 1) t from rfl, this]
      rfl
    rw [e1, e2, map_sub]
    linarith
  -- integrability
  have hcv : ∀ j, Continuous (iterVel ω₀ j t) := fun j =>
    (iterVel_slice_contDiff h hne j t).continuous
  have int1 : Integrable (fun x => δ t x * fderiv ℝ (δ t) x (iterVel ω₀ (k + 1) t x)) :=
    (hδt.continuous.mul ((hδt.continuous_fderiv one_ne_zero).clm_apply (hcv (k + 1)))
      ).integrable_of_hasCompactSupport hδtc.mul_right
  have int2 : Integrable (fun x => δ t x *
      fderiv ℝ (iter ω₀ (k + 1) t) x (iterVel ω₀ (k + 1) t x - iterVel ω₀ k t x)) :=
    (hδt.continuous.mul (((hsl (k + 1)).continuous_fderiv one_ne_zero).clm_apply
      ((hcv (k + 1)).sub (hcv k)))).integrable_of_hasCompactSupport hδtc.mul_right
  -- the transport term vanishes
  have htr : ∫ x, δ t x * fderiv ℝ (δ t) x (iterVel ω₀ (k + 1) t x) = 0 :=
    integral_mul_fderiv_apply_eq_zero hδt hδtc (iterVel_slice_contDiff h hne (k + 1) t)
      ((iterates_velocity h hne (k + 1)).2.2.1 t)
  have hpt : ∀ x, 2 * δ t x * deriv (fun τ => δ τ x) t =
      -2 * (δ t x * fderiv ℝ (δ t) x (iterVel ω₀ (k + 1) t x)) +
        -2 * (δ t x * fderiv ℝ (iter ω₀ (k + 1) t) x
          (iterVel ω₀ (k + 1) t x - iterVel ω₀ k t x)) := by
    intro x
    rw [hdt x]
    ring
  simp_rw [hpt]
  rw [integral_add (int1.const_mul _) (int2.const_mul _), integral_const_mul,
    integral_const_mul, htr]
  simp only [hδ_def, mul_zero, zero_add]

/-- The bound of the forcing term (`B_global_smooth.tex:370-373`): for `|t| ≤ T`,
`|∫ δ (v^{[k+1]} - v^{[k]})·∇ω^{[k+1]}| ≤ Ψ(T) e_{k+2}(t) · 2R(T) e_{k+1}(t)`. -/
theorem abs_integral_le (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (k : ℕ) {T : ℝ}
    {t : ℝ} (ht : t ∈ Icc (-T) T) :
    |∫ x, (iter ω₀ (k + 2) t x - iter ω₀ (k + 1) t x) *
        fderiv ℝ (iter ω₀ (k + 1) t) x (iterVel ω₀ (k + 1) t x - iterVel ω₀ k t x)| ≤
      Psi ω₀ T * (iterErr ω₀ (k + 2) t * (2 * suppRadius ω₀ R₀ T * iterErr ω₀ (k + 1) t)) := by
  have ht' : |t| ≤ T := abs_le.2 ht
  set R := suppRadius ω₀ R₀ T with hR_def
  have hRpos : 0 < R := suppRadius_pos h hne T
  set μ : Measure ℂ := volume.restrict (ball (0 : ℂ) R) with hμ_def
  set g : ℂ → ℝ := iter ω₀ (k + 2) t - iter ω₀ (k + 1) t with hg_def
  set gp : ℂ → ℝ := iter ω₀ (k + 1) t - iter ω₀ k t with hgp_def
  set w : ℂ → ℂ := fun x => iterVel ω₀ (k + 1) t x - iterVel ω₀ k t x with hw_def
  have hw : w = velocity gp := funext fun x => iterVel_sub h hne (k + 1) k t x
  set F : ℂ → ℝ := fun x => g x * fderiv ℝ (iter ω₀ (k + 1) t) x (w x) with hF_def
  have hFe : (fun x => (iter ω₀ (k + 2) t x - iter ω₀ (k + 1) t x) *
      fderiv ℝ (iter ω₀ (k + 1) t) x (iterVel ω₀ (k + 1) t x - iterVel ω₀ k t x)) = F := rfl
  rw [hFe]
  have hgm : MemLp g 2 volume := (iter_memLp h hne (k + 2) t 2).sub (iter_memLp h hne (k + 1) t 2)
  have hgpm : MemLp gp 2 volume := (iter_memLp h hne (k + 1) t 2).sub (iter_memLp h hne k t 2)
  have hg0 : ∀ x : ℂ, R ≤ ‖x‖ → g x = 0 := by
    intro x hx
    simp [hg_def, iter_eq_zero h hne _ ht' hx]
  have hgp0 : ∀ x : ℂ, R ≤ ‖x‖ → gp x = 0 := by
    intro x hx
    simp [hgp_def, iter_eq_zero h hne _ ht' hx]
  -- (1) `|∫ F| ≤ ‖F‖_{L¹}`
  have h1 : ‖∫ x, F x‖ₑ ≤ eLpNorm F 1 volume := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    exact enorm_integral_le_lintegral_enorm F
  -- (2) `F` vanishes outside `B_R`
  have hsupF : Function.support F ⊆ ball (0 : ℂ) R := by
    intro x hx
    rw [mem_ball, dist_zero_right]
    by_contra hcon
    exact hx (by simp [hF_def, hg0 x (not_lt.1 hcon)])
  have h2 : eLpNorm F 1 volume = eLpNorm F 1 μ :=
    (eLpNorm_restrict_eq_of_support_subset hsupF).symm
  -- (3) `|∇ω^{[k+1]}(t)| ≤ Ψ(T)`
  have hPsi : ∀ x, ‖fderiv ℝ (iter ω₀ (k + 1) t) x‖ ≤ Psi ω₀ T := fun x =>
    (iter_lip h hne (k + 1) t x).1.trans (Psi_mono ω₀ (ht'.trans (le_abs_self T)))
  have h3 : eLpNorm F 1 μ ≤ ENNReal.ofReal (Psi ω₀ T) * eLpNorm (fun x => g x * ‖w x‖) 1 μ := by
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    refine ae_of_all _ fun x => ?_
    have hB : |fderiv ℝ (iter ω₀ (k + 1) t) x (w x)| ≤ Psi ω₀ T * ‖w x‖ := by
      have := (fderiv ℝ (iter ω₀ (k + 1) t) x).le_opNorm (w x)
      rw [Real.norm_eq_abs] at this
      exact this.trans (mul_le_mul_of_nonneg_right (hPsi x) (norm_nonneg _))
    simp only [hF_def, norm_mul, Real.norm_eq_abs, abs_norm]
    calc |g x| * |fderiv ℝ (iter ω₀ (k + 1) t) x (w x)| ≤ |g x| * (Psi ω₀ T * ‖w x‖) :=
          mul_le_mul_of_nonneg_left hB (abs_nonneg _)
      _ = Psi ω₀ T * (|g x| * ‖w x‖) := by ring
  -- (4) Cauchy–Schwarz on `B_R`, and `lem:BS-basic`(c) with `ρ = R`
  have hBS := BS.velocity_L2_ball_le hRpos hRpos hgpm
    (ae_of_all _ fun y hy => hgp0 y (by simpa [mem_ball, dist_zero_right, not_lt] using hy))
  have hwm : AEStronglyMeasurable w μ := by
    rw [hw]
    exact hBS.2.1.aestronglyMeasurable
  have h4 : eLpNorm (fun x => g x * ‖w x‖) 1 μ ≤ eLpNorm g 2 μ * eLpNorm w 2 μ := by
    have := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm (p := 2) (q := 2) (r := 1) (μ := μ)
      hgm.aestronglyMeasurable.restrict hwm (fun (a : ℝ) (z : ℂ) => a * ‖z‖) 1
      (ae_of_all _ fun x => by simp [norm_mul])
    simpa using this
  have h5 : eLpNorm g 2 μ ≤ eLpNorm g 2 volume := eLpNorm_mono_measure _ Measure.restrict_le_self
  have h6 : eLpNorm w 2 μ ≤ ENNReal.ofReal (R + R) * eLpNorm gp 2 volume := by
    rw [hw]
    exact hBS.2.2
  have htot : ‖∫ x, F x‖ₑ ≤ ENNReal.ofReal (Psi ω₀ T) *
      (eLpNorm g 2 volume * (ENNReal.ofReal (R + R) * eLpNorm gp 2 volume)) := by
    calc ‖∫ x, F x‖ₑ ≤ eLpNorm F 1 volume := h1
      _ = eLpNorm F 1 μ := h2
      _ ≤ ENNReal.ofReal (Psi ω₀ T) * eLpNorm (fun x => g x * ‖w x‖) 1 μ := h3
      _ ≤ ENNReal.ofReal (Psi ω₀ T) * (eLpNorm g 2 μ * eLpNorm w 2 μ) := by gcongr
      _ ≤ ENNReal.ofReal (Psi ω₀ T) *
          (eLpNorm g 2 volume * (ENNReal.ofReal (R + R) * eLpNorm gp 2 volume)) := by
        gcongr
  have hfin : ENNReal.ofReal (Psi ω₀ T) *
      (eLpNorm g 2 volume * (ENNReal.ofReal (R + R) * eLpNorm gp 2 volume)) ≠ ∞ := by
    have := hgm.eLpNorm_ne_top
    have := hgpm.eLpNorm_ne_top
    finiteness
  have hreal := ENNReal.toReal_mono hfin htot
  rw [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _)] at hreal
  refine hreal.trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Psi_nonneg ω₀ T), ENNReal.toReal_ofReal (by linarith)]
  rw [iterErr_succ, iterErr_succ]
  ring

/-- `|d/dt e_{k+2}²| ≤ 4R(T)Ψ(T) e_{k+1} e_{k+2}` on `[-T, T]` (`B_global_smooth.tex:373-374`). -/
theorem iterErr_sq_deriv_bound (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (k : ℕ) {T : ℝ}
    {t : ℝ} (ht : t ∈ Icc (-T) T) :
    ∃ D : ℝ, HasDerivAt (fun τ => iterErr ω₀ (k + 2) τ ^ 2) D t ∧
      |D| ≤ 2 * Real.sqrt (iterErr ω₀ (k + 2) t ^ 2) *
        (2 * suppRadius ω₀ R₀ T * Psi ω₀ T * iterErr ω₀ (k + 1) t) := by
  refine ⟨_, hasDerivAt_iterErr_sq h hne k t, ?_⟩
  have hnn : 0 ≤ iterErr ω₀ (k + 2) t := ENNReal.toReal_nonneg
  rw [Real.sqrt_sq hnn, abs_mul]
  have := abs_integral_le h hne k ht
  have h2 : |(-2 : ℝ)| = 2 := by norm_num
  rw [h2]
  calc 2 * |∫ x, (iter ω₀ (k + 2) t x - iter ω₀ (k + 1) t x) *
        fderiv ℝ (iter ω₀ (k + 1) t) x (iterVel ω₀ (k + 1) t x - iterVel ω₀ k t x)|
      ≤ 2 * (Psi ω₀ T *
          (iterErr ω₀ (k + 2) t * (2 * suppRadius ω₀ R₀ T * iterErr ω₀ (k + 1) t))) := by
        linarith
    _ = 2 * iterErr ω₀ (k + 2) t *
        (2 * suppRadius ω₀ R₀ T * Psi ω₀ T * iterErr ω₀ (k + 1) t) := by ring

end NonUniqueEuler.Smooth.IterCauchyAux
