import NonUniqueEuler.Defs.SmoothB.Iteration
import Mathlib.Topology.UniformSpace.UniformConvergence
import NonUniqueEuler.I.Sec2.BSSmooth
import NonUniqueEuler.I.SmoothB.VelocitySupBound
import NonUniqueEuler.I.SmoothB.Iterates

/-!
# Proof: `prop:iter-limit`, step 3 — uniform convergence of the derivatives of the velocities

Proof of `I/SmoothB/IterLimit/Velocity.lean`, following the
second paragraph of the proof of `prop:iter-limit` (`B_global_smooth.tex:422-431`).

Fix `T > 0`, `γ`, and put `r = R(T)`, `ρ = |r| + 1`.
1. For `|t| ≤ T`, `ω^{[j]}(t)` and `ω(t)` are `C^∞` and vanish outside `\bar B_r`
   (`iterates_smooth_support` with `R₀' = R₀`, `suppRadius_mono_abs`); so they are test
   functions supported in `B_ρ`, and so are their derivatives `∂^γ` (`Sob.IsTestFn.partialD`).
2. `lem:BS-basic`(d) (`BS.partialD_velocity_of_smooth`): `∂^γ (K ∗ g) = K ∗ ∂^γ g`.
3. Both Biot–Savart integrals converge absolutely (`norm_velocity_le_sqrt_two_mul_radius`), so
   `K ∗ a - K ∗ b = K ∗ (a - b)`, and the same lemma bounds it by `√2 ρ ‖a - b‖_{L^∞}`
   (helper `IterVelAux.norm_partialD_velocity_sub_le`).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace NonUniqueEuler.Smooth

namespace IterVelAux

/-- A smooth real function vanishing outside `\bar B_r` is, as a complex function, a test function
supported in `B_{|r|+1}`. -/
theorem isTestFn_ofReal_ball {g : ℂ → ℝ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) {r : ℝ}
    (hv : ∀ x : ℂ, r < ‖x‖ → g x = 0) :
    Sob.IsTestFn (Metric.ball (0 : ℂ) (|r| + 1)) (fun y => (g y : ℂ)) := by
  have hsub : tsupport (fun y => (g y : ℂ)) ⊆ Metric.closedBall 0 r := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hlt
    rw [not_le] at hlt
    exact hx (by simp [hv x hlt])
  refine ⟨?_, ?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp hg
  · exact (isCompact_closedBall (0 : ℂ) r).of_isClosed_subset (isClosed_tsupport _) hsub
  · exact hsub.trans (Metric.closedBall_subset_ball (by linarith [le_abs_self r]))

/-- A smooth real function vanishing outside `\bar B_r` has compact support. -/
theorem hasCompactSupport_of_vanish {g : ℂ → ℝ} {r : ℝ} (hv : ∀ x : ℂ, r < ‖x‖ → g x = 0) :
    HasCompactSupport g := by
  have hsub : tsupport g ⊆ Metric.closedBall 0 r := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hlt
    rw [not_le] at hlt
    exact hx (hv x hlt)
  exact (isCompact_closedBall (0 : ℂ) r).of_isClosed_subset (isClosed_tsupport _) hsub

/-- For a smooth real `g` vanishing outside `\bar B_r`, `∂^γ g` is bounded and vanishes outside
`B_{|r|+1}`. -/
theorem partialDR_memLp_vanish {g : ℂ → ℝ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) {r : ℝ}
    (hv : ∀ x : ℂ, r < ‖x‖ → g x = 0) (γ : ℕ × ℕ) :
    MemLp (Prelim.partialDR γ g) ⊤ volume ∧
      ∀ y : ℂ, y ∉ Metric.ball (0 : ℂ) (|r| + 1) → Prelim.partialDR γ g y = 0 := by
  have hT := (isTestFn_ofReal_ball hg hv).partialD γ
  have hfun : Prelim.partialDR γ g =
      Complex.re ∘ Sob.partialD γ (fun y => (g y : ℂ)) := rfl
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact (Complex.continuous_re.comp hT.continuous).memLp_of_hasCompactSupport
      (hT.compact.comp_left Complex.zero_re)
  · intro y hy
    have hy' : y ∉ tsupport (Sob.partialD γ (fun y => (g y : ℂ))) := fun h => hy (hT.subset h)
    simp only [Prelim.partialDR, image_eq_zero_of_notMem_tsupport hy', Complex.zero_re]

/-- The core estimate (`B_global_smooth.tex:422-427`): for smooth real `g`, `h` vanishing outside
`\bar B_r` with `|∂^γ g - ∂^γ h| ≤ δ` everywhere,
`|∂^γ (K ∗ g)(x) - ∂^γ (K ∗ h)(x)| ≤ √2 (|r| + 1) δ` for every `x`. -/
theorem norm_partialD_velocity_sub_le {g h : ℂ → ℝ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h) {r : ℝ}
    (hgv : ∀ x : ℂ, r < ‖x‖ → g x = 0) (hhv : ∀ x : ℂ, r < ‖x‖ → h x = 0) (γ : ℕ × ℕ)
    {δ : ℝ}
    (hδ : ∀ y : ℂ, ‖Sob.partialD γ (fun y => (g y : ℂ)) y -
      Sob.partialD γ (fun y => (h y : ℂ)) y‖ ≤ δ) (x : ℂ) :
    ‖Sob.partialD γ (velocity g) x - Sob.partialD γ (velocity h) x‖ ≤
      Real.sqrt 2 * (|r| + 1) * δ := by
  have hρ : 0 < |r| + 1 := by positivity
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hδ 0)
  obtain ⟨ha, hav⟩ := partialDR_memLp_vanish hg hgv γ
  obtain ⟨hb, hbv⟩ := partialDR_memLp_vanish hh hhv γ
  set a := Prelim.partialDR γ g with ha_def
  set b := Prelim.partialDR γ h with hb_def
  set d : ℂ → ℝ := fun y => a y - b y with hd_def
  have hd : MemLp d ⊤ volume := ha.sub hb
  have hdv : ∀ y : ℂ, y ∉ Metric.ball (0 : ℂ) (|r| + 1) → d y = 0 := fun y hy => by
    simp only [hd_def, hav y hy, hbv y hy, sub_zero]
  rw [BS.partialD_velocity_of_smooth hg (hasCompactSupport_of_vanish hgv) γ,
    BS.partialD_velocity_of_smooth hh (hasCompactSupport_of_vanish hhv) γ]
  have I1 := (norm_velocity_le_sqrt_two_mul_radius hρ ha (ae_of_all _ hav) x).1
  have I2 := (norm_velocity_le_sqrt_two_mul_radius hρ hb (ae_of_all _ hbv) x).1
  have hsub : velocity a x - velocity b x = velocity d x := by
    simp only [velocity]
    rw [← integral_sub I1 I2]
    congr 1
    funext y
    simp only [hd_def]
    push_cast
    ring
  rw [hsub]
  refine (norm_velocity_le_sqrt_two_mul_radius hρ hd (ae_of_all _ hdv) x).2.trans ?_
  have hpt : ∀ y : ℂ, ‖d y‖ ≤ δ := fun y => by
    have h1 : d y = (Sob.partialD γ (fun y => (g y : ℂ)) y -
        Sob.partialD γ (fun y => (h y : ℂ)) y).re := by
      simp only [hd_def, ha_def, hb_def, Prelim.partialDR, Complex.sub_re]
    rw [h1, Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans (hδ y)
  have hess : (eLpNorm d ⊤ volume).toReal ≤ δ := by
    rw [eLpNorm_exponent_top]
    exact ENNReal.toReal_le_of_le_ofReal hδ0 (eLpNormEssSup_le_of_ae_bound (ae_of_all _ hpt))
  have hc : 0 ≤ Real.sqrt 2 * (|r| + 1) := by positivity
  exact mul_le_mul_of_nonneg_left hess hc

end IterVelAux

variable {ω₀ : ℂ → ℝ} {R₀ : ℝ}

/-- `prop:iter-limit`, step 3 (`B_global_smooth.tex:422-431`): if `ω(t) ∈ C^∞` vanishes outside
`B_{R(t)}` and `∂_x^γ ω^{[j]} → ∂_x^γ ω` uniformly on slabs, then `∂_x^γ v^{[j]} → ∂_x^γ v`
uniformly on slabs. -/
theorem iterVel_spaceD_tendstoUniformlyOn (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0)
    {ω : ℝ → ℂ → ℝ} (hsm : ∀ t, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ω t))
    (hsupp : ∀ (t : ℝ) (x : ℂ), suppRadius ω₀ R₀ t < ‖x‖ → ω t x = 0)
    (hconv : ∀ T : ℝ, 0 < T → ∀ γ : ℕ × ℕ,
      TendstoUniformlyOn (fun (j : ℕ) (p : ℝ × ℂ) => spaceD γ (ofRealST (iter ω₀ j)) p.1 p.2)
        (fun p : ℝ × ℂ => spaceD γ (ofRealST ω) p.1 p.2) atTop (Icc (-T) T ×ˢ univ))
    {T : ℝ} (hT : 0 < T) (γ : ℕ × ℕ) :
    TendstoUniformlyOn (fun (j : ℕ) (p : ℝ × ℂ) => spaceD γ (iterVel ω₀ j) p.1 p.2)
      (fun p : ℝ × ℂ => spaceD γ (velocityField ω) p.1 p.2) atTop (Icc (-T) T ×ˢ univ) := by
  -- `ω₀ = 0` outside `\bar B_{R₀}`
  have hR : ∀ x : ℂ, R₀ < ‖x‖ → ω₀ x = 0 := fun x hx => by
    have hx' : x ∉ tsupport ω₀ := fun hx' => by
      have hb := h.tsupport_subset hx'
      rw [Metric.mem_ball, dist_zero_right] at hb
      linarith
    exact image_eq_zero_of_notMem_tsupport hx'
  set r := suppRadius ω₀ R₀ T with hr_def
  have hrt : ∀ t ∈ Icc (-T) T, suppRadius ω₀ R₀ t ≤ r := fun t ht =>
    suppRadius_mono_abs ω₀ R₀ (by rw [abs_of_pos hT]; exact abs_le.2 ⟨ht.1, ht.2⟩)
  have hiter_sm : ∀ (j : ℕ) (t : ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (iter ω₀ j t) :=
    fun j t => (iterates_smooth_support h hne j).1.comp (contDiff_const.prodMk contDiff_id)
  have hiter_v : ∀ (j : ℕ), ∀ t ∈ Icc (-T) T, ∀ x : ℂ, r < ‖x‖ → iter ω₀ j t x = 0 :=
    fun j t ht x hx =>
      (iterates_smooth_support h hne j).2 R₀ hR t x (lt_of_le_of_lt (hrt t ht) hx)
  have hω_v : ∀ t ∈ Icc (-T) T, ∀ x : ℂ, r < ‖x‖ → ω t x = 0 := fun t ht x hx =>
    hsupp t x (lt_of_le_of_lt (hrt t ht) hx)
  have hconvT := hconv T hT γ
  rw [Metric.tendstoUniformlyOn_iff] at hconvT ⊢
  intro ε hε
  set C := Real.sqrt 2 * (|r| + 1) with hC_def
  have hC : 0 < C := by positivity
  filter_upwards [hconvT (ε / (2 * C)) (by positivity)] with j hj
  rintro ⟨t, x⟩ ⟨ht, -⟩
  have hδ : ∀ y : ℂ, ‖Sob.partialD γ (fun y => (iter ω₀ j t y : ℂ)) y -
      Sob.partialD γ (fun y => (ω t y : ℂ)) y‖ ≤ ε / (2 * C) := fun y => by
    have hjy := hj (t, y) ⟨ht, mem_univ _⟩
    rw [dist_comm, dist_eq_norm] at hjy
    exact hjy.le
  have key := IterVelAux.norm_partialD_velocity_sub_le (hiter_sm j t) (hsm t)
    (hiter_v j t ht) (hω_v t ht) γ hδ x
  have hlt : C * (ε / (2 * C)) < ε := by
    rw [mul_div_assoc', mul_comm 2 C, mul_div_mul_left _ _ hC.ne']
    linarith
  rw [dist_eq_norm, norm_sub_rev]
  exact lt_of_le_of_lt key hlt

end NonUniqueEuler.Smooth
