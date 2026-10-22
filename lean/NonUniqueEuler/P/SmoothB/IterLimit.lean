import NonUniqueEuler.I.SmoothB.IterLimit.Cauchy
import NonUniqueEuler.I.SmoothB.IterLimit.Velocity
import NonUniqueEuler.I.SmoothB.IterLimit.Equation
import NonUniqueEuler.I.SmoothB.IterLimit.Bootstrap
import NonUniqueEuler.I.Infra.Sobolev.UniformLimit
import NonUniqueEuler.I.Infra.BSParam.ContDiff
import NonUniqueEuler.I.SmoothB.Iterates
import NonUniqueEuler.I.SmoothB.IterLip
import NonUniqueEuler.I.SmoothB.Constants
import NonUniqueEuler.I.Sec2.BSSmooth
import NonUniqueEuler.H.SmoothB.IterLimit.Basic

/-!
# Proof: `prop:iter-limit` and `eq:limit-bounds` (the limit of the iterates)

Proof of `I/SmoothB/IterLimit.lean` (`B_global_smooth.tex:381-473`). The limit is the pointwise
limit `IterLimitAux.lim ω₀ t x = lim_j ω^{[j]}(t, x)`. The analytic steps are interface files:
* step 1 (`I/SmoothB/IterLimit/Cauchy.lean`): `∂_x^γ ω^{[j]}` is uniformly Cauchy on slabs;
* step 2 (`I/Infra/Sobolev/UniformLimit.lean`): for each `t`, the limit `ω(t)` is smooth and
  `∂^γ ω^{[j]}(t) → ∂^γ ω(t)` uniformly; combined here into uniform convergence on slabs;
* step 3 (`I/SmoothB/IterLimit/Velocity.lean`): convergence of `∂_x^γ v^{[j]}`;
* step 4 (`I/SmoothB/IterLimit/Equation.lean`): `∂_t ∂_x^γ ω = -∂_x^γ(v · ∇ω)`;
* step 5 (`I/SmoothB/IterLimit/Bootstrap.lean`): `ω ∈ C^∞(ℝ × ℝ²)`;
* `I/Infra/BSParam/ContDiff.lean`: `v ∈ C^∞` with bounded derivatives on slabs.
This file assembles them and passes the bounds of `lem:iterates` and `lem:iter-lip` to the limit
(`eq:limit-bounds`).
-/

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace NonUniqueEuler.Smooth

namespace IterLimitAux

variable {ω₀ : ℂ → ℝ} {R₀ : ℝ}

/-- The pointwise limit `ω(t, x) = lim_j ω^{[j]}(t, x)` (`B_global_smooth.tex:401-416`). -/
def lim (ω₀ : ℂ → ℝ) (t : ℝ) (x : ℂ) : ℝ :=
  limUnder atTop (fun j => iter ω₀ j t x)

theorem datum_eq_zero (h : IsSmoothDatum ω₀ R₀) {x : ℂ} (hx : R₀ < ‖x‖) : ω₀ x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hx'
  have := h.tsupport_subset hx'
  rw [mem_ball, dist_zero_right] at this
  linarith

theorem iter_eq_zero (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (j : ℕ) {t : ℝ} {x : ℂ}
    (hx : suppRadius ω₀ R₀ t < ‖x‖) : iter ω₀ j t x = 0 :=
  (iterates_smooth_support h hne j).2 R₀ (fun _ hy => datum_eq_zero h hy) t x hx

theorem tendsto_iter (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (t : ℝ) (x : ℂ) :
    Tendsto (fun j => iter ω₀ j t x) atTop (𝓝 (lim ω₀ t x)) := by
  have hT : 0 < |t| + 1 := by positivity
  have hC := iter_spaceD_uniformCauchySeqOn h hne hT (0, 0)
  have h1 : CauchySeq (fun j => ((iter ω₀ j t x : ℝ) : ℂ)) :=
    hC.cauchySeq (mem_slab (t, x))
  have h2 : CauchySeq (fun j => iter ω₀ j t x) := by
    have := Complex.reCLM.uniformContinuous.comp_cauchySeq h1
    simpa [Function.comp_def] using this
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete h2
  exact tendsto_nhds_limUnder ⟨a, ha⟩

theorem lim_eq_zero_of (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) {t : ℝ} {x : ℂ}
    (hx : ∀ j, iter ω₀ j t x = 0) : lim ω₀ t x = 0 := by
  have h1 := tendsto_iter h hne t x
  simp only [hx] at h1
  exact tendsto_nhds_unique h1 tendsto_const_nhds

theorem lim_supp (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (t : ℝ) (x : ℂ)
    (hx : suppRadius ω₀ R₀ t < ‖x‖) : lim ω₀ t x = 0 :=
  lim_eq_zero_of h hne fun j => iter_eq_zero h hne j hx

theorem lim_supp' (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (R₀' : ℝ)
    (hR : ∀ x : ℂ, R₀' < ‖x‖ → ω₀ x = 0) (t : ℝ) (x : ℂ) (hx : R₀' + Ustar ω₀ * |t| < ‖x‖) :
    lim ω₀ t x = 0 :=
  lim_eq_zero_of h hne fun j => (iterates_smooth_support h hne j).2 R₀' hR t x hx

theorem lim_suppT (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (T : ℝ) :
    ∃ ρ : ℝ, ∀ t ∈ Icc (-T) T, ∀ x : ℂ, ρ < ‖x‖ → lim ω₀ t x = 0 := by
  refine ⟨suppRadius ω₀ R₀ T, fun t ht x hx => lim_supp h hne t x ?_⟩
  have htT : |t| ≤ |T| := by
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2, le_abs_self T, neg_abs_le T]
  exact lt_of_le_of_lt (suppRadius_mono_abs ω₀ R₀ htT) hx

theorem contDiff_iter_slice (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (j : ℕ) (t : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (iter ω₀ j t) :=
  contDiff_slice (iterates_smooth_support h hne j).1 t

/-- Step 2, for one time `t`: `ω(t)` is smooth and `∂^γ ω^{[j]}(t) → ∂^γ ω(t)` uniformly. -/
theorem slice_limit (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (t : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => ((lim ω₀ t x : ℝ) : ℂ)) ∧
      ∀ γ : ℕ × ℕ, TendstoUniformly
        (fun j => Sob.partialD γ (fun x => ((iter ω₀ j t x : ℝ) : ℂ)))
        (Sob.partialD γ (fun x => ((lim ω₀ t x : ℝ) : ℂ))) atTop := by
  have hT : 0 < |t| + 1 := by positivity
  refine Sob.contDiff_and_tendstoUniformly_partialD (fun j => ?_) (fun γ => ?_) (fun x => ?_)
  · exact Complex.ofRealCLM.contDiff.comp (contDiff_iter_slice h hne j t)
  · have hC := (iter_spaceD_uniformCauchySeqOn h hne hT γ).comp (fun x : ℂ => (t, x))
    have hpre : (fun x : ℂ => (t, x)) ⁻¹' (Icc (-(|t| + 1)) (|t| + 1) ×ˢ univ) = univ := by
      ext x
      simpa using (mem_slab (t, x)).1
    rw [hpre] at hC
    exact hC
  · exact (Complex.continuous_ofReal.tendsto _).comp (tendsto_iter h hne t x)

theorem lim_slice_contDiff (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (t : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lim ω₀ t) := by
  have := Complex.reCLM.contDiff.comp (slice_limit h hne t).1
  simpa [Function.comp_def] using this

theorem lim_hasCompactSupport (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (t : ℝ) :
    HasCompactSupport (lim ω₀ t) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (suppRadius ω₀ R₀ t))
    fun x hx => lim_supp h hne t x ?_
  simpa [mem_closedBall, dist_zero_right, not_le] using hx

/-- Steps 1–2: uniform convergence of all spatial derivatives on slabs. -/
theorem lim_conv (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (T : ℝ) (hT : 0 < T) (γ : ℕ × ℕ) :
    TendstoUniformlyOn (fun (j : ℕ) (p : ℝ × ℂ) => spaceD γ (ofRealST (iter ω₀ j)) p.1 p.2)
      (fun p : ℝ × ℂ => spaceD γ (ofRealST (lim ω₀)) p.1 p.2) atTop (Icc (-T) T ×ˢ univ) :=
  (iter_spaceD_uniformCauchySeqOn h hne hT γ).tendstoUniformlyOn_of_tendsto
    fun p _ => ((slice_limit h hne p.1).2 γ).tendsto_at p.2

theorem lim_vel (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (T : ℝ) (hT : 0 < T) (γ : ℕ × ℕ) :
    TendstoUniformlyOn (fun (j : ℕ) (p : ℝ × ℂ) => spaceD γ (iterVel ω₀ j) p.1 p.2)
      (fun p : ℝ × ℂ => spaceD γ (velocityField (lim ω₀)) p.1 p.2) atTop
      (Icc (-T) T ×ˢ univ) :=
  iterVel_spaceD_tendstoUniformlyOn h hne (lim_slice_contDiff h hne) (lim_supp h hne)
    (lim_conv h hne) hT γ

theorem lim_eq (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (γ : ℕ × ℕ) (t : ℝ) (x : ℂ) :
    HasDerivAt (fun s => spaceD γ (ofRealST (lim ω₀)) s x)
      (-(spaceD γ (fun s y => ((fderiv ℝ (lim ω₀ s) y (velocityField (lim ω₀) s y) : ℝ) : ℂ))
        t x)) t :=
  limit_hasDerivAt_spaceD h hne (lim_slice_contDiff h hne) (lim_supp h hne) (lim_conv h hne)
    (lim_vel h hne) γ t x

theorem lim_cont (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (γ : ℕ × ℕ) :
    Continuous (fun p : ℝ × ℂ => spaceD γ (ofRealST (lim ω₀)) p.1 p.2) :=
  continuous_of_tendstoUniformlyOn_slabs
    (fun j => (contDiff_spaceD (contDiff_ofRealST (iterates_smooth_support h hne j).1) γ).continuous)
    (fun T hT => lim_conv h hne T hT γ)

/-- Step 5: `ω ∈ C^∞(ℝ × ℝ²)`. -/
theorem lim_contDiff (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry (lim ω₀)) :=
  contDiff_uncurry_of_transport (lim_slice_contDiff h hne) (lim_cont h hne) (lim_suppT h hne)
    (lim_eq h hne)

/-! ### Passing the bounds to the limit -/

theorem iter_zero_time (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (j : ℕ) (x : ℂ) :
    iter ω₀ j 0 x = ω₀ x := by
  cases j with
  | zero => rfl
  | succ k => exact congrFun (iterates_flow h hne k).2.2.2.1 x

theorem lim_init (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) : lim ω₀ 0 = ω₀ := by
  funext x
  have h1 := tendsto_iter h hne 0 x
  simp only [iter_zero_time h hne] at h1
  exact tendsto_nhds_unique h1 tendsto_const_nhds

theorem lim_transport (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (t : ℝ) (x : ℂ) :
    deriv (fun s => lim ω₀ s x) t +
      fderiv ℝ (lim ω₀ t) x (velocityField (lim ω₀) t x) = 0 := by
  have hd := lim_eq h hne (0, 0) t x
  simp only [spaceD_zero] at hd
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd
  simp only [Function.comp_def, Complex.reCLM_apply, Complex.ofReal_re, Complex.neg_re,
    ofRealST] at hr
  rw [hr.deriv]
  ring

theorem lim_tsupport (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (R₁ : ℝ)
    (hR : tsupport ω₀ ⊆ ball 0 R₁) (t : ℝ) :
    tsupport (lim ω₀ t) ⊆ ball 0 (suppRadius ω₀ R₁ t) := by
  obtain ⟨R', hR'lt, hR'⟩ := exists_inner_radius (⟨h.contDiff, hR⟩ : IsSmoothDatum ω₀ R₁)
  have hsub : tsupport (lim ω₀ t) ⊆ closedBall 0 (R' + Ustar ω₀ * |t|) := by
    refine closure_minimal (fun x hx => ?_) isClosed_closedBall
    by_contra hxb
    have hx' : R' + Ustar ω₀ * |t| < ‖x‖ := by
      simpa [mem_closedBall, dist_zero_right, not_le] using hxb
    exact hx (lim_supp' h hne R' hR' t x hx')
  refine hsub.trans (closedBall_subset_ball ?_)
  simp only [suppRadius]
  linarith

theorem lim_eLpNorm (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (t : ℝ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    eLpNorm (lim ω₀ t) p volume = eLpNorm ω₀ p volume := by
  have hu : TendstoUniformly (fun j => iter ω₀ j t) (lim ω₀ t) atTop := by
    have := Complex.reCLM.uniformContinuous.comp_tendstoUniformly ((slice_limit h hne t).2 (0, 0))
    simpa [Function.comp_def, Sob.partialD, Sob.pdList] using this
  exact eLpNorm_eq_of_tendstoUniformly hp (fun j => (contDiff_iter_slice h hne j t).continuous)
    (lim_slice_contDiff h hne t).continuous (fun j x hx => iter_eq_zero h hne j hx)
    (fun x hx => lim_supp h hne t x hx) hu (fun j => iterates_eLpNorm h hne j t hp)

/-- `∂_l` of the iterates converges to `∂_l` of the limit, for the directions `1` and `i`. -/
theorem tendsto_fderiv_apply (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (t : ℝ) (x : ℂ) {v : ℂ}
    (hv : v = 1 ∨ v = Complex.I) :
    Tendsto (fun j => fderiv ℝ (iter ω₀ j t) x v) atTop (𝓝 (fderiv ℝ (lim ω₀ t) x v)) := by
  have hγ : ∃ γ : ℕ × ℕ, ∀ g : ℂ → ℂ, Sob.partialD γ g x = fderiv ℝ g x v := by
    rcases hv with rfl | rfl
    · exact ⟨(1, 0), fun g => rfl⟩
    · exact ⟨(0, 1), fun g => rfl⟩
  obtain ⟨γ, hγ⟩ := hγ
  have h1 := ((slice_limit h hne t).2 γ).tendsto_at x
  simp only [hγ] at h1
  have hdj : ∀ j, fderiv ℝ (fun y => ((iter ω₀ j t y : ℝ) : ℂ)) x v =
      ((fderiv ℝ (iter ω₀ j t) x v : ℝ) : ℂ) := fun j =>
    fderiv_ofReal_apply ((contDiff_iter_slice h hne j t).differentiable (by simp) x) v
  have hd : fderiv ℝ (fun y => ((lim ω₀ t y : ℝ) : ℂ)) x v =
      ((fderiv ℝ (lim ω₀ t) x v : ℝ) : ℂ) :=
    fderiv_ofReal_apply ((lim_slice_contDiff h hne t).differentiable (by simp) x) v
  simp only [hdj, hd] at h1
  have := (Complex.reCLM.continuous.tendsto _).comp h1
  simpa [Function.comp_def] using this

theorem lim_grad_le (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (t : ℝ) (x : ℂ) :
    ‖fderiv ℝ (lim ω₀ t) x‖ ≤ Psi ω₀ t :=
  norm_clm_le_of_tendsto (Psi_nonneg ω₀ t) (tendsto_fderiv_apply h hne t x (Or.inl rfl))
    (tendsto_fderiv_apply h hne t x (Or.inr rfl)) fun j => (iter_lip h hne j t x).1

theorem lim_vel_le (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (t : ℝ) (x : ℂ) :
    ‖velocityField (lim ω₀) t x‖ ≤ Ustar ω₀ := by
  have h1 := (lim_vel h hne (|t| + 1) (by positivity) (0, 0)).tendsto_at (mem_slab (t, x))
  simp only [spaceD_zero] at h1
  exact le_of_tendsto' h1.norm fun j => (iterates_velocity h hne j).2.2.2.1 t x

theorem tendsto_pd_vel (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (t : ℝ) (x : ℂ) (l : Fin 2) :
    Tendsto (fun j => Prelim.pd l (iterVel ω₀ j t) x) atTop
      (𝓝 (Prelim.pd l (velocityField (lim ω₀) t) x)) := by
  have hγ : ∃ γ : ℕ × ℕ, ∀ F : ℝ → ℂ → ℂ, spaceD γ F t x = Prelim.pd l (F t) x := by
    fin_cases l
    · exact ⟨(1, 0), fun F => by simp [spaceD_one_zero, Prelim.pd, Prelim.e2]⟩
    · exact ⟨(0, 1), fun F => by simp [spaceD_zero_one, Prelim.pd, Prelim.e2]⟩
  obtain ⟨γ, hγ⟩ := hγ
  have h1 := (lim_vel h hne (|t| + 1) (by positivity) γ).tendsto_at (mem_slab (t, x))
  simpa only [hγ] using h1

theorem continuous_comp2 (i : Fin 2) : Continuous (Prelim.comp2 i) := by
  fin_cases i
  · exact Complex.continuous_re
  · exact Complex.continuous_im

theorem lim_gradEntry_le (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (t : ℝ) (x : ℂ)
    (i l : Fin 2) :
    |Prelim.gradEntry (velocityField (lim ω₀) t) i l x| ≤
      Amax ω₀ * (calL ω₀ t + cstar ω₀) := by
  have h1 := ((continuous_comp2 i).tendsto _).comp (tendsto_pd_vel h hne t x l)
  exact le_of_tendsto' (continuous_abs.tendsto _ |>.comp h1)
    fun j => (iter_lip h hne j t x).2.1 i l

theorem lim_isSmoothSolAll (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) :
    IsSmoothSolAll ω₀ (lim ω₀) := by
  have hsm := lim_contDiff h hne
  refine ⟨⟨hsm, ?_, ?_, ?_, lim_transport h hne, lim_init h hne⟩, lim_tsupport h hne⟩
  · exact BS.contDiff_velocityField_of_slabSupport (n := ⊤) hsm (lim_suppT h hne)
  · intro T hT n
    exact BS.iteratedFDeriv_velocityField_bounded (n := ⊤) hsm (lim_suppT h hne) hT le_top
  · intro t x
    exact (BS.divergence_curl_velocity_of_smooth (lim_slice_contDiff h hne t)
      (lim_hasCompactSupport h hne t)).1 x

end IterLimitAux

open IterLimitAux

variable {ω₀ : ℂ → ℝ} {R₀ : ℝ}

/-- `prop:iter-limit` with `eq:limit-bounds`: there is a real `ω ∈ C^∞(ℝ × ℝ²)` such that, with
`v = K_BS ∗ ω`, for every `T > 0` and every multi-index `γ`, `∂_x^γ ω^{[j]} → ∂_x^γ ω` and
`∂_x^γ v^{[j]} → ∂_x^γ v` uniformly on `[-T, T] × ℝ²`; `ω` has properties (1)–(3) of
thm:smooth; and for all `t`, `x`, `p ∈ [1, ∞]`: `ω(t, x) = 0` for `|x| > R₀' + U_*|t|`,
`‖ω(t)‖_{L^p} = ‖ω₀‖_{L^p}`, `|∇ω(t, x)| ≤ Ψ(t)`, `|v(t, x)| ≤ U_*`,
`max_{i,l} |∂_l v_i(t, x)| ≤ A(𝓛(t) + c_*)`. -/
theorem iter_limit (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) :
    ∃ ω : ℝ → ℂ → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry ω) ∧
      (∀ T : ℝ, 0 < T → ∀ γ : ℕ × ℕ,
        TendstoUniformlyOn (fun (j : ℕ) (p : ℝ × ℂ) => spaceD γ (ofRealST (iter ω₀ j)) p.1 p.2)
          (fun p : ℝ × ℂ => spaceD γ (ofRealST ω) p.1 p.2) atTop (Icc (-T) T ×ˢ univ) ∧
        TendstoUniformlyOn (fun (j : ℕ) (p : ℝ × ℂ) => spaceD γ (iterVel ω₀ j) p.1 p.2)
          (fun p : ℝ × ℂ => spaceD γ (velocityField ω) p.1 p.2) atTop (Icc (-T) T ×ˢ univ)) ∧
      IsSmoothSolAll ω₀ ω ∧
      (∀ R₀' : ℝ, (∀ x : ℂ, R₀' < ‖x‖ → ω₀ x = 0) →
        ∀ t : ℝ, ∀ x : ℂ, R₀' + Ustar ω₀ * |t| < ‖x‖ → ω t x = 0) ∧
      (∀ t : ℝ, ∀ p : ℝ≥0∞, 1 ≤ p → eLpNorm (ω t) p volume = eLpNorm ω₀ p volume) ∧
      (∀ t : ℝ, ∀ x : ℂ, ‖fderiv ℝ (ω t) x‖ ≤ Psi ω₀ t) ∧
      (∀ t : ℝ, ∀ x : ℂ, ‖velocityField ω t x‖ ≤ Ustar ω₀) ∧
      (∀ t : ℝ, ∀ x : ℂ, ∀ i l : Fin 2,
        |Prelim.gradEntry (velocityField ω t) i l x| ≤ Amax ω₀ * (calL ω₀ t + cstar ω₀)) :=
  ⟨lim ω₀, lim_contDiff h hne, fun T hT γ => ⟨lim_conv h hne T hT γ, lim_vel h hne T hT γ⟩,
    lim_isSmoothSolAll h hne, lim_supp' h hne, lim_eLpNorm h hne, lim_grad_le h hne,
    lim_vel_le h hne, lim_gradEntry_le h hne⟩

end NonUniqueEuler.Smooth
