import NonUniqueEuler.H.Sec2.Velocity.Bounds
import NonUniqueEuler.I.Sec2.BSSmooth
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv

/-!
# Helpers for `lem:velocity`(c): the weak gradient of `K ∗ w`

Helper file of `P/Sec2/Velocity.lean` (namespace `NonUniqueEuler.BS.VelH`), following
`02_prelim.tex:376-381`. Let `w_j ∈ C_c^∞` with `w_j → w` in `L¹` and `L²`, `v_j = K ∗ w_j`.

* `velocity_sub_of_smooth`, `pd_velocity_sub_of_smooth`: linearity for smooth compactly supported
  vorticities;
* `memLp_pd_velocity`, `eLpNorm_pd_velocity_le`, `sum_sq_l2_pd_velocity`: `‖∂_l v‖₂ ≤ ‖g‖₂`,
  `Σ_l ‖∂_l v‖₂² = ‖g‖₂²` (`lem:BS-basic`(d), `BS.sum_l2_pd_partialD_velocity_of_smooth`);
* `exists_lim_pd_velocity`: `∂_l v_j` is Cauchy in `L²`, with limit `F_l`;
* `hasWeakDerivOn_velocity`: `F_l` is the weak derivative `∂_l v` (`v_j → v` in `L¹_loc` by
  `lem:BS-basic`(e)).
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology ContDiff

namespace NonUniqueEuler.BS.VelH

/-! ### Smooth compactly supported vorticities -/

section Smooth

variable {g h : ℂ → ℝ}

theorem memLp_of_smooth (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (q : ℝ≥0∞) :
    MemLp g q volume :=
  hg.continuous.memLp_of_hasCompactSupport hgc

theorem integrable_K_of_smooth (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (x : ℂ) :
    Integrable (fun y => biotSavartKernel (x - y) * (g y : ℂ)) :=
  (integrable_and_norm_velocity_le_sqrt_L1_Linf (memLp_of_smooth hg hgc 1)
    (memLp_of_smooth hg hgc ⊤) x).1

theorem velocity_sub_of_smooth (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hh : ContDiff ℝ ∞ h) (hhc : HasCompactSupport h) :
    velocity (g - h) = velocity g - velocity h := by
  funext x
  exact cv_sub_right (integrable_K_of_smooth hg hgc x) (integrable_K_of_smooth hh hhc x)

theorem pd_velocity_sub_of_smooth (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hh : ContDiff ℝ ∞ h) (hhc : HasCompactSupport h) (l : Fin 2) :
    Prelim.pd l (velocity (g - h)) = Prelim.pd l (velocity g) - Prelim.pd l (velocity h) := by
  rw [velocity_sub_of_smooth hg hgc hh hhc]
  funext x
  have dg : DifferentiableAt ℝ (velocity g) x :=
    ((contDiff_velocity_of_smooth hg hgc).1.differentiable (by simp)).differentiableAt
  have dh : DifferentiableAt ℝ (velocity h) x :=
    ((contDiff_velocity_of_smooth hh hhc).1.differentiable (by simp)).differentiableAt
  simp only [Prelim.pd, Pi.sub_apply]
  rw [fderiv_sub dg dh]
  rfl

theorem partialD_zero_zero (φ : ℂ → ℂ) : Sob.partialD (0, 0) φ = φ := rfl

theorem eLpNorm_ofReal_eq (f : ℂ → ℝ) (q : ℝ≥0∞) :
    eLpNorm (fun y => (f y : ℂ)) q volume = eLpNorm f q volume :=
  eLpNorm_congr_norm_ae (Eventually.of_forall fun _ => Complex.norm_real _)

theorem memLp_pd_velocity (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (l : Fin 2) :
    MemLp (Prelim.pd l (velocity g)) 2 volume :=
  (sum_l2_pd_partialD_velocity_of_smooth hg hgc (0, 0)).1 l

/-- `Σ_l ‖∂_l v‖₂² = ‖g‖₂²`. -/
theorem sum_sq_l2_pd_velocity (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    (eLpNorm (Prelim.pd 0 (velocity g)) 2 volume).toReal ^ 2 +
        (eLpNorm (Prelim.pd 1 (velocity g)) 2 volume).toReal ^ 2 =
      (eLpNorm g 2 volume).toReal ^ 2 := by
  have h := (sum_l2_pd_partialD_velocity_of_smooth hg hgc (0, 0)).2
  rw [Fin.sum_univ_two] at h
  simp only [Sob.l2, partialD_zero_zero, eLpNorm_ofReal_eq] at h
  exact h

theorem eLpNorm_pd_velocity_le (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (l : Fin 2) :
    eLpNorm (Prelim.pd l (velocity g)) 2 volume ≤ eLpNorm g 2 volume := by
  have hs := sum_sq_l2_pd_velocity hg hgc
  have hle : (eLpNorm (Prelim.pd l (velocity g)) 2 volume).toReal ^ 2 ≤
      (eLpNorm g 2 volume).toReal ^ 2 := by
    rw [← hs]
    fin_cases l
    · exact le_add_of_nonneg_right (sq_nonneg _)
    · exact le_add_of_nonneg_left (sq_nonneg _)
  have hle' := (pow_le_pow_iff_left₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    two_ne_zero).1 hle
  exact (ENNReal.toReal_le_toReal (memLp_pd_velocity hg hgc l).eLpNorm_ne_top
    (memLp_of_smooth hg hgc 2).eLpNorm_ne_top).1 hle'

end Smooth

/-! ### The `L²` limit of the gradients -/

theorem exists_eta {ε : ℝ≥0∞} (hε : 0 < ε) : ∃ η : ℝ≥0∞, 0 < η ∧ η + η < ε := by
  rcases eq_or_ne ε ⊤ with rfl | hε'
  · exact ⟨1, one_pos, by simp⟩
  · refine ⟨ε / 3, ENNReal.div_pos hε.ne' (by norm_num), ?_⟩
    calc ε / 3 + ε / 3 < ε / 3 + ε / 3 + ε / 3 :=
          ENNReal.lt_add_right (ENNReal.add_ne_top.2 ⟨ENNReal.div_ne_top hε' (by norm_num),
            ENNReal.div_ne_top hε' (by norm_num)⟩) (ENNReal.div_pos hε.ne' (by norm_num)).ne'
      _ = ε := ENNReal.add_thirds ε

/-- `∂_l v_j` converges in `L²` to some `F`, with `‖∂_l v_j‖₂ → ‖F‖₂`. -/
theorem exists_lim_pd_velocity {w : ℂ → ℝ} (h2 : MemLp w 2 volume) {ws : ℕ → ℂ → ℝ} (hs : ∀ j, ContDiff ℝ ∞ (ws j))
    (hc : ∀ j, HasCompactSupport (ws j))
    (hconv : Tendsto (fun j => eLpNorm (w - ws j) 2 volume) atTop (𝓝 0)) (l : Fin 2) :
    ∃ F : ℂ → ℂ, MemLp F 2 volume ∧
      Tendsto (fun j => eLpNorm (Prelim.pd l (velocity (ws j)) - F) 2 volume) atTop (𝓝 0) ∧
      Tendsto (fun j => (eLpNorm (Prelim.pd l (velocity (ws j))) 2 volume).toReal) atTop
        (𝓝 (eLpNorm F 2 volume).toReal) := by
  have hmem : ∀ j, MemLp (Prelim.pd l (velocity (ws j))) 2 volume := fun j =>
    memLp_pd_velocity (hs j) (hc j) l
  set Gs : ℕ → Lp ℂ 2 (volume : Measure ℂ) := fun j => (hmem j).toLp _ with hGs
  have hcs : CauchySeq Gs := by
    rw [EMetric.cauchySeq_iff']
    intro ε hε
    obtain ⟨η, hη0, hηε⟩ := exists_eta hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((ENNReal.tendsto_nhds_zero.1 hconv) η hη0)
    refine ⟨N, fun n hn => ?_⟩
    rw [hGs, Lp.edist_toLp_toLp, ← pd_velocity_sub_of_smooth (hs n) (hc n) (hs N) (hc N)]
    refine lt_of_le_of_lt ((eLpNorm_pd_velocity_le ((hs n).sub (hs N))
      ((hc n).sub (hc N)) l).trans ?_) hηε
    have heq : (fun x => ws n x - ws N x) = (w - ws N) - (w - ws n) := by
      funext x
      simp only [Pi.sub_apply]
      ring
    rw [heq]
    have hm : ∀ j, AEStronglyMeasurable (w - ws j) volume := fun j =>
      h2.1.sub (memLp_of_smooth (hs j) (hc j) 2).1
    exact (eLpNorm_sub_le (hm N) (hm n) one_le_two).trans
      (add_le_add (hN N le_rfl) (hN n hn))
  obtain ⟨F, hF⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨F, Lp.memLp F, ?_, ?_⟩
  · have h := tendsto_iff_edist_tendsto_0.1 hF
    refine h.congr fun j => ?_
    rw [Lp.edist_def]
    exact eLpNorm_congr_ae ((hmem j).coeFn_toLp.sub (EventuallyEq.refl _ _))
  · have h := (continuous_norm.tendsto F).comp hF
    rw [← Lp.norm_def]
    refine h.congr fun j => ?_
    simp only [Function.comp, hGs]
    exact Lp.norm_toLp _ _

/-- Convergence in `L²` gives convergence of the `L²` norms. -/
theorem tendsto_toReal_eLpNorm_of_tendsto {f : ℕ → ℂ → ℝ} {g : ℂ → ℝ}
    (hf : ∀ j, MemLp (f j) 2 volume) (hg : MemLp g 2 volume)
    (h : Tendsto (fun j => eLpNorm (g - f j) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun j => (eLpNorm (f j) 2 volume).toReal) atTop (𝓝 (eLpNorm g 2 volume).toReal) := by
  have hT : Tendsto (fun j => (hf j).toLp (f j)) atTop (𝓝 (hg.toLp g)) := by
    rw [tendsto_iff_edist_tendsto_0]
    refine h.congr fun j => ?_
    rw [Lp.edist_toLp_toLp, eLpNorm_sub_comm]
  have := (continuous_norm.tendsto _).comp hT
  simp only [Function.comp_def, Lp.norm_toLp] at this
  exact this

/-! ### Passing to the limit in the weak formulation -/

/-- `∫ g_j ψ → ∫ g ψ` if `g_j → g` in `L²` and `ψ ∈ L²`. -/
theorem tendsto_integral_mul_L2 {Gs : ℕ → ℂ → ℂ} {F : ℂ → ℂ} (hG : ∀ j, MemLp (Gs j) 2 volume)
    (hF : MemLp F 2 volume) (hGF : Tendsto (fun j => eLpNorm (Gs j - F) 2 volume) atTop (𝓝 0))
    {φ : ℂ → ℂ} (hφ : MemLp φ 2 volume) :
    Tendsto (fun j => ∫ x, Gs j x * φ x) atTop (𝓝 (∫ x, F x * φ x)) := by
  have hint : ∀ G : ℂ → ℂ, MemLp G 2 volume → Integrable (fun x => G x * φ x) := fun G hG =>
    hG.integrable_mul hφ
  have hbound : ∀ j, ‖(∫ x, Gs j x * φ x) - ∫ x, F x * φ x‖ₑ ≤
      eLpNorm (Gs j - F) 2 volume * eLpNorm φ 2 volume := by
    intro j
    rw [← integral_sub (hint _ (hG j)) (hint _ hF)]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    have h := lintegral_enorm_mul_le ((hG j).1.sub hF.1) hφ.1.enorm Real.HolderConjugate.two_two
    rw [ENNReal.ofReal_ofNat, eLpNorm_enorm] at h
    refine le_trans (le_of_eq ?_) h
    congr 1
    funext x
    rw [← sub_mul, enorm_mul]
    rfl
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h0 := ENNReal.Tendsto.mul_const hGF (Or.inr hφ.eLpNorm_ne_top)
  rw [zero_mul] at h0
  have hlim := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h0
  rw [ENNReal.toReal_zero] at hlim
  refine squeeze_zero (fun j => norm_nonneg _) (fun j => ?_) hlim
  have hfin : eLpNorm (Gs j - F) 2 volume * eLpNorm φ 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top ((hG j).sub hF).eLpNorm_ne_top hφ.eLpNorm_ne_top
  have := hbound j
  rw [← ofReal_norm] at this
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp this

/-- `∫ (K ∗ w_j) ψ → ∫ (K ∗ w) ψ` for a test function `ψ`, if `w_j → w` in `L¹`
(`v_j → v` in `L¹_loc`, `lem:BS-basic`(e)). -/
theorem tendsto_integral_velocity_mul {w : ℂ → ℝ} (h1 : MemLp w 1 volume) {ws : ℕ → ℂ → ℝ}
    (hs : ∀ j, ContDiff ℝ ∞ (ws j)) (hc : ∀ j, HasCompactSupport (ws j))
    (hconv : Tendsto (fun j => eLpNorm (w - ws j) 1 volume) atTop (𝓝 0)) {ψ : ℂ → ℂ}
    (hψ : Sob.IsTestFn univ ψ) :
    Tendsto (fun j => ∫ x, velocity (ws j) x * ψ x) atTop (𝓝 (∫ x, velocity w x * ψ x)) := by
  obtain ⟨r, hr⟩ := hψ.compact.isBounded.subset_ball (0 : ℂ)
  set R := max r 1 with hRdef
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hsub : tsupport ψ ⊆ ball (0 : ℂ) R := hr.trans (ball_subset_ball (le_max_left _ _))
  obtain ⟨C, hC⟩ := hψ.continuous.bounded_above_of_compact_support hψ.compact
  have hint : ∀ f : ℂ → ℝ, MemLp f 1 volume → Integrable (fun x => velocity f x * ψ x) :=
    fun f hf => by
      have := (locallyIntegrable_velocity_of_L1 hf).integrable_smul_right_of_hasCompactSupport
        hψ.continuous hψ.compact
      simpa [smul_eq_mul] using this
  have hwsL1 : ∀ j, MemLp (ws j) 1 volume := fun j => memLp_of_smooth (hs j) (hc j) 1
  have hbound : ∀ j, ‖(∫ x, velocity (ws j) x * ψ x) - ∫ x, velocity w x * ψ x‖ₑ ≤
      ENNReal.ofReal R * eLpNorm (ws j - w) 1 volume * ENNReal.ofReal C := by
    intro j
    rw [← integral_sub (hint _ (hwsL1 j)) (hint _ h1)]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    have hae : ∀ᵐ x, ‖velocity (ws j) x * ψ x - velocity w x * ψ x‖ₑ ≤
        (ball (0 : ℂ) R).indicator (Conv.convAbs biotSavartKernel (ws j - w)) x *
          ENNReal.ofReal C := by
      filter_upwards [ae_convAbs_lt_top (hwsL1 j), ae_convAbs_lt_top h1] with x hx1 hx2
      have heq : velocity (ws j) x - velocity w x = cv biotSavartKernel (ws j - w) x :=
        (cv_sub_right (integrable_of_convAbs measurable_K.aestronglyMeasurable (hwsL1 j).1 hx1.ne)
          (integrable_of_convAbs measurable_K.aestronglyMeasurable h1.1 hx2.ne)).symm
      rw [← sub_mul, enorm_mul, heq]
      by_cases hx : x ∈ ball (0 : ℂ) R
      · rw [indicator_of_mem hx]
        gcongr
        · exact enorm_cv_le _ _ _
        · rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hC x)
      · have : ψ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hsub h))
        simp [this]
    refine (lintegral_mono_ae hae).trans ?_
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_indicator measurableSet_ball]
    gcongr
    exact setLIntegral_convAbs_ball_le ((hwsL1 j).sub h1) hR
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h0 : Tendsto (fun j => ENNReal.ofReal R * eLpNorm (ws j - w) 1 volume * ENNReal.ofReal C)
      atTop (𝓝 0) := by
    have := ENNReal.Tendsto.mul_const (b := ENNReal.ofReal C)
      (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal R) hconv (Or.inr ENNReal.ofReal_ne_top))
      (Or.inr ENNReal.ofReal_ne_top)
    rw [mul_zero, zero_mul] at this
    refine this.congr fun j => ?_
    rw [eLpNorm_sub_comm]
  have hlim := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h0
  rw [ENNReal.toReal_zero] at hlim
  refine squeeze_zero (fun j => norm_nonneg _) (fun j => ?_) hlim
  have hfin : ENNReal.ofReal R * eLpNorm (ws j - w) 1 volume * ENNReal.ofReal C ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      ((hwsL1 j).sub h1).eLpNorm_ne_top) ENNReal.ofReal_ne_top
  have := hbound j
  rw [← ofReal_norm] at this
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp this

/-- The `L²` limit `F` of `∂_l v_j` is the weak derivative `∂_l v` on the plane. -/
theorem hasWeakDerivOn_velocity {w : ℂ → ℝ} (h1 : MemLp w 1 volume) {ws : ℕ → ℂ → ℝ}
    (hs : ∀ j, ContDiff ℝ ∞ (ws j)) (hc : ∀ j, HasCompactSupport (ws j))
    (hconv : Tendsto (fun j => eLpNorm (w - ws j) 1 volume) atTop (𝓝 0)) (l : Fin 2)
    {F : ℂ → ℂ} (hF : MemLp F 2 volume)
    (hGF : Tendsto (fun j => eLpNorm (Prelim.pd l (velocity (ws j)) - F) 2 volume) atTop (𝓝 0)) :
    Sob.HasWeakDerivOn univ [Prelim.e2 l] (velocity w) F := by
  intro φ hφ
  have hψ := hφ.iterDirDeriv [Prelim.e2 l]
  have hj : ∀ j, ∫ x, velocity (ws j) x * Sob.iterDirDeriv [Prelim.e2 l] φ x =
      (-1 : ℂ) ^ [Prelim.e2 l].length * ∫ x, Prelim.pd l (velocity (ws j)) x * φ x := fun j =>
    Sob.hasWeakDerivOn_of_contDiffOn isOpen_univ (n := 1) (by simp)
      (contDiff_infty.1 (contDiff_velocity_of_smooth (hs j) (hc j)).1 1).contDiffOn φ hφ
  have hL := tendsto_integral_velocity_mul h1 hs hc hconv hψ
  have hR := (tendsto_integral_mul_L2 (fun j => memLp_pd_velocity (hs j) (hc j) l) hF hGF
    (hφ.memLp 2 volume)).const_mul ((-1 : ℂ) ^ [Prelim.e2 l].length)
  simp_rw [← hj] at hR
  exact tendsto_nhds_unique hL hR

end NonUniqueEuler.BS.VelH
