import NonUniqueEuler.H.Sec3.Commutator.SmoothApprox.Conv
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv
import NonUniqueEuler.I.Infra.Sobolev.Smooth
import NonUniqueEuler.Defs.Infra.Instances

/-!
# Helper for `P/Sec3/Commutator/SmoothApprox`: `H¹(B_r)` bookkeeping

* `locallyIntegrable_of_memHOn`: `H¹_loc ⊆ L¹_loc`;
* `memHOn_ball_of_contDiff`: smooth functions lie in `H^k(B_r)`;
* `memHOn_sub`: `H^k(B_r)` is closed under subtraction;
* `tendsto_l2On_weakDerivOn_sub_conv`: if `G = ∂_{vs} f` weakly on `B_R` (`|vs| ≤ 1`,
  `G ∈ L²`) and `∂_{vs}(ρ_n ⋆ f) = ρ_n ⋆ G` on `B_R`, then the weak derivative `∂_{vs}` of
  `f - ρ_n ⋆ f` on `B_R` tends to `0` in `L²(B_R)` (`03_compactness.tex:440-447`:
  "`∇w_δ → ∇w` in `L^a(B_{R+2})`").

The instance `IsFiniteMeasure (volume.restrict (ball x r))` comes from `Defs/Infra/Instances`; this
file declares no instance.
-/

noncomputable section

open MeasureTheory Set Filter Metric Function
open scoped ENNReal ContDiff Topology Convolution

namespace NonUniqueEuler.Weak.SmoothApproxAux

open NonUniqueEuler.Sob

theorem locallyIntegrableOn_ball_of_memLp {h : ℂ → ℂ} {r : ℝ}
    (hh : MemLp h 2 (volume.restrict (ball (0 : ℂ) r))) :
    LocallyIntegrableOn h (ball (0 : ℂ) r) :=
  IntegrableOn.locallyIntegrableOn (hh.integrable (by norm_num))

/-- `H¹_loc ⊆ L¹_loc`. -/
theorem locallyIntegrable_of_memHOn {k : ℕ} {f : ℂ → ℂ}
    (hf : ∀ r : ℝ, 0 < r → MemHOn k (ball (0 : ℂ) r) f) : LocallyIntegrable f volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨r, hr⟩ := hK.isBounded.subset_ball (0 : ℂ)
  have hr1 : 0 < max r 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hi : IntegrableOn f (ball (0 : ℂ) (max r 1)) volume :=
    (hf _ hr1).memLp.integrable (by norm_num)
  exact hi.mono_set
    (hr.trans (ball_subset_ball (le_max_left _ _)))

theorem memLp_ball_of_continuous {h : ℂ → ℂ} (hc : Continuous h) (r : ℝ) :
    MemLp h 2 (volume.restrict (ball (0 : ℂ) r)) := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn hc.continuousOn
  refine MemLp.of_bound hc.aestronglyMeasurable C ?_
  exact (ae_restrict_iff' measurableSet_ball).2
    (Eventually.of_forall fun x hx => hC x (ball_subset_closedBall hx))

theorem contDiff_iterDirDeriv {g : ℂ → ℂ} (hg : ContDiff ℝ ∞ g) (vs : List ℂ) :
    ContDiff ℝ ∞ (iterDirDeriv vs g) := by
  induction vs with
  | nil => simpa using hg
  | cons v vs ih =>
    rw [iterDirDeriv_cons]
    exact (ContDiff.fderiv_right (m := ∞) ih (by simp)).clm_apply contDiff_const

/-- Smooth functions lie in `H^k(B_r)`. -/
theorem memHOn_ball_of_contDiff {g : ℂ → ℂ} (hg : ContDiff ℝ ∞ g) (k : ℕ) (r : ℝ) :
    MemHOn k (ball (0 : ℂ) r) g :=
  (memHOn_of_contDiffOn isOpen_ball (hg.of_le (by exact_mod_cast le_top)).contDiffOn
    fun γ _ => memLp_ball_of_continuous (contDiff_iterDirDeriv hg _).continuous r).1

/-- Linearity of weak derivatives: difference. -/
theorem hasWeakDerivOn_sub_on {V : Set ℂ} (hV : IsOpen V) {vs : List ℂ} {f₁ f₂ g₁ g₂ : ℂ → ℂ}
    (hf₁ : LocallyIntegrableOn f₁ V) (hf₂ : LocallyIntegrableOn f₂ V)
    (hg₁ : LocallyIntegrableOn g₁ V) (hg₂ : LocallyIntegrableOn g₂ V)
    (h₁ : HasWeakDerivOn V vs f₁ g₁) (h₂ : HasWeakDerivOn V vs f₂ g₂) :
    HasWeakDerivOn V vs (fun x => f₁ x - f₂ x) (fun x => g₁ x - g₂ x) := by
  have hn := h₂.const_mul (-1)
  have ef : (fun x => -1 * f₂ x) = -f₂ := by funext x; simp
  have eg : (fun x => -1 * g₂ x) = -g₂ := by funext x; simp
  have key := HasWeakDerivOn.add hV hf₁ (ef ▸ hf₂.neg) hg₁ (eg ▸ hg₂.neg) h₁ hn
  have e1 : f₁ + (fun x => -1 * f₂ x) = fun x => f₁ x - f₂ x := by
    funext x; simp [sub_eq_add_neg]
  have e2 : g₁ + (fun x => -1 * g₂ x) = fun x => g₁ x - g₂ x := by
    funext x; simp [sub_eq_add_neg]
  rwa [e1, e2] at key

/-- `H^k(B_r)` is closed under subtraction. -/
theorem memHOn_sub {k : ℕ} {r : ℝ} {f g : ℂ → ℂ} (hf : MemHOn k (ball (0 : ℂ) r) f)
    (hg : MemHOn k (ball (0 : ℂ) r) g) : MemHOn k (ball (0 : ℂ) r) (fun x => f x - g x) where
  memLp := hf.memLp.sub hg.memLp
  deriv γ hγ := by
    obtain ⟨F, hF, hfF⟩ := hf.deriv γ hγ
    obtain ⟨G, hG, hgG⟩ := hg.deriv γ hγ
    exact ⟨fun x => F x - G x, hF.sub hG,
      hasWeakDerivOn_sub_on isOpen_ball (locallyIntegrableOn_ball_of_memLp hf.memLp)
        (locallyIntegrableOn_ball_of_memLp hg.memLp) (locallyIntegrableOn_ball_of_memLp hF)
        (locallyIntegrableOn_ball_of_memLp hG) hfF hgG⟩

/-- The weak derivatives of `f - ρ_n ⋆ f` tend to `0` in `L²(B_R)`. -/
theorem tendsto_l2On_weakDerivOn_sub_conv {R : ℝ} {f G : ℂ → ℂ} {vs : List ℂ}
    (hvs : vs.length ≤ 1) {b : ℕ → ContDiffBump (0 : ℂ)}
    (hb : Tendsto (fun n => (b n).rOut) atTop (𝓝 0)) (hb1 : ∀ n, (b n).rOut ≤ 1)
    (hfl : LocallyIntegrable f volume) (hG : MemLp G 2 volume)
    (hfG : HasWeakDerivOn (ball (0 : ℂ) R) vs f G)
    (hcomm : ∀ n, ∀ x ∈ ball (0 : ℂ) R,
      iterDirDeriv vs (conv ((b n).normed volume) f) x = conv ((b n).normed volume) G x) :
    Tendsto (fun n => l2On (ball (0 : ℂ) R)
      (weakDerivOn (ball (0 : ℂ) R) vs (fun x => f x - conv ((b n).normed volume) f x)))
      atTop (𝓝 0) := by
  have hGl : LocallyIntegrable G volume := hG.locallyIntegrable (by norm_num)
  have heq : ∀ n, l2On (ball (0 : ℂ) R)
      (weakDerivOn (ball (0 : ℂ) R) vs (fun x => f x - conv ((b n).normed volume) f x)) =
      (eLpNorm (G - conv ((b n).normed volume) G) 2
        (volume.restrict (ball (0 : ℂ) R))).toReal := by
    intro n
    have hgs : ContDiff ℝ ∞ (conv ((b n).normed volume) f) :=
      contDiff_conv (b n).contDiff_normed (b n).hasCompactSupport_normed hfl
    have hcG : Continuous (conv ((b n).normed volume) G) :=
      continuous_conv (b n).continuous_normed (b n).hasCompactSupport_normed hGl
    have h1 : HasWeakDerivOn (ball (0 : ℂ) R) vs (conv ((b n).normed volume) f)
        (iterDirDeriv vs (conv ((b n).normed volume) f)) :=
      hasWeakDerivOn_of_contDiffOn isOpen_ball (n := 1) hvs
        (hgs.of_le (by exact_mod_cast le_top)).contDiffOn
    have h2 : HasWeakDerivOn (ball (0 : ℂ) R) vs (conv ((b n).normed volume) f)
        (conv ((b n).normed volume) G) :=
      h1.congr_ae (Eventually.of_forall fun _ _ => rfl)
        (Eventually.of_forall fun x hx => hcomm n x hx)
    have h3 := hasWeakDerivOn_sub_on isOpen_ball (hfl.locallyIntegrableOn _)
      (hgs.continuous.locallyIntegrable.locallyIntegrableOn _) (hGl.locallyIntegrableOn _)
      (hcG.locallyIntegrable.locallyIntegrableOn _) hfG h2
    have h4 := weakDerivOn_ae_eq isOpen_ball
      ((hGl.sub hcG.locallyIntegrable).locallyIntegrableOn _) h3
    rw [l2On]
    congr 1
    exact eLpNorm_congr_ae ((ae_restrict_iff' measurableSet_ball).2 h4)
  simp_rw [heq]
  have hlim := tendsto_eLpNorm_conv_sub hb hb1 hG
  have hle : ∀ n, eLpNorm (G - conv ((b n).normed volume) G) 2
      (volume.restrict (ball (0 : ℂ) R)) ≤ eLpNorm (conv ((b n).normed volume) G - G) 2 volume := by
    intro n
    rw [eLpNorm_sub_comm]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  have h0 := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le) hle
  have h5 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h0
  simpa [Function.comp_def] using h5

end NonUniqueEuler.Weak.SmoothApproxAux
