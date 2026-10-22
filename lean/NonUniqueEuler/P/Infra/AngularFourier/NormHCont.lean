import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import NonUniqueEuler.I.Infra.AngularFourier.NormEquiv
import NonUniqueEuler.I.Infra.Sobolev.Norm
import NonUniqueEuler.I.Infra.SobolevOneD.Basic

/-!
# Proof: continuity of `t ↦ ‖h_t(r) e^{iℓθ}‖_{H^k}` (`I/Infra/AngularFourier/NormHCont.lean`)

Manuscript: proof of `prop:U`(b) (`04_ring.tex:1416-1417`).

Proof (as in the interface docstring). Fix `t₀ ∈ T` and put `d_t = h t - h t₀`.
* A profile smooth on `(0,∞)` and vanishing on `(0,∞) \ [ρ₋, ρ₊]` lies in `H^k((0,∞))`
  (`memH1On_of_smooth_supp`): its classical derivatives are continuous on `(0,∞)` and vanish
  off `[ρ₋, ρ₊]`, so they are in `L²((0,∞))`; `Sob.memH1On_of_contDiffOn`.
* `‖d_t‖²_{k,ℓ} ≤ (∑_j (1+ℓ²)^{k-j}) η² ρ₊ (ρ₊ - ρ₋)` when `|∂_r^j d_t| ≤ η` on `[ρ₋, ρ₊]`
  for `j ≤ k` (`secNormSq_le_of_deriv_le`; weak = classical derivatives,
  `Sob.weakDeriv1On_ae_eq_iteratedDeriv`).
* Joint continuity on `T × [ρ₋, ρ₊]` and compactness of `[ρ₋, ρ₊]` give uniform closeness of
  `∂_r^j h_t` to `∂_r^j h_{t₀}` for `t` near `t₀` in `T` (`IsCompact.mem_uniformity_of_prod`).
* The norm equivalence `exists_norm_equiv_ofProfile` bounds `‖ofProfile ℓ d_t‖²_{H^k}` by
  `C ‖d_t‖²_{k,ℓ}`, and the triangle inequality (`Sob.MemH.add`, `Sob.MemH.sub`) gives
  `|‖f_t‖_{H^k} - ‖f_{t₀}‖_{H^k}| ≤ ‖ofProfile ℓ d_t‖_{H^k}`.
-/

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace NonUniqueEuler.Ang

namespace NormHContAux

/-- The iterated derivatives of a profile vanishing on `(0,∞) \ [ρ₋, ρ₊]` vanish there too. -/
theorem iteratedDeriv_eq_zero_of_supp {ρm ρp : ℝ} {g : ℝ → ℂ}
    (hsupp : ∀ r : ℝ, 0 < r → r ∉ Icc ρm ρp → g r = 0) (j : ℕ) {r : ℝ} (hr : 0 < r)
    (hrI : r ∉ Icc ρm ρp) : iteratedDeriv j g r = 0 := by
  have hopen : IsOpen (Ioi (0 : ℝ) ∩ (Icc ρm ρp)ᶜ) := isOpen_Ioi.inter isClosed_Icc.isOpen_compl
  have hev : g =ᶠ[nhds r] fun _ => (0 : ℂ) := by
    filter_upwards [hopen.mem_nhds ⟨hr, hrI⟩] with x hx
    exact hsupp x hx.1 hx.2
  rw [Filter.EventuallyEq.iteratedDeriv_eq j hev]
  simp

/-- The iterated derivatives of a profile smooth on `(0,∞)` are continuous on `(0,∞)`. -/
theorem continuousOn_iteratedDeriv {g : ℝ → ℂ} (hg : ContDiffOn ℝ ∞ g (Ioi 0)) (j : ℕ) :
    ContinuousOn (iteratedDeriv j g) (Ioi 0) := by
  have h1 : ContinuousOn (iteratedDerivWithin j g (Ioi 0)) (Ioi 0) :=
    hg.continuousOn_iteratedDerivWithin (by exact_mod_cast le_top) isOpen_Ioi.uniqueDiffOn
  exact h1.congr fun x hx => (iteratedDerivWithin_of_isOpen isOpen_Ioi hx).symm

/-- A profile smooth on `(0,∞)` and vanishing on `(0,∞) \ [ρ₋, ρ₊]` (`ρ₋ > 0`) lies in
`H^k((0,∞))`. -/
theorem memH1On_of_smooth_supp (k : ℕ) {ρm ρp : ℝ} (hρm : 0 < ρm) {g : ℝ → ℂ}
    (hg : ContDiffOn ℝ ∞ g (Ioi 0)) (hsupp : ∀ r : ℝ, 0 < r → r ∉ Icc ρm ρp → g r = 0) :
    Sob.MemH1On k (Ioi 0) g := by
  refine Sob.memH1On_of_contDiffOn isOpen_Ioi (hg.of_le (by exact_mod_cast le_top))
    fun j _ => ?_
  set F := iteratedDeriv j g with hF
  have hIcc : Icc ρm ρp ⊆ Ioi 0 := fun r hr => lt_of_lt_of_le hρm hr.1
  have hcont : ContinuousOn F (Icc ρm ρp) := (continuousOn_iteratedDeriv hg j).mono hIcc
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have : IsFiniteMeasure (volume.restrict (Icc ρm ρp)) :=
    isFiniteMeasure_restrict.2 measure_Icc_lt_top.ne
  have hF2 : MemLp F 2 (volume.restrict (Icc ρm ρp)) :=
    MemLp.of_bound (hcont.aestronglyMeasurable measurableSet_Icc) M
      ((ae_restrict_mem measurableSet_Icc).mono fun r hr => hM r hr)
  have hind : MemLp ((Icc ρm ρp).indicator F) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_Icc).2 hF2
  refine (hind.restrict (Ioi 0)).ae_eq ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  by_cases hrI : r ∈ Icc ρm ρp
  · simp [indicator_of_mem hrI]
  · rw [indicator_of_notMem hrI]
    exact (iteratedDeriv_eq_zero_of_supp hsupp j hr hrI).symm

/-- The sector norm `‖g‖²_{k,ℓ}` of a profile smooth on `(0,∞)` whose derivatives of order
`≤ k` are bounded by `η` on `[ρ₋, ρ₊]`. -/
theorem secNormSq_le_of_deriv_le (k : ℕ) (ℓ : ℤ) {ρm ρp : ℝ} (hρm : 0 < ρm) (hρ : ρm ≤ ρp)
    {g : ℝ → ℂ} (hg : ContDiffOn ℝ ∞ g (Ioi 0)) {η : ℝ}
    (hη : ∀ j ≤ k, ∀ r ∈ Icc ρm ρp, ‖iteratedDeriv j g r‖ ≤ η) :
    Sob.secNormSq k ℓ (Icc ρm ρp) g ≤
      (∑ j ∈ Finset.range (k + 1), Sob.secWeight k j ℓ) * (η ^ 2 * ρp * (ρp - ρm)) := by
  unfold Sob.secNormSq
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  refine mul_le_mul_of_nonneg_left ?_ (Sob.secWeight_nonneg k j ℓ)
  have hae := Sob.weakDeriv1On_ae_eq_iteratedDeriv (k := k) isOpen_Ioi
    (hg.of_le (by exact_mod_cast le_top)) hjk
  have : IsFiniteMeasure (volume.restrict (Icc ρm ρp)) :=
    isFiniteMeasure_restrict.2 measure_Icc_lt_top.ne
  have hle : ∫ r in Icc ρm ρp, ‖Sob.weakDeriv1On (Ioi 0) j g r‖ ^ 2 * r ≤
      ∫ _ in Icc ρm ρp, η ^ 2 * ρp := by
    refine integral_mono_of_nonneg ?_ (integrable_const _) ?_
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact mul_nonneg (sq_nonneg _) (hρm.le.trans hr.1)
    · filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hae] with r hr hr'
      have hr0 : 0 < r := lt_of_lt_of_le hρm hr.1
      rw [hr' hr0]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hη j hjk r hr) 2) hr.2 hr0.le
        (sq_nonneg η)
  refine hle.trans (le_of_eq ?_)
  rw [setIntegral_const, Real.volume_real_Icc_of_le hρ, smul_eq_mul]
  ring

end NormHContAux

open NormHContAux

/-- If profiles `h t` (`t ∈ T`) are smooth on `(0,∞)`, vanish outside `[ρ₋, ρ₊]`, and their
`r`-derivatives of order `≤ k` are jointly continuous on `T × [ρ₋, ρ₊]`, then
`t ↦ ‖h_t(|x|) e^{iℓθ}‖_{H^k}` is continuous on `T`. -/
theorem continuousOn_normH_ofProfile (k : ℕ) {ρm ρp : ℝ} (hρm : 0 < ρm) (hρ : ρm < ρp)
    (ℓ : ℤ) {T : Set ℝ} {h : ℝ → ℝ → ℂ}
    (hsmooth : ∀ t ∈ T, ContDiffOn ℝ ∞ (h t) (Ioi 0))
    (hsupp : ∀ t ∈ T, ∀ r : ℝ, 0 < r → r ∉ Icc ρm ρp → h t r = 0)
    (hcont : ∀ j ≤ k,
      ContinuousOn (fun q : ℝ × ℝ => iteratedDeriv j (h q.1) q.2) (T ×ˢ Icc ρm ρp)) :
    ContinuousOn (fun t => Sob.normH k (ofProfile ℓ (h t))) T := by
  obtain ⟨c, C, -, hC, hequiv⟩ := exists_norm_equiv_ofProfile k hρm hρ
  -- the a.e. support condition from the pointwise one
  have hsuppAE : ∀ g : ℝ → ℂ, (∀ r : ℝ, 0 < r → r ∉ Icc ρm ρp → g r = 0) →
      ∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc ρm ρp → g r = 0 := fun g hg =>
    (ae_restrict_mem measurableSet_Ioi).mono fun r hr hrI => hg r hr hrI
  -- sector functions of admissible profiles are in `H^k`, with the upper norm bound
  have hmem : ∀ g : ℝ → ℂ, ContDiffOn ℝ ∞ g (Ioi 0) →
      (∀ r : ℝ, 0 < r → r ∉ Icc ρm ρp → g r = 0) →
      Sob.MemH k (ofProfile ℓ g) ∧
        Sob.normH k (ofProfile ℓ g) ^ 2 ≤ C * Sob.secNormSq k ℓ (Icc ρm ρp) g := by
    intro g hg hgs
    obtain ⟨h1, -, h3⟩ := hequiv ℓ g (memH1On_of_smooth_supp k hρm hg hgs) (hsuppAE g hgs)
    exact ⟨h1, h3⟩
  intro t₀ ht₀
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  set W : ℝ := ∑ j ∈ Finset.range (k + 1), Sob.secWeight k j ℓ with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun j _ => Sob.secWeight_nonneg k j ℓ
  set K : ℝ := C * W * (ρp * (ρp - ρm)) with hK
  have hK0 : 0 ≤ K := by
    have : 0 < ρp - ρm := sub_pos.2 hρ
    have : 0 < ρp := hρm.trans hρ
    positivity
  set η : ℝ := ε / Real.sqrt (K + 1) with hη
  have hsq : 0 < Real.sqrt (K + 1) := Real.sqrt_pos.2 (by linarith)
  have hηpos : 0 < η := div_pos hε hsq
  have hKη : K * η ^ 2 < ε ^ 2 := by
    rw [hη, div_pow, Real.sq_sqrt (by linarith), mul_div_assoc', div_lt_iff₀ (by linarith)]
    nlinarith [sq_pos_of_pos hε]
  -- uniform closeness of the derivatives for `t` near `t₀` in `T`
  have hunif : ∀ j ∈ Finset.range (k + 1), ∀ᶠ t in nhdsWithin t₀ T,
      ∀ r ∈ Icc ρm ρp, dist (iteratedDeriv j (h t) r) (iteratedDeriv j (h t₀) r) < η := by
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    obtain ⟨v, hv, hvp⟩ := IsCompact.mem_uniformity_of_prod
      (f := fun t r => iteratedDeriv j (h t) r) isCompact_Icc (hcont j hjk) ht₀
      (Metric.dist_mem_uniformity hηpos)
    exact Filter.mem_of_superset hv fun t ht r hr => hvp t ht r hr
  have hev : ∀ᶠ t in nhdsWithin t₀ T, t ∈ T ∧ ∀ j ∈ Finset.range (k + 1),
      ∀ r ∈ Icc ρm ρp, dist (iteratedDeriv j (h t) r) (iteratedDeriv j (h t₀) r) < η :=
    Filter.Eventually.and self_mem_nhdsWithin ((Filter.eventually_all_finset _).2 hunif)
  filter_upwards [hev] with t ⟨ht, htη⟩
  -- the difference profile
  set d : ℝ → ℂ := fun r => h t r - h t₀ r with hd
  have hd_smooth : ContDiffOn ℝ ∞ d (Ioi 0) := (hsmooth t ht).sub (hsmooth t₀ ht₀)
  have hd_supp : ∀ r : ℝ, 0 < r → r ∉ Icc ρm ρp → d r = 0 := fun r hr hrI => by
    simp [hd, hsupp t ht r hr hrI, hsupp t₀ ht₀ r hr hrI]
  have hd_deriv : ∀ j ≤ k, ∀ r ∈ Icc ρm ρp, ‖iteratedDeriv j d r‖ ≤ η := by
    intro j hj r hr
    have hr0 : (0 : ℝ) < r := lt_of_lt_of_le hρm hr.1
    have h1 : ContDiffAt ℝ j (h t) r :=
      ((hsmooth t ht).contDiffAt (Ioi_mem_nhds hr0)).of_le (by exact_mod_cast le_top)
    have h2 : ContDiffAt ℝ j (h t₀) r :=
      ((hsmooth t₀ ht₀).contDiffAt (Ioi_mem_nhds hr0)).of_le (by exact_mod_cast le_top)
    rw [hd, iteratedDeriv_fun_sub h1 h2, ← dist_eq_norm]
    exact (htη j (Finset.mem_range.2 (Nat.lt_succ_of_le hj)) r hr).le
  obtain ⟨hmd, hnd⟩ := hmem d hd_smooth hd_supp
  obtain ⟨hmt, -⟩ := hmem (h t) (hsmooth t ht) (hsupp t ht)
  obtain ⟨hm0, -⟩ := hmem (h t₀) (hsmooth t₀ ht₀) (hsupp t₀ ht₀)
  -- `‖ofProfile ℓ d‖_{H^k} < ε`
  have hsec := secNormSq_le_of_deriv_le k ℓ hρm hρ.le hd_smooth hd_deriv
  have hnd' : Sob.normH k (ofProfile ℓ d) ^ 2 < ε ^ 2 := by
    calc Sob.normH k (ofProfile ℓ d) ^ 2 ≤ C * Sob.secNormSq k ℓ (Icc ρm ρp) d := hnd
      _ ≤ C * (W * (η ^ 2 * ρp * (ρp - ρm))) := mul_le_mul_of_nonneg_left hsec hC.le
      _ = K * η ^ 2 := by rw [hK]; ring
      _ < ε ^ 2 := hKη
  have hlt : Sob.normH k (ofProfile ℓ d) < ε :=
    lt_of_pow_lt_pow_left₀ 2 hε.le hnd'
  -- the triangle inequality
  have hadd : ofProfile ℓ (h t) = ofProfile ℓ (h t₀) + ofProfile ℓ d := by
    funext x
    simp only [ofProfile, Pi.add_apply, hd]
    ring
  have hsub : ofProfile ℓ (h t₀) = ofProfile ℓ (h t) - ofProfile ℓ d := by
    funext x
    simp only [ofProfile, Pi.sub_apply, hd]
    ring
  have h1 := (hm0.add hmd).2
  have h2 := (hmt.sub hmd).2
  rw [← hadd] at h1
  rw [← hsub] at h2
  rw [Real.dist_eq]
  exact lt_of_le_of_lt (abs_sub_le_iff.2 ⟨by linarith, by linarith⟩) hlt

end NonUniqueEuler.Ang
