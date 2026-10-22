import NonUniqueEuler.Defs.Sec3.Transport
import NonUniqueEuler.Defs.Sec3.Commutator
import NonUniqueEuler.Defs.Sec2.Spaces
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Helper for `P/Sec3/Transport/Mollified`: basic facts

* Derivatives of test functions (`timeDeriv_eq_fderiv`, `spaceDeriv_eq_fderiv`, bounds,
  continuity, the support in `(-∞,b] × B_R`). Copied from `H/Sec3/Transport/Basic.lean`
  (a helper of the proof of `Sec3/Transport`, not imported here).
* Renormalizations: `|Υ(s)| ≤ L|s|`, `|Υ'| ≤ C`.
* The slab `(t₀,T) × ℝ²` as a product measure.
* `L^∞(I; L^p)` facts: `w ∈ L^∞(0,T; L¹(B_R))` from `w ∈ L^∞(0,T; H¹(B_R))`, integrability on
  products.
* The kernel `ρ_ε = scaled ρ ε`: `C^∞`, compactly supported, bounded with bounded derivative.

All lemmas are in the namespace `NonUniqueEuler.Weak.MollifiedH` to avoid clashes.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace NonUniqueEuler.Weak.MollifiedH

/-! ### Derivatives of a test function -/

theorem timeDeriv_eq_fderiv {φ : ℝ × ℂ → ℝ} (hφ : Differentiable ℝ φ) (t : ℝ) (x : ℂ) :
    timeDeriv φ t x = fderiv ℝ φ (t, x) ((1 : ℝ), (0 : ℂ)) := by
  have h1 : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : ℂ)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  exact ((hφ (t, x)).hasFDerivAt.comp_hasDerivAt t h1).deriv

theorem fderiv_slice_eq {φ : ℝ × ℂ → ℝ} (hφ : Differentiable ℝ φ) (t : ℝ) (x : ℂ) :
    fderiv ℝ (fun y => φ (t, y)) x = (fderiv ℝ φ (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ ℂ) :=
  ((hφ (t, x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)).fderiv

theorem spaceDeriv_eq_fderiv {φ : ℝ × ℂ → ℝ} (hφ : Differentiable ℝ φ) (t : ℝ) (x w : ℂ) :
    spaceDeriv φ t x w = fderiv ℝ φ (t, x) ((0 : ℝ), w) := by
  simp only [spaceDeriv, fderiv_slice_eq hφ t x, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply]

theorem differentiable_of_isTestFunction {T : ℝ} {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) :
    Differentiable ℝ φ :=
  hφ.contDiff.differentiable (by simp)

theorem continuous_fderiv_of_isTestFunction {T : ℝ} {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) :
    Continuous (fderiv ℝ φ) :=
  hφ.contDiff.continuous_fderiv (by simp)

/-- A test function has a bounded derivative. -/
theorem exists_bound_fderiv_of_isTestFunction {T : ℝ} {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ p, ‖fderiv ℝ φ p‖ ≤ D := by
  obtain ⟨D, hD⟩ :=
    (continuous_fderiv_of_isTestFunction hφ).bounded_above_of_compact_support
      (hφ.hasCompactSupport.fderiv (𝕜 := ℝ))
  exact ⟨D, (norm_nonneg _).trans (hD 0), hD⟩

/-- A test function is bounded. -/
theorem exists_bound_of_isTestFunction {T : ℝ} {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ p, |φ p| ≤ A := by
  obtain ⟨A, hA⟩ := hφ.contDiff.continuous.bounded_above_of_compact_support hφ.hasCompactSupport
  exact ⟨A, (norm_nonneg _).trans (hA 0), fun p => by rw [← Real.norm_eq_abs]; exact hA p⟩

theorem abs_spaceDeriv_le {T : ℝ} {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) {D : ℝ}
    (hD : ∀ p, ‖fderiv ℝ φ p‖ ≤ D) (t : ℝ) (x w : ℂ) : |spaceDeriv φ t x w| ≤ D * ‖w‖ := by
  rw [spaceDeriv_eq_fderiv (differentiable_of_isTestFunction hφ), ← Real.norm_eq_abs]
  refine ((fderiv ℝ φ (t, x)).le_opNorm _).trans ?_
  have h1 : ‖((0 : ℝ), w)‖ = ‖w‖ := by simp [Prod.norm_def]
  rw [h1]
  exact mul_le_mul_of_nonneg_right (hD _) (norm_nonneg _)

theorem continuous_timeDeriv {T : ℝ} {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) :
    Continuous (fun p : ℝ × ℂ => timeDeriv φ p.1 p.2) := by
  have : (fun p : ℝ × ℂ => timeDeriv φ p.1 p.2) =
      fun p => fderiv ℝ φ p ((1 : ℝ), (0 : ℂ)) := by
    funext p
    rw [timeDeriv_eq_fderiv (differentiable_of_isTestFunction hφ)]
  rw [this]
  exact (continuous_fderiv_of_isTestFunction hφ).clm_apply continuous_const

theorem continuous_fderiv_slice {T : ℝ} {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) :
    Continuous (fun p : ℝ × ℂ => fderiv ℝ (fun y => φ (p.1, y)) p.2) := by
  have : (fun p : ℝ × ℂ => fderiv ℝ (fun y => φ (p.1, y)) p.2) =
      fun p => (fderiv ℝ φ p).comp (ContinuousLinearMap.inr ℝ ℝ ℂ) := by
    funext p
    rw [fderiv_slice_eq (differentiable_of_isTestFunction hφ)]
  rw [this]
  exact (continuous_fderiv_of_isTestFunction hφ).clm_comp continuous_const

/-- The time slices of a test function vanish outside the projection of its support. -/
theorem exists_ball_of_isTestFunction {T : ℝ} {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) :
    ∃ R : ℝ, 0 < R ∧ ∃ b : ℝ, b < T ∧ ∀ p ∈ tsupport φ, p.1 ≤ b ∧ p.2 ∈ ball (0 : ℂ) R := by
  have hK := hφ.hasCompactSupport.isCompact
  obtain ⟨R, hR⟩ := (hK.image continuous_snd).isBounded.subset_ball (0 : ℂ)
  rcases (tsupport φ).eq_empty_or_nonempty with he | hne
  · exact ⟨max R 1, lt_of_lt_of_le one_pos (le_max_right _ _), T - 1, by linarith,
      fun p hp => by simp [he] at hp⟩
  · obtain ⟨q, hq, hqmax⟩ := hK.exists_isMaxOn hne continuous_fst.continuousOn
    refine ⟨max R 1, lt_of_lt_of_le one_pos (le_max_right _ _), q.1, hφ.support_lt q hq,
      fun p hp => ⟨hqmax hp, ?_⟩⟩
    exact ball_subset_ball (le_max_left _ _) (hR (mem_image_of_mem _ hp))

theorem eq_zero_of_notMem_tsupport {φ : ℝ × ℂ → ℝ} {p : ℝ × ℂ} (hp : p ∉ tsupport φ) :
    φ p = 0 :=
  image_eq_zero_of_notMem_tsupport hp

theorem fderiv_eq_zero_of_notMem_tsupport {φ : ℝ × ℂ → ℝ} {p : ℝ × ℂ} (hp : p ∉ tsupport φ) :
    fderiv ℝ φ p = 0 := by
  have : p ∉ tsupport (fderiv ℝ φ) := fun h => hp (tsupport_fderiv_subset ℝ h)
  exact image_eq_zero_of_notMem_tsupport this

/-- Outside the support of `φ`, `w·∇φ = 0`. -/
theorem spaceDeriv_eq_zero_of_notMem {T : ℝ} {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ)
    {t : ℝ} {x : ℂ} (hp : (t, x) ∉ tsupport φ) (v : ℂ) : spaceDeriv φ t x v = 0 := by
  rw [spaceDeriv_eq_fderiv (differentiable_of_isTestFunction hφ),
    fderiv_eq_zero_of_notMem_tsupport hp]
  simp

/-- The slice `x ↦ φ(t, x)` of a test function is `C^∞` with compact support. -/
theorem slice_contDiff_hasCompactSupport {T : ℝ} {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ)
    (t : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℂ => φ (t, x)) ∧
      HasCompactSupport (fun x : ℂ => φ (t, x)) := by
  refine ⟨hφ.contDiff.comp (contDiff_const.prodMk contDiff_id), ?_⟩
  refine HasCompactSupport.intro (hφ.hasCompactSupport.isCompact.image continuous_snd)
    fun x hx => ?_
  by_contra hne
  exact hx ⟨(t, x), subset_tsupport _ hne, rfl⟩

/-- The slice `s ↦ φ(s, x)` of a test function lies in `C_c^∞((-∞,T))`. -/
theorem isTimeTestFn_slice {T : ℝ} {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) (x : ℂ) :
    IsTimeTestFn T (fun s : ℝ => φ (s, x)) := by
  have hsub : tsupport (fun s : ℝ => φ (s, x)) ⊆ (fun s : ℝ => (s, x)) ⁻¹' tsupport φ := by
    refine closure_minimal (fun s hs => subset_tsupport _ hs) ?_
    exact (isClosed_tsupport φ).preimage (continuous_id.prodMk continuous_const)
  refine ⟨hφ.contDiff.comp (contDiff_id.prodMk contDiff_const), ?_, ?_⟩
  · refine HasCompactSupport.intro (hφ.hasCompactSupport.isCompact.image continuous_fst)
      fun s hs => ?_
    by_contra hne
    exact hs ⟨(s, x), subset_tsupport _ hne, rfl⟩
  · intro s hs
    exact hφ.support_lt _ (hsub hs)

/-! ### Renormalizations -/

theorem exists_abs_le_of_isRenormalization {Υ : ℝ → ℝ} (hΥ : IsRenormalization Υ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ s, |Υ s| ≤ L * |s| := by
  obtain ⟨C, hC⟩ := hΥ.deriv_bounded
  have hd : Differentiable ℝ Υ := hΥ.contDiff.differentiable one_ne_zero
  refine ⟨C, (abs_nonneg _).trans (hC 0), fun s => ?_⟩
  have h := convex_univ.norm_image_sub_le_of_norm_deriv_le (f := Υ) (fun x _ => hd x)
    (fun x _ => by rw [Real.norm_eq_abs]; exact hC x) (mem_univ (0 : ℝ)) (mem_univ s)
  simpa [hΥ.map_zero, Real.norm_eq_abs] using h

theorem exists_abs_deriv_le_of_isRenormalization {Υ : ℝ → ℝ} (hΥ : IsRenormalization Υ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, |deriv Υ s| ≤ C := by
  obtain ⟨C, hC⟩ := hΥ.deriv_bounded
  exact ⟨C, (abs_nonneg _).trans (hC 0), hC⟩

theorem continuous_deriv_of_isRenormalization {Υ : ℝ → ℝ} (hΥ : IsRenormalization Υ) :
    Continuous (deriv Υ) :=
  hΥ.contDiff.continuous_deriv le_rfl

/-! ### The slab as a product -/

theorem restrict_slabFrom_eq_prod (t₀ T : ℝ) :
    volume.restrict (slabFrom t₀ T) =
      (volume.restrict (Ioo t₀ T)).prod (volume : Measure ℂ) := by
  rw [slabFrom, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

theorem restrict_prod_eq_prod (I : Set ℝ) (Ω : Set ℂ) :
    volume.restrict (I ×ˢ Ω) = (volume.restrict I).prod (volume.restrict Ω) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]

theorem slabFrom_subset_prod {t₀ T : ℝ} (ht₀ : 0 ≤ t₀) :
    slabFrom t₀ T ⊆ Ioo (0 : ℝ) T ×ˢ (univ : Set ℂ) :=
  prod_mono (Ioo_subset_Ioo_left ht₀) le_rfl

theorem volume_Ioo_ne_top (a b : ℝ) : volume (Ioo a b) ≠ ∞ := by
  rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top

/-- Integrability on `I × Ω` from an essential bound of the slice integrals. -/
theorem integrableOn_prod_of_ae_lintegral_le {E : Type*} [NormedAddCommGroup E] {I : Set ℝ}
    (hI : volume I ≠ ∞) {Ω : Set ℂ} {f : ℝ × ℂ → E}
    (hf : AEStronglyMeasurable f (volume.restrict (I ×ˢ Ω))) {M : ℝ≥0∞} (hM : M ≠ ∞)
    (hb : ∀ᵐ t ∂(volume.restrict I), ∫⁻ x in Ω, ‖f (t, x)‖ₑ ≤ M) :
    IntegrableOn f (I ×ˢ Ω) := by
  refine ⟨hf, ?_⟩
  rw [HasFiniteIntegral, restrict_prod_eq_prod]
  rw [restrict_prod_eq_prod] at hf
  rw [lintegral_prod _ hf.enorm]
  calc ∫⁻ t, ∫⁻ x, ‖f (t, x)‖ₑ ∂(volume.restrict Ω) ∂(volume.restrict I)
      ≤ ∫⁻ _t, M ∂(volume.restrict I) := lintegral_mono_ae hb
    _ = M * volume I := by rw [lintegral_const, Measure.restrict_apply_univ]
    _ < ∞ := ENNReal.mul_lt_top hM.lt_top hI.lt_top

/-- From `‖g‖_{L^p(Ω)} ≤ M` (real form) to the `ℝ≥0∞` form. -/
theorem eLpNorm_le_ofReal {E : Type*} [NormedAddCommGroup E] {g : ℂ → E} {p : ℝ≥0∞}
    {μ : Measure ℂ} (hg : MemLp g p μ) {M : ℝ} (hM : (eLpNorm g p μ).toReal ≤ M) :
    eLpNorm g p μ ≤ ENNReal.ofReal M := by
  rw [← ENNReal.ofReal_toReal hg.eLpNorm_ne_top]
  exact ENNReal.ofReal_le_ofReal hM

/-- `u ∈ L^∞(I; L¹(Ω))` on an interval of finite measure is integrable on `I × Ω`. -/
theorem integrableOn_of_memLinfLp_one {E : Type*} [NormedAddCommGroup E] {I : Set ℝ}
    (hI : volume I ≠ ∞) {Ω : Set ℂ} {u : ℝ → ℂ → E} (hu : Prelim.MemLinfLp I Ω 1 u) :
    IntegrableOn (Function.uncurry u) (I ×ˢ Ω) := by
  obtain ⟨M, hM⟩ := hu.essBounded
  refine integrableOn_prod_of_ae_lintegral_le hI hu.aestronglyMeasurable
    (ENNReal.ofReal_ne_top (r := M)) (hM.mono fun t ht => ?_)
  have h := eLpNorm_le_ofReal ht.1 ht.2
  rw [eLpNorm_one_eq_lintegral_enorm] at h
  exact h

/-- `L^∞(I; L²(Ω)) ⊂ L^∞(I; L¹(Ω))` for `|Ω| < ∞`. -/
theorem memLinfLp_one_of_two {E : Type*} [NormedAddCommGroup E] {I : Set ℝ} {Ω : Set ℂ}
    (hΩ : volume Ω ≠ ∞) {u : ℝ → ℂ → E} (hu : Prelim.MemLinfLp I Ω 2 u) :
    Prelim.MemLinfLp I Ω 1 u := by
  obtain ⟨M, hM⟩ := hu.essBounded
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.2 hΩ
  refine ⟨hu.aestronglyMeasurable, M * ((volume Ω).toReal ^ (1 / 2 : ℝ)), hM.mono fun t ht => ?_⟩
  refine ⟨ht.1.mono_exponent (by norm_num), ?_⟩
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict Ω) (p := 1) (q := 2)
    (by norm_num) ht.1.aestronglyMeasurable
  rw [Measure.restrict_apply_univ] at h
  have h1 : (1 : ℝ≥0∞).toReal = 1 := by simp
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by simp
  rw [h1, h2] at h
  have hne : eLpNorm (u t) 2 (volume.restrict Ω) * volume Ω ^ (1 / 1 - 1 / 2 : ℝ) ≠ ∞ :=
    ENNReal.mul_ne_top ht.1.eLpNorm_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hΩ)
  refine (ENNReal.toReal_mono hne h).trans ?_
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
  norm_num
  exact mul_le_mul_of_nonneg_right ht.2 (by positivity)

/-! ### `H¹(B_R) ⊂ L²(B_R)` -/

theorem l2On_congr_ae {V : Set ℂ} (hV : MeasurableSet V) {f g : ℂ → ℂ}
    (h : ∀ᵐ x, x ∈ V → f x = g x) : Sob.l2On V f = Sob.l2On V g := by
  unfold Sob.l2On
  rw [eLpNorm_congr_ae ((ae_restrict_iff' hV).2 h)]

theorem hasWeakDerivOn_zero_order (V : Set ℂ) (f : ℂ → ℂ) :
    Sob.HasWeakDerivOn V (Sob.pdList (0, 0)) f f := by
  intro φ _
  simp [Sob.pdList, Sob.iterDirDeriv]

/-- `‖f‖_{L²(V)} ≤ ‖f‖_{H^k(V)}`. -/
theorem l2On_le_normHOn {k : ℕ} {V : Set ℂ} (hV : IsOpen V) {f : ℂ → ℂ}
    (hf : MemLp f 2 (volume.restrict V)) : Sob.l2On V f ≤ Sob.normHOn k V f := by
  have hloc : LocallyIntegrableOn f V :=
    locallyIntegrableOn_of_locallyIntegrable_restrict (hf.locallyIntegrable one_le_two)
  have hae := Sob.weakDerivOn_ae_eq hV hloc (hasWeakDerivOn_zero_order V f)
  have e : Sob.l2On V (Sob.weakPartialOn V (0, 0) f) = Sob.l2On V f :=
    l2On_congr_ae hV.measurableSet hae
  rw [← e]
  unfold Sob.normHOn
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun β => Sob.l2On V (Sob.weakPartialOn V β f) ^ 2)
    (fun β _ => sq_nonneg _) (Sob.zero_mem_multiIdx k)

/-- A field in `L^∞(0,T; H¹(B_R))` lies in `L^∞(0,T; L²(B_R))`. -/
theorem memLinfLp_two_of_isBddH1 {I : Set ℝ} {w : ℝ → ℂ → ℂ} (hw : IsBddH1DivFreeField I w)
    {R : ℝ} (hR : 0 < R) : Prelim.MemLinfLp I (ball (0 : ℂ) R) 2 w := by
  obtain ⟨M, hM⟩ := hw.bound R hR
  refine ⟨hw.aestronglyMeasurable.mono_measure
    (Measure.restrict_mono (prod_mono le_rfl (subset_univ _)) le_rfl), M, hM.mono fun t ht => ?_⟩
  exact ⟨ht.1.memLp, (l2On_le_normHOn isOpen_ball ht.1.memLp).trans ht.2⟩

/-- A field in `L^∞(0,T; H¹_loc)` is integrable on `(0,T) × B_R`. -/
theorem integrableOn_ball_of_isBddH1 {T : ℝ} {w : ℝ → ℂ → ℂ}
    (hw : IsBddH1DivFreeField (Ioo 0 T) w) {R : ℝ} (hR : 0 < R) :
    IntegrableOn (Function.uncurry w) (Ioo 0 T ×ˢ ball (0 : ℂ) R) :=
  integrableOn_of_memLinfLp_one (volume_Ioo_ne_top 0 T)
    (memLinfLp_one_of_two measure_ball_lt_top.ne (memLinfLp_two_of_isBddH1 hw hR))

/-- For a.e. `t`, `w(t)` is locally integrable and weakly divergence free. -/
theorem ae_locallyIntegrable_divFree {I : Set ℝ} {w : ℝ → ℂ → ℂ}
    (hw : IsBddH1DivFreeField I w) :
    ∀ᵐ t ∂(volume.restrict I), LocallyIntegrable (w t) volume ∧ Prelim.IsWeaklyDivFree (w t) := by
  have hall : ∀ᵐ t ∂(volume.restrict I), ∀ n : ℕ,
      Sob.MemHOn 1 (ball (0 : ℂ) ((n : ℝ) + 1)) (w t) := by
    rw [ae_all_iff]
    intro n
    obtain ⟨M, hM⟩ := hw.bound ((n : ℝ) + 1) (by positivity)
    exact hM.mono fun t ht => ht.1
  filter_upwards [hall, hw.divFree] with t ht hdiv
  refine ⟨?_, hdiv⟩
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨r, hr⟩ := hK.isBounded.subset_ball (0 : ℂ)
  obtain ⟨n, hn⟩ := exists_nat_gt r
  have hsub : K ⊆ ball (0 : ℂ) ((n : ℝ) + 1) :=
    hr.trans (ball_subset_ball (by linarith))
  have : IsFiniteMeasure (volume.restrict (ball (0 : ℂ) ((n : ℝ) + 1))) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hint : IntegrableOn (w t) (ball (0 : ℂ) ((n : ℝ) + 1)) :=
    (ht n).memLp.integrable (by norm_num)
  exact hint.mono_set hsub

/-! ### The kernel `ρ_ε` -/

section Kernel

variable {ρ : ℂ → ℝ}

theorem scaled_eq_comp (ρ : ℂ → ℝ) (ε : ℝ) :
    scaled ρ ε = fun x => (ε ^ 2)⁻¹ * ρ ((ε : ℂ)⁻¹ * x) :=
  rfl

theorem contDiff_scaled (hρ : IsMollifier ρ) (ε : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (scaled ρ ε) :=
  contDiff_const.mul (hρ.contDiff.comp (contDiff_const.mul contDiff_id))

theorem hasCompactSupport_scaled (hρ : IsMollifier ρ) {ε : ℝ} (hε : ε ≠ 0) :
    HasCompactSupport (scaled ρ ε) := by
  have hc : HasCompactSupport (fun x : ℂ => ρ ((ε : ℂ)⁻¹ * x)) := by
    have hε' : ((ε : ℂ)⁻¹) ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.2 hε)
    have h := hρ.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft₀ _ hε')
    exact h
  exact hc.mul_left

theorem continuous_scaled (hρ : IsMollifier ρ) (ε : ℝ) : Continuous (scaled ρ ε) :=
  (contDiff_scaled hρ ε).continuous

theorem continuous_fderiv_scaled (hρ : IsMollifier ρ) (ε : ℝ) :
    Continuous (fderiv ℝ (scaled ρ ε)) :=
  (contDiff_scaled hρ ε).continuous_fderiv (by simp)

/-- `ρ_ε` is bounded. -/
theorem exists_bound_scaled (hρ : IsMollifier ρ) {ε : ℝ} (hε : ε ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, |scaled ρ ε z| ≤ C := by
  obtain ⟨C, hC⟩ := (continuous_scaled hρ ε).bounded_above_of_compact_support
    (hasCompactSupport_scaled hρ hε)
  exact ⟨C, (norm_nonneg _).trans (hC 0), fun z => by rw [← Real.norm_eq_abs]; exact hC z⟩

/-- `Dρ_ε` is bounded. -/
theorem exists_bound_fderiv_scaled (hρ : IsMollifier ρ) {ε : ℝ} (hε : ε ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖fderiv ℝ (scaled ρ ε) z‖ ≤ C := by
  obtain ⟨C, hC⟩ := (continuous_fderiv_scaled hρ ε).bounded_above_of_compact_support
    ((hasCompactSupport_scaled hρ hε).fderiv (𝕜 := ℝ))
  exact ⟨C, (norm_nonneg _).trans (hC 0), hC⟩

end Kernel

end NonUniqueEuler.Weak.MollifiedH
