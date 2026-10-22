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
# Helper for `P/Sec3/Transport`: basic facts

* Derivatives of test functions (`timeDeriv_eq_fderiv`, `spaceDeriv_eq_fderiv`, bounds and
  continuity; adapted from `P/Sec2/WeakIntegrability.lean`).
* `Lip₀` and renormalizations: `|β(s)| ≤ L|s|`.
* The slab `(t₀,T) × ℝ²` as a product measure; integrability on products from an essential
  bound of the slice integrals (`integrableOn_prod_of_ae_lintegral_le`).
* `L^∞(I; L^p)` facts: integrability of `u` on the slab, `w ∈ L^∞(0,T; L²(B_R))` from
  `w ∈ L^∞(0,T; H¹(B_R))` (`l2On_le_normHOn`, copied in spirit from
  `H/Infra/Sobolev/Local/Basic.lean`).
* The transport integrand of `β(u)` for `|β(s)| ≤ L|s|` is integrable on `(t₀,T) × ℝ²`, and so
  is the datum term (`integrableOn_transportIntegrand_comp`, `integrable_datum_comp`).
* The standing assumptions `IsTEData` of `(te)` under the hypotheses of `lem:transport`
  (`isTEData_of_transport`), for `lem:lip-renorm`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace NonUniqueEuler.Weak.TransportH

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

theorem abs_timeDeriv_le {T : ℝ} {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) {D : ℝ}
    (hD : ∀ p, ‖fderiv ℝ φ p‖ ≤ D) (t : ℝ) (x : ℂ) : |timeDeriv φ t x| ≤ D := by
  rw [timeDeriv_eq_fderiv (differentiable_of_isTestFunction hφ), ← Real.norm_eq_abs]
  refine ((fderiv ℝ φ (t, x)).le_opNorm _).trans ?_
  have h1 : ‖((1 : ℝ), (0 : ℂ))‖ = 1 := by simp [Prod.norm_def]
  rw [h1, mul_one]
  exact hD _

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

/-- The integrand `u (∂_tφ + w·∇φ)` is a.e.-strongly measurable when `u` and `w` are. -/
theorem aestronglyMeasurable_transportIntegrand {T : ℝ} {φ : ℝ × ℂ → ℝ}
    (hφ : IsTestFunction T φ) {μ : Measure (ℝ × ℂ)} {u : ℝ → ℂ → ℝ} {w : ℝ → ℂ → ℂ}
    (hu : AEStronglyMeasurable (Function.uncurry u) μ)
    (hw : AEStronglyMeasurable (fun p : ℝ × ℂ => w p.1 p.2) μ) :
    AEStronglyMeasurable (transportIntegrand u w φ) μ := by
  have hsd : AEStronglyMeasurable (fun p : ℝ × ℂ => spaceDeriv φ p.1 p.2 (w p.1 p.2)) μ :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂
      (continuous_fderiv_slice hφ).aestronglyMeasurable hw
  exact hu.mul ((continuous_timeDeriv hφ).aestronglyMeasurable.add hsd)

/-- `|∂_tφ + w·∇φ| ≤ D (1 + |w|)`. -/
theorem abs_timeDeriv_add_spaceDeriv_le {T : ℝ} {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ)
    {D : ℝ} (hD : ∀ p, ‖fderiv ℝ φ p‖ ≤ D) (t : ℝ) (x v : ℂ) :
    |timeDeriv φ t x + spaceDeriv φ t x v| ≤ D + D * ‖v‖ :=
  (abs_add_le _ _).trans (add_le_add (abs_timeDeriv_le hφ hD t x) (abs_spaceDeriv_le hφ hD t x v))

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

/-- Outside the support of `φ`, `∂_tφ + w·∇φ = 0`. -/
theorem timeDeriv_add_spaceDeriv_eq_zero {T : ℝ} {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ)
    {t : ℝ} {x : ℂ} (hp : (t, x) ∉ tsupport φ) (v : ℂ) :
    timeDeriv φ t x + spaceDeriv φ t x v = 0 := by
  have hd := differentiable_of_isTestFunction hφ
  rw [timeDeriv_eq_fderiv hd, spaceDeriv_eq_fderiv hd, fderiv_eq_zero_of_notMem_tsupport hp]
  simp

/-! ### `Lip₀` and renormalizations -/

theorem exists_abs_le_of_isLipO {β : ℝ → ℝ} (hβ : Equimeas.IsLipO β) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ s, |β s| ≤ L * |s| := by
  obtain ⟨⟨K, hK⟩, h0⟩ := hβ
  refine ⟨K, K.coe_nonneg, fun s => ?_⟩
  have h := hK.dist_le_mul s 0
  simpa [Real.dist_eq, h0] using h

theorem continuous_of_isLipO {β : ℝ → ℝ} (hβ : Equimeas.IsLipO β) : Continuous β := by
  obtain ⟨⟨K, hK⟩, _⟩ := hβ
  exact hK.continuous

theorem exists_abs_le_of_isRenormalization {Υ : ℝ → ℝ} (hΥ : IsRenormalization Υ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ s, |Υ s| ≤ L * |s| := by
  obtain ⟨C, hC⟩ := hΥ.deriv_bounded
  have hd : Differentiable ℝ Υ := hΥ.contDiff.differentiable one_ne_zero
  refine ⟨C, (abs_nonneg _).trans (hC 0), fun s => ?_⟩
  have h := convex_univ.norm_image_sub_le_of_norm_deriv_le (f := Υ) (fun x _ => hd x)
    (fun x _ => by rw [Real.norm_eq_abs]; exact hC x) (mem_univ (0 : ℝ)) (mem_univ s)
  simpa [hΥ.map_zero, Real.norm_eq_abs] using h

/-- `|Υ(a) - Υ(b)| ≤ C |a - b|` for a renormalization. -/
theorem exists_lipschitz_of_isRenormalization {Υ : ℝ → ℝ} (hΥ : IsRenormalization Υ) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ s, |deriv Υ s| ≤ C) ∧ ∀ a b, |Υ a - Υ b| ≤ C * |a - b| := by
  obtain ⟨C, hC⟩ := hΥ.deriv_bounded
  have hd : Differentiable ℝ Υ := hΥ.contDiff.differentiable one_ne_zero
  refine ⟨C, (abs_nonneg _).trans (hC 0), hC, fun a b => ?_⟩
  have h := convex_univ.norm_image_sub_le_of_norm_deriv_le (f := Υ) (fun x _ => hd x)
    (fun x _ => by rw [Real.norm_eq_abs]; exact hC x) (mem_univ b) (mem_univ a)
  simpa [Real.norm_eq_abs] using h

theorem continuous_of_isRenormalization {Υ : ℝ → ℝ} (hΥ : IsRenormalization Υ) : Continuous Υ :=
  hΥ.contDiff.continuous

/-! ### The slab as a product -/

theorem restrict_slabFrom_eq_prod (t₀ T : ℝ) :
    volume.restrict (slabFrom t₀ T) =
      (volume.restrict (Ioo t₀ T)).prod (volume : Measure ℂ) := by
  rw [slabFrom, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

theorem restrict_prod_eq_prod (I : Set ℝ) (Ω : Set ℂ) :
    volume.restrict (I ×ˢ Ω) = (volume.restrict I).prod (volume.restrict Ω) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]

theorem slabFrom_subset_slab {t₀ T : ℝ} (ht₀ : 0 ≤ t₀) : slabFrom t₀ T ⊆ slab T :=
  prod_mono (Ioo_subset_Ioo_left ht₀) le_rfl

theorem slabFrom_subset_prod {t₀ T : ℝ} (ht₀ : 0 ≤ t₀) :
    slabFrom t₀ T ⊆ Ioo (0 : ℝ) T ×ˢ (univ : Set ℂ) :=
  prod_mono (Ioo_subset_Ioo_left ht₀) le_rfl

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

/-! ### Integrability of the renormalized transport integrand -/

section Integrability

variable {T t₀ : ℝ} {w : ℝ → ℂ → ℂ} {u : ℝ → ℂ → ℝ} {u₀ : ℂ → ℝ}

theorem volume_Ioo_ne_top (a b : ℝ) : volume (Ioo a b) ≠ ∞ := by
  rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top

/-- `u ∈ L^∞(0,T; L¹)` is integrable on the slab `(t₀,T) × ℝ²`. -/
theorem integrableOn_slabFrom_of_memLinfLp_one (ht₀ : 0 ≤ t₀)
    (hu1 : Prelim.MemLinfLp (Ioo 0 T) univ 1 u) :
    IntegrableOn (Function.uncurry u) (slabFrom t₀ T) :=
  (integrableOn_of_memLinfLp_one (volume_Ioo_ne_top 0 T) hu1).mono_set (slabFrom_subset_prod ht₀)

theorem aestronglyMeasurable_w_slabFrom (ht₀ : 0 ≤ t₀) (hw : IsBddH1DivFreeField (Ioo 0 T) w) :
    AEStronglyMeasurable (fun p : ℝ × ℂ => w p.1 p.2) (volume.restrict (slabFrom t₀ T)) :=
  hw.aestronglyMeasurable.mono_measure (Measure.restrict_mono (slabFrom_subset_prod ht₀) le_rfl)

/-- The transport integrand of `v` with `|v| ≤ L |u|` is integrable on `(t₀,T) × ℝ²`. -/
theorem integrableOn_transportIntegrand_of_abs_le (ht₀ : 0 ≤ t₀)
    (hw : IsBddH1DivFreeField (Ioo 0 T) w) (hu1 : Prelim.MemLinfLp (Ioo 0 T) univ 1 u)
    (huw : Integrable (fun p : ℝ × ℂ => u p.1 p.2 • w p.1 p.2) (volume.restrict (slab T)))
    {v : ℝ → ℂ → ℝ} (hv : AEStronglyMeasurable (Function.uncurry v)
      (volume.restrict (slabFrom t₀ T)))
    {L : ℝ} (hL : 0 ≤ L) (hvu : ∀ t x, |v t x| ≤ L * |u t x|) {φ : ℝ × ℂ → ℝ}
    (hφ : IsTestFunction T φ) :
    IntegrableOn (transportIntegrand v w φ) (slabFrom t₀ T) := by
  obtain ⟨D, hD0, hD⟩ := exists_bound_fderiv_of_isTestFunction hφ
  have hu : IntegrableOn (Function.uncurry u) (slabFrom t₀ T) :=
    integrableOn_slabFrom_of_memLinfLp_one ht₀ hu1
  have huw' : IntegrableOn (fun p : ℝ × ℂ => u p.1 p.2 • w p.1 p.2) (slabFrom t₀ T) :=
    IntegrableOn.mono_set (t := slab T) huw (slabFrom_subset_slab ht₀)
  have hmaj : Integrable (fun p : ℝ × ℂ => L * D * (‖Function.uncurry u p‖ +
      ‖u p.1 p.2 • w p.1 p.2‖)) (volume.restrict (slabFrom t₀ T)) :=
    (hu.norm.add huw'.norm).const_mul _
  refine hmaj.mono' (aestronglyMeasurable_transportIntegrand hφ hv
    (aestronglyMeasurable_w_slabFrom ht₀ hw)) (Filter.Eventually.of_forall fun p => ?_)
  have h1 := abs_timeDeriv_add_spaceDeriv_le hφ hD p.1 p.2 (w p.1 p.2)
  have h2 := hvu p.1 p.2
  simp only [transportIntegrand, Real.norm_eq_abs, abs_mul, norm_smul]
  calc |v p.1 p.2| * |timeDeriv φ p.1 p.2 + spaceDeriv φ p.1 p.2 (w p.1 p.2)|
      ≤ (L * |u p.1 p.2|) * (D + D * ‖w p.1 p.2‖) :=
        mul_le_mul h2 h1 (abs_nonneg _) (mul_nonneg hL (abs_nonneg _))
    _ = L * D * (|u p.1 p.2| + |u p.1 p.2| * ‖w p.1 p.2‖) := by ring

/-- The datum term `v₀ φ(t₀)` with `|v₀| ≤ L |u₀|` is integrable. -/
theorem integrable_datum_of_abs_le (hu₀1 : MemLp u₀ 1 volume) {v₀ : ℂ → ℝ}
    (hv₀ : AEStronglyMeasurable v₀ volume) {L : ℝ} (hL : 0 ≤ L) (hvu : ∀ x, |v₀ x| ≤ L * |u₀ x|)
    {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) :
    Integrable (fun x : ℂ => v₀ x * φ (t₀, x)) := by
  obtain ⟨A, hA0, hA⟩ := exists_bound_of_isTestFunction hφ
  have hcont : Continuous fun x : ℂ => φ (t₀, x) :=
    hφ.contDiff.continuous.comp (continuous_const.prodMk continuous_id)
  refine ((memLp_one_iff_integrable.1 hu₀1).norm.const_mul (L * A)).mono'
    (hv₀.mul hcont.aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
  calc |v₀ x| * |φ (t₀, x)| ≤ (L * |u₀ x|) * A :=
        mul_le_mul (hvu x) (hA _) (abs_nonneg _) (mul_nonneg hL (abs_nonneg _))
    _ = L * A * |u₀ x| := by ring

/-- The transport integrand of `β(u)`, `β` continuous with `|β(s)| ≤ L|s|`, is integrable on
`(t₀,T) × ℝ²`. -/
theorem integrableOn_transportIntegrand_comp (ht₀ : 0 ≤ t₀)
    (hw : IsBddH1DivFreeField (Ioo 0 T) w) (hu1 : Prelim.MemLinfLp (Ioo 0 T) univ 1 u)
    (huw : Integrable (fun p : ℝ × ℂ => u p.1 p.2 • w p.1 p.2) (volume.restrict (slab T)))
    {β : ℝ → ℝ} (hβc : Continuous β) {L : ℝ} (hL : 0 ≤ L) (hβ : ∀ s, |β s| ≤ L * |s|)
    {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) :
    IntegrableOn (transportIntegrand (fun t x => β (u t x)) w φ) (slabFrom t₀ T) := by
  have hum : AEStronglyMeasurable (Function.uncurry u) (volume.restrict (slabFrom t₀ T)) :=
    hu1.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono (slabFrom_subset_prod ht₀) le_rfl)
  exact integrableOn_transportIntegrand_of_abs_le (v := fun t x => β (u t x)) ht₀ hw hu1 huw
    (hβc.comp_aestronglyMeasurable hum) hL (fun t x => hβ (u t x)) hφ

/-- The datum term `β(u₀) φ(t₀)` is integrable. -/
theorem integrable_datum_comp (hu₀1 : MemLp u₀ 1 volume) {β : ℝ → ℝ} (hβc : Continuous β)
    {L : ℝ} (hL : 0 ≤ L) (hβ : ∀ s, |β s| ≤ L * |s|) {φ : ℝ × ℂ → ℝ}
    (hφ : IsTestFunction T φ) :
    Integrable (fun x : ℂ => β (u₀ x) * φ (t₀, x)) :=
  integrable_datum_of_abs_le hu₀1 (hβc.comp_aestronglyMeasurable hu₀1.aestronglyMeasurable) hL
    (fun x => hβ (u₀ x)) hφ

/-- The standing assumptions of `(te)` under the hypotheses of `lem:transport`. -/
theorem isTEData_of_transport (ht₀ : t₀ ∈ Ico 0 T) (hw : IsBddH1DivFreeField (Ioo 0 T) w)
    (hu1 : Prelim.MemLinfLp (Ioo 0 T) univ 1 u)
    (huw : Integrable (fun p : ℝ × ℂ => u p.1 p.2 • w p.1 p.2) (volume.restrict (slab T)))
    (hu₀1 : MemLp u₀ 1 volume) : IsTEData t₀ T u w u₀ where
  integrableOn_u _ hT' _ _ :=
    (integrableOn_slabFrom_of_memLinfLp_one ht₀.1 hu1).mono_set
      (prod_mono (Ioo_subset_Ioo_right hT'.le) (subset_univ _))
  integrableOn_w _ hT' _ hR :=
    (integrableOn_of_memLinfLp_one (volume_Ioo_ne_top 0 T)
      (memLinfLp_one_of_two measure_ball_lt_top.ne (memLinfLp_two_of_isBddH1 hw hR))).mono_set
      (prod_mono (Ioo_subset_Ioo ht₀.1 hT'.le) le_rfl)
  integrableOn_uw _ hT' _ _ :=
    IntegrableOn.mono_set (t := slab T) huw
      (prod_mono (Ioo_subset_Ioo ht₀.1 hT'.le) (subset_univ _))
  locallyIntegrable_datum := (memLp_one_iff_integrable.1 hu₀1).locallyIntegrable

end Integrability

end NonUniqueEuler.Weak.TransportH
