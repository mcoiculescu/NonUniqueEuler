import NonUniqueEuler.Defs.Sec3.Compact
import NonUniqueEuler.Defs.Sec3.Transport
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Helpers for `prop:stable`, step 1a: generic lemmas

Helper file of `P/Sec3/Stable/WeakLimit.lean` (`03_compactness.tex:739-785`).

* Test functions `φ ∈ 𝒟_T`: derivatives, bounds, supports, `∂_tφ ∈ L²` (the first lemmas are
  adapted from `H/Sec3/Transport/Basic.lean`, namespace `Weak.TransportH`).
* `Lip₀`: `|β(s)| ≤ L|s|`, `|β(a) - β(b)| ≤ L|a - b|`, `β² ∈ Lip₀` for bounded `β ∈ Lip₀`.
* Tonelli on products `I × Ω` (`lintegral_prodSet_le`, no measurability needed).
* `eLpNorm_two_le_of_bound`: `‖g‖₂² ≤ B ‖g‖₁` for `|g| ≤ B`.
* `memLp_two_prodSet_of_ae_slice`: `L^∞(I; L²(Ω)) ⊂ L²(I × Ω)` for `|I| < ∞`.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace NonUniqueEuler.Compact.WeakLimitAux

open Weak

/-! ### Test functions -/

section TestFunction

variable {T : ℝ} {φ : ℝ × ℂ → ℝ}

theorem differentiable_of_isTestFunction (hφ : IsTestFunction T φ) : Differentiable ℝ φ :=
  hφ.contDiff.differentiable (by simp)

theorem continuous_fderiv_of_isTestFunction (hφ : IsTestFunction T φ) :
    Continuous (fderiv ℝ φ) :=
  hφ.contDiff.continuous_fderiv (by simp)

theorem timeDeriv_eq_fderiv (hφ : IsTestFunction T φ) (t : ℝ) (x : ℂ) :
    timeDeriv φ t x = fderiv ℝ φ (t, x) ((1 : ℝ), (0 : ℂ)) := by
  have h1 : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : ℂ)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  exact (((differentiable_of_isTestFunction hφ) (t, x)).hasFDerivAt.comp_hasDerivAt t h1).deriv

theorem fderiv_slice_eq (hφ : IsTestFunction T φ) (t : ℝ) (x : ℂ) :
    fderiv ℝ (fun y => φ (t, y)) x = (fderiv ℝ φ (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ ℂ) :=
  (((differentiable_of_isTestFunction hφ) (t, x)).hasFDerivAt.comp x
    (hasFDerivAt_prodMk_right t x)).fderiv

theorem spaceDeriv_eq_fderiv (hφ : IsTestFunction T φ) (t : ℝ) (x w : ℂ) :
    spaceDeriv φ t x w = fderiv ℝ φ (t, x) ((0 : ℝ), w) := by
  simp only [spaceDeriv, fderiv_slice_eq hφ t x, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply]

/-- `w ↦ w · ∇φ(t, x)` is additive. -/
theorem spaceDeriv_sub (φ : ℝ × ℂ → ℝ) (t : ℝ) (x a b : ℂ) :
    spaceDeriv φ t x (a - b) = spaceDeriv φ t x a - spaceDeriv φ t x b := by
  simp only [spaceDeriv, map_sub]

theorem exists_bound_fderiv_of_isTestFunction (hφ : IsTestFunction T φ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ p, ‖fderiv ℝ φ p‖ ≤ D := by
  obtain ⟨D, hD⟩ :=
    (continuous_fderiv_of_isTestFunction hφ).bounded_above_of_compact_support
      (hφ.hasCompactSupport.fderiv (𝕜 := ℝ))
  exact ⟨D, (norm_nonneg _).trans (hD 0), hD⟩

theorem exists_bound_of_isTestFunction (hφ : IsTestFunction T φ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ p, |φ p| ≤ A := by
  obtain ⟨A, hA⟩ := hφ.contDiff.continuous.bounded_above_of_compact_support hφ.hasCompactSupport
  exact ⟨A, (norm_nonneg _).trans (hA 0), fun p => by rw [← Real.norm_eq_abs]; exact hA p⟩

theorem abs_spaceDeriv_le (hφ : IsTestFunction T φ) {D : ℝ} (hD : ∀ p, ‖fderiv ℝ φ p‖ ≤ D)
    (t : ℝ) (x w : ℂ) : |spaceDeriv φ t x w| ≤ D * ‖w‖ := by
  rw [spaceDeriv_eq_fderiv hφ, ← Real.norm_eq_abs]
  refine ((fderiv ℝ φ (t, x)).le_opNorm _).trans ?_
  have h1 : ‖((0 : ℝ), w)‖ = ‖w‖ := by simp [Prod.norm_def]
  rw [h1]
  exact mul_le_mul_of_nonneg_right (hD _) (norm_nonneg _)

theorem continuous_timeDeriv (hφ : IsTestFunction T φ) :
    Continuous (fun p : ℝ × ℂ => timeDeriv φ p.1 p.2) := by
  have : (fun p : ℝ × ℂ => timeDeriv φ p.1 p.2) =
      fun p => fderiv ℝ φ p ((1 : ℝ), (0 : ℂ)) := by
    funext p
    rw [timeDeriv_eq_fderiv hφ]
  rw [this]
  exact (continuous_fderiv_of_isTestFunction hφ).clm_apply continuous_const

theorem continuous_fderiv_slice (hφ : IsTestFunction T φ) :
    Continuous (fun p : ℝ × ℂ => fderiv ℝ (fun y => φ (p.1, y)) p.2) := by
  have : (fun p : ℝ × ℂ => fderiv ℝ (fun y => φ (p.1, y)) p.2) =
      fun p => (fderiv ℝ φ p).comp (ContinuousLinearMap.inr ℝ ℝ ℂ) := by
    funext p
    rw [fderiv_slice_eq hφ]
  rw [this]
  exact (continuous_fderiv_of_isTestFunction hφ).clm_comp continuous_const

/-- `p ↦ w(p) · ∇φ(p)` is a.e.-strongly measurable when `w` is. -/
theorem aestronglyMeasurable_spaceDeriv (hφ : IsTestFunction T φ) {μ : Measure (ℝ × ℂ)}
    {w : ℝ × ℂ → ℂ} (hw : AEStronglyMeasurable w μ) :
    AEStronglyMeasurable (fun p : ℝ × ℂ => spaceDeriv φ p.1 p.2 (w p)) μ :=
  (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂
    (continuous_fderiv_slice hφ).aestronglyMeasurable hw

/-- The support of a test function lies in `(-∞, b] × B_R` with `b < T`. -/
theorem exists_ball_of_isTestFunction (hφ : IsTestFunction T φ) :
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

theorem fderiv_eq_zero_of_notMem_tsupport {p : ℝ × ℂ} (hp : p ∉ tsupport φ) :
    fderiv ℝ φ p = 0 := by
  have : p ∉ tsupport (fderiv ℝ φ) := fun h => hp (tsupport_fderiv_subset ℝ h)
  exact image_eq_zero_of_notMem_tsupport this

theorem spaceDeriv_eq_zero_of_notMem (hφ : IsTestFunction T φ) {t : ℝ} {x : ℂ}
    (hp : (t, x) ∉ tsupport φ) (w : ℂ) : spaceDeriv φ t x w = 0 := by
  rw [spaceDeriv_eq_fderiv hφ, fderiv_eq_zero_of_notMem_tsupport hp]
  rfl

/-- `∂_tφ` has compact support. -/
theorem hasCompactSupport_timeDeriv (hφ : IsTestFunction T φ) :
    HasCompactSupport (fun p : ℝ × ℂ => timeDeriv φ p.1 p.2) := by
  have : (fun p : ℝ × ℂ => timeDeriv φ p.1 p.2) =
      fun p => fderiv ℝ φ p ((1 : ℝ), (0 : ℂ)) := by
    funext p
    rw [timeDeriv_eq_fderiv hφ]
  rw [this]
  exact hφ.hasCompactSupport.fderiv_apply (𝕜 := ℝ) _

/-- `∂_tφ ∈ L²(μ)` for every restriction `μ` of the Lebesgue measure. -/
theorem memLp_timeDeriv (hφ : IsTestFunction T φ) (s : Set (ℝ × ℂ)) (p : ℝ≥0∞) :
    MemLp (fun q : ℝ × ℂ => timeDeriv φ q.1 q.2) p (volume.restrict s) :=
  ((continuous_timeDeriv hφ).memLp_of_hasCompactSupport (hasCompactSupport_timeDeriv hφ)).restrict s

end TestFunction

/-! ### `Lip₀` -/

section Lip

theorem isLipO_exists_abs_le {β : ℝ → ℝ} (hβ : Equimeas.IsLipO β) :
    ∃ L : ℝ, 0 ≤ L ∧ (∀ s, |β s| ≤ L * |s|) ∧ ∀ a b, |β a - β b| ≤ L * |a - b| := by
  obtain ⟨⟨K, hK⟩, h0⟩ := hβ
  refine ⟨K, K.coe_nonneg, fun s => ?_, fun a b => ?_⟩
  · have h := hK.dist_le_mul s 0
    simpa [Real.dist_eq, h0] using h
  · have h := hK.dist_le_mul a b
    simpa [Real.dist_eq] using h

theorem isLipO_continuous {β : ℝ → ℝ} (hβ : Equimeas.IsLipO β) : Continuous β := by
  obtain ⟨⟨K, hK⟩, _⟩ := hβ
  exact hK.continuous

/-- `β² ∈ Lip₀` for bounded `β ∈ Lip₀` (`03_compactness.tex:741`). -/
theorem isLipO_sq {β : ℝ → ℝ} (hβ : Equimeas.IsLipO β) {B : ℝ} (hB : ∀ s, |β s| ≤ B) :
    Equimeas.IsLipO (fun s => β s ^ 2) := by
  obtain ⟨L, hL0, -, hL⟩ := isLipO_exists_abs_le hβ
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  refine ⟨⟨Real.toNNReal (2 * B * L), LipschitzWith.of_dist_le_mul fun a b => ?_⟩, ?_⟩
  · rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
    have h1 : β a ^ 2 - β b ^ 2 = (β a + β b) * (β a - β b) := by ring
    rw [h1, abs_mul]
    have h2 : |β a + β b| ≤ 2 * B := (abs_add_le _ _).trans (by linarith [hB a, hB b])
    calc |β a + β b| * |β a - β b| ≤ (2 * B) * (L * |a - b|) :=
          mul_le_mul h2 (hL a b) (abs_nonneg _) (by positivity)
      _ = 2 * B * L * |a - b| := by ring
  · simp [hβ.2]

end Lip

/-! ### Tonelli on products `I × Ω` -/

section Tonelli

theorem restrict_prodSet_eq_prod (I : Set ℝ) (Ω : Set ℂ) :
    volume.restrict (I ×ˢ Ω) = (volume.restrict I).prod (volume.restrict Ω) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]

theorem restrict_slab_eq_prod (T : ℝ) :
    volume.restrict (slab T) = (volume.restrict (Ioo (0 : ℝ) T)).prod (volume : Measure ℂ) := by
  rw [slab, restrict_prodSet_eq_prod, Measure.restrict_univ]

/-- Tonelli inequality on `I × Ω` (no measurability needed). -/
theorem lintegral_prodSet_le (I : Set ℝ) (Ω : Set ℂ) (F : ℝ × ℂ → ℝ≥0∞) :
    ∫⁻ p in I ×ˢ Ω, F p ≤ ∫⁻ t in I, ∫⁻ x in Ω, F (t, x) := by
  rw [restrict_prodSet_eq_prod]
  exact lintegral_prod_le F

/-- Tonelli on `I × Ω` for measurable integrands. -/
theorem lintegral_prodSet_eq (I : Set ℝ) (Ω : Set ℂ) {F : ℝ × ℂ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p in I ×ˢ Ω, F p = ∫⁻ t in I, ∫⁻ x in Ω, F (t, x) := by
  rw [restrict_prodSet_eq_prod]
  exact lintegral_prod F hF.aemeasurable

/-- An a.e. slice bound gives a bound on `I × Ω`. -/
theorem lintegral_prodSet_le_of_ae_slice (I : Set ℝ) (Ω : Set ℂ) (F : ℝ × ℂ → ℝ≥0∞)
    {C : ℝ≥0∞} (hC : ∀ᵐ t ∂(volume.restrict I), ∫⁻ x in Ω, F (t, x) ≤ C) :
    ∫⁻ p in I ×ˢ Ω, F p ≤ C * volume I := by
  refine (lintegral_prodSet_le I Ω F).trans ?_
  refine (lintegral_mono_ae hC).trans ?_
  rw [setLIntegral_const]

/-- `‖g‖_{L²(μ)}² ≤ B ‖g‖_{L¹(μ)}` when `|g| ≤ B`. -/
theorem eLpNorm_two_le_of_bound {α : Type*} [MeasurableSpace α] {μ : Measure α} {g : α → ℝ}
    {B : ℝ} (hB : ∀ᵐ x ∂μ, |g x| ≤ B) :
    eLpNorm g 2 μ ≤ (ENNReal.ofReal B * ∫⁻ x, ‖g x‖ₑ ∂μ) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by simp
  rw [h2]
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae (hB.mono fun x hx => ?_)
  rw [ENNReal.rpow_two, sq]
  have : ‖g x‖ₑ ≤ ENNReal.ofReal B := by
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal hx
  gcongr

/-- `L^∞(I; L²(Ω)) ⊂ L²(I × Ω)` for `|I| < ∞`. -/
theorem memLp_two_prodSet_of_ae_slice {E : Type*} [NormedAddCommGroup E] {I : Set ℝ}
    (hI : volume I ≠ ∞) {Ω : Set ℂ} {f : ℝ × ℂ → E}
    (hf : AEStronglyMeasurable f (volume.restrict (I ×ˢ Ω))) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hb : ∀ᵐ t ∂(volume.restrict I), eLpNorm (fun x => f (t, x)) 2 (volume.restrict Ω) ≤ C) :
    MemLp f 2 (volume.restrict (I ×ˢ Ω)) := by
  refine ⟨hf, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by simp
  rw [h2]
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ne_of_lt ?_)
  refine (lintegral_prodSet_le_of_ae_slice I Ω (fun p => ‖f p‖ₑ ^ (2 : ℝ)) (C := C ^ (2 : ℝ))
    (hb.mono fun t ht => ?_)).trans_lt ?_
  · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), h2] at ht
    have h3 : ∫⁻ x in Ω, ‖f (t, x)‖ₑ ^ (2 : ℝ) =
        ((∫⁻ x in Ω, ‖f (t, x)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
      rw [← ENNReal.rpow_mul]
      norm_num
    rw [h3]
    exact ENNReal.rpow_le_rpow ht (by norm_num)
  · exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hC) hI.lt_top

end Tonelli

/-! ### Real sequences from `ℝ≥0∞` bounds -/

/-- `‖aₙ - a‖ₑ ≤ eₙ → 0` gives `aₙ → a`. -/
theorem tendsto_of_enorm_sub_le {a : ℕ → ℝ} {a₀ : ℝ} {e : ℕ → ℝ≥0∞}
    (hle : ∀ n, ‖a n - a₀‖ₑ ≤ e n) (he : Tendsto e atTop (𝓝 0)) :
    Tendsto a atTop (𝓝 a₀) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have he' : Tendsto (fun n => (e n).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp he
    simpa [Function.comp_def] using this
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ he'
  filter_upwards [he.eventually (gt_mem_nhds (zero_lt_one' ℝ≥0∞))] with n hn
  rw [← toReal_enorm]
  exact ENNReal.toReal_mono (ne_top_of_lt hn) (hle n)

end NonUniqueEuler.Compact.WeakLimitAux
