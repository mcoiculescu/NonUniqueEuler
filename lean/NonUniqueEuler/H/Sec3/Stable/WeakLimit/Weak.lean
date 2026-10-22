import NonUniqueEuler.I.Infra.WeakL2.Compact
import NonUniqueEuler.I.Infra.WeakL2.LpNorm

/-!
# Helpers for `prop:stable`, step 1a: weak limits in `L²(μ)` of functions

Helper file of `P/Sec3/Stable/WeakLimit.lean` (`03_compactness.tex:743-755`, restructuring R5:
weak limits in `L²((0,T) × ℝ²)` instead of weak-* limits in `L^∞`).

Weak convergence of functions `fₙ ⇀ F` in `L²(μ)` is written in the function form
`∀ Φ ∈ L²(μ), ∫ fₙ Φ → ∫ F Φ`.
* `exists_subseq_weak`: a bounded sequence of `L²(μ)` has a weakly convergent subsequence, with
  a strongly measurable limit (`WeakL2.exists_subseq_weakTendsto`);
* `eLpNorm_le_of_weak`: `‖fₙ‖_q ≤ A` passes to the weak limit (`q ∈ [1, ∞]`,
  `WeakL2.eLpNorm_le_of_weakTendsto`);
* `setLIntegral_le_of_weak`: `∫_S |fₙ| ≤ A` passes to the weak limit;
* `ae_abs_le_of_weak`: `|fₙ| ≤ B` passes to the weak limit;
* `exists_subseq_weak_bdd`: extraction with a measurable limit bounded by `B` everywhere
  (truncation of a representative).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.Compact.WeakLimitAux

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Bounded sequences of `L²(μ)` have weakly convergent subsequences. -/
theorem exists_subseq_weak {f : ℕ → α → ℝ} (hf : ∀ n, MemLp (f n) 2 μ) {C : ℝ}
    (hC : ∀ n, eLpNorm (f n) 2 μ ≤ ENNReal.ofReal C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ F : α → ℝ, StronglyMeasurable F ∧ MemLp F 2 μ ∧
      ∀ Φ : α → ℝ, MemLp Φ 2 μ →
        Tendsto (fun n => ∫ x, f (φ n) x * Φ x ∂μ) atTop (𝓝 (∫ x, F x * Φ x ∂μ)) := by
  set u : ℕ → Lp ℝ 2 μ := fun n => (hf n).toLp (f n) with hu
  have hub : ∀ n, ‖u n‖ ≤ max C 0 := by
    intro n
    rw [hu, Lp.norm_toLp]
    exact ENNReal.toReal_le_of_le_ofReal (le_max_right _ _)
      ((hC n).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  obtain ⟨φ, hφ, x, -, hx⟩ := WeakL2.exists_subseq_weakTendsto hub
  refine ⟨φ, hφ, x, Lp.stronglyMeasurable x, Lp.memLp x, fun Φ hΦ => ?_⟩
  have h := hx.integral_mul_tendsto hΦ
  refine h.congr fun n => integral_congr_ae ?_
  filter_upwards [(hf (φ n)).coeFn_toLp] with a ha
  simp only [Function.comp_apply, hu, ha]

/-- Weak convergence is preserved by multiplication with an indicator. -/
theorem weak_indicator {f : ℕ → α → ℝ} {F : α → ℝ}
    (hw : ∀ Φ : α → ℝ, MemLp Φ 2 μ →
      Tendsto (fun n => ∫ x, f n x * Φ x ∂μ) atTop (𝓝 (∫ x, F x * Φ x ∂μ)))
    {S : Set α} (hS : MeasurableSet S) :
    ∀ Φ : α → ℝ, MemLp Φ 2 μ →
      Tendsto (fun n => ∫ x, S.indicator (f n) x * Φ x ∂μ) atTop
        (𝓝 (∫ x, S.indicator F x * Φ x ∂μ)) := by
  intro Φ hΦ
  have key : ∀ g : α → ℝ, (fun x => S.indicator g x * Φ x) = fun x => g x * S.indicator Φ x := by
    intro g
    funext x
    by_cases hx : x ∈ S <;> simp [hx]
  simp_rw [key]
  exact hw _ (hΦ.indicator hS)

variable [SigmaFinite μ]

/-- A uniform `L^q` bound (`q ∈ [1, ∞]`) passes to weak `L²` limits. -/
theorem eLpNorm_le_of_weak {f : ℕ → α → ℝ} {F : α → ℝ} (hf : ∀ n, MemLp (f n) 2 μ)
    (hF : MemLp F 2 μ)
    (hw : ∀ Φ : α → ℝ, MemLp Φ 2 μ →
      Tendsto (fun n => ∫ x, f n x * Φ x ∂μ) atTop (𝓝 (∫ x, F x * Φ x ∂μ)))
    {q : ℝ≥0∞} (hq : 1 ≤ q) {A : ℝ≥0∞} (hA : ∀ n, eLpNorm (f n) q μ ≤ A) :
    eLpNorm F q μ ≤ A := by
  have h := (WeakL2.weakTendsto_toLp_iff (l := atTop) hf hF).2 hw
  have h2 := WeakL2.eLpNorm_le_of_weakTendsto hq h (M := A) (Eventually.of_forall fun n => by
    rw [eLpNorm_congr_ae (hf n).coeFn_toLp]
    exact hA n)
  rwa [eLpNorm_congr_ae hF.coeFn_toLp] at h2

/-- A uniform bound of `∫_S |fₙ|` passes to weak `L²` limits. -/
theorem setLIntegral_le_of_weak {f : ℕ → α → ℝ} {F : α → ℝ} (hf : ∀ n, MemLp (f n) 2 μ)
    (hF : MemLp F 2 μ)
    (hw : ∀ Φ : α → ℝ, MemLp Φ 2 μ →
      Tendsto (fun n => ∫ x, f n x * Φ x ∂μ) atTop (𝓝 (∫ x, F x * Φ x ∂μ)))
    {S : Set α} (hS : MeasurableSet S) {A : ℝ≥0∞} (hA : ∀ n, ∫⁻ x in S, ‖f n x‖ₑ ∂μ ≤ A) :
    ∫⁻ x in S, ‖F x‖ₑ ∂μ ≤ A := by
  have h := eLpNorm_le_of_weak (f := fun n => S.indicator (f n)) (F := S.indicator F)
    (fun n => (hf n).indicator hS) (hF.indicator hS) (weak_indicator hw hS) le_rfl (A := A)
    (fun n => by
      rw [eLpNorm_indicator_eq_eLpNorm_restrict hS, eLpNorm_one_eq_lintegral_enorm]
      exact hA n)
  rwa [eLpNorm_indicator_eq_eLpNorm_restrict hS, eLpNorm_one_eq_lintegral_enorm] at h

/-- A uniform bound `|fₙ| ≤ B` passes to weak `L²` limits. -/
theorem ae_abs_le_of_weak {f : ℕ → α → ℝ} {F : α → ℝ} (hf : ∀ n, MemLp (f n) 2 μ)
    (hF : MemLp F 2 μ)
    (hw : ∀ Φ : α → ℝ, MemLp Φ 2 μ →
      Tendsto (fun n => ∫ x, f n x * Φ x ∂μ) atTop (𝓝 (∫ x, F x * Φ x ∂μ)))
    {B : ℝ} (hB : 0 ≤ B) (hfB : ∀ n, ∀ᵐ x ∂μ, |f n x| ≤ B) : ∀ᵐ x ∂μ, |F x| ≤ B := by
  have h := eLpNorm_le_of_weak hf hF hw le_top (A := ENNReal.ofReal B) (fun n => by
    rw [eLpNorm_exponent_top]
    exact eLpNormEssSup_le_of_ae_bound ((hfB n).mono fun x hx => by rwa [Real.norm_eq_abs]))
  rw [eLpNorm_exponent_top] at h
  filter_upwards [ae_le_eLpNormEssSup (f := F) (μ := μ)] with x hx
  have h3 := hx.trans h
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_le_ofReal_iff hB] at h3
  exact h3

/-- **Extraction with a bounded measurable limit.** A sequence bounded in `L²(μ)` and by `B`
has a subsequence converging weakly in `L²(μ)` to a measurable function bounded by `B`
everywhere. -/
theorem exists_subseq_weak_bdd {f : ℕ → α → ℝ} (hf : ∀ n, MemLp (f n) 2 μ) {C : ℝ}
    (hC : ∀ n, eLpNorm (f n) 2 μ ≤ ENNReal.ofReal C) {B : ℝ} (hB : 0 ≤ B)
    (hfB : ∀ n, ∀ᵐ x ∂μ, |f n x| ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : α → ℝ, Measurable G ∧ (∀ x, |G x| ≤ B) ∧
      MemLp G 2 μ ∧ ∀ Φ : α → ℝ, MemLp Φ 2 μ →
        Tendsto (fun n => ∫ x, f (φ n) x * Φ x ∂μ) atTop (𝓝 (∫ x, G x * Φ x ∂μ)) := by
  obtain ⟨φ, hφ, F, hFm, hF2, hw⟩ := exists_subseq_weak hf hC
  have hFB : ∀ᵐ x ∂μ, |F x| ≤ B :=
    ae_abs_le_of_weak (fun n => hf (φ n)) hF2 hw hB (fun n => hfB (φ n))
  set G : α → ℝ := fun x => max (-B) (min B (F x)) with hG
  have hGF : G =ᵐ[μ] F := by
    filter_upwards [hFB] with x hx
    rw [abs_le] at hx
    simp only [hG]
    rw [min_eq_right hx.2, max_eq_right hx.1]
  refine ⟨φ, hφ, G, ?_, fun x => ?_, hF2.ae_eq hGF.symm, fun Φ hΦ => ?_⟩
  · exact (measurable_const.max (measurable_const.min hFm.measurable))
  · rw [abs_le]
    simp only [hG]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  · have h : ∫ x, G x * Φ x ∂μ = ∫ x, F x * Φ x ∂μ :=
      integral_congr_ae (hGF.mono fun x hx => by simp only [hx])
    rw [h]
    exact hw Φ hΦ

end NonUniqueEuler.Compact.WeakLimitAux
