import NonUniqueEuler.Defs.Infra.Equimeasurable
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov

/-!
# Proof: equimeasurable functions have the same distribution off `0` (I-EQM)

Proof of `NonUniqueEuler/I/Infra/Equimeasurable/Distribution.lean` (the "layer-cake" step of
`thm:criterion`(ii), `03_compactness.tex:996-1003`, for every `Φ` at once).

Argument. For `g ∈ L¹` let `M_g = volume.map g` (a measure on `ℝ`; `g` is only a.e.-measurable,
and `Measure.map_apply_of_aemeasurable` gives `M_g A = |g⁻¹(A)|` for Borel `A`). For `c > 0` the
restriction `M_g|_(c,∞)` is finite (Chebyshev) and is determined by its values on the π-system
`{(a, ∞)}` (`ext_of_generate_finite`, `borel_eq_generateFrom_Ioi`), where
`M_g|_(c,∞) (a,∞) = |{g > max a c}|`. Hence `M_g|_(c,∞) = M_h|_(c,∞)`, and likewise
`M_g|_(-∞,-c) = M_h|_(-∞,-c)`. Since `ℝ \ {0} = ⋃ₙ ((1/(n+1), ∞) ∪ (-∞, -1/(n+1)))`,
`Measure.restrict_iUnion_congr` gives `M_g|_{0}ᶜ = M_h|_{0}ᶜ` (`restrict_compl_zero_eq`).
Everything else follows: `lintegral_map'` and `Φ = 1_{0}ᶜ Φ` for the lower integrals, the
positive/negative parts for the Bochner integral.

The auxiliary lemmas live in the namespace `NonUniqueEuler.Equimeasurable.DistributionAux`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace NonUniqueEuler.Equimeasurable

namespace DistributionAux

variable {g h : ℂ → ℝ}

/-- Chebyshev: `|{g > s}| < ∞` for `g ∈ L¹` and `s > 0`. -/
theorem volume_gt_lt_top (hg : MemLp g 1) {s : ℝ} (hs : 0 < s) :
    volume {x | s < g x} < ∞ := by
  have h1 := hg.meas_ge_lt_top (p := 1) one_ne_zero ENNReal.one_ne_top
    (ε := s.toNNReal) (Real.toNNReal_pos.2 hs).ne'
  refine lt_of_le_of_lt (measure_mono ?_) h1
  intro x hx
  simp only [mem_ofPred_eq] at hx ⊢
  rw [Real.toNNReal_le_iff_le_coe, coe_nnnorm, Real.norm_eq_abs]
  exact hx.le.trans (le_abs_self _)

/-- Chebyshev: `|{g < -s}| < ∞` for `g ∈ L¹` and `s > 0`. -/
theorem volume_lt_neg_lt_top (hg : MemLp g 1) {s : ℝ} (hs : 0 < s) :
    volume {x | g x < -s} < ∞ := by
  have h1 := hg.meas_ge_lt_top (p := 1) one_ne_zero ENNReal.one_ne_top
    (ε := s.toNNReal) (Real.toNNReal_pos.2 hs).ne'
  refine lt_of_le_of_lt (measure_mono ?_) h1
  intro x hx
  simp only [mem_ofPred_eq] at hx ⊢
  rw [Real.toNNReal_le_iff_le_coe, coe_nnnorm, Real.norm_eq_abs]
  have := neg_abs_le (g x)
  linarith

/-- The push-forwards agree on `(c, ∞)`, `c > 0`. -/
theorem restrict_Ioi_eq (hg : MemLp g 1) (hh : MemLp h 1)
    (H : ∀ s : ℝ, 0 < s → volume {x | s < g x} = volume {x | s < h x}) {c : ℝ} (hc : 0 < c) :
    (volume.map g).restrict (Ioi c) = (volume.map h).restrict (Ioi c) := by
  have hgm : AEMeasurable g := hg.aestronglyMeasurable.aemeasurable
  have hhm : AEMeasurable h := hh.aestronglyMeasurable.aemeasurable
  have : IsFiniteMeasure ((volume.map g).restrict (Ioi c)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, Measure.map_apply_of_aemeasurable hgm measurableSet_Ioi]
    exact volume_gt_lt_top hg hc
  refine ext_of_generate_finite (range Ioi)
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ioi ℝ)) isPiSystem_Ioi ?_ ?_
  · rintro _ ⟨a, rfl⟩
    rw [Measure.restrict_apply measurableSet_Ioi, Measure.restrict_apply measurableSet_Ioi,
      Ioi_inter_Ioi, Measure.map_apply_of_aemeasurable hgm measurableSet_Ioi,
      Measure.map_apply_of_aemeasurable hhm measurableSet_Ioi]
    exact H _ (lt_of_lt_of_le hc le_sup_right)
  · rw [Measure.restrict_apply_univ, Measure.restrict_apply_univ,
      Measure.map_apply_of_aemeasurable hgm measurableSet_Ioi,
      Measure.map_apply_of_aemeasurable hhm measurableSet_Ioi]
    exact H c hc

/-- The push-forwards agree on `(-∞, -c)`, `c > 0`. -/
theorem restrict_Iio_eq (hg : MemLp g 1) (hh : MemLp h 1)
    (H : ∀ s : ℝ, 0 < s → volume {x | g x < -s} = volume {x | h x < -s}) {c : ℝ} (hc : 0 < c) :
    (volume.map g).restrict (Iio (-c)) = (volume.map h).restrict (Iio (-c)) := by
  have hgm : AEMeasurable g := hg.aestronglyMeasurable.aemeasurable
  have hhm : AEMeasurable h := hh.aestronglyMeasurable.aemeasurable
  have : IsFiniteMeasure ((volume.map g).restrict (Iio (-c))) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, Measure.map_apply_of_aemeasurable hgm measurableSet_Iio]
    exact volume_lt_neg_lt_top hg hc
  refine ext_of_generate_finite (range Iio)
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Iio ℝ)) isPiSystem_Iio ?_ ?_
  · rintro _ ⟨a, rfl⟩
    rw [Measure.restrict_apply measurableSet_Iio, Measure.restrict_apply measurableSet_Iio,
      Iio_inter_Iio, Measure.map_apply_of_aemeasurable hgm measurableSet_Iio,
      Measure.map_apply_of_aemeasurable hhm measurableSet_Iio]
    have hpos : 0 < -(a ⊓ -c) := by
      have : a ⊓ -c ≤ -c := inf_le_right
      linarith
    have := H _ hpos
    rw [neg_neg] at this
    exact this
  · rw [Measure.restrict_apply_univ, Measure.restrict_apply_univ,
      Measure.map_apply_of_aemeasurable hgm measurableSet_Iio,
      Measure.map_apply_of_aemeasurable hhm measurableSet_Iio]
    exact H c hc

/-- `ℝ \ {0} = ⋃ₙ ((1/(n+1), ∞) ∪ (-∞, -1/(n+1)))`. -/
theorem compl_zero_eq_iUnion :
    ({0}ᶜ : Set ℝ) = ⋃ n : ℕ, (Ioi (1 / ((n : ℝ) + 1)) ∪ Iio (-(1 / ((n : ℝ) + 1)))) := by
  ext x
  simp only [mem_compl_iff, mem_singleton_iff, mem_iUnion, mem_union, mem_Ioi, mem_Iio]
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (abs_pos.2 hx)
    refine ⟨n, ?_⟩
    rcases le_or_gt 0 x with h | h
    · left
      rw [abs_of_nonneg h] at hn
      exact hn
    · right
      rw [abs_of_neg h] at hn
      linarith
  · rintro ⟨n, hn⟩ hx0
    subst hx0
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    rcases hn with hn | hn <;> linarith

/-- The key step: the push-forwards of `volume` by `g` and `h` agree off `0`. -/
theorem restrict_compl_zero_eq (H : Equimeasurable g h) :
    (volume.map g).restrict {0}ᶜ = (volume.map h).restrict {0}ᶜ := by
  rw [compl_zero_eq_iUnion, Measure.restrict_iUnion_congr]
  intro n
  have hc : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  rw [Measure.restrict_union_congr]
  exact ⟨restrict_Ioi_eq H.1 H.2.1 (fun s hs => (H.2.2 s hs).1) hc,
    restrict_Iio_eq H.1 H.2.1 (fun s hs => (H.2.2 s hs).2) hc⟩

end DistributionAux

open DistributionAux

variable {g h : ℂ → ℝ}

/-- Equal measures of preimages of Borel sets avoiding `0`. -/
theorem volume_preimage_eq (H : Equimeasurable g h) {A : Set ℝ} (hA : MeasurableSet A)
    (h0 : (0 : ℝ) ∉ A) : volume (g ⁻¹' A) = volume (h ⁻¹' A) := by
  have hgm : AEMeasurable g := H.1.aestronglyMeasurable.aemeasurable
  have hhm : AEMeasurable h := H.2.1.aestronglyMeasurable.aemeasurable
  have hA0 : A ⊆ ({0}ᶜ : Set ℝ) := by
    intro x hx hx0
    rw [mem_singleton_iff] at hx0
    exact h0 (hx0 ▸ hx)
  calc volume (g ⁻¹' A) = (volume.map g) A := (Measure.map_apply_of_aemeasurable hgm hA).symm
    _ = (volume.map g).restrict {0}ᶜ A := (Measure.restrict_eq_self _ hA0).symm
    _ = (volume.map h).restrict {0}ᶜ A := by rw [restrict_compl_zero_eq H]
    _ = (volume.map h) A := Measure.restrict_eq_self _ hA0
    _ = volume (h ⁻¹' A) := Measure.map_apply_of_aemeasurable hhm hA

/-- `∫⁻ Φ(g) = ∫⁻ Φ(h)` for measurable `Φ ≥ 0` with `Φ(0) = 0`. -/
theorem lintegral_comp_eq (H : Equimeasurable g h) {Φ : ℝ → ℝ≥0∞} (hΦ : Measurable Φ)
    (hΦ0 : Φ 0 = 0) : ∫⁻ x, Φ (g x) = ∫⁻ x, Φ (h x) := by
  have hgm : AEMeasurable g := H.1.aestronglyMeasurable.aemeasurable
  have hhm : AEMeasurable h := H.2.1.aestronglyMeasurable.aemeasurable
  have hind : Φ = ({0}ᶜ : Set ℝ).indicator Φ := by
    funext s
    by_cases hs : s = 0
    · subst hs
      simp [hΦ0]
    · rw [indicator_of_mem (by simpa using hs)]
  rw [← lintegral_map' hΦ.aemeasurable hgm, ← lintegral_map' hΦ.aemeasurable hhm, hind,
    lintegral_indicator (measurableSet_singleton 0).compl,
    lintegral_indicator (measurableSet_singleton 0).compl, restrict_compl_zero_eq H]

theorem integrable_comp_iff (H : Equimeasurable g h) {Φ : ℝ → ℝ} (hΦ : Measurable Φ)
    (hΦ0 : Φ 0 = 0) : Integrable (fun x => Φ (g x)) ↔ Integrable (fun x => Φ (h x)) := by
  have hgm : AEMeasurable g := H.1.aestronglyMeasurable.aemeasurable
  have hhm : AEMeasurable h := H.2.1.aestronglyMeasurable.aemeasurable
  have hfin : ∫⁻ x, ‖Φ (g x)‖ₑ = ∫⁻ x, ‖Φ (h x)‖ₑ :=
    lintegral_comp_eq H (Φ := fun s => ‖Φ s‖ₑ) hΦ.enorm (by simp [hΦ0])
  constructor
  · intro hi
    refine ⟨(hΦ.comp_aemeasurable hhm).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, ← hfin]
    exact hasFiniteIntegral_iff_enorm.1 hi.2
  · intro hi
    refine ⟨(hΦ.comp_aemeasurable hgm).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, hfin]
    exact hasFiniteIntegral_iff_enorm.1 hi.2

/-- `∫ Φ(g) = ∫ Φ(h)` for measurable `Φ` with `Φ(0) = 0`. -/
theorem integral_comp_eq (H : Equimeasurable g h) {Φ : ℝ → ℝ} (hΦ : Measurable Φ)
    (hΦ0 : Φ 0 = 0) : ∫ x, Φ (g x) = ∫ x, Φ (h x) := by
  by_cases hi : Integrable (fun x => Φ (g x))
  · have hi' := (integrable_comp_iff H hΦ hΦ0).1 hi
    have e1 : ∫⁻ x, ENNReal.ofReal (Φ (g x)) = ∫⁻ x, ENNReal.ofReal (Φ (h x)) :=
      lintegral_comp_eq H (Φ := fun s => ENNReal.ofReal (Φ s)) hΦ.ennreal_ofReal (by simp [hΦ0])
    have e2 : ∫⁻ x, ENNReal.ofReal (-Φ (g x)) = ∫⁻ x, ENNReal.ofReal (-Φ (h x)) :=
      lintegral_comp_eq H (Φ := fun s => ENNReal.ofReal (-Φ s)) hΦ.neg.ennreal_ofReal
        (by simp [hΦ0])
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi,
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi', e1, e2]
  · have hi' : ¬ Integrable (fun x => Φ (h x)) := fun hi' =>
      hi ((integrable_comp_iff H hΦ hΦ0).2 hi')
    rw [integral_undef hi, integral_undef hi']

/-- Equimeasurability is preserved by composition with `Φ`, `Φ(0) = 0`. -/
theorem comp (H : Equimeasurable g h) {Φ : ℝ → ℝ} (hΦ : Measurable Φ) (hΦ0 : Φ 0 = 0)
    (hint : MemLp (fun x => Φ (g x)) 1) :
    Equimeasurable (fun x => Φ (g x)) (fun x => Φ (h x)) := by
  refine ⟨hint, ?_, fun s hs => ⟨?_, ?_⟩⟩
  · rw [memLp_one_iff_integrable] at hint ⊢
    exact (integrable_comp_iff H hΦ hΦ0).1 hint
  · have h0 : (0 : ℝ) ∉ Φ ⁻¹' Ioi s := by
      simp only [mem_preimage, mem_Ioi, hΦ0, not_lt]
      exact hs.le
    exact volume_preimage_eq H (hΦ measurableSet_Ioi) h0
  · have h0 : (0 : ℝ) ∉ Φ ⁻¹' Iio (-s) := by
      simp only [mem_preimage, mem_Iio, hΦ0, not_lt]
      linarith
    exact volume_preimage_eq H (hΦ measurableSet_Iio) h0

end NonUniqueEuler.Equimeasurable
