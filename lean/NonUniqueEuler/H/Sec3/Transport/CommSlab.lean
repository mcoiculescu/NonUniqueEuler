import NonUniqueEuler.H.Sec3.Transport.Basic
import NonUniqueEuler.I.Sec3.Commutator

/-!
# Helper for `P/Sec3/Transport`: the commutator on `(t₀, T') × B_R`

`lem:commutator` (`I/Sec3/Commutator.lean`) is stated on an open interval `I` and compact
`J ⊆ I`. As in the manuscript (`03_compactness.tex:481-491`) we extend the data below `t = 0`:
`ũ(t) = u(t)`, `w̃(t) = w(t)` for `t > 0`, and `ũ(t) = 0`, `w̃(t) = 0` for `t ≤ 0` (the manuscript
uses `u = u₀`, `w = 0` on `(t₀-1, t₀]`; only the hypotheses of `lem:commutator` matter here, and
`C_ε[ũ, w̃](t) = C_ε[u, w](t)` for `t > 0`, since `C_ε` acts in `x` only). On
`I = (-1, T)`, `w̃ ∈ L¹_loc(I; W^{1,2}_loc)` is divergence free and `ũ ∈ L^∞_loc(I; L²_loc)`, and
`J = [t₀, T']` is a compact subset of `I`. Hence (`tendsto_lintegral_commEps_slab`)
`∫_{(t₀,T')×B_R} |C_ε[u,w]| → 0` as `ε → 0⁺`, for every `T' < T` and `R > 0`.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.Weak.TransportH

/-- Extension by zero to `t ≤ 0`. -/
def extZero {E : Type*} [Zero E] (f : ℝ → ℂ → E) : ℝ → ℂ → E :=
  fun t => if 0 < t then f t else 0

theorem extZero_of_pos {E : Type*} [Zero E] (f : ℝ → ℂ → E) {t : ℝ} (ht : 0 < t) :
    extZero f t = f t := by
  simp [extZero, ht]

theorem extZero_of_nonpos {E : Type*} [Zero E] (f : ℝ → ℂ → E) {t : ℝ} (ht : t ≤ 0) :
    extZero f t = 0 := by
  simp [extZero, not_lt.2 ht]

theorem uncurry_extZero {E : Type*} [Zero E] (f : ℝ → ℂ → E) :
    Function.uncurry (extZero f) = (Ioi (0 : ℝ) ×ˢ (univ : Set ℂ)).indicator (Function.uncurry f) := by
  funext p
  rcases p with ⟨t, x⟩
  by_cases hp : 0 < t
  · simp [Function.uncurry, extZero, hp, indicator, mem_prod]
  · simp [Function.uncurry, extZero, hp, indicator, mem_prod]

theorem aestronglyMeasurable_uncurry_extZero {E : Type*} [NormedAddCommGroup E] {T : ℝ}
    {f : ℝ → ℂ → E}
    (hf : AEStronglyMeasurable (Function.uncurry f) (volume.restrict (Ioo 0 T ×ˢ univ)))
    {I : Set ℝ} (hI : I ⊆ Iio T) (Ω : Set ℂ) :
    AEStronglyMeasurable (Function.uncurry (extZero f)) (volume.restrict (I ×ˢ Ω)) := by
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ (univ : Set ℂ)) :=
    measurableSet_Ioi.prod MeasurableSet.univ
  rw [uncurry_extZero, aestronglyMeasurable_indicator_iff hS, Measure.restrict_restrict hS]
  refine hf.mono_measure (Measure.restrict_mono (fun p hp => ?_) le_rfl)
  exact ⟨⟨hp.1.1, hI hp.2.1⟩, mem_univ _⟩

theorem memHOn_zero (k : ℕ) (V : Set ℂ) : Sob.MemHOn k V 0 :=
  ⟨MemLp.zero, fun _ _ => ⟨0, MemLp.zero, fun φ _ => by simp⟩⟩

theorem isWeaklyDivFree_zero : Prelim.IsWeaklyDivFree 0 := by
  intro φ _ _
  simp

/-- `w̃ ∈ L¹_loc((-1,T); W^{1,2}_loc)` with `div w̃ = 0`. -/
theorem isLocH1DivFreeField_extZero {T : ℝ} {w : ℝ → ℂ → ℂ}
    (hw : IsBddH1DivFreeField (Ioo 0 T) w) : IsLocH1DivFreeField (Ioo (-1) T) (extZero w) where
  aestronglyMeasurable :=
    aestronglyMeasurable_uncurry_extZero hw.aestronglyMeasurable (fun _ ht => ht.2) univ
  memHOn R hR := by
    obtain ⟨M, hM⟩ := hw.bound R hR
    rw [ae_restrict_iff' measurableSet_Ioo] at hM ⊢
    filter_upwards [hM] with t ht ht'
    by_cases h0 : 0 < t
    · rw [extZero_of_pos w h0]; exact (ht ⟨h0, ht'.2⟩).1
    · rw [extZero_of_nonpos w (not_lt.1 h0)]; exact memHOn_zero 1 _
  integrableOn_normHOn R hR J hJI hJ := by
    obtain ⟨M, hM⟩ := hw.bound R hR
    set c₀ : ℝ := Sob.normHOn 1 (ball (0 : ℂ) R) 0 with hc₀
    set g : ℝ → ℝ := fun t => Sob.normHOn 1 (ball (0 : ℂ) R) (w t) with hg
    have hfeq : (fun t => Sob.normHOn 1 (ball (0 : ℂ) R) (extZero w t)) =
        fun t => (Ioi (0 : ℝ)).indicator (fun t => g t - c₀) t + c₀ := by
      funext t
      by_cases h0 : 0 < t
      · simp [extZero_of_pos w h0, indicator, h0, hg]
      · simp [extZero_of_nonpos w (not_lt.1 h0), indicator, h0, hc₀]
    rw [hfeq]
    have hmeas : AEStronglyMeasurable
        (fun t => (Ioi (0 : ℝ)).indicator (fun t => g t - c₀) t + c₀) (volume.restrict J) := by
      refine AEStronglyMeasurable.add ?_ aestronglyMeasurable_const
      rw [aestronglyMeasurable_indicator_iff measurableSet_Ioi, Measure.restrict_restrict
        measurableSet_Ioi]
      refine ((hw.aestronglyMeasurable_normHOn R hR).sub aestronglyMeasurable_const).mono_measure
        (Measure.restrict_mono
          (show Ioi 0 ∩ J ⊆ Ioo 0 T from fun t ht => ⟨ht.1, (hJI ht.2).2⟩) le_rfl)
    have : IsFiniteMeasure (volume.restrict J) :=
      isFiniteMeasure_restrict.2 hJ.measure_lt_top.ne
    refine Integrable.of_bound hmeas (|M - c₀| + |c₀|) ?_
    have hM' := ae_restrict_of_ae_restrict_of_subset (s := J ∩ Ioi 0) (t := Ioo 0 T)
      (fun t ht => ⟨ht.2, (hJI ht.1).2⟩) hM
    rw [ae_restrict_iff' (hJ.measurableSet.inter measurableSet_Ioi)] at hM'
    rw [ae_restrict_iff' hJ.measurableSet]
    filter_upwards [hM'] with t ht htJ
    by_cases h0 : 0 < t
    · have h1 := ht ⟨htJ, h0⟩
      have h2 : 0 ≤ g t := Sob.normHOn_nonneg _ _ _
      simp only [indicator, mem_Ioi, h0, ite_true, sub_add_cancel, Real.norm_eq_abs]
      rw [abs_of_nonneg h2]
      have : M - c₀ ≤ |M - c₀| := le_abs_self _
      have : c₀ ≤ |c₀| := le_abs_self _
      linarith [h1.2]
    · simp only [indicator, mem_Ioi, h0, ite_false, zero_add, Real.norm_eq_abs]
      linarith [abs_nonneg (M - c₀)]
  divFree := by
    have h := hw.divFree
    rw [ae_restrict_iff' measurableSet_Ioo] at h ⊢
    filter_upwards [h] with t ht ht'
    by_cases h0 : 0 < t
    · rw [extZero_of_pos w h0]; exact ht ⟨h0, ht'.2⟩
    · rw [extZero_of_nonpos w (not_lt.1 h0)]; exact isWeaklyDivFree_zero

/-- `ũ ∈ L^∞(J; L²(B_R))` for every `J ⊆ (-∞, T)`. -/
theorem memLinfLp_extZero {T : ℝ} {u : ℝ → ℂ → ℝ} (hu2 : Prelim.MemLinfLp (Ioo 0 T) univ 2 u)
    {J : Set ℝ} (hJm : MeasurableSet J) (hJ : J ⊆ Iio T) (R : ℝ) :
    Prelim.MemLinfLp J (ball (0 : ℂ) R) 2 (extZero u) := by
  obtain ⟨M, hM⟩ := hu2.essBounded
  refine ⟨aestronglyMeasurable_uncurry_extZero hu2.aestronglyMeasurable hJ _, max M 0, ?_⟩
  have hM' := hM
  rw [ae_restrict_iff' measurableSet_Ioo] at hM'
  -- `J` need not be measurable: work with the a.e. statement on the whole line
  have hall : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Iio T →
      MemLp (extZero u t) 2 (volume.restrict (ball (0 : ℂ) R)) ∧
        (eLpNorm (extZero u t) 2 (volume.restrict (ball (0 : ℂ) R))).toReal ≤ max M 0 := by
    filter_upwards [hM'] with t ht htT
    by_cases h0 : 0 < t
    · rw [extZero_of_pos u h0]
      obtain ⟨h1, h2⟩ := ht ⟨h0, htT⟩
      rw [Measure.restrict_univ] at h1 h2
      refine ⟨h1.mono_measure Measure.restrict_le_self, ?_⟩
      refine le_trans ?_ (h2.trans (le_max_left _ _))
      exact ENNReal.toReal_mono h1.eLpNorm_ne_top
        (eLpNorm_mono_measure _ Measure.restrict_le_self)
    · rw [extZero_of_nonpos u (not_lt.1 h0)]
      refine ⟨MemLp.zero, ?_⟩
      simp
  rw [ae_restrict_iff' hJm]
  filter_upwards [hall] with t ht htJ
  exact ht (hJ htJ)

/-- `C_ε[ũ, w̃](t) = C_ε[u, w](t)` for `t > 0`. -/
theorem commEps_extZero {ρ : ℂ → ℝ} {ε : ℝ} {u : ℝ → ℂ → ℝ} {w : ℝ → ℂ → ℂ} {t : ℝ}
    (ht : 0 < t) (x : ℂ) :
    commEps ρ ε (extZero u) (extZero w) t x = commEps ρ ε u w t x := by
  simp only [commEps, dotGradMollify, mollifyDiv, extZero_of_pos _ ht]

/-- `lem:commutator` on the slab: for `T' < T` and `R > 0`,
`∫_{(t₀,T') × B_R} |C_ε[u,w]| → 0` as `ε → 0⁺`. -/
theorem tendsto_lintegral_commEps_slab {ρ : ℂ → ℝ} (hρ : IsMollifier ρ) {T t₀ : ℝ}
    (ht₀ : 0 ≤ t₀) {w : ℝ → ℂ → ℂ} (hw : IsBddH1DivFreeField (Ioo 0 T) w) {u : ℝ → ℂ → ℝ}
    (hu2 : Prelim.MemLinfLp (Ioo 0 T) univ 2 u) {T' : ℝ} (hT' : T' < T) {R : ℝ} (hR : 0 < R) :
    Tendsto (fun ε : ℝ => ∫⁻ p in Ioo t₀ T' ×ˢ ball (0 : ℂ) R, ‖commEps ρ ε u w p.1 p.2‖ₑ)
      (𝓝[>] 0) (𝓝 0) := by
  have hJ : Icc t₀ T' ⊆ Ioo (-1) T := Icc_subset_Ioo (by linarith) hT'
  have h := commutator_tendsto hρ isOpen_Ioo ordConnected_Ioo (isLocH1DivFreeField_extZero hw)
    (fun J hJI hJc R _ => memLinfLp_extZero hu2 hJc.measurableSet (hJI.trans fun _ ht => ht.2) R)
    (Icc t₀ T') hJ isCompact_Icc R hR
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le)
    (fun ε => ?_)
  calc ∫⁻ p in Ioo t₀ T' ×ˢ ball (0 : ℂ) R, ‖commEps ρ ε u w p.1 p.2‖ₑ
      = ∫⁻ p in Ioo t₀ T' ×ˢ ball (0 : ℂ) R,
          ‖commEps ρ ε (extZero u) (extZero w) p.1 p.2‖ₑ := by
        refine setLIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_ball) ?_
        intro p hp
        dsimp only
        rw [commEps_extZero (lt_of_le_of_lt ht₀ hp.1.1)]
    _ ≤ ∫⁻ p in Icc t₀ T' ×ˢ ball (0 : ℂ) R,
          ‖commEps ρ ε (extZero u) (extZero w) p.1 p.2‖ₑ :=
        lintegral_mono_set (prod_mono Ioo_subset_Icc_self le_rfl)

end NonUniqueEuler.Weak.TransportH
