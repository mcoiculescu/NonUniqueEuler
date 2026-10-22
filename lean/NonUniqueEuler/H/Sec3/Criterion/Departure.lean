import NonUniqueEuler.H.Sec3.Criterion.Basic
import NonUniqueEuler.I.Infra.JointRep.Slab

/-!
# Helper for `P/Sec3/Criterion`: item (v) of `thm:criterion`

Manuscript: proof of `thm:criterion`, paragraph "We now prove (v)", `03_compactness.tex:1058-1077`.

* `supDist_eq_of_tendsto`: the defect passes to the limit under uniform `L¹` convergence;
* `isOpen_departureSet_of`: `𝒪 = {t ∈ [0, T₀) : ω(t) ≠ f}` is open if `ω ∈ C([0, T₀); L¹)` and
  `ω(0) = f`;
* `departureSet_inter_nonempty_of`, `departureTime_lt_of`: `𝒪 ∩ (0, T] ≠ ∅`, `t₀ = inf 𝒪 < T`;
* `distinctInX_of`: for `T' > t₀`, `𝒪 ∩ (0, T')` contains an interval, so `ω ≠ f` in `X_q(T')`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.Compact.CriterionAux

open Weak

/-- Triangle inequality for the distances `sup_{t ∈ s} ‖·‖_{L¹}`. -/
theorem supDist_le_add {s : Set ℝ} {ω₁ ω₂ ω₃ : ℝ → ℂ → ℝ}
    (h₁ : ∀ t ∈ s, AEStronglyMeasurable (ω₁ t) volume)
    (h₂ : ∀ t ∈ s, AEStronglyMeasurable (ω₂ t) volume)
    (h₃ : ∀ t ∈ s, AEStronglyMeasurable (ω₃ t) volume) :
    supDist 1 s ω₁ ω₃ ≤ supDist 1 s ω₂ ω₁ + supDist 1 s ω₂ ω₃ := by
  refine supDist_le_iff.2 fun t ht => ?_
  have e : ω₁ t - ω₃ t = (ω₁ t - ω₂ t) + (ω₂ t - ω₃ t) := by abel
  rw [e]
  refine (eLpNorm_add_le ((h₁ t ht).sub (h₂ t ht)) ((h₂ t ht).sub (h₃ t ht)) le_rfl).trans ?_
  rw [eLpNorm_sub_comm]
  exact add_le_add (eLpNorm_le_supDist ht) (eLpNorm_le_supDist ht)

/-- (v), first assertion: if `sup_{t ∈ s} ‖ωₙ(t) - f‖₁ → c` and `sup_{t ∈ s} ‖ωₙ(t) - ω(t)‖₁ → 0`,
then `sup_{t ∈ s} ‖ω(t) - f‖₁ = c`. -/
theorem supDist_eq_of_tendsto {s : Set ℝ} {ωs : ℕ → ℝ → ℂ → ℝ} {ω : ℝ → ℂ → ℝ} {f : ℂ → ℝ}
    {c : ℝ≥0∞} (hωs : ∀ n, ∀ t ∈ s, AEStronglyMeasurable (ωs n t) volume)
    (hω : ∀ t ∈ s, AEStronglyMeasurable (ω t) volume) (hf : AEStronglyMeasurable f volume)
    (hc : Tendsto (fun n => supDist 1 s (ωs n) (stationary f)) atTop (𝓝 c))
    (hu : Tendsto (fun n => supDist 1 s (ωs n) ω) atTop (𝓝 0)) :
    supDist 1 s ω (stationary f) = c := by
  have hst : ∀ t ∈ s, AEStronglyMeasurable (stationary f t) volume := fun _ _ => hf
  apply le_antisymm
  · have h := hu.add hc
    rw [zero_add] at h
    exact ge_of_tendsto' h fun n => supDist_le_add hω (hωs n) hst
  · have h := hu.add (tendsto_const_nhds (x := supDist 1 s ω (stationary f)))
    rw [zero_add] at h
    exact le_of_tendsto_of_tendsto' hc h fun n => by
      have := supDist_le_add (hωs n) hω hst
      rwa [show supDist 1 s ω (ωs n) = supDist 1 s (ωs n) ω by
        simp only [supDist, eLpNorm_sub_comm]] at this

theorem not_ae_eq_iff_pos {g f : ℂ → ℝ} (hg : AEStronglyMeasurable g volume)
    (hf : AEStronglyMeasurable f volume) :
    ¬ (g =ᵐ[volume] f) ↔ 0 < eLpNorm (g - f) 1 volume := by
  rw [pos_iff_ne_zero, Ne, eLpNorm_eq_zero_iff (hg.sub hf) one_ne_zero]
  refine not_congr ⟨fun h => h.mono fun x hx => ?_, fun h => h.mono fun x hx => ?_⟩
  · simpa [sub_eq_zero] using hx
  · simpa [sub_eq_zero] using hx

variable {T₀ : ℝ≥0∞} {f : ℂ → ℝ} {ω : ℝ → ℂ → ℝ}

theorem zero_not_mem_departureSet_of (hω0 : ω 0 =ᵐ[volume] f) :
    (0 : ℝ) ∉ departureSet T₀ ω f :=
  fun h => h.2 hω0

/-- `𝒪` is a neighbourhood, within `[0, T₀)`, of each of its points. -/
theorem departureSet_mem_nhdsWithin (hc1 : ContinuousIntoLpOn 1 (timeInterval T₀) ω)
    (hf : AEStronglyMeasurable f volume) {t₀ : ℝ} (ht₀ : t₀ ∈ departureSet T₀ ω f) :
    departureSet T₀ ω f ∈ 𝓝[timeInterval T₀] t₀ := by
  have hm₀ : AEStronglyMeasurable (ω t₀) volume := (hc1.1 t₀ ht₀.1).aestronglyMeasurable
  have hpos : 0 < eLpNorm (ω t₀ - f) 1 volume := (not_ae_eq_iff_pos hm₀ hf).1 ht₀.2
  have hev : ∀ᶠ t in 𝓝[timeInterval T₀] t₀,
      eLpNorm (ω t - ω t₀) 1 volume < eLpNorm (ω t₀ - f) 1 volume :=
    (hc1.2 t₀ ht₀.1).eventually (gt_mem_nhds hpos)
  filter_upwards [hev, self_mem_nhdsWithin] with t ht hts
  refine ⟨hts, fun hae => ?_⟩
  have e : ω t₀ - f =ᵐ[volume] ω t₀ - ω t := hae.mono fun x hx => by simp [hx]
  rw [eLpNorm_congr_ae e, eLpNorm_sub_comm] at ht
  exact lt_irrefl _ ht

/-- `{t : 0 < t ∧ t < T₀}` is open. -/
theorem isOpen_posTimeInterval (T₀ : ℝ≥0∞) :
    IsOpen {t : ℝ | 0 < t ∧ ENNReal.ofReal t < T₀} :=
  isOpen_Ioi.inter (isOpen_lt ENNReal.continuous_ofReal continuous_const)

/-- (v): `𝒪` is open. -/
theorem isOpen_departureSet_of (hc1 : ContinuousIntoLpOn 1 (timeInterval T₀) ω)
    (hf : AEStronglyMeasurable f volume) (hω0 : ω 0 =ᵐ[volume] f) :
    IsOpen (departureSet T₀ ω f) := by
  refine isOpen_iff_mem_nhds.2 fun t₀ ht₀ => ?_
  have hpos : 0 < t₀ := lt_of_le_of_ne ht₀.1.1 fun h => by
    subst h; exact zero_not_mem_departureSet_of hω0 ht₀
  obtain ⟨U, hU, hUsub⟩ :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.1 (departureSet_mem_nhdsWithin hc1 hf ht₀)
  have hV : {t : ℝ | 0 < t ∧ ENNReal.ofReal t < T₀} ∈ 𝓝 t₀ :=
    (isOpen_posTimeInterval T₀).mem_nhds ⟨hpos, ht₀.1.2⟩
  filter_upwards [hU, hV] with t htU htV
  exact hUsub ⟨htU, htV.1.le, htV.2⟩

/-- (v): `𝒪 ∩ (0, T] ≠ ∅` when `sup_{t ≤ T} ‖ω(t) - f‖₁ > 0` and `ω(0) = f`. -/
theorem departureSet_inter_nonempty_of {T : ℝ} (hTT₀ : ENNReal.ofReal T < T₀)
    (hm : ∀ t ∈ Icc 0 T, AEStronglyMeasurable (ω t) volume) (hf : AEStronglyMeasurable f volume)
    (hω0 : ω 0 =ᵐ[volume] f) (hpos : 0 < supDist 1 (Icc 0 T) ω (stationary f)) :
    (departureSet T₀ ω f ∩ Ioc 0 T).Nonempty := by
  obtain ⟨t, ht⟩ := lt_iSup_iff.1 hpos
  obtain ⟨htT, ht'⟩ := lt_iSup_iff.1 ht
  have hne : ¬ (ω t =ᵐ[volume] f) := (not_ae_eq_iff_pos (hm t htT) hf).2 ht'
  have ht0 : t ≠ 0 := fun h => by subst h; exact hne hω0
  exact ⟨t, ⟨Icc_subset_timeInterval hTT₀ htT, hne⟩, lt_of_le_of_ne htT.1 (Ne.symm ht0), htT.2⟩

/-- (v): `t₀ = inf 𝒪 < T`. -/
theorem departureTime_lt_of {T : ℝ} (hopen : IsOpen (departureSet T₀ ω f))
    (hne : (departureSet T₀ ω f ∩ Ioc 0 T).Nonempty) : departureTime T₀ ω f < T := by
  obtain ⟨t₁, ht₁, ht₁T⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen t₁ ht₁
  have hmem : t₁ - ε / 2 ∈ departureSet T₀ ω f := hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
  have := departureTime_le hmem
  linarith [ht₁T.2]

/-- (v): for `T' > t₀`, `ω` and the stationary solution `f` are distinct in `X_q(T')`. -/
theorem distinctInX_of (hopen : IsOpen (departureSet T₀ ω f))
    (hne : (departureSet T₀ ω f).Nonempty) {T' : ℝ} (hT' : departureTime T₀ ω f < T') :
    DistinctInX T' ω (stationary f) := by
  intro hae
  obtain ⟨s₁, hs₁, hs₁T'⟩ := exists_lt_of_csInf_lt hne hT'
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen s₁ hs₁
  have hs₁0 : 0 ≤ s₁ := hs₁.1.1
  set b := min (s₁ + ε) T'
  have hb : s₁ < b := lt_min (by linarith) hs₁T'
  have hsub : Ioo s₁ b ⊆ departureSet T₀ ω f := fun t ht => hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2, min_le_left (s₁ + ε) T'])
  have hsub' : Ioo s₁ b ⊆ Ioo 0 T' := fun t ht =>
    ⟨hs₁0.trans_lt ht.1, ht.2.trans_le (min_le_right _ _)⟩
  have hae' := JointRep.ae_ae_of_ae_eq_slab hae
  rw [ae_restrict_iff' measurableSet_Ioo] at hae'
  have hnull : volume (Ioo s₁ b) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae'] with t ht htI
    exact (hsub htI).2 (ht (hsub' htI))
  rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at hnull
  linarith

end NonUniqueEuler.Compact.CriterionAux
