import NonUniqueEuler.Defs.Infra.AngularFourier
import NonUniqueEuler.I.Infra.AngularFourier.Sector
import NonUniqueEuler.I.Infra.AngularFourier.SectorL2
import NonUniqueEuler.I.Infra.AngularFourier.Parseval
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-!
# Proof: `m`-fold symmetry, radial symmetry and reality in terms of sectors (library I-ANG)

Proves the declarations of `NonUniqueEuler/I/Infra/AngularFourier/Symmetry.lean`
(`02_prelim.tex:34-35`).

Proof. `P_ℓ (g ∘ O_α) = (P_ℓ g) ∘ O_α = e^{iℓα} P_ℓ g` pointwise (`sectorProj_rot`), so
`g ∘ O_α = g` a.e. forces `(e^{iℓα} - 1) P_ℓ g = 0` a.e. Conversely, `P_ℓ` is linear on `L²`
up to null sets (through `sectorProjL`), so all sectors of `g ∘ O_α - g` vanish when the sectors
`ℓ` with `e^{iℓα} ≠ 1` of `g` vanish, and `ae_eq_zero_of_sectorProj` gives `g ∘ O_α = g` a.e.
For `α = 2π/m`, `e^{iℓα} = 1 ↔ m ∣ ℓ`; for radial symmetry, `α = π/ℓ` gives `e^{iℓα} = -1`.
The profile version uses `P_ℓ g(x) = g_ℓ(|x|) e^{iℓθ}` and the fact that `x ↦ |x|` sends
null sets of `(0, ∞)` to null sets of `ℂ` and conversely (Mathlib's polar coordinates,
`Complex.lintegral_comp_polarCoord_symm`, and `Measure.ae_ae_of_ae_prod`; no measurability of
the profile is needed). Conjugation: `intervalIntegral_conj` and `conj (e^z) = e^{conj z}`.
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal ComplexConjugate

namespace NonUniqueEuler.Ang

/-! ### Helpers -/

/-- `P_ℓ (g ∘ O_α) = (P_ℓ g) ∘ O_α`, pointwise (rotations commute). -/
private theorem sectorProj_comp_rot (ℓ : ℤ) (g : ℂ → ℂ) (α : ℝ) (x : ℂ) :
    sectorProj ℓ (fun y => g (rot α y)) x = sectorProj ℓ g (rot α x) := by
  unfold sectorProj
  congr 1
  refine intervalIntegral.integral_congr fun φ _ => ?_
  simp only [rot]
  rw [mul_left_comm]

/-- If `g ∘ O_α = g` a.e. and `e^{iℓα} ≠ 1`, then `P_ℓ g = 0` a.e. -/
private theorem sectorProj_ae_zero_of_rot {g : ℂ → ℂ} {α : ℝ}
    (h : (fun x => g (rot α x)) =ᵐ[volume] g) {ℓ : ℤ}
    (hℓ : Complex.exp ((ℓ : ℂ) * α * Complex.I) ≠ 1) :
    sectorProj ℓ g =ᵐ[volume] 0 := by
  filter_upwards [sectorProj_congr_ae ℓ h] with x hx
  rw [sectorProj_comp_rot, sectorProj_rot] at hx
  have h2 : (Complex.exp ((ℓ : ℂ) * α * Complex.I) - 1) * sectorProj ℓ g x = 0 := by
    rw [sub_mul, one_mul, hx, sub_self]
  rcases mul_eq_zero.1 h2 with h1 | h1
  · exact absurd (sub_eq_zero.1 h1) hℓ
  · simpa using h1

/-- `P_ℓ` is linear up to null sets on `L²` (through the `L²` operator `sectorProjL`). -/
private theorem sectorProj_sub_ae {f g : ℂ → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (ℓ : ℤ) :
    sectorProj ℓ (fun x => f x - g x) =ᵐ[volume]
      fun x => sectorProj ℓ f x - sectorProj ℓ g x := by
  set F := hf.toLp f
  set G := hg.toLp g
  have hFG : (fun x => f x - g x) =ᵐ[volume] ⇑(F - G) := by
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp, Lp.coeFn_sub F G] with x h1 h2 h3
    rw [h3, Pi.sub_apply, h1, h2]
  have hF : sectorProj ℓ ⇑F =ᵐ[volume] sectorProj ℓ f := sectorProj_congr_ae ℓ hf.coeFn_toLp
  have hG : sectorProj ℓ ⇑G =ᵐ[volume] sectorProj ℓ g := sectorProj_congr_ae ℓ hg.coeFn_toLp
  have h1 := sectorProj_congr_ae ℓ hFG
  have h2 := sectorProjL_spec ℓ (F - G)
  have h3 := sectorProjL_spec ℓ F
  have h4 := sectorProjL_spec ℓ G
  have h5 := Lp.coeFn_sub (sectorProjL ℓ F) (sectorProjL ℓ G)
  rw [map_sub] at h2
  filter_upwards [h1, h2, h3, h4, h5, hF, hG] with x e1 e2 e3 e4 e5 e6 e7
  rw [e1, ← e2, e5, Pi.sub_apply, e3, e4, e6, e7]

/-- If the sectors `ℓ` of `g ∈ L²` with `e^{iℓα} ≠ 1` vanish, then `g ∘ O_α = g` a.e. -/
private theorem rot_ae_eq_of_sectorProj {g : ℂ → ℂ} (hg : MemLp g 2 volume) (α : ℝ)
    (h : ∀ ℓ : ℤ, Complex.exp ((ℓ : ℂ) * α * Complex.I) ≠ 1 → sectorProj ℓ g =ᵐ[volume] 0) :
    (fun x => g (rot α x)) =ᵐ[volume] g := by
  have hgr : MemLp (fun x => g (rot α x)) 2 volume :=
    hg.comp_measurePreserving (Polar.measurePreserving_rot α)
  have hd : MemLp (fun x => g (rot α x) - g x) 2 volume := hgr.sub hg
  refine (ae_eq_zero_of_sectorProj hd fun ℓ => ?_).mono fun x hx => ?_
  · by_cases hℓ : Complex.exp ((ℓ : ℂ) * α * Complex.I) = 1
    · filter_upwards [sectorProj_sub_ae hgr hg ℓ] with x hx
      rw [hx, sectorProj_comp_rot, sectorProj_rot, hℓ, one_mul, sub_self]
      rfl
    · filter_upwards [sectorProj_sub_ae hgr hg ℓ, h ℓ hℓ] with x hx h0
      rw [hx, sectorProj_comp_rot, sectorProj_rot]
      simp only [Pi.zero_apply] at h0 ⊢
      rw [h0, mul_zero, sub_zero]
  · simpa [sub_eq_zero] using hx

/-- `e^{iℓ 2π/m} = 1 ↔ m ∣ ℓ`. -/
private theorem exp_mfold_eq_one_iff {m : ℕ} (hm : 0 < m) (ℓ : ℤ) :
    Complex.exp ((ℓ : ℂ) * ((2 * π / m : ℝ) : ℂ) * Complex.I) = 1 ↔ (m : ℤ) ∣ ℓ := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hπ : (2 * π * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    have key : (ℓ : ℂ) * (2 * π * Complex.I) = ((n : ℂ) * m) * (2 * π * Complex.I) := by
      calc (ℓ : ℂ) * (2 * π * Complex.I)
          = ((ℓ : ℂ) * ((2 * π / m : ℝ) : ℂ) * Complex.I) * m := by
            push_cast; field_simp
        _ = (n : ℂ) * (2 * π * Complex.I) * m := by rw [hn]
        _ = ((n : ℂ) * m) * (2 * π * Complex.I) := by ring
    have h1 : (ℓ : ℂ) = (n : ℂ) * m := mul_right_cancel₀ hπ key
    have h2 : ℓ = n * (m : ℤ) := by exact_mod_cast h1
    exact ⟨n, by rw [h2, mul_comm]⟩
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    push_cast
    field_simp

/-- The norm map sends null sets of `(0, ∞)` to null sets of `ℂ` and conversely: for any
predicate `p`, `p ‖x‖` holds for a.e. `x ∈ ℂ` iff `p r` holds for a.e. `r > 0`. -/
private theorem ae_comp_norm_iff {p : ℝ → Prop} :
    (∀ᵐ x : ℂ, p ‖x‖) ↔ ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), p r := by
  have hsymm : Measurable fun q : ℝ × ℝ => Complex.polarCoord.symm q := by
    have : (fun q : ℝ × ℝ => Complex.polarCoord.symm q) =
        fun q => (q.1 : ℂ) * ((Real.cos q.2 : ℂ) + (Real.sin q.2 : ℂ) * Complex.I) := by
      funext q
      exact Complex.polarCoord_symm_apply q
    rw [this]
    exact (by fun_prop : Continuous fun q : ℝ × ℝ =>
      (q.1 : ℂ) * ((Real.cos q.2 : ℂ) + (Real.sin q.2 : ℂ) * Complex.I)).measurable
  have htm : MeasurableSet Complex.polarCoord.target := Complex.polarCoord.open_target.measurableSet
  have hprod : (volume : Measure (ℝ × ℝ)).restrict Complex.polarCoord.target =
      (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-π) π)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod, Complex.polarCoord_target]
  constructor
  · intro h
    set T := toMeasurable volume {x : ℂ | ¬ p ‖x‖} with hT
    have hT0 : volume T = 0 := by
      rw [hT, measure_toMeasurable]
      exact h
    have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
    have hsub : {x : ℂ | ¬ p ‖x‖} ⊆ T := subset_toMeasurable _ _
    have hint := Complex.lintegral_comp_polarCoord_symm (T.indicator 1)
    rw [lintegral_indicator_one hTm, hT0] at hint
    simp only [smul_eq_mul] at hint
    have hmeas : Measurable fun q : ℝ × ℝ =>
        ENNReal.ofReal q.1 * T.indicator 1 (Complex.polarCoord.symm q) :=
      (ENNReal.measurable_ofReal.comp measurable_fst).mul
        ((measurable_one.indicator hTm).comp hsymm)
    have hae := (lintegral_eq_zero_iff hmeas).1 hint
    have hp : ∀ᵐ q ∂((volume : Measure (ℝ × ℝ)).restrict Complex.polarCoord.target), p q.1 := by
      filter_upwards [hae, ae_restrict_mem htm] with q hq hmem
      rw [Complex.polarCoord_target] at hmem
      have hq1 : 0 < q.1 := hmem.1
      have hq' : T.indicator 1 (Complex.polarCoord.symm q) = (0 : ℝ≥0∞) := by
        simp only [Pi.zero_apply, mul_eq_zero, ENNReal.ofReal_eq_zero] at hq
        rcases hq with hq | hq
        · exact absurd hq (not_le.2 hq1)
        · exact hq
      have hnot : Complex.polarCoord.symm q ∉ T := by
        intro hmemT
        rw [Set.indicator_of_mem hmemT] at hq'
        exact one_ne_zero hq'
      have hp' : p ‖Complex.polarCoord.symm q‖ := by
        by_contra hc
        exact hnot (hsub hc)
      rwa [Complex.norm_polarCoord_symm, abs_of_pos hq1] at hp'
    rw [hprod] at hp
    have hne : (volume.restrict (Ioo (-π) π) : Measure ℝ) ≠ 0 := by
      rw [Ne, Measure.restrict_eq_zero, Real.volume_Ioo]
      simp [Real.pi_pos]
    have : (ae (volume.restrict (Ioo (-π) π) : Measure ℝ)).NeBot := ae_neBot.2 hne
    filter_upwards [Measure.ae_ae_of_ae_prod hp] with r hr
    exact hr.exists.choose_spec
  · intro h
    set M := toMeasurable (volume.restrict (Ioi (0 : ℝ))) {r | ¬ p r} with hM
    have hMm : MeasurableSet M := measurableSet_toMeasurable _ _
    have hM0 : volume.restrict (Ioi (0 : ℝ)) M = 0 := by
      rw [hM, measure_toMeasurable]
      exact h
    have hMsub : {r | ¬ p r} ⊆ M := subset_toMeasurable _ _
    set M' := M ∩ Ioi (0 : ℝ) with hM'
    have hM'0 : volume M' = 0 := by rwa [Measure.restrict_apply hMm] at hM0
    have hM'm : MeasurableSet M' := hMm.inter measurableSet_Ioi
    set S := {x : ℂ | ‖x‖ ∈ M'} with hS
    have hSm : MeasurableSet S := measurable_norm hM'm
    have hS0 : volume S = 0 := by
      have hint := Complex.lintegral_comp_polarCoord_symm (S.indicator 1)
      rw [lintegral_indicator_one hSm] at hint
      rw [← hint]
      have hfst : ∀ᵐ q : ℝ × ℝ, q.1 ∉ M' := by
        rw [Measure.volume_eq_prod]
        exact (Measure.quasiMeasurePreserving_fst).ae
          (measure_eq_zero_iff_ae_notMem.1 hM'0)
      have hz : ∀ᵐ q ∂((volume : Measure (ℝ × ℝ)).restrict Complex.polarCoord.target),
          ENNReal.ofReal q.1 • S.indicator 1 (Complex.polarCoord.symm q) = (0 : ℝ≥0∞) := by
        filter_upwards [ae_restrict_of_ae hfst, ae_restrict_mem htm] with q hq hmem
        rw [Complex.polarCoord_target] at hmem
        have hq1 : 0 < q.1 := hmem.1
        have hnot : Complex.polarCoord.symm q ∉ S := by
          intro hmemS
          rw [hS, Set.mem_ofPred_eq, Complex.norm_polarCoord_symm, abs_of_pos hq1] at hmemS
          exact hq hmemS
        rw [Set.indicator_of_notMem hnot, smul_zero]
      exact (lintegral_congr_ae hz).trans lintegral_zero
    have h0 : volume ({0} : Set ℂ) = 0 := measure_singleton 0
    rw [ae_iff]
    refine measure_mono_null (fun x hx => ?_) (measure_union_null hS0 h0)
    by_cases hx0 : x = 0
    · exact Or.inr hx0
    · refine Or.inl ⟨hMsub hx, ?_⟩
      exact norm_pos_iff.2 hx0

/-- `P_ℓ g = 0` a.e. iff its radial profile `g_ℓ` vanishes a.e. on `(0, ∞)`. -/
private theorem sectorProj_ae_zero_iff (ℓ : ℤ) (g : ℂ → ℂ) :
    sectorProj ℓ g =ᵐ[volume] 0 ↔ Polar.angularSector g ℓ =ᵐ[volume.restrict (Ioi 0)] 0 := by
  have hne : ∀ᵐ x : ℂ, x ≠ 0 := by
    rw [ae_iff]
    simp only [not_not, Set.ofPred_eq_eq_singleton]
    exact measure_singleton 0
  have key : sectorProj ℓ g =ᵐ[volume] 0 ↔ ∀ᵐ x : ℂ, Polar.angularSector g ℓ ‖x‖ = 0 := by
    constructor
    · intro h
      filter_upwards [h, hne] with x hx hx0
      simp only [Pi.zero_apply] at hx
      rw [sectorProj_eq_angularSector ℓ g hx0] at hx
      refine (mul_eq_zero.1 hx).resolve_right fun h0 => ?_
      have h1 := norm_angPhase hx0 ℓ
      rw [h0, norm_zero] at h1
      exact zero_ne_one h1
    · intro h
      filter_upwards [h, hne] with x hx hx0
      rw [Pi.zero_apply, sectorProj_eq_angularSector ℓ g hx0, hx, zero_mul]
  exact key.trans (ae_comp_norm_iff (p := fun r => Polar.angularSector g ℓ r = 0))

/-! ### The interface declarations -/

/-- `m`-fold symmetry iff the sectors outside `mℤ` vanish. -/
theorem isMFoldSymmetricC_iff {m : ℕ} (hm : 0 < m) {g : ℂ → ℂ} (hg : MemLp g 2 volume) :
    IsMFoldSymmetricC m g ↔ ∀ ℓ : ℤ, ¬ (m : ℤ) ∣ ℓ → sectorProj ℓ g =ᵐ[volume] 0 := by
  constructor
  · intro h ℓ hℓ
    exact sectorProj_ae_zero_of_rot h fun h1 => hℓ ((exp_mfold_eq_one_iff hm ℓ).1 h1)
  · intro h
    exact rot_ae_eq_of_sectorProj hg _ fun ℓ hℓ =>
      h ℓ fun h1 => hℓ ((exp_mfold_eq_one_iff hm ℓ).2 h1)

/-- The same in terms of the radial profiles `g_ℓ`. -/
theorem isMFoldSymmetricC_iff_angularSector {m : ℕ} (hm : 0 < m) {g : ℂ → ℂ}
    (hg : MemLp g 2 volume) :
    IsMFoldSymmetricC m g ↔ ∀ ℓ : ℤ, ¬ (m : ℤ) ∣ ℓ →
      Polar.angularSector g ℓ =ᵐ[volume.restrict (Ioi 0)] 0 := by
  rw [isMFoldSymmetricC_iff hm hg]
  exact forall_congr' fun ℓ => imp_congr_right fun _ => sectorProj_ae_zero_iff ℓ g

/-- The statement layer's (real) `m`-fold symmetry in terms of sectors. -/
theorem isMFoldSymmetric_iff_sectorProj {m : ℕ} (hm : 0 < m) {g : ℂ → ℝ}
    (hg : MemLp g 2 volume) :
    IsMFoldSymmetric m g ↔
      ∀ ℓ : ℤ, ¬ (m : ℤ) ∣ ℓ → sectorProj ℓ (fun x => (g x : ℂ)) =ᵐ[volume] 0 := by
  rw [isMFoldSymmetric_iff_C]
  exact isMFoldSymmetricC_iff hm hg.ofReal

/-- A real `L²` function is radial iff all its sectors `ℓ ≠ 0` vanish. -/
theorem isRadial_iff_sectorProj {g : ℂ → ℝ} (hg : MemLp g 2 volume) :
    IsRadial g ↔ ∀ ℓ : ℤ, ℓ ≠ 0 → sectorProj ℓ (fun x => (g x : ℂ)) =ᵐ[volume] 0 := by
  constructor
  · intro h ℓ hℓ
    have hrot : (fun x => (g (rot (π / ℓ) x) : ℂ)) =ᵐ[volume] fun x => (g x : ℂ) := by
      filter_upwards [h (π / ℓ)] with x hx
      rw [hx]
    refine sectorProj_ae_zero_of_rot hrot ?_
    have hℓ' : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ
    have he : (ℓ : ℂ) * ((π / ℓ : ℝ) : ℂ) * Complex.I = π * Complex.I := by
      push_cast
      field_simp
    rw [he, Complex.exp_pi_mul_I]
    norm_num
  · intro h θ
    have h1 := rot_ae_eq_of_sectorProj (hg.ofReal (K := ℂ)) θ fun ℓ hℓ =>
      h ℓ (by rintro rfl; simp at hℓ)
    filter_upwards [h1] with x hx
    exact_mod_cast hx

/-- Conjugation exchanges the sectors `ℓ` and `-ℓ`. -/
theorem angularSector_conj (g : ℂ → ℂ) (ℓ : ℤ) (r : ℝ) :
    Polar.angularSector (fun x => conj (g x)) (-ℓ) r = conj (Polar.angularSector g ℓ r) := by
  unfold Polar.angularSector
  rw [map_mul, ← intervalIntegral.intervalIntegral_conj]
  congr 1
  · simp [Complex.conj_ofReal, map_ofNat]
  · refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [map_mul, ← Complex.exp_conj]
    congr 2
    simp [Complex.conj_ofReal]

theorem sectorProj_conj (g : ℂ → ℂ) (ℓ : ℤ) (x : ℂ) :
    sectorProj (-ℓ) (fun y => conj (g y)) x = conj (sectorProj ℓ g x) := by
  unfold sectorProj
  rw [map_mul, ← intervalIntegral.intervalIntegral_conj]
  congr 1
  · simp [Complex.conj_ofReal, map_ofNat]
  · refine intervalIntegral.integral_congr fun φ _ => ?_
    simp only [map_mul, ← Complex.exp_conj]
    congr 2
    simp [Complex.conj_ofReal]

/-- For real functions, `P_{-ℓ} g = conj (P_ℓ g)`. -/
theorem sectorProj_neg_of_real (g : ℂ → ℝ) (ℓ : ℤ) (x : ℂ) :
    sectorProj (-ℓ) (fun y => (g y : ℂ)) x = conj (sectorProj ℓ (fun y => (g y : ℂ)) x) := by
  rw [← sectorProj_conj]
  simp only [Complex.conj_ofReal]

end NonUniqueEuler.Ang
