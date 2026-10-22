import NonUniqueEuler.Defs.Infra.AngularFourier
import NonUniqueEuler.I.Infra.AngularFourier.Sector
import NonUniqueEuler.I.Infra.AngularFourier.SectorL2
import NonUniqueEuler.I.Infra.Polar.Radial
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv

/-!
# Helper for `P/Infra/AngularFourier/NormEquiv`: radial profiles and sector functions

* null sets of `(0, ∞)` pull back to null sets of `ℂ` under `x ↦ |x|`
  (`ae_norm_of_ae_restrict_Ioi`), hence `ofProfile` respects a.e. equality and supports;
* `P_ℓ g = g_ℓ(|x|) e^{iℓθ}` a.e. (`sectorProj_ae_eq_ofProfile`); a profile whose sector function
  vanishes a.e. vanishes a.e. on `(0, ∞)` (`profile_ae_zero`);
* the sectors of `h(r) e^{iℓθ}` and of finite sector sums;
* `secNormSq` only depends on the profile on `(0, ∞)`; it vanishes for the zero profile;
* `P_ℓ` is a.e. additive on `L²`; `L²` on an open set gives local integrability.
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace NonUniqueEuler.Ang.NormEquivAux

open Sob

theorem ae_ne_zero : ∀ᵐ x : ℂ, x ≠ 0 := by
  simpa using (Set.countable_singleton (0 : ℂ)).ae_notMem volume

/-- A property holding for a.e. `r > 0` holds at `|x|` for a.e. `x ∈ ℂ`. -/
theorem ae_norm_of_ae_restrict_Ioi {P : ℝ → Prop}
    (h : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), P r) : ∀ᵐ x : ℂ, P ‖x‖ := by
  have h0 : (volume.restrict (Ioi (0 : ℝ))) {r | ¬ P r} = 0 := ae_iff.1 h
  obtain ⟨T, hT, hTm, hT0⟩ := exists_measurable_superset_of_null h0
  have hmeas : MeasurableSet (T ∩ Ioi (0 : ℝ)) := hTm.inter measurableSet_Ioi
  have hpre : volume {x : ℂ | ‖x‖ ∈ T ∩ Ioi 0} = 0 := by
    have hpm : MeasurableSet {x : ℂ | ‖x‖ ∈ T ∩ Ioi 0} :=
      hmeas.preimage continuous_norm.measurable
    have h1 := Polar.lintegral_comp_norm (f := (T ∩ Ioi (0 : ℝ)).indicator 1)
      (measurable_one.indicator hmeas)
    have hL : ∫⁻ x : ℂ, (T ∩ Ioi (0 : ℝ)).indicator 1 ‖x‖ =
        volume {x : ℂ | ‖x‖ ∈ T ∩ Ioi 0} := by
      rw [← lintegral_indicator_one hpm]
      rfl
    have hR : ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * (T ∩ Ioi (0 : ℝ)).indicator 1 r = 0 := by
      have hz : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), r ∉ T :=
        measure_eq_zero_iff_ae_notMem.1 hT0
      rw [← lintegral_zero]
      refine lintegral_congr_ae ?_
      filter_upwards [hz] with r hr
      simp [indicator, hr]
    rw [← hL, h1, hR, mul_zero]
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hpre, ae_ne_zero] with x hx hx0
  by_contra hP
  apply hx
  exact ⟨hT hP, norm_pos_iff.2 hx0⟩

theorem ofProfile_congr_ae {ℓ : ℤ} {f f' : ℝ → ℂ}
    (h : f =ᵐ[volume.restrict (Ioi 0)] f') : ofProfile ℓ f =ᵐ[volume] ofProfile ℓ f' := by
  filter_upwards [ae_norm_of_ae_restrict_Ioi h] with x hx
  simp [ofProfile, hx]

/-- A profile vanishing outside `[ρ₋, ρ₊]` gives a sector function vanishing outside `N_*`. -/
theorem ofProfile_eq_zero_outside {ℓ : ℤ} {ρm ρp : ℝ} {h : ℝ → ℂ}
    (hh : ∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc ρm ρp → h r = 0) :
    ∀ᵐ x, ¬ (ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp) → ofProfile ℓ h x = 0 := by
  filter_upwards [ae_norm_of_ae_restrict_Ioi hh] with x hx hxK
  simp [ofProfile, hx (by simpa [mem_Icc] using hxK)]

theorem ofProfile_sub (ℓ : ℤ) (f g : ℝ → ℂ) :
    ofProfile ℓ (fun r => f r - g r) = fun x => ofProfile ℓ f x - ofProfile ℓ g x := by
  funext x
  simp [ofProfile, sub_mul]

theorem ofProfile_const_mul (ℓ : ℤ) (c : ℂ) (f : ℝ → ℂ) :
    ofProfile ℓ (fun r => c * f r) = fun x => c * ofProfile ℓ f x := by
  funext x
  simp [ofProfile, mul_assoc]

/-- `P_ℓ g = g_ℓ(|x|) e^{iℓθ}` almost everywhere. -/
theorem sectorProj_ae_eq_ofProfile (ℓ : ℤ) (g : ℂ → ℂ) :
    sectorProj ℓ g =ᵐ[volume] ofProfile ℓ (Polar.angularSector g ℓ) := by
  filter_upwards [ae_ne_zero] with x hx
  rw [sectorProj_eq_angularSector ℓ g hx]
  rfl

/-- If `f(|x|) e^{iℓθ} = 0` a.e. on `ℂ`, then `f = 0` a.e. on `(0, ∞)`. -/
theorem profile_ae_zero {ℓ : ℤ} {f : ℝ → ℂ} (hm : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (h0 : ofProfile ℓ f =ᵐ[volume] 0) : f =ᵐ[volume.restrict (Ioi 0)] 0 := by
  obtain ⟨hiff, hnorm⟩ := memLp_ofProfile_iff (ℓ := ℓ) hm
  have hmem : MemLp (ofProfile ℓ f) 2 volume :=
    MemLp.ae_eq h0.symm (MemLp.zero : MemLp (0 : ℂ → ℂ) 2 volume)
  have hint := hiff.1 hmem
  have hl2 : Sob.l2 (ofProfile ℓ f) = 0 := by
    simp [Sob.l2, eLpNorm_congr_ae h0]
  rw [hl2] at hnorm
  have hI : ∫ r in Ioi 0, ‖f r‖ ^ 2 * r = 0 := by
    have hpi : (0 : ℝ) < 2 * π := by positivity
    have : 2 * π * ∫ r in Ioi 0, ‖f r‖ ^ 2 * r = 0 := by
      rw [← hnorm]; norm_num
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact h
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi 0)] fun r => ‖f r‖ ^ 2 * r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_nonneg (sq_nonneg _) (le_of_lt hr)
  have hz := (integral_eq_zero_iff_of_nonneg_ae hnn hint).1 hI
  filter_upwards [hz, ae_restrict_mem measurableSet_Ioi] with r hr hr0
  have hr0' : (r : ℝ) ≠ 0 := ne_of_gt hr0
  simp only [Pi.zero_apply, mul_eq_zero, hr0', or_false, pow_eq_zero_iff, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, norm_eq_zero] at hr
  simpa using hr

theorem angPhase_ofReal {r : ℝ} (hr : 0 < r) (m : ℤ) : angPhase m (r : ℂ) = 1 := by
  have h1 : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_of_nonneg hr.le]
  rw [angPhase, h1, div_self (Complex.ofReal_ne_zero.2 hr.ne'), one_zpow]

/-- The sectors of `h(r) e^{iℓθ}`: `h` in sector `ℓ`, `0` elsewhere (at every `r > 0`). -/
theorem angularSector_ofProfile (ℓ m : ℤ) (h : ℝ → ℂ) {r : ℝ} (hr : 0 < r) :
    Polar.angularSector (ofProfile ℓ h) m r = if m = ℓ then h r else 0 := by
  have hx : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  have h1 := sectorProj_eq_angularSector m (ofProfile ℓ h) hx
  have hn : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_of_nonneg hr.le]
  rw [sectorProj_ofProfile, hn, angPhase_ofReal hr, mul_one] at h1
  rw [← h1]
  split_ifs
  · simp [ofProfile, angPhase_ofReal hr, abs_of_pos hr]
  · rfl

/-- Weak derivatives on `V` only depend on the function a.e. on `V`. -/
theorem weakDerivOn_congr_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]
    {V : Set E} {vs : List E} {f f' : E → ℂ} (hfg : ∀ᵐ x, x ∈ V → f x = f' x) :
    weakDerivOn V vs f = weakDerivOn V vs f' := by
  have key : HasWeakDerivOn V vs f = HasWeakDerivOn V vs f' := by
    funext g
    have hI : ∀ φ : E → ℂ, IsTestFn V φ →
        ∫ x, f x * iterDirDeriv vs φ x = ∫ x, f' x * iterDirDeriv vs φ x := by
      intro φ hφ
      refine integral_congr_ae ?_
      filter_upwards [hfg] with x hx
      by_cases hxV : x ∈ V
      · rw [hx hxV]
      · have : iterDirDeriv vs φ x = 0 :=
          image_eq_zero_of_notMem_tsupport fun h => hxV ((hφ.iterDirDeriv vs).subset h)
        rw [this, mul_zero, mul_zero]
    apply propext
    constructor
    · intro H φ hφ
      rw [← hI φ hφ]
      exact H φ hφ
    · intro H φ hφ
      rw [hI φ hφ]
      exact H φ hφ
  unfold weakDerivOn
  rw [key]

/-- `‖g‖_{k,ℓ;I}` only depends on `g` on `(0, ∞)`. -/
theorem secNormSq_congr {k : ℕ} {ℓ : ℤ} {I : Set ℝ} {f f' : ℝ → ℂ}
    (hfg : ∀ r, 0 < r → f r = f' r) : secNormSq k ℓ I f = secNormSq k ℓ I f' := by
  have h : ∀ᵐ x : ℝ, x ∈ Ioi 0 → f x = f' x := Filter.Eventually.of_forall fun r hr => hfg r hr
  unfold secNormSq
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [weakDeriv1On, weakDerivOn_congr_ae h]
  rfl

theorem hasWeakDerivOn_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]
    (V : Set E) (vs : List E) : HasWeakDerivOn V vs (fun _ => (0 : ℂ)) (fun _ => 0) := by
  intro φ _
  simp

theorem weakDeriv1On_zero_ae (j : ℕ) :
    ∀ᵐ r, r ∈ Ioi (0 : ℝ) → weakDeriv1On (Ioi 0) j (fun _ => (0 : ℂ)) r = 0 :=
  weakDerivOn_ae_eq isOpen_Ioi (locallyIntegrableOn_zero) (hasWeakDerivOn_zero _ _)

theorem secNormSq_zero_fun {k : ℕ} {ℓ : ℤ} {I : Set ℝ} (hIm : MeasurableSet I)
    (hI : I ⊆ Ioi 0) : secNormSq k ℓ I (fun _ => (0 : ℂ)) = 0 := by
  unfold secNormSq
  refine Finset.sum_eq_zero fun j _ => ?_
  have h0 : ∫ r in I, ‖weakDeriv1On (Ioi 0) j (fun _ => (0 : ℂ)) r‖ ^ 2 * r = 0 := by
    refine integral_eq_zero_of_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' hIm]
    filter_upwards [weakDeriv1On_zero_ae j] with r hr hrI
    simp [hr (hI hrI)]
  rw [h0, mul_zero]

/-- `‖·‖_{k,m}` of the `m`-th sector of `h(r)e^{iℓθ}`. -/
theorem secNormSq_angularSector_ofProfile {k : ℕ} {I : Set ℝ} (hIm : MeasurableSet I)
    (hI : I ⊆ Ioi 0) (ℓ m : ℤ) (h : ℝ → ℂ) :
    secNormSq k m I (Polar.angularSector (ofProfile ℓ h) m) =
      if m = ℓ then secNormSq k ℓ I h else 0 := by
  split_ifs with hm
  · subst hm
    refine secNormSq_congr fun r hr => ?_
    rw [angularSector_ofProfile _ _ h hr]
    simp
  · rw [← secNormSq_zero_fun (k := k) (ℓ := m) hIm hI]
    refine secNormSq_congr fun r hr => ?_
    rw [angularSector_ofProfile _ _ h hr]
    simp [hm]

theorem continuous_angPhase_rot (m : ℤ) (x : ℂ) :
    Continuous fun φ : ℝ => angPhase m (rot φ x) := by
  by_cases hx : x = 0
  · subst hx
    simp only [rot, mul_zero]
    exact continuous_const
  · have h1 : (fun φ : ℝ => angPhase m (rot φ x)) =
        fun φ : ℝ => (Complex.exp ((φ : ℂ) * Complex.I) * x / (‖x‖ : ℂ)) ^ m := by
      funext φ
      rw [angPhase, Polar.norm_rot]
      rfl
    rw [h1]
    refine Continuous.zpow₀ ?_ m fun φ => Or.inl ?_
    · exact ((Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)).mul
        continuous_const).div_const _
    · refine div_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) hx) ?_
      exact Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hx)

theorem intervalIntegrable_sectorProj_ofProfile (ℓ m : ℤ) (h : ℝ → ℂ) (x : ℂ) :
    IntervalIntegrable (fun φ : ℝ => Complex.exp (-((ℓ : ℂ) * φ * Complex.I)) *
      ofProfile m h (rot φ x)) volume 0 (2 * π) := by
  refine Continuous.intervalIntegrable ?_ _ _
  have h1 : (fun φ : ℝ => Complex.exp (-((ℓ : ℂ) * φ * Complex.I)) * ofProfile m h (rot φ x)) =
      fun φ : ℝ => Complex.exp (-((ℓ : ℂ) * φ * Complex.I)) * (h ‖x‖ * angPhase m (rot φ x)) := by
    funext φ
    rw [ofProfile, Polar.norm_rot]
  rw [h1]
  refine Continuous.mul ?_ (continuous_const.mul (continuous_angPhase_rot m x))
  exact Complex.continuous_exp.comp
    (((continuous_const.mul Complex.continuous_ofReal).mul continuous_const).neg)

/-- `P_ℓ` of a finite sector sum. -/
theorem sectorProj_sum_ofProfile (ℓ : ℤ) (S : Finset ℤ) (h : ℤ → ℝ → ℂ) :
    sectorProj ℓ (∑ m ∈ S, ofProfile m (h m)) = if ℓ ∈ S then ofProfile ℓ (h ℓ) else 0 := by
  have hlin : ∀ x, sectorProj ℓ (∑ m ∈ S, ofProfile m (h m)) x =
      ∑ m ∈ S, sectorProj ℓ (ofProfile m (h m)) x := by
    intro x
    simp only [sectorProj, Finset.sum_apply, Finset.mul_sum]
    rw [intervalIntegral.integral_finsetSum]
    · rw [Finset.mul_sum]
    · intro m _
      exact intervalIntegrable_sectorProj_ofProfile ℓ m (h m) x
  funext x
  rw [hlin]
  simp only [sectorProj_ofProfile]
  simp only [ite_apply, Pi.zero_apply]
  rw [Finset.sum_ite_eq]

/-- `P_ℓ` is a.e. additive on `L²`. -/
theorem sectorProj_sub_ae (ℓ : ℤ) {f g : ℂ → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    sectorProj ℓ (f - g) =ᵐ[volume] sectorProj ℓ f - sectorProj ℓ g := by
  have h1 := sectorProjL_spec ℓ (hf.toLp f - hg.toLp g)
  rw [map_sub] at h1
  have h2 : sectorProj ℓ ⇑(hf.toLp f - hg.toLp g) =ᵐ[volume] sectorProj ℓ (f - g) :=
    sectorProj_congr_ae ℓ ((Lp.coeFn_sub _ _).trans (hf.coeFn_toLp.sub hg.coeFn_toLp))
  have h3 := Lp.coeFn_sub (sectorProjL ℓ (hf.toLp f)) (sectorProjL ℓ (hg.toLp g))
  have h4 := sectorProjL_spec ℓ (hf.toLp f)
  have h5 := sectorProjL_spec ℓ (hg.toLp g)
  have h6 := sectorProj_congr_ae ℓ hf.coeFn_toLp
  have h7 := sectorProj_congr_ae ℓ hg.coeFn_toLp
  filter_upwards [h1, h2, h3, h4, h5, h6, h7] with x e1 e2 e3 e4 e5 e6 e7
  rw [← e2, ← e1, e3, Pi.sub_apply, e4, e5, e6, e7, Pi.sub_apply]

/-- `L²` on an open subset of the line gives local integrability there. -/
theorem locallyIntegrableOn_of_memLp_restrict {V : Set ℝ} (hV : IsOpen V) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict V)) : LocallyIntegrableOn f V := by
  rw [locallyIntegrableOn_iff hV.isLocallyClosed]
  intro K hKV hK
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  exact (hf.mono_measure (Measure.restrict_mono hKV le_rfl)).integrable one_le_two

end NonUniqueEuler.Ang.NormEquivAux
