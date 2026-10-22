import Mathlib.Algebra.Order.Field.Pointwise
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.ConstMulAction
import NonUniqueEuler.Defs.Infra.SobolevOneD
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv

/-!
# Helper: dilations `f ↦ f(c ·)` of profiles on `(0, ∞)`

Helper for `P/Infra/FaaDiBruno/ExpPhase.lean`. For `c > 0` the dilation `f ↦ f(c ·)` maps
`(0, ∞)` onto itself. We prove:
* `map_mul_restrict_Ioi`: the push-forward of `dr|_{(0,∞)}` under `x ↦ c x` is `c⁻¹ dr|_{(0,∞)}`;
  hence dilations preserve a.e. statements (`ae_comp_mul`) and `L^p((0,∞))` (`memLp_comp_mul`);
* `hasWeakDerivOn_comp_mul`: if `h = ∂^j f` weakly on `(0, ∞)`, then `c^j h(c ·) = ∂^j (f(c ·))`;
* `memH1On_comp_mul`, `weakDeriv1On_comp_mul_ae`: `H^k((0,∞))` is dilation invariant and the
  chosen weak derivatives transform accordingly;
* `secNormSq_comp_mul`: the change of variables in the weighted norms `‖·‖_{k,ℓ;[a,b]}`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff Pointwise

namespace NonUniqueEuler.FaaDiBruno.ExpPhaseAux

open NonUniqueEuler.Sob

variable {c : ℝ}

theorem preimage_mul_Ioi (hc : 0 < c) : (fun x : ℝ => c * x) ⁻¹' Ioi 0 = Ioi 0 := by
  ext x
  simp [mul_pos_iff_of_pos_left hc]

/-- The push-forward of `dr|_{(0,∞)}` under `x ↦ c x`. -/
theorem map_mul_restrict_Ioi (hc : 0 < c) :
    Measure.map (fun x => c * x) (volume.restrict (Ioi (0 : ℝ))) =
      ENNReal.ofReal c⁻¹ • volume.restrict (Ioi (0 : ℝ)) := by
  calc Measure.map (fun x => c * x) (volume.restrict (Ioi (0 : ℝ)))
      = Measure.map (fun x => c * x)
          (volume.restrict ((fun x : ℝ => c * x) ⁻¹' Ioi 0)) := by rw [preimage_mul_Ioi hc]
    _ = (Measure.map (fun x => c * x) volume).restrict (Ioi (0 : ℝ)) :=
        (Measure.restrict_map (measurable_const_mul c) measurableSet_Ioi).symm
    _ = ENNReal.ofReal c⁻¹ • volume.restrict (Ioi (0 : ℝ)) := by
        rw [Real.map_volume_mul_left hc.ne', Measure.restrict_smul, abs_of_pos (inv_pos.2 hc)]

theorem ae_comp_mul (hc : 0 < c) {p : ℝ → Prop}
    (h : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), p r) :
    ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), p (c * x) := by
  have h' : ∀ᵐ r ∂(Measure.map (fun x => c * x) (volume.restrict (Ioi (0 : ℝ)))), p r := by
    rw [map_mul_restrict_Ioi hc,
      Measure.ae_ennreal_smul_measure_eq (ENNReal.ofReal_pos.2 (inv_pos.2 hc)).ne']
    exact h
  exact ae_of_ae_map (measurable_const_mul c).aemeasurable h'

/-- The same, for statements of the form `∀ᵐ r, r ∈ (0, ∞) → p r`. -/
theorem ae_comp_mul' (hc : 0 < c) {p : ℝ → Prop} (h : ∀ᵐ r, r ∈ Ioi (0 : ℝ) → p r) :
    ∀ᵐ x, x ∈ Ioi (0 : ℝ) → p (c * x) := by
  rw [← ae_restrict_iff' measurableSet_Ioi] at h ⊢
  exact ae_comp_mul hc h

theorem memLp_comp_mul (hc : 0 < c) {f : ℝ → ℂ} {p : ℝ≥0∞}
    (hf : MemLp f p (volume.restrict (Ioi (0 : ℝ)))) :
    MemLp (fun x => f (c * x)) p (volume.restrict (Ioi (0 : ℝ))) := by
  have h1 : MemLp f p (Measure.map (fun x => c * x) (volume.restrict (Ioi (0 : ℝ)))) := by
    rw [map_mul_restrict_Ioi hc]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact h1.comp_of_map (measurable_const_mul c).aemeasurable

/-- An `L²((0,∞))` function is locally integrable on `(0, ∞)`. -/
theorem locallyIntegrableOn_of_memLp {h : ℝ → ℂ}
    (hL2 : MemLp h 2 (volume.restrict (Ioi (0 : ℝ)))) : LocallyIntegrableOn h (Ioi (0 : ℝ)) := by
  have h1 : LocallyIntegrable h (volume.restrict (Ioi (0 : ℝ))) :=
    hL2.locallyIntegrable (by norm_num)
  rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
  intro K hK hKc
  have h2 : IntegrableOn h K (volume.restrict (Ioi (0 : ℝ))) := h1.integrableOn_isCompact hKc
  rwa [IntegrableOn, Measure.restrict_restrict_of_subset hK] at h2

theorem isTestFn_comp_mul (hc : 0 < c) {ψ : ℝ → ℂ} (hψ : IsTestFn (Ioi (0 : ℝ)) ψ) :
    IsTestFn (Ioi (0 : ℝ)) (fun y => ψ (c * y)) := by
  have hs : ContDiff ℝ ∞ (fun y => ψ (c * y)) :=
    hψ.smooth.comp (contDiff_const.mul contDiff_id)
  have hcs : HasCompactSupport (fun y => ψ (c * y)) :=
    HasCompactSupport.comp_smul (G₀ := ℝ) hψ.compact hc.ne'
  refine ⟨hs, hcs, ?_⟩
  have e : (fun y => ψ (c * y)) = ψ ∘ (Homeomorph.mulLeft₀ c hc.ne') := rfl
  rw [e, tsupport_comp_eq_preimage]
  intro y hy
  have h1 : c * y ∈ Ioi (0 : ℝ) := hψ.subset hy
  exact (mul_pos_iff_of_pos_left hc).1 h1

/-- Dilation of weak derivatives on `(0, ∞)`: if `g = ∂^j f` weakly, then
`c^j g(c ·) = ∂^j (f(c ·))` weakly. -/
theorem hasWeakDerivOn_comp_mul (hc : 0 < c) {j : ℕ} {f g : ℝ → ℂ}
    (h : HasWeakDerivOn (Ioi (0 : ℝ)) (derivList j) f g) :
    HasWeakDerivOn (Ioi (0 : ℝ)) (derivList j) (fun x => f (c * x))
      (fun x => (c : ℂ) ^ j * g (c * x)) := by
  intro ψ hψ
  set ψ' : ℝ → ℂ := fun y => ψ (c⁻¹ * y) with hψ'_def
  have hψ'T : IsTestFn (Ioi (0 : ℝ)) ψ' := isTestFn_comp_mul (inv_pos.2 hc) hψ
  have key := h ψ' hψ'T
  rw [iterDirDeriv_derivList] at key ⊢
  have hd : iteratedDeriv j ψ' = fun y => c⁻¹ ^ j • iteratedDeriv j ψ (c⁻¹ * y) :=
    iteratedDeriv_comp_const_smul (hψ.smooth.of_le (by exact_mod_cast le_top)) c⁻¹
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  -- left side as an integral of a dilated function
  have eL : (fun x => f (c * x) * iteratedDeriv j ψ x) =
      fun x => (fun y => (c : ℂ) ^ j * (f y * iteratedDeriv j ψ' y)) (c * x) := by
    funext x
    simp only [hd, inv_mul_cancel_left₀ hc.ne', Complex.real_smul]
    push_cast
    rw [inv_pow]
    field_simp
  have eR : (fun x => (c : ℂ) ^ j * g (c * x) * ψ x) =
      fun x => (fun y => (c : ℂ) ^ j * (g y * ψ' y)) (c * x) := by
    funext x
    simp only [hψ'_def, inv_mul_cancel_left₀ hc.ne']
    ring
  rw [eL, eR, Measure.integral_comp_mul_left (fun y => (c : ℂ) ^ j * (f y * iteratedDeriv j ψ' y)) c,
    Measure.integral_comp_mul_left (fun y => (c : ℂ) ^ j * (g y * ψ' y)) c,
    integral_const_mul, integral_const_mul, key]
  simp only [Complex.real_smul]
  ring

/-- `H^k((0, ∞))` is invariant under dilations. -/
theorem memH1On_comp_mul (hc : 0 < c) {k : ℕ} {f : ℝ → ℂ} (hf : MemH1On k (Ioi 0) f) :
    MemH1On k (Ioi 0) (fun x => f (c * x)) := by
  refine ⟨memLp_comp_mul hc hf.memLp, fun j hj => ?_⟩
  obtain ⟨h, hL2, hw⟩ := hf.deriv j hj
  exact ⟨_, (memLp_comp_mul hc hL2).const_mul _, hasWeakDerivOn_comp_mul hc hw⟩

/-- The chosen weak derivatives of a dilation. -/
theorem weakDeriv1On_comp_mul_ae (hc : 0 < c) {k : ℕ} {f : ℝ → ℂ} (hf : MemH1On k (Ioi 0) f)
    {j : ℕ} (hj : j ≤ k) :
    ∀ᵐ x, x ∈ Ioi (0 : ℝ) → weakDeriv1On (Ioi 0) j (fun x => f (c * x)) x =
      (c : ℂ) ^ j * weakDeriv1On (Ioi 0) j f (c * x) := by
  obtain ⟨h, hL2, hw⟩ := hf.deriv j hj
  have h1 : ∀ᵐ r, r ∈ Ioi (0 : ℝ) → weakDeriv1On (Ioi 0) j f r = h r :=
    weakDerivOn_ae_eq isOpen_Ioi (locallyIntegrableOn_of_memLp hL2) hw
  have hL2' : MemLp (fun x => (c : ℂ) ^ j * h (c * x)) 2 (volume.restrict (Ioi (0 : ℝ))) :=
    (memLp_comp_mul hc hL2).const_mul _
  have h2 : ∀ᵐ x, x ∈ Ioi (0 : ℝ) →
      weakDeriv1On (Ioi 0) j (fun x => f (c * x)) x = (c : ℂ) ^ j * h (c * x) :=
    weakDerivOn_ae_eq isOpen_Ioi (locallyIntegrableOn_of_memLp hL2')
      (hasWeakDerivOn_comp_mul hc hw)
  have h1' := ae_comp_mul' hc h1
  filter_upwards [h1', h2] with x hx1 hx2 hx
  rw [hx2 hx, hx1 hx]

/-- Change of variables in the weighted integrals. -/
theorem setIntegral_Icc_comp_mul (hc : 0 < c) (w : ℝ → ℂ) (a b : ℝ) :
    ∫ x in Icc a b, ‖w (c * x)‖ ^ 2 * x =
      (c ^ 2)⁻¹ * ∫ r in Icc (c * a) (c * b), ‖w r‖ ^ 2 * r := by
  have h := Measure.setIntegral_comp_smul_of_pos volume (fun r => ‖w r‖ ^ 2 * r) (Icc a b) hc
  rw [LinearOrderedField.smul_Icc hc] at h
  simp only [smul_eq_mul, Module.finrank_self, pow_one] at h
  have e : ∫ x in Icc a b, ‖w (c * x)‖ ^ 2 * (c * x) =
      c * ∫ x in Icc a b, ‖w (c * x)‖ ^ 2 * x := by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [e] at h
  have hc0 : c ≠ 0 := hc.ne'
  calc ∫ x in Icc a b, ‖w (c * x)‖ ^ 2 * x
      = c⁻¹ * (c * ∫ x in Icc a b, ‖w (c * x)‖ ^ 2 * x) := by field_simp
    _ = (c ^ 2)⁻¹ * ∫ r in Icc (c * a) (c * b), ‖w r‖ ^ 2 * r := by
        rw [h]
        field_simp

/-- The weighted norms of a dilation. -/
theorem secNormSq_comp_mul (hc : 0 < c) {k : ℕ} {f : ℝ → ℂ} (hf : MemH1On k (Ioi 0) f)
    (ℓ : ℤ) {a b : ℝ} (ha : 0 < a) :
    secNormSq k ℓ (Icc a b) (fun x => f (c * x)) = ∑ j ∈ Finset.range (k + 1),
      secWeight k j ℓ * (c ^ (2 * j) * (c ^ 2)⁻¹ *
        ∫ r in Icc (c * a) (c * b), ‖weakDeriv1On (Ioi 0) j f r‖ ^ 2 * r) := by
  unfold secNormSq
  refine Finset.sum_congr rfl fun j hj => ?_
  congr 1
  have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have hae := weakDeriv1On_comp_mul_ae hc hf hjk
  have hcongr : ∫ x in Icc a b, ‖weakDeriv1On (Ioi 0) j (fun x => f (c * x)) x‖ ^ 2 * x =
      ∫ x in Icc a b, ‖(c : ℂ) ^ j * weakDeriv1On (Ioi 0) j f (c * x)‖ ^ 2 * x := by
    refine setIntegral_congr_ae measurableSet_Icc ?_
    filter_upwards [hae] with x hx hxI
    rw [hx (lt_of_lt_of_le ha hxI.1)]
  rw [hcongr]
  have e : ∀ x : ℝ, ‖(c : ℂ) ^ j * weakDeriv1On (Ioi 0) j f (c * x)‖ ^ 2 * x =
      c ^ (2 * j) * (‖weakDeriv1On (Ioi 0) j f (c * x)‖ ^ 2 * x) := by
    intro x
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    ring
  simp_rw [e]
  rw [integral_const_mul, setIntegral_Icc_comp_mul hc]
  ring

end NonUniqueEuler.FaaDiBruno.ExpPhaseAux
