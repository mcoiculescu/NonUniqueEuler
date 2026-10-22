import NonUniqueEuler.Defs.Infra.JointRep
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Proof of (I-JOINT): a.e. equality, integrability and integrals on the slab `(0, T) × ℂ`

Proof of `NonUniqueEuler/I/Infra/JointRep/Slab.lean` (same declarations, same statements).
Everything is Fubini–Tonelli on the slab, after rewriting the slab measure as the product
measure with `volume_restrict_slab`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace NonUniqueEuler.JointRep

variable {T : ℝ}

/-- Slice-wise a.e. equality gives a.e. equality on the slab (for a.e. strongly measurable
functions). -/
theorem ae_eq_slab_of_ae_ae {U V : ℝ → ℂ → ℝ}
    (hU : AEStronglyMeasurable (Function.uncurry U) (volume.restrict (slab T)))
    (hV : AEStronglyMeasurable (Function.uncurry V) (volume.restrict (slab T)))
    (h : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)), U t =ᵐ[volume] V t) :
    Function.uncurry U =ᵐ[volume.restrict (slab T)] Function.uncurry V := by
  rw [volume_restrict_slab] at hU hV ⊢
  -- pass to the strongly measurable versions `hU.mk _`, `hV.mk _`
  have hUm : Measurable (hU.mk (Function.uncurry U)) := hU.stronglyMeasurable_mk.measurable
  have hVm : Measurable (hV.mk (Function.uncurry V)) := hV.stronglyMeasurable_mk.measurable
  have hUe := Measure.ae_ae_of_ae_prod hU.ae_eq_mk
  have hVe := Measure.ae_ae_of_ae_prod hV.ae_eq_mk
  have hmeas : MeasurableSet
      {p : ℝ × ℂ | hU.mk (Function.uncurry U) p = hV.mk (Function.uncurry V) p} :=
    measurableSet_eq_fun hUm hVm
  have hUV' : hU.mk (Function.uncurry U)
      =ᵐ[(volume.restrict (Ioo (0 : ℝ) T)).prod (volume : Measure ℂ)]
        hV.mk (Function.uncurry V) := by
    refine (Measure.ae_prod_iff_ae_ae hmeas).2 ?_
    filter_upwards [h, hUe, hVe] with t ht htU htV
    filter_upwards [ht, htU, htV] with x hx hxU hxV
    simp only [Function.uncurry_apply_pair] at hxU hxV
    rw [← hxU, ← hxV, hx]
  exact hU.ae_eq_mk.trans (hUV'.trans hV.ae_eq_mk.symm)

/-- A.e. equality on the slab gives slice-wise a.e. equality for a.e. time. -/
theorem ae_ae_of_ae_eq_slab {U V : ℝ → ℂ → ℝ}
    (h : Function.uncurry U =ᵐ[volume.restrict (slab T)] Function.uncurry V) :
    ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)), U t =ᵐ[volume] V t := by
  rw [volume_restrict_slab] at h
  exact Measure.ae_ae_eq_of_ae_eq_uncurry h

/-- Two jointly measurable representatives of the same path agree a.e. on the slab. -/
theorem IsJointRep.ae_eq_slab {U V : ℝ → ℂ → ℝ} {u : ℝ → Lp ℝ 2 (volume : Measure ℂ)}
    (hU : IsJointRep U u (Ioo 0 T)) (hV : IsJointRep V u (Ioo 0 T)) :
    Function.uncurry U =ᵐ[volume.restrict (slab T)] Function.uncurry V := by
  refine ae_eq_slab_of_ae_ae hU.measurable.aestronglyMeasurable
    hV.measurable.aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => ?_
  exact (hU.ae_eq t ht).trans (hV.ae_eq t ht).symm

/-- A representative of `u` agrees a.e. on the slab with any a.e. strongly measurable `ω` whose
slices represent `u t` for a.e. `t ∈ (0, T)`. -/
theorem IsJointRep.ae_eq_slab_of_ae {U ω : ℝ → ℂ → ℝ} {u : ℝ → Lp ℝ 2 (volume : Measure ℂ)}
    (hU : IsJointRep U u (Ioo 0 T))
    (hω : AEStronglyMeasurable (Function.uncurry ω) (volume.restrict (slab T)))
    (h : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)), ω t =ᵐ[volume] u t) :
    Function.uncurry U =ᵐ[volume.restrict (slab T)] Function.uncurry ω := by
  refine ae_eq_slab_of_ae_ae hU.measurable.aestronglyMeasurable hω ?_
  have hmem : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)), t ∈ Ioo (0 : ℝ) T :=
    ae_restrict_mem measurableSet_Ioo
  filter_upwards [h, hmem] with t ht htm
  exact (hU.ae_eq t htm).trans ht.symm

/-- Integrability on the slab, Fubini–Tonelli form. -/
theorem integrableOn_slab_iff {F : ℝ × ℂ → ℝ}
    (hF : AEStronglyMeasurable F (volume.restrict (slab T))) :
    IntegrableOn F (slab T) ↔
      (∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)), Integrable fun x : ℂ => F (t, x)) ∧
        Integrable (fun t => ∫ x : ℂ, ‖F (t, x)‖) (volume.restrict (Ioo (0 : ℝ) T)) := by
  rw [volume_restrict_slab] at hF
  rw [IntegrableOn, volume_restrict_slab]
  exact integrable_prod_iff hF

/-- The integral over the slab as an iterated integral (Fubini). -/
theorem integral_slab_eq {F : ℝ × ℂ → ℝ} (hF : IntegrableOn F (slab T)) :
    ∫ p in slab T, F p = ∫ t in Ioo (0 : ℝ) T, ∫ x : ℂ, F (t, x) := by
  rw [IntegrableOn, volume_restrict_slab] at hF
  rw [volume_restrict_slab]
  exact integral_prod F hF

/-- `t ↦ ∫ F(t, x) dx` is a.e. strongly measurable on `(0, T)`. -/
theorem aestronglyMeasurable_integral_slab {F : ℝ × ℂ → ℝ}
    (hF : AEStronglyMeasurable F (volume.restrict (slab T))) :
    AEStronglyMeasurable (fun t => ∫ x : ℂ, F (t, x)) (volume.restrict (Ioo (0 : ℝ) T)) := by
  rw [volume_restrict_slab] at hF
  exact hF.integral_prod_right'

end NonUniqueEuler.JointRep
