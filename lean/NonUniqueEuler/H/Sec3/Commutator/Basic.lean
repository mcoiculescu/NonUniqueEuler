import NonUniqueEuler.Defs.Sec3.Commutator
import NonUniqueEuler.Defs.Infra.Instances
import NonUniqueEuler.I.Sec3.CommFormula
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Helpers for `P/Sec3/Commutator.lean`: integrability and measurability at a fixed time

* `locallyIntegrable_of_ball`, `integrableOn_ball_of_memLp_two`: `L²` on every ball gives
  `L¹_loc`;
* `SliceHyp`-style consequences of the fixed-time hypotheses
  (`u(t) ∈ L²(B_r)`, `w(t) ∈ L²(B_r)` for all `r`): `u(t)`, `u(t)w(t)` are locally integrable,
  `w(t)` is a.e. strongly measurable;
* `aestronglyMeasurable_commEps`: `x ↦ C_ε[u,w](t,x)` is a.e. strongly measurable (the first
  term is `D(u(t) ⋆ ρ_ε)(x)(w(t,x))` with a continuous derivative, the second is a convolution
  of `u(t)w(t) ∈ L¹_loc` with the continuous compactly supported `Dρ_ε`).

Helper names live in the namespace `NonUniqueEuler.Weak.CommutatorH` (no clash in the full
library). Instances: `IsFiniteMeasure (volume.restrict (ball x r))` comes
from `Defs/Infra/Instances` and `ENNReal.HolderTriple 2 2 1` from Mathlib
(`ENNReal.HolderConjugate.instTwoTwo`); this file declares no instance.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal Convolution

namespace NonUniqueEuler.Weak.CommutatorH

theorem locallyIntegrable_of_ball {E : Type*} [NormedAddCommGroup E] {f : ℂ → E}
    (h : ∀ r : ℝ, 0 < r → IntegrableOn f (ball (0 : ℂ) r) volume) :
    LocallyIntegrable f volume := by
  rw [locallyIntegrable_iff]
  intro k hk
  obtain ⟨r, hr⟩ := hk.isBounded.subset_ball (0 : ℂ)
  exact (h (max r 1) (lt_of_lt_of_le one_pos (le_max_right _ _))).mono_set
    (hr.trans (ball_subset_ball (le_max_left _ _)))

theorem integrableOn_ball_of_memLp_two {E : Type*} [NormedAddCommGroup E] {f : ℂ → E} {r : ℝ}
    (h : MemLp f 2 (volume.restrict (ball (0 : ℂ) r))) : IntegrableOn f (ball (0 : ℂ) r) volume :=
  h.integrable (by norm_num)

theorem locallyIntegrable_of_memLp_two {E : Type*} [NormedAddCommGroup E] {f : ℂ → E}
    (h : ∀ r : ℝ, 0 < r → MemLp f 2 (volume.restrict (ball (0 : ℂ) r))) :
    LocallyIntegrable f volume :=
  locallyIntegrable_of_ball fun r hr => integrableOn_ball_of_memLp_two (h r hr)

theorem locallyIntegrable_smul_of_memLp_two {f : ℂ → ℝ} {g : ℂ → ℂ}
    (hf : ∀ r : ℝ, 0 < r → MemLp f 2 (volume.restrict (ball (0 : ℂ) r)))
    (hg : ∀ r : ℝ, 0 < r → MemLp g 2 (volume.restrict (ball (0 : ℂ) r))) :
    LocallyIntegrable (fun y => f y • g y) volume := by
  refine locallyIntegrable_of_ball fun r hr => ?_
  have : MemLp (f • g) 1 (volume.restrict (ball (0 : ℂ) r)) := (hg r hr).smul (hf r hr)
  exact memLp_one_iff_integrable.1 this

/-- A continuous field times an `L¹_loc` function is `L¹_loc`. -/
theorem locallyIntegrable_smul_of_continuous {f : ℂ → ℝ} {g : ℂ → ℂ}
    (hf : LocallyIntegrable f volume) (hg : Continuous g) :
    LocallyIntegrable (fun y => f y • g y) volume :=
  hf.smul_continuous hg

/-! ### Measurability of the commutator in `x` -/

/-- `x ↦ C_ε[u,w](t,x)` is a.e. strongly measurable when `u(t), u(t)w(t) ∈ L¹_loc` and `w(t)`
is a.e. strongly measurable. -/
theorem aestronglyMeasurable_commEps {ρ : ℂ → ℝ} (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    {u : ℝ → ℂ → ℝ} {w : ℝ → ℂ → ℂ} {t : ℝ} (hu : LocallyIntegrable (u t) volume)
    (huw : LocallyIntegrable (fun y => u t y • w t y) volume)
    (hw : AEStronglyMeasurable (w t) volume) :
    AEStronglyMeasurable (fun x => commEps ρ ε u w t x) volume := by
  obtain ⟨hcd, heq⟩ := dotGradMollify_eq_fderiv (w := w) hρ hε hu
  -- the first term
  have h1 : AEStronglyMeasurable (fun x => dotGradMollify ρ ε u w t x) volume := by
    have hcont : Continuous (fderiv ℝ (mollify ρ ε (u t))) := hcd.continuous_fderiv (by simp)
    have : AEStronglyMeasurable
        (fun x => fderiv ℝ (mollify ρ ε (u t)) x (w t x)) volume :=
      Continuous.comp_aestronglyMeasurable₂ (g := fun (L : ℂ →L[ℝ] ℝ) (v : ℂ) => L v)
        (continuous_fst.clm_apply continuous_snd) hcont.aestronglyMeasurable hw
    exact this.congr (Filter.Eventually.of_forall fun x => (heq x).symm)
  -- the second term: a convolution with a continuous compactly supported kernel
  have hscd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (scaled ρ ε) := by
    have : scaled ρ ε = fun x => (ε ^ 2)⁻¹ * ρ ((ε : ℂ)⁻¹ * x) := rfl
    rw [this]
    exact contDiff_const.mul (hρ.contDiff.comp (contDiff_const.mul contDiff_id))
  have hscs : HasCompactSupport (scaled ρ ε) := by
    have hsm : scaled ρ ε = fun x => (ε ^ 2)⁻¹ * ρ ((ε⁻¹ : ℝ) • x) := by
      funext x
      simp [scaled, Complex.real_smul, Complex.ofReal_inv]
    rw [hsm]
    refine (hρ.hasCompactSupport.comp_smul (inv_ne_zero hε.ne')).mono fun x hx => ?_
    rw [Function.mem_support] at hx ⊢
    intro h
    exact hx (by rw [h, mul_zero])
  have hK : Continuous (fderiv ℝ (scaled ρ ε)) := hscd.continuous_fderiv (by simp)
  have hKs : HasCompactSupport (fderiv ℝ (scaled ρ ε)) := hscs.fderiv ℝ
  have h2 : Continuous (fun x => mollifyDiv ρ ε u w t x) := by
    have hc := hKs.continuous_convolution_right
      (ContinuousLinearMap.apply ℝ ℝ : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ) →L[ℝ] ℝ) huw hK
    refine hc.congr fun x => ?_
    rw [convolution_def, mollifyDiv]
    congr 1
    funext y
    simp only [map_smul, IsSMulApply.smul_apply, ContinuousLinearMap.apply_apply,
      smul_eq_mul]
  exact h1.sub h2.aestronglyMeasurable

end NonUniqueEuler.Weak.CommutatorH
