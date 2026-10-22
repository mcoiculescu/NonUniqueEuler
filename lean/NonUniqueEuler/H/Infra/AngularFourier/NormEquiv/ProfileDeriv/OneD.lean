import NonUniqueEuler.Defs.Infra.SobolevOneD
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Helpers for `P/Infra/AngularFourier/NormEquiv/ProfileDeriv`: the profile on `(0, ∞)`

For `h ∈ H^1((0,∞))` vanishing a.e. outside `[ρ₋, ρ₊]`, `0 < ρ₋ ≤ ρ₊`, and
`h' = Sob.weakDeriv1On (Ioi 0) 1 h`:
* `weakDeriv_spec`: `h' ∈ L²((0,∞))` is a locally integrable weak derivative of `h` on `(0,∞)`;
* `weakDeriv_ae_zero`: `h' = 0` a.e. on `(0,∞) \ [ρ₋, ρ₊]` (uniqueness of weak derivatives on
  that open set, where `0` is a weak derivative);
* `integrableOn_of_eq`: `h' g₁ + h g₂` is integrable on `(0,∞)` for continuous `g₁, g₂`;
* `weak_identity`: `∫_{(0,∞)} h (X + r X') = -∫_{(0,∞)} h' r X` for every smooth `X`, by testing
  the weak derivative against `χ(r) r X(r)`, `χ` a smooth cutoff equal to `1` near `[ρ₋, ρ₊]`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace NonUniqueEuler.Ang.NEProfileDerivAux

variable {ρm ρp : ℝ} {h : ℝ → ℂ}

theorem weakDeriv_spec (hh : Sob.MemH1On 1 (Ioi 0) h) :
    MemLp (Sob.weakDeriv1On (Ioi 0) 1 h) 2 (volume.restrict (Ioi 0)) ∧
      LocallyIntegrableOn (Sob.weakDeriv1On (Ioi 0) 1 h) (Ioi 0) ∧
      Sob.HasWeakDerivOn (Ioi 0) (Sob.derivList 1) h (Sob.weakDeriv1On (Ioi 0) 1 h) := by
  obtain ⟨g, hg2, hgw⟩ := hh.deriv 1 le_rfl
  have hgli : LocallyIntegrableOn g (Ioi 0) :=
    locallyIntegrableOn_of_locallyIntegrable_restrict (hg2.locallyIntegrable (by norm_num))
  have hspec := Sob.weakDerivOn_spec hgli hgw
  have hae := Sob.weakDerivOn_ae_eq isOpen_Ioi hgli hgw
  have hae' : Sob.weakDeriv1On (Ioi 0) 1 h =ᵐ[volume.restrict (Ioi 0)] g :=
    (ae_restrict_iff' measurableSet_Ioi).2 hae
  exact ⟨hg2.ae_eq hae'.symm, hspec.1, hspec.2⟩

theorem ae_restrict_Ioi_iff {p : ℝ → Prop} :
    (∀ᵐ r ∂(volume.restrict (Ioi 0)), p r) ↔ ∀ᵐ r, r ∈ Ioi (0 : ℝ) → p r :=
  ae_restrict_iff' measurableSet_Ioi

theorem weakDeriv_ae_zero (hh : Sob.MemH1On 1 (Ioi 0) h)
    (hhI : ∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc ρm ρp → h r = 0) :
    ∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc ρm ρp → Sob.weakDeriv1On (Ioi 0) 1 h r = 0 := by
  set U : Set ℝ := Ioi 0 ∩ (Icc ρm ρp)ᶜ with hUdef
  have hU : IsOpen U := isOpen_Ioi.inter isClosed_Icc.isOpen_compl
  have hUsub : U ⊆ Ioi 0 := inter_subset_left
  have hhI' := ae_restrict_Ioi_iff.1 hhI
  have h0 : Sob.HasWeakDerivOn U (Sob.derivList 1) h (fun _ => 0) := by
    intro ψ hψ
    have hψ' := hψ.iterDirDeriv (Sob.derivList 1)
    simp only [zero_mul, integral_zero, mul_zero]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hhI'] with x hx
    by_cases hxU : x ∈ U
    · rw [hx hxU.1 hxU.2, zero_mul, Pi.zero_apply]
    · have : x ∉ tsupport (Sob.iterDirDeriv (Sob.derivList 1) ψ) := fun h' => hxU (hψ'.subset h')
      rw [image_eq_zero_of_notMem_tsupport this, mul_zero, Pi.zero_apply]
  obtain ⟨_, hli, hw⟩ := weakDeriv_spec hh
  have hae := Sob.HasWeakDerivOn.ae_eq hU (hli.mono_set hUsub) locallyIntegrableOn_zero
    (hw.mono hUsub) h0
  refine ae_restrict_Ioi_iff.2 ?_
  filter_upwards [hae] with x hx hx0 hxI
  exact hx ⟨hx0, hxI⟩

/-- `h' g₁ + h g₂` (and anything equal to it on `(0,∞)`) is integrable on `(0,∞)`. -/
theorem integrableOn_of_eq (hρm : 0 < ρm) (hh : Sob.MemH1On 1 (Ioi 0) h)
    (hhI : ∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc ρm ρp → h r = 0)
    {g₁ g₂ : ℝ → ℂ} (hg₁ : Continuous g₁) (hg₂ : Continuous g₂) {F : ℝ → ℂ}
    (hF : ∀ r ∈ Ioi (0 : ℝ), F r = Sob.weakDeriv1On (Ioi 0) 1 h r * g₁ r + h r * g₂ r) :
    IntegrableOn F (Ioi 0) := by
  have hIcc : Icc ρm ρp ⊆ Ioi (0 : ℝ) := fun r hr => lt_of_lt_of_le hρm hr.1
  have hres : (volume.restrict (Ioi (0 : ℝ))).restrict (Icc ρm ρp) = volume.restrict (Icc ρm ρp) := by
    rw [Measure.restrict_restrict measurableSet_Icc, inter_eq_left.2 hIcc]
  have hL1 : ∀ u : ℝ → ℂ, MemLp u 2 (volume.restrict (Ioi 0)) → IntegrableOn u (Icc ρm ρp) := by
    intro u hu
    have hu' : MemLp u 2 (volume.restrict (Icc ρm ρp)) := by
      rw [← hres]; exact hu.restrict _
    exact hu'.integrable (by norm_num)
  have hd := (weakDeriv_spec hh).1
  have hA : IntegrableOn (fun r => Sob.weakDeriv1On (Ioi 0) 1 h r * g₁ r + h r * g₂ r)
      (Icc ρm ρp) :=
    ((hL1 _ hd).mul_continuousOn hg₁.continuousOn isCompact_Icc).add
      ((hL1 _ hh.memLp).mul_continuousOn hg₂.continuousOn isCompact_Icc)
  have hA' : IntegrableOn F (Icc ρm ρp) :=
    hA.congr_fun (fun r hr => (hF r (hIcc hr)).symm) measurableSet_Icc
  refine hA'.of_ae_sdiff_eq_zero measurableSet_Ioi.nullMeasurableSet ?_
  have h1 := ae_restrict_Ioi_iff.1 hhI
  have h2 := ae_restrict_Ioi_iff.1 (weakDeriv_ae_zero hh hhI)
  filter_upwards [h1, h2] with r hr1 hr2 hr
  rw [hF r hr.1, hr1 hr.1 hr.2, hr2 hr.1 hr.2, zero_mul, zero_mul, add_zero]

/-- A smooth cutoff on `(0, ∞)` equal to `1` near `[ρ₋, ρ₊]`. -/
theorem exists_cutoff (hρm : 0 < ρm) (hρ : ρm ≤ ρp) :
    ∃ χ : ℝ → ℂ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Ioi 0 ∧
      ∀ r ∈ Icc ρm ρp, χ r = 1 ∧ HasDerivAt χ 0 r := by
  let f : ContDiffBump ((ρm + ρp) / 2) :=
    ⟨(ρp - ρm) / 2 + ρm / 4, (ρp - ρm) / 2 + ρm / 2, by linarith, by linarith⟩
  refine ⟨fun r => ((f r : ℝ) : ℂ), Complex.ofRealCLM.contDiff.comp f.contDiff,
    f.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp), ?_, ?_⟩
  · refine (tsupport_comp_subset (g := fun t : ℝ => (t : ℂ)) (by simp) f).trans ?_
    have hf : f.rOut = (ρp - ρm) / 2 + ρm / 2 := rfl
    rw [f.tsupport_eq, Real.closedBall_eq_Icc, hf]
    intro r hr
    simp only [mem_Icc] at hr
    show (0 : ℝ) < r
    have : (ρm + ρp) / 2 - ((ρp - ρm) / 2 + ρm / 2) = ρm / 2 := by ring
    linarith [hr.1]
  · intro r hr
    have hball : r ∈ Metric.ball ((ρm + ρp) / 2) ((ρp - ρm) / 2 + ρm / 4) := by
      rw [Real.ball_eq_Ioo]
      constructor <;> linarith [hr.1, hr.2]
    have hev : (fun r => ((f r : ℝ) : ℂ)) =ᶠ[𝓝 r] fun _ => (1 : ℂ) := by
      filter_upwards [f.eventuallyEq_one_of_mem_ball hball] with x hx
      simp [hx]
    refine ⟨by simpa using hev.eq_of_nhds, ?_⟩
    exact (hasDerivAt_const r (1 : ℂ)).congr_of_eventuallyEq hev

/-- The weak derivative tested against `χ(r) r X(r)`: `∫ h (X + r X') = -∫ h' r X` on `(0,∞)`. -/
theorem weak_identity (hρm : 0 < ρm) (hρ : ρm ≤ ρp) (hh : Sob.MemH1On 1 (Ioi 0) h)
    (hhI : ∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc ρm ρp → h r = 0)
    {X X' : ℝ → ℂ} (hX : ContDiff ℝ ∞ X) (hX' : ∀ r, HasDerivAt X (X' r) r) :
    ∫ r in Ioi 0, h r * (X r + r * X' r) =
      -∫ r in Ioi 0, Sob.weakDeriv1On (Ioi 0) 1 h r * (r * X r) := by
  obtain ⟨χ, hχ, hχc, hχs, hχ1⟩ := exists_cutoff hρm hρ
  set η : ℝ → ℂ := fun r => χ r * ((r : ℂ) * X r) with hηdef
  have hrX : ContDiff ℝ ∞ (fun r : ℝ => (r : ℂ) * X r) := Complex.ofRealCLM.contDiff.mul hX
  have hη : Sob.IsTestFn (Ioi 0) η :=
    ⟨hχ.mul hrX, hχc.mul_right, (tsupport_mul_subset_left).trans hχs⟩
  obtain ⟨_, _, hw⟩ := weakDeriv_spec hh
  have hwη := hw η hη
  rw [Sob.iterDirDeriv_derivList, iteratedDeriv_one, Sob.derivList_length, pow_one] at hwη
  -- the derivative of `η`
  have hχd : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hηd : ∀ r, HasDerivAt η (deriv χ r * ((r : ℂ) * X r) + χ r * (1 * X r + r * X' r)) r := by
    intro r
    have h1 : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 r := (hasDerivAt_id r).ofReal_comp
    exact (hχd r).hasDerivAt.mul (h1.mul (hX' r))
  have hderiv : deriv η = fun r => deriv χ r * ((r : ℂ) * X r) + χ r * (1 * X r + r * X' r) := by
    funext r; exact (hηd r).deriv
  have hηout : ∀ r, r ∉ Ioi (0 : ℝ) → η r = 0 := by
    intro r hr
    have : r ∉ tsupport χ := fun h' => hr (hχs h')
    simp [hηdef, image_eq_zero_of_notMem_tsupport this]
  have hη'out : ∀ r, r ∉ Ioi (0 : ℝ) → deriv η r = 0 := by
    intro r hr
    have : r ∉ tsupport η := fun h' => hr (hη.subset h')
    exact deriv_of_notMem_tsupport this
  have hL : ∫ x, h x * deriv η x = ∫ r in Ioi 0, h r * (X r + r * X' r) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi 0)
      (fun r hr => by rw [hη'out r hr, mul_zero])]
    refine setIntegral_congr_ae measurableSet_Ioi ?_
    filter_upwards [ae_restrict_Ioi_iff.1 hhI] with r hr hr0
    by_cases hI : r ∈ Icc ρm ρp
    · rw [hderiv]
      beta_reduce
      rw [(hχ1 r hI).2.deriv, (hχ1 r hI).1]
      ring
    · rw [hr hr0 hI, zero_mul, zero_mul]
  have hR : ∫ x, Sob.weakDeriv1On (Ioi 0) 1 h x * η x =
      ∫ r in Ioi 0, Sob.weakDeriv1On (Ioi 0) 1 h r * (r * X r) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi 0)
      (fun r hr => by rw [hηout r hr, mul_zero])]
    refine setIntegral_congr_ae measurableSet_Ioi ?_
    filter_upwards [ae_restrict_Ioi_iff.1 (weakDeriv_ae_zero hh hhI)] with r hr hr0
    by_cases hI : r ∈ Icc ρm ρp
    · rw [hηdef]; simp only; rw [(hχ1 r hI).1, one_mul]
    · rw [hr hr0 hI, zero_mul, zero_mul]
  rw [← hL, ← hR, hwη]
  ring

end NonUniqueEuler.Ang.NEProfileDerivAux
