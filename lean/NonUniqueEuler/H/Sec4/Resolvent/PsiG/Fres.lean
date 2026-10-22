import NonUniqueEuler.Defs.Sec4.Evans
import NonUniqueEuler.Defs.Sec4.Extra1Sector
import NonUniqueEuler.I.Sec4.SectorSetting
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Helpers for `P/Sec4/Resolvent/PsiG`: the forcing `F = S.Fres ℓ z G g`

Step 1 of the proof of `psiG_spec` (proof of `lem:resolvent`(1), `04_ring.tex:412-422`): for
`g ∈ Y^0_ℓ` (`IsProfileL2`), the forcing `F(ξ) = e^{2ξ}(M_λ g)(e^ξ)`
* vanishes almost everywhere off `[log ρ₋, log ρ₊]` (`Fres_ae_eq_zero`): null sets of `(0,∞)`
  pull back under `exp` to null sets, being images of null sets under the differentiable map
  `log` (`addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`);
* is integrable on `[log ρ₋, log ρ₊]` (`integrableOn_Fres`): change of variables `r = e^ξ`
  (`integrableOn_image_iff_integrableOn_abs_deriv_smul`), with `g ∈ L²[ρ₋,ρ₊] ⊆ L¹[ρ₋,ρ₊]` and
  `r ↦ r M_λ(r)` continuous on `[ρ₋, ρ₊]` (`contDiffOn_Omega`);
* hence `φ F ∈ L¹(ℝ)` for every continuous `φ` (`integrable_mul_Fres`).
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler.PsiGAux

open SectorSetting

/-- `F = 0` almost everywhere off `[log ρ₋, log ρ₊]`. -/
theorem Fres_ae_eq_zero (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (z : ℂ) (G : ℝ)
    {g : ℝ → ℂ} (hg : S.IsProfileL2 g) :
    ∀ᵐ ξ ∂volume, ξ ∉ Icc (Real.log S.ρm) (Real.log S.ρp) → S.Fres ℓ z G g ξ = 0 := by
  have h2 := hg.2
  rw [ae_restrict_iff' measurableSet_Ioi] at h2
  set N : Set ℝ := {r | ¬(r ∈ Ioi (0 : ℝ) → r ∉ Icc S.ρm S.ρp → g r = 0)} with hNdef
  have hN : volume N = 0 := ae_iff.1 h2
  have hNpos : N ⊆ Ioi 0 := by
    intro r hr
    by_contra hneg
    exact hr fun h => absurd h hneg
  have hlog : volume (Real.log '' N) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (Real.differentiableOn_log.mono fun r hr => by
        simpa using (ne_of_gt (show (0 : ℝ) < r from hNpos hr)))
      hN
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hlog] with ξ hξ hξnot
  have hnotin : Real.exp ξ ∉ Icc S.ρm S.ρp := by
    rintro ⟨h1, h2⟩
    apply hξnot
    constructor
    · have := Real.log_le_log hS.ρm_pos h1
      rwa [Real.log_exp] at this
    · have := Real.log_le_log (Real.exp_pos ξ) h2
      rwa [Real.log_exp] at this
  have hg0 : g (Real.exp ξ) = 0 := by
    by_contra hne
    apply hξ
    refine ⟨Real.exp ξ, ?_, Real.log_exp ξ⟩
    exact fun h => hne (h (Real.exp_pos ξ) hnotin)
  simp [Fres, hg0]

theorem continuousOn_Mres (S : SectorSetting) (hS : S.Valid) {z : ℂ} (hz : 0 < z.re) (ℓ : ℤ)
    (G : ℝ) : ContinuousOn (S.Mres ℓ z G) (Ioi 0) := by
  have h1 : ContinuousOn (fun r : ℝ => ((S.Omega G r : ℝ) : ℂ)) (Ioi 0) :=
    Complex.continuous_ofReal.comp_continuousOn (contDiffOn_Omega S hS G).continuousOn
  have h2 : ContinuousOn (fun r : ℝ => z + Complex.I * (ℓ : ℂ) * ((S.Omega G r : ℝ) : ℂ))
      (Ioi 0) := continuousOn_const.add (continuousOn_const.mul h1)
  refine h2.inv₀ fun r _ h => ?_
  have := congrArg Complex.re h
  simp at this
  linarith

/-- `F` is integrable on `[log ρ₋, log ρ₊]`. -/
theorem integrableOn_Fres (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) {z : ℂ} (hz : 0 < z.re)
    (G : ℝ) {g : ℝ → ℂ} (hg : S.IsProfileL2 g) :
    IntegrableOn (S.Fres ℓ z G g) (Icc (Real.log S.ρm) (Real.log S.ρp)) := by
  set c := Real.log S.ρm
  set d := Real.log S.ρp
  have hρp : 0 < S.ρp := hS.ρm_pos.trans hS.ρm_lt_ρp
  -- `g ∈ L¹[ρ₋, ρ₊]`
  have hgi : IntegrableOn g (Icc S.ρm S.ρp) := hg.1.integrable (by norm_num)
  -- `r ↦ r M_λ(r) g(r)` is integrable on `[ρ₋, ρ₊]`
  have hk : ContinuousOn (fun r : ℝ => (r : ℂ) * S.Mres ℓ z G r) (Icc S.ρm S.ρp) :=
    (Complex.continuous_ofReal.continuousOn).mul
      ((continuousOn_Mres S hS hz ℓ G).mono fun r hr => hS.ρm_pos.trans_le hr.1)
  have hg0 : IntegrableOn (fun r : ℝ => (r : ℂ) * (S.Mres ℓ z G r * g r)) (Icc S.ρm S.ρp) := by
    have := hgi.continuousOn_mul hk isCompact_Icc
    refine this.congr_fun (fun r _ => ?_) measurableSet_Icc
    simp only [mul_assoc]
  -- the image of `[c, d]` under `exp` lies in `[ρ₋, ρ₊]`
  have himg : Real.exp '' Icc c d ⊆ Icc S.ρm S.ρp := by
    rintro _ ⟨ξ, ⟨h1, h2⟩, rfl⟩
    constructor
    · calc S.ρm = Real.exp c := (Real.exp_log hS.ρm_pos).symm
        _ ≤ Real.exp ξ := Real.exp_le_exp.2 h1
    · calc Real.exp ξ ≤ Real.exp d := Real.exp_le_exp.2 h2
        _ = S.ρp := Real.exp_log hρp
  have hcv := (integrableOn_image_iff_integrableOn_abs_deriv_smul (f := Real.exp)
    (f' := Real.exp) measurableSet_Icc
    (fun ξ _ => (Real.hasDerivAt_exp ξ).hasDerivWithinAt) Real.exp_injective.injOn
    (fun r : ℝ => (r : ℂ) * (S.Mres ℓ z G r * g r))).1 (hg0.mono_set himg)
  refine hcv.congr_fun (fun ξ _ => ?_) measurableSet_Icc
  show |Real.exp ξ| • ((Real.exp ξ : ℂ) * (S.Mres ℓ z G (Real.exp ξ) * g (Real.exp ξ))) = _
  rw [abs_of_pos (Real.exp_pos ξ), Complex.real_smul, Fres, two_mul, Real.exp_add]
  push_cast
  ring

/-- `F ∈ L¹(ℝ)`. -/
theorem integrable_Fres (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) {z : ℂ} (hz : 0 < z.re)
    (G : ℝ) {g : ℝ → ℂ} (hg : S.IsProfileL2 g) : Integrable (S.Fres ℓ z G g) :=
  (integrableOn_Fres S hS ℓ hz G hg).integrable_of_ae_notMem_eq_zero
    (Fres_ae_eq_zero S hS ℓ z G hg)

/-- `φ F ∈ L¹(ℝ)` for every continuous `φ`. -/
theorem integrable_mul_Fres (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) {z : ℂ} (hz : 0 < z.re)
    (G : ℝ) {g : ℝ → ℂ} (hg : S.IsProfileL2 g) {φ : ℝ → ℂ} (hφ : Continuous φ) :
    Integrable (fun t => φ t * S.Fres ℓ z G g t) := by
  refine ((integrableOn_Fres S hS ℓ hz G hg).continuousOn_mul hφ.continuousOn
    isCompact_Icc).integrable_of_ae_notMem_eq_zero ?_
  filter_upwards [Fres_ae_eq_zero S hS ℓ z G hg] with ξ hξ hnot
  simp [hξ hnot]

end NonUniqueEuler.PsiGAux
