import NonUniqueEuler.H.Sec4.Sector.CouplingOfProfile.Basic
import NonUniqueEuler.I.Infra.ConvMinkowski.Young
import NonUniqueEuler.I.Sec2.BSBasic

/-!
# Helper for `couplingFn_ofProfile`: `|K_BS| ⋆ |W|` is finite at almost every real radius

Helper file of `P/Sec4/Sector/CouplingOfProfile.lean` (fully proved). For `W = g(r)e^{iℓθ}`
with `g ∈ Y^0_ℓ`: `W ∈ L²` with support in `B_{ρ₊+1}`, so by Young on balls
(`Conv.eLpNorm_convAbs_ball_le`, `∫_{B_ρ}|K_BS| = ρ`) `|K_BS| ⋆ |W| ∈ L²(B_R)`, hence finite
almost everywhere on `B_R`; it is radial (`convAbs_eq_norm`), so it is finite at almost every
radius `r ∈ (0, R)` (`ae_restrict_Ioi_of_ae_norm`).
-/

noncomputable section

open MeasureTheory Set Real Filter Metric
open scoped ENNReal

namespace NonUniqueEuler.CouplingOfProfileH

open Ang SectorSetting

/-- `(|K_BS| ⋆ |W|)(r) < ∞` for almost every `r ∈ (0, R)`. -/
theorem ae_convAbs_lt_top {S : SectorSetting} (hS : S.Valid) {g : ℝ → ℂ}
    (hg : S.IsProfileL2 g) (ℓ : ℤ) (R : ℝ) :
    ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), r < R →
      Conv.convAbs biotSavartKernel (ofProfile ℓ g) (r : ℂ) < ∞ := by
  have hW := memLp_ofProfile hg ℓ
  have hFm : Measurable (Conv.convAbs biotSavartKernel (ofProfile ℓ g)) :=
    measurable_convAbs hW.aestronglyMeasurable
  have hK : AEStronglyMeasurable biotSavartKernel volume :=
    measurable_bsKernel.aestronglyMeasurable
  set R' := max R 0 with hR'
  have hY := Conv.eLpNorm_convAbs_ball_le hK hW.aestronglyMeasurable (p := 2) (by norm_num)
    (R := R') (ofProfile_eq_zero_of_le hg ℓ)
  have hball := (BS.integral_norm_biotSavartKernel_ball (ρ := R' + (S.ρp + 1)) (by
    have := hS.ρm_pos; have := hS.ρm_lt_ρp; have := le_max_right R 0; linarith)).2.2
  have hlt : eLpNorm (Conv.convAbs biotSavartKernel (ofProfile ℓ g)) 2
      (volume.restrict (ball (0 : ℂ) R')) < ∞ := by
    refine hY.trans_lt ?_
    rw [hball]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hW.2
  have hint := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)).1 hlt
  have hae : ∀ᵐ x ∂(volume.restrict (ball (0 : ℂ) R')),
      ‖Conv.convAbs biotSavartKernel (ofProfile ℓ g) x‖ₑ ^ (2 : ℝ≥0∞).toReal < ∞ :=
    ae_lt_top (hFm.enorm.pow_const _) hint.ne
  rw [ae_restrict_iff' measurableSet_ball] at hae
  set N : Set ℝ := {r | r < R ∧ Conv.convAbs biotSavartKernel (ofProfile ℓ g) (r : ℂ) = ∞}
    with hN
  have hNm : MeasurableSet N :=
    (measurableSet_lt measurable_id measurable_const).inter
      ((hFm.comp Complex.measurable_ofReal) (measurableSet_singleton ∞))
  have h2 : ∀ᵐ x : ℂ, ‖x‖ ∉ N := by
    filter_upwards [hae] with x hx hxN
    obtain ⟨hxR, hxF⟩ := hxN
    have hxb : x ∈ ball (0 : ℂ) R' := by
      rw [mem_ball_zero_iff]
      exact hxR.trans_le (le_max_left R 0)
    have h3 := hx hxb
    rw [convAbs_eq_norm, hxF] at h3
    simp at h3
  filter_upwards [ae_restrict_Ioi_of_ae_norm hNm h2] with r hr hrR
  exact lt_top_iff_ne_top.2 fun h => hr ⟨hrR, h⟩

end NonUniqueEuler.CouplingOfProfileH
