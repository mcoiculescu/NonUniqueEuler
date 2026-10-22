import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import NonUniqueEuler.Defs.Infra.SectorSpace
import NonUniqueEuler.I.Infra.SectorSpace.BanachExp
import NonUniqueEuler.I.Infra.SectorSpace.Decomposition
import NonUniqueEuler.I.Infra.SectorSpace.DirectSum
import NonUniqueEuler.I.Infra.SectorSpace.Projection

/-!
# Proof: the sector-wise exponential `e^{tL} = ⊕_ℓ exp(t L_ℓ)` (library I-SECT; D8, R1)

Proof of `I/Infra/SectorSpace/Semigroup.lean`. Everything is reduced to the direct-sum
interface `I/Infra/SectorSpace/DirectSum.lean` with `A ℓ = exp(t L_ℓ)` and to the bounded
operator exponential `I/Infra/SectorSpace/BanachExp.lean`:
* `sectorExp_zero`: `exp 0 = 1` and `sectorSum_one`;
* `sectorExp_add`: `exp((t+t')L_ℓ) = exp(tL_ℓ) exp(t'L_ℓ)` (`BanachExp.exp_smul_add`) and
  `sectorSum_comp`, with the uniform bounds of `ExpBounded` at the times `t` and `t'`;
* `secProj_sectorExp`, `sectorExp_mem_YZSub`: `secProj_sectorSum`, `sectorSum_mem_YZSub`;
* `continuousOn_sectorExp`: `continuousOn_sectorSum` on `[0, t + 1]` (the bound of
  `ExpBounded (t + 1)`), localized to `Ici 0` at `t`;
* `hasDerivWithinAt_sectorExp`: for `t ≥ 0`, `e^{tL} w = w + ∫₀ᵗ e^{τL} v dτ`. Both sides are
  compared sector by sector (an element of `Y^s` is determined by its sector projections,
  `hasSum_secProj`); `P_ℓ` commutes with the integral, `P_ℓ v = L_ℓ P_ℓ w`
  (`secProj_inclSec`), and sector-wise the identity is the fundamental theorem of calculus for
  `τ ↦ exp(τ L_ℓ) P_ℓ w` (`BanachExp.hasDerivAt_exp_smul`). The derivative of the right side is
  `e^{tL} v` by the FTC for the continuous integrand `τ ↦ e^{max(τ,0) L} v`.
-/

noncomputable section

open MeasureTheory Set Real Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.Sect

open Sob Ang

variable {s : ℕ} {ρm ρp : ℝ}

/-! ### Helpers -/

/-- An element of `Y^s` on the annulus is determined by its sector projections. -/
private theorem Y_ext_of_secProj (hρm : 0 < ρm) (hρ : ρm < ρp)
    {a b : Y s (closedAnnulus ρm ρp)}
    (h : ∀ ℓ, secProj s _ ℓ a = secProj s _ ℓ b) : a = b := by
  have ha := hasSum_secProj hρm hρ a
  have hb := hasSum_secProj hρm hρ b
  simp only [h] at ha
  exact ha.unique hb

/-- Continuity of `τ ↦ exp(τ A)` for a bounded operator `A`. -/
private theorem continuous_exp_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (A : E →L[ℂ] E) :
    Continuous fun τ : ℝ => NormedSpace.exp ((τ : ℂ) • A) :=
  continuous_iff_continuousAt.2 fun τ => (BanachExp.hasDerivAt_exp_smul A τ).1.continuousAt

/-- `d/dτ exp(τ A) g = exp(τ A) (A g)`. -/
private theorem hasDerivAt_exp_smul_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (A : E →L[ℂ] E) (g : E) (τ : ℝ) :
    HasDerivAt (fun σ : ℝ => NormedSpace.exp ((σ : ℂ) • A) g)
      (NormedSpace.exp ((τ : ℂ) • A) (A g)) τ := by
  have h := ((ContinuousLinearMap.apply ℂ E g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt τ
    (BanachExp.hasDerivAt_exp_smul A τ).1
  simpa [Function.comp_def, ContinuousLinearMap.mul_apply'] using h

/-! ### The interface statements -/

theorem sectorExp_zero (hρm : 0 < ρm) (hρ : ρm < ρp)
    (L : ∀ ℓ : ℤ, Ysec s (closedAnnulus ρm ρp) ℓ →L[ℂ] Ysec s (closedAnnulus ρm ρp) ℓ) :
    sectorExp s _ L 0 = ContinuousLinearMap.id ℂ _ := by
  have h : (fun ℓ => NormedSpace.exp (((0 : ℝ) : ℂ) • L ℓ)) =
      fun _ => ContinuousLinearMap.id ℂ _ := by
    funext ℓ
    rw [Complex.ofReal_zero, zero_smul ℂ (L ℓ), NormedSpace.exp_zero, ContinuousLinearMap.one_def]
  unfold sectorExp
  rw [h]
  exact sectorSum_one hρm hρ

theorem sectorExp_add (hρm : 0 < ρm) (hρ : ρm < ρp)
    {L : ∀ ℓ : ℤ, Ysec s (closedAnnulus ρm ρp) ℓ →L[ℂ] Ysec s (closedAnnulus ρm ρp) ℓ}
    (hb : ExpBounded s _ L) {t t' : ℝ} (ht : 0 ≤ t) (ht' : 0 ≤ t') :
    sectorExp s _ L (t + t') = (sectorExp s _ L t).comp (sectorExp s _ L t') := by
  obtain ⟨M, hM⟩ := hb t
  obtain ⟨M', hM'⟩ := hb t'
  have h1 : ∀ ℓ, ‖NormedSpace.exp ((t : ℂ) • L ℓ)‖ ≤ M := fun ℓ => hM t ⟨ht, le_rfl⟩ ℓ
  have h2 : ∀ ℓ, ‖NormedSpace.exp ((t' : ℂ) • L ℓ)‖ ≤ M' := fun ℓ => hM' t' ⟨ht', le_rfl⟩ ℓ
  unfold sectorExp
  rw [← sectorSum_comp hρm hρ h1 h2]
  congr 1
  funext ℓ
  rw [BanachExp.exp_smul_add, ContinuousLinearMap.mul_def]

theorem secProj_sectorExp (hρm : 0 < ρm) (hρ : ρm < ρp)
    {L : ∀ ℓ : ℤ, Ysec s (closedAnnulus ρm ρp) ℓ →L[ℂ] Ysec s (closedAnnulus ρm ρp) ℓ}
    (hb : ExpBounded s _ L) {t : ℝ} (ht : 0 ≤ t) (ℓ : ℤ) (w : Y s (closedAnnulus ρm ρp)) :
    secProj s _ ℓ (sectorExp s _ L t w) = NormedSpace.exp ((t : ℂ) • L ℓ) (secProj s _ ℓ w) := by
  obtain ⟨M, hM⟩ := hb t
  exact secProj_sectorSum hρm hρ (fun ℓ => hM t ⟨ht, le_rfl⟩ ℓ) ℓ w

theorem continuousOn_sectorExp (hρm : 0 < ρm) (hρ : ρm < ρp)
    {L : ∀ ℓ : ℤ, Ysec s (closedAnnulus ρm ρp) ℓ →L[ℂ] Ysec s (closedAnnulus ρm ρp) ℓ}
    (hb : ExpBounded s _ L) (w : Y s (closedAnnulus ρm ρp)) :
    ContinuousOn (fun t => sectorExp s _ L t w) (Ici 0) := by
  intro t ht
  obtain ⟨M, hM⟩ := hb (t + 1)
  have hc : ContinuousOn (fun τ => sectorExp s _ L τ w) (Icc 0 (t + 1)) :=
    continuousOn_sectorSum hρm hρ (A := fun τ ℓ => NormedSpace.exp ((τ : ℂ) • L ℓ)) hM
      (fun ℓ g => ((continuous_exp_smul (L ℓ)).clm_apply continuous_const).continuousOn) w
  have hmem : Icc 0 (t + 1) ∈ 𝓝[Ici 0] t := by
    rw [← Ici_inter_Iic]
    exact inter_mem_nhdsWithin _ (Iic_mem_nhds (by linarith))
  exact (hc t ⟨ht, by linarith⟩).mono_of_mem_nhdsWithin hmem

/-- `d/dt e^{tL} w = e^{tL} v` when `v = ∑_ℓ L_ℓ P_ℓ w` converges. -/
theorem hasDerivWithinAt_sectorExp (hρm : 0 < ρm) (hρ : ρm < ρp)
    {L : ∀ ℓ : ℤ, Ysec s (closedAnnulus ρm ρp) ℓ →L[ℂ] Ysec s (closedAnnulus ρm ρp) ℓ}
    (hb : ExpBounded s _ L) {w v : Y s (closedAnnulus ρm ρp)}
    (hv : HasSum (fun ℓ : ℤ => inclSec s _ ℓ (L ℓ (secProj s _ ℓ w))) v) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun t => sectorExp s _ L t w) (sectorExp s _ L t v) (Ici 0) t := by
  -- the sector components of `v`
  have hPv : ∀ ℓ, secProj s _ ℓ v = L ℓ (secProj s _ ℓ w) := by
    intro ℓ
    have h1 := hv.map (secProj s _ ℓ) (secProj s _ ℓ).continuous
    have h2 : HasSum (fun m : ℤ => secProj s _ ℓ (inclSec s _ m (L m (secProj s _ m w))))
        (L ℓ (secProj s _ ℓ w)) := by
      have h3 : secProj s _ ℓ (inclSec s _ ℓ (L ℓ (secProj s _ ℓ w))) =
          L ℓ (secProj s _ ℓ w) := by
        apply Subtype.ext
        rw [secProj_inclSec (isRotInvariant_closedAnnulus ρm ρp)]
        simp
      rw [← h3]
      refine hasSum_single ℓ fun m hm => ?_
      apply Subtype.ext
      rw [secProj_inclSec (isRotInvariant_closedAnnulus ρm ρp)]
      simp [Ne.symm hm]
    exact h1.unique h2
  -- the continuous integrand `τ ↦ e^{max(τ,0) L} v`
  set f : ℝ → Y s (closedAnnulus ρm ρp) := fun τ => sectorExp s _ L (max τ 0) v with hf
  have hfc : Continuous f :=
    (continuousOn_sectorExp hρm hρ hb v).comp_continuous (continuous_id.max continuous_const)
      fun τ => le_max_right τ 0
  -- the integral identity `e^{tL} w = w + ∫₀ᵗ e^{τL} v dτ` for `t ≥ 0`
  have hint : ∀ t : ℝ, 0 ≤ t → sectorExp s _ L t w = w + ∫ τ in (0 : ℝ)..t, f τ := by
    intro t ht
    apply Y_ext_of_secProj hρm hρ
    intro ℓ
    rw [map_add, ← ContinuousLinearMap.intervalIntegral_comp_comm _ (hfc.intervalIntegrable 0 t),
      secProj_sectorExp hρm hρ hb ht]
    have h1 : ∀ τ ∈ uIcc (0 : ℝ) t, secProj s _ ℓ (f τ) =
        NormedSpace.exp ((τ : ℂ) • L ℓ) (L ℓ (secProj s _ ℓ w)) := by
      intro τ hτ
      rw [uIcc_of_le ht] at hτ
      simp only [hf, max_eq_left hτ.1]
      rw [secProj_sectorExp hρm hρ hb hτ.1, hPv]
    rw [intervalIntegral.integral_congr h1,
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun τ _ => hasDerivAt_exp_smul_apply (L ℓ) (secProj s _ ℓ w) τ)
        (((continuous_exp_smul (L ℓ)).clm_apply continuous_const).intervalIntegrable 0 t)]
    rw [Complex.ofReal_zero, zero_smul ℂ (L ℓ), NormedSpace.exp_zero]
    change _ = _ + (_ - secProj s _ ℓ w)
    abel
  -- FTC for the right-hand side
  have hd : HasDerivAt (fun t => w + ∫ τ in (0 : ℝ)..t, f τ) (sectorExp s _ L t v) t := by
    have := ((hfc.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add w
    simpa [hf, max_eq_left ht] using this
  exact hd.hasDerivWithinAt.congr_of_mem (fun x hx => hint x hx) ht

/-- `e^{tL}` preserves `Y^s_𝒵`. -/
theorem sectorExp_mem_YZSub (hρm : 0 < ρm) (hρ : ρm < ρp)
    {L : ∀ ℓ : ℤ, Ysec s (closedAnnulus ρm ρp) ℓ →L[ℂ] Ysec s (closedAnnulus ρm ρp) ℓ}
    (hb : ExpBounded s _ L) {t : ℝ} (ht : 0 ≤ t) (Z : Set ℤ) {w : Y s (closedAnnulus ρm ρp)}
    (hw : (w : SobTuple s) ∈ YZSub s (closedAnnulus ρm ρp) Z) :
    ((sectorExp s _ L t w : Y s (closedAnnulus ρm ρp)) : SobTuple s) ∈
      YZSub s (closedAnnulus ρm ρp) Z := by
  obtain ⟨M, hM⟩ := hb t
  exact sectorSum_mem_YZSub hρm hρ (fun ℓ => hM t ⟨ht, le_rfl⟩ ℓ) Z hw

end NonUniqueEuler.Sect
