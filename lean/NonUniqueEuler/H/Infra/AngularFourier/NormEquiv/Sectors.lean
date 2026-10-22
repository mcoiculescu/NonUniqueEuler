import NonUniqueEuler.H.Infra.AngularFourier.NormEquiv.PolarOps
import NonUniqueEuler.H.Infra.AngularFourier.NormEquiv.Profile
import NonUniqueEuler.I.Infra.AngularFourier.Derivatives
import NonUniqueEuler.I.Infra.AngularFourier.Derivatives.ProfileDeriv

/-!
# Helper for `P/Infra/AngularFourier/NormEquiv`: sectors of the polar derivatives

For `w ∈ H^k` supported in `N_*` with sectors `g_ℓ` and `i + n ≤ k`:
the `ℓ`-th sector of `∂_θ^n ∂_r^i w` is `(iℓ)^n ∂_r^i g_ℓ` a.e. on `(0, ∞)`
(`angularSector_polar`), and `∂_r^i g_ℓ` vanishes outside `[ρ₋, ρ₊]` (`weakDeriv1On_supp`).
This is the manuscript's "by Parseval's identity in `θ`" step (`04_ring.tex:858-860`):
`∂_θ` acts as `iℓ` on sector `ℓ` (`sectorProj_thetaDeriv`) and `∂_r` commutes with taking
sectors (`hasWeakDerivOn_angularSector`, `I/Infra/AngularFourier/Derivatives/ProfileDeriv.lean`).
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace NonUniqueEuler.Ang.NormEquivAux

open Sob

theorem aesm_angularSector {k : ℕ} {ρm ρp : ℝ} (hρm : 0 < ρm) {g : ℂ → ℂ} (hg : MemH k g)
    (hgK : ∀ᵐ x, ¬ (ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp) → g x = 0) (ℓ : ℤ) :
    AEStronglyMeasurable (Polar.angularSector g ℓ) (volume.restrict (Ioi 0)) :=
  (memH1On_angularSector hρm hg hgK ℓ).1.memLp.aestronglyMeasurable

theorem locInt_angularSector {k : ℕ} {ρm ρp : ℝ} (hρm : 0 < ρm) {g : ℂ → ℂ} (hg : MemH k g)
    (hgK : ∀ᵐ x, ¬ (ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp) → g x = 0) (ℓ : ℤ) :
    LocallyIntegrableOn (Polar.angularSector g ℓ) (Ioi 0) :=
  locallyIntegrableOn_of_memLp_restrict isOpen_Ioi (memH1On_angularSector hρm hg hgK ℓ).1.memLp

/-- `∂_θ` acts as `iℓ` on the `ℓ`-th profile. -/
theorem angularSector_thetaDeriv {ρm ρp : ℝ} (hρm : 0 < ρm) {F : ℂ → ℂ} (hF : MemH 1 F)
    (hFK : ∀ᵐ x, ¬ (ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp) → F x = 0) (ℓ : ℤ) :
    Polar.angularSector (thetaDeriv F) ℓ =ᵐ[volume.restrict (Ioi 0)]
      fun r => ((ℓ : ℂ) * Complex.I) * Polar.angularSector F ℓ r := by
  obtain ⟨Ct, -, ht⟩ := thetaDeriv_bound 0 ρm ρp
  obtain ⟨hθ, hθK, -⟩ := ht 0 le_rfl F (by simpa using hF) hFK
  have hm1 := aesm_angularSector hρm hθ hθK ℓ
  have hm2 := aesm_angularSector hρm hF hFK ℓ
  set D : ℝ → ℂ := fun r => Polar.angularSector (thetaDeriv F) ℓ r -
    ((ℓ : ℂ) * Complex.I) * Polar.angularSector F ℓ r with hD
  have hDm : AEStronglyMeasurable D (volume.restrict (Ioi 0)) := hm1.sub (hm2.const_mul _)
  have hD0 : ofProfile ℓ D =ᵐ[volume] 0 := by
    have e1 := sectorProj_ae_eq_ofProfile ℓ (thetaDeriv F)
    have e2 := sectorProj_ae_eq_ofProfile ℓ F
    have e3 := sectorProj_thetaDeriv hF ℓ
    filter_upwards [e1, e2, e3] with x h1 h2 h3
    have : ofProfile ℓ D x = ofProfile ℓ (Polar.angularSector (thetaDeriv F) ℓ) x -
        ((ℓ : ℂ) * Complex.I) * ofProfile ℓ (Polar.angularSector F ℓ) x := by
      simp only [ofProfile, hD]
      ring
    rw [Pi.zero_apply, this, ← h1, ← h2, h3, sub_self]
  filter_upwards [profile_ae_zero hDm hD0] with r hr
  simpa [hD, sub_eq_zero] using hr

theorem hasWeakDerivOn_nil_self {V : Set ℝ} (f : ℝ → ℂ) : HasWeakDerivOn V [] f f := by
  intro φ _
  simp

theorem rad_iter_mem {k : ℕ} {ρm ρp : ℝ} (hρm : 0 < ρm) {w : ℂ → ℂ} (hw : MemH k w)
    (hwK : ∀ᵐ x, ¬ (ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp) → w x = 0) {i : ℕ} (hi : i ≤ k) :
    MemH (k - i) (radDeriv^[i] w) ∧
      ∀ᵐ x, ¬ (ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp) → radDeriv^[i] w x = 0 := by
  obtain ⟨C, -, hC⟩ := polar_iter k (ρp := ρp) hρm
  obtain ⟨h1, h2, -⟩ := hC w hw hwK i 0 (by omega)
  simp only [Function.iterate_zero, id, add_zero] at h1 h2
  exact ⟨h1, h2⟩

/-- `∂_r^i g_ℓ` (weakly on `(0,∞)`) is the `ℓ`-th profile of `∂_r^i w`. -/
theorem hasWeakDerivOn_angularSector_iter {k : ℕ} {ρm ρp : ℝ} (hρm : 0 < ρm) {w : ℂ → ℂ}
    (hw : MemH k w) (hwK : ∀ᵐ x, ¬ (ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp) → w x = 0) (ℓ : ℤ) :
    ∀ i ≤ k, HasWeakDerivOn (Ioi 0) (derivList i) (Polar.angularSector w ℓ)
      (Polar.angularSector (radDeriv^[i] w) ℓ) := by
  intro i
  induction i with
  | zero =>
    intro _
    exact hasWeakDerivOn_nil_self _
  | succ i ih =>
    intro hi
    obtain ⟨hm, hK⟩ := rad_iter_mem hρm hw hwK (i := i) (by omega)
    have h1 : MemH 1 (radDeriv^[i] w) := hm.mono_order (by omega)
    have step := hasWeakDerivOn_angularSector h1 ℓ
    have := (ih (by omega)).trans step
    rw [Function.iterate_succ_apply']
    exact this

theorem weakDeriv1On_angularSector_ae {k : ℕ} {ρm ρp : ℝ} (hρm : 0 < ρm) {w : ℂ → ℂ}
    (hw : MemH k w) (hwK : ∀ᵐ x, ¬ (ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp) → w x = 0) (ℓ : ℤ) {i : ℕ}
    (hi : i ≤ k) :
    ∀ᵐ r, r ∈ Ioi 0 → weakDeriv1On (Ioi 0) i (Polar.angularSector w ℓ) r =
      Polar.angularSector (radDeriv^[i] w) ℓ r := by
  obtain ⟨hm, hK⟩ := rad_iter_mem hρm hw hwK hi
  exact weakDerivOn_ae_eq isOpen_Ioi (locInt_angularSector hρm hm hK ℓ)
    (hasWeakDerivOn_angularSector_iter hρm hw hwK ℓ i hi)

/-- The `ℓ`-th profile of `∂_θ^n ∂_r^i w` is `(iℓ)^n ∂_r^i g_ℓ`. -/
theorem angularSector_polar {k : ℕ} {ρm ρp : ℝ} (hρm : 0 < ρm) {w : ℂ → ℂ}
    (hw : MemH k w) (hwK : ∀ᵐ x, ¬ (ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp) → w x = 0) (ℓ : ℤ) (i n : ℕ)
    (hin : i + n ≤ k) :
    Polar.angularSector (thetaDeriv^[n] (radDeriv^[i] w)) ℓ =ᵐ[volume.restrict (Ioi 0)]
      fun r => ((ℓ : ℂ) * Complex.I) ^ n * weakDeriv1On (Ioi 0) i (Polar.angularSector w ℓ) r := by
  induction n with
  | zero =>
    simp only [Function.iterate_zero, id, pow_zero, one_mul]
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioi]
    filter_upwards [weakDeriv1On_angularSector_ae hρm hw hwK ℓ (i := i) (by omega)] with r hr hr0
    exact (hr hr0).symm
  | succ n ih =>
    obtain ⟨C, -, hC⟩ := polar_iter k (ρp := ρp) hρm
    obtain ⟨hG, hGK, -⟩ := hC w hw hwK i n (by omega)
    have hG1 : MemH 1 (thetaDeriv^[n] (radDeriv^[i] w)) := hG.mono_order (by omega)
    have h1 := angularSector_thetaDeriv hρm hG1 hGK ℓ
    rw [Function.iterate_succ_apply']
    filter_upwards [h1, ih (by omega)] with r e1 e2
    rw [e1, e2, pow_succ]
    ring

/-- `∂_r^i g_ℓ` vanishes outside `[ρ₋, ρ₊]`. -/
theorem weakDeriv1On_supp {k : ℕ} {ρm ρp : ℝ} (hρm : 0 < ρm) {w : ℂ → ℂ}
    (hw : MemH k w) (hwK : ∀ᵐ x, ¬ (ρm ≤ ‖x‖ ∧ ‖x‖ ≤ ρp) → w x = 0) (ℓ : ℤ) {i : ℕ}
    (hi : i ≤ k) :
    ∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc ρm ρp →
      weakDeriv1On (Ioi 0) i (Polar.angularSector w ℓ) r = 0 := by
  obtain ⟨hm, hK⟩ := rad_iter_mem hρm hw hwK hi
  filter_upwards [ae_restrict_of_ae (weakDeriv1On_angularSector_ae hρm hw hwK ℓ hi),
    ae_restrict_mem measurableSet_Ioi, (memH1On_angularSector hρm hm hK ℓ).2] with r h1 hr0 h2 hr
  rw [h1 hr0]
  exact h2 hr

end NonUniqueEuler.Ang.NormEquivAux
