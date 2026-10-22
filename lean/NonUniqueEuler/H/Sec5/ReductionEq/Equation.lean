import NonUniqueEuler.H.Sec5.ReductionEq.Config
import NonUniqueEuler.H.Sec5.ReductionEq.Pointwise
import NonUniqueEuler.I.Sec5.ReductionVelocity
import NonUniqueEuler.I.Infra.Sobolev.Smooth
import NonUniqueEuler.I.Sec2.BSBasic

/-!
# Helpers for `lem:reduction`(3): `eq:ring` holds almost everywhere at each time

Helper of `P/Sec5/ReductionEq.lean` (`05_single_ring.tex:206-217`). For `t ∈ [0,T]`,
`ringRHS χ G (h t) (w t) = ∂_t w(t)` almost everywhere (`RedEqH.ringRHS_ae_eq_deriv`):
* at the points where the weak first derivatives of `w(t)` and `Φ` are the classical ones (a.e.,
  `memH_of_contDiff_hasCompactSupport`), the right side is
  `-(Ω ∂_θ w + (K_BS*w)·∇Φ + (K_BS*w)·∇w + h·∇w + h·∇Φ)` (`RedEqH.ringRHS_eq_classical`);
* the transport equation gives `∂_t w = -v·∇ω_r` (`RedEqH.deriv_w`);
* on `N` insert `v = Ω x^⊥ + h + K_BS*w` (`lem:reduction`(2), `reduction_velocity`),
  `∇ω_r = ∇w + ∇Φ` and `x^⊥·∇Φ = 0`;
* outside `N`, `∇ω_r(t)`, `∇Φ` and `∇w(t)` vanish, so both sides are `0`.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ContDiff

namespace NonUniqueEuler.OneRing.RedEqH

open RingData

variable {c : RingConfig} {T : ℝ}

theorem a_pos : 0 < a := Real.exp_pos _

theorem annN_subset_annN' : annN ⊆ annN' := by
  intro x hx
  have ha := a_pos
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- The weak first derivatives of a smooth compactly supported function are the classical ones
almost everywhere. -/
theorem weakPartial_ae_eq_fderiv {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    (∀ᵐ x ∂(volume : Measure ℂ), Sob.weakPartial (1, 0) f x = fderiv ℝ f x 1) ∧
      ∀ᵐ x ∂(volume : Measure ℂ), Sob.weakPartial (0, 1) f x = fderiv ℝ f x Complex.I := by
  have h := (Sob.memH_of_contDiff_hasCompactSupport hf hc 1).2.1
  have h10 := h (1, 0) (by simp [Sob.multiIdx])
  have h01 := h (0, 1) (by simp [Sob.multiIdx])
  refine ⟨?_, ?_⟩
  · filter_upwards [h10] with x hx
    rw [hx, partialD_one_zero]
  · filter_upwards [h01] with x hx
    rw [hx, partialD_zero_one]

/-- **`eq:ring` a.e. at each time** (`05_single_ring.tex:206-217`): for `t ∈ [0,T]`,
`L(G)w + B(w,w) - h·∇w - h·∇Φ = ∂_t w` almost everywhere on `ℝ²`. -/
theorem ringRHS_ae_eq_deriv {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (hc : c.Hyp T)
    (hsupp : c.RingSupportedIn T annN) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    (fun x => ringRHS χ c.G (c.h t) (c.w χ t) x) =ᵐ[volume]
      fun x => deriv (fun s => c.w χ s x) t := by
  set wR : ℂ → ℝ := fun y => c.ringPart t y - ringPhi χ y with hwR
  have hRs : ContDiff ℝ ∞ (c.ringPart t) :=
    (RingConfig.setting_parts_smooth hc).2.2.2.1.comp (contDiff_const.prodMk contDiff_id)
  have hPs : ContDiff ℝ ∞ (ringPhi χ) := (ringFacts_of_admissible hχ).1
  have hPc : HasCompactSupport (ringPhi χ) := (ringFacts_of_admissible hχ).2.1
  have hwRs : ContDiff ℝ ∞ wR := hRs.sub hPs
  have hWeq : c.w χ t = fun y => ((wR y : ℝ) : ℂ) := rfl
  have hWs : ContDiff ℝ ∞ (c.w χ t) := Complex.ofRealCLM.contDiff.comp hwRs
  have hWc : HasCompactSupport (c.w χ t) :=
    HasCompactSupport.intro isCompact_annN fun x hx => w_eq_zero_of_not_mem hχ hsupp ht hx
  have hwRc : HasCompactSupport wR :=
    HasCompactSupport.intro isCompact_annN fun x hx => by
      have := w_eq_zero_of_not_mem hχ hsupp ht hx
      simpa [hWeq] using this
  have hΦs : ContDiff ℝ ∞ (PhiC χ) := Complex.ofRealCLM.contDiff.comp hPs
  have hΦc : HasCompactSupport (PhiC χ) := hPc.comp_left (by simp)
  obtain ⟨hW10, hW01⟩ := weakPartial_ae_eq_fderiv hWs hWc
  obtain ⟨hΦ10, hΦ01⟩ := weakPartial_ae_eq_fderiv hΦs hΦc
  have hint : ∀ x, Integrable (fun y => biotSavartKernel (x - y) * (wR y : ℂ)) := fun x =>
    (BS.integrable_and_norm_velocity_le_sqrt_L1_Linf
      (hwRs.continuous.memLp_of_hasCompactSupport hwRc)
      (hwRs.continuous.memLp_of_hasCompactSupport hwRc) x).1
  filter_upwards [hW10, hW01, hΦ10, hΦ01] with x e1 e2 e3 e4
  have hdwR : DifferentiableAt ℝ wR x := (hwRs.differentiable (by simp)).differentiableAt
  have hdP : DifferentiableAt ℝ (ringPhi χ) x := (hPs.differentiable (by simp)).differentiableAt
  have hdR : DifferentiableAt ℝ (c.ringPart t) x :=
    (hRs.differentiable (by simp)).differentiableAt
  have e1' : Sob.weakPartial (1, 0) (fun y => ((wR y : ℝ) : ℂ)) x =
      ((fderiv ℝ wR x 1 : ℝ) : ℂ) := by
    rw [← hWeq, e1, hWeq, fderiv_ofReal_apply hdwR]
  have e2' : Sob.weakPartial (0, 1) (fun y => ((wR y : ℝ) : ℂ)) x =
      ((fderiv ℝ wR x Complex.I : ℝ) : ℂ) := by
    rw [← hWeq, e2, hWeq, fderiv_ofReal_apply hdwR]
  have e3' : Sob.weakPartial (1, 0) (PhiC χ) x = ((fderiv ℝ (ringPhi χ) x 1 : ℝ) : ℂ) := by
    rw [e3]
    exact fderiv_ofReal_apply hdP 1
  have e4' : Sob.weakPartial (0, 1) (PhiC χ) x =
      ((fderiv ℝ (ringPhi χ) x Complex.I : ℝ) : ℂ) := by
    rw [e4]
    exact fderiv_ofReal_apply hdP Complex.I
  have hrhs := ringRHS_eq_classical χ c.G (c.h t) wR x (hint x) e1' e2' e3' e4'
  rw [hWeq, hrhs, deriv_w χ hc t x]
  have hsplit : c.ringPart t = fun y => wR y + ringPhi χ y := by
    funext y
    simp [hwR]
  by_cases hx : x ∈ annN
  · have hv := (reduction_velocity χ hχ hc).2.1 t ht x (annN_subset_annN' hx)
    have hDR : fderiv ℝ (c.ringPart t) x = fderiv ℝ wR x + fderiv ℝ (ringPhi χ) x := by
      rw [hsplit]
      exact fderiv_add hdwR hdP
    have hrad : fderiv ℝ (ringPhi χ) x (Complex.I * x) = 0 :=
      fderiv_mul_I_eq_zero_of_radial (ringFacts_of_admissible hχ).2.2.1 hdP
    have hom : omegaField χ c.G x = Lin.Omega χ c.G ‖x‖ • (Complex.I * x) := by
      rw [omegaField, Complex.real_smul]
    rw [hDR, hv, hom]
    simp only [_root_.add_apply, map_add, map_smul, smul_eq_mul, hrad]
    push_cast
    ring
  · have h1 : fderiv ℝ (c.ringPart t) x = 0 := fderiv_ringPart_eq_zero hsupp ht hx
    have h2 : fderiv ℝ (ringPhi χ) x = 0 := fderiv_ringPhi_eq_zero hχ hx
    have h3 : fderiv ℝ wR x = 0 := by
      have : fderiv ℝ wR x = fderiv ℝ (c.ringPart t) x - fderiv ℝ (ringPhi χ) x :=
        fderiv_sub hdR hdP
      rw [this, h1, h2, sub_zero]
    simp [h1, h2, h3]

end NonUniqueEuler.OneRing.RedEqH
