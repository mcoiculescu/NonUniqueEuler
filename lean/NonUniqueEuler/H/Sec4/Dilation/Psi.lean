import NonUniqueEuler.H.Sec4.Dilation.Basic
import NonUniqueEuler.I.Sec4.EvansBasic
import NonUniqueEuler.I.Sec4.Sector
import NonUniqueEuler.I.Infra.ODE.Uniqueness

/-!
# Helpers for `lem:dilation`: validity, the solution `ψ_ℓ`, the Evans function, `g_*`

Helper of `P/Sec4/Dilation.lean` (`lem:dilation`, `04_ring.tex:653-712`).

* `DilationH.dilate_valid'`: `S.dilate R` is a sector setting;
* `DilationH.dilate_psi`: with `t = log R`, `ψ^{ω̄_R}_ℓ(ξ;λ,G) = ψ^{ω̄}_ℓ(ξ+t;λ,R²G)` (and the same
  for `ψ'`). The Riccati coefficient is translated (`Vric_dilate`), the data point moves from
  `ξ₁` to `ξ₁ - t`, and uniqueness for the initial value problem (`IsSolOn.eqOn`) identifies the
  two solutions. (The manuscript normalizes `ψ = e^{ℓξ}` on the left and so gets a factor
  `R^{-ℓ}`; with the normalization `ψ(ξ₁) = 1` of `def:evans` there is no factor.)
* `DilationH.evans_dilate`: `E^{ω̄_R}_ℓ(λ;G) = E^{ω̄}_ℓ(λ;R²G)`;
* `DilationH.gStar_dilate`: `g^{ω̄_R}_*(r) = R² g^{ω̄}_*(Rr)` (unnormalized eigenprofiles);
* `DilationH.l2_const_mul`, `DilationH.ofProfile_gStar_dilate`.
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler

namespace DilationH

open SectorSetting

variable (S : SectorSetting)

theorem dilate_valid' (hS : S.Valid) {R : ℝ} (hR : 0 < R) : (S.dilate R).Valid where
  contDiff := hS.contDiff.comp (contDiff_const.mul contDiff_id)
  hasCompactSupport :=
    hS.hasCompactSupport.comp_isClosedEmbedding
      (Homeomorph.mulLeft₀ (R : ℂ) (Complex.ofReal_ne_zero.2 hR.ne')).isClosedEmbedding
  radial := by
    intro θ x
    show S.om ((R : ℂ) * rot θ x) = S.om ((R : ℂ) * x)
    rw [show (R : ℂ) * rot θ x = rot θ ((R : ℂ) * x) by simp only [rot]; ring]
    exact hS.radial θ _
  r₁_pos := div_pos hS.r₁_pos hR
  r₁_le_r₂ := div_le_div_of_nonneg_right hS.r₁_le_r₂ hR.le
  dom_eq_zero := by
    intro r hr hmem
    rw [dilate_dom]
    have h : R * r ∉ Icc S.r₁ S.r₂ := by
      rintro ⟨h1, h2⟩
      apply hmem
      show S.r₁ / R ≤ r ∧ r ≤ S.r₂ / R
      constructor
      · rw [div_le_iff₀ hR]; linarith
      · rw [le_div_iff₀ hR]; linarith
    rw [hS.dom_eq_zero (R * r) (mul_pos hR hr) h, mul_zero]
  ρm_pos := div_pos hS.ρm_pos hR
  ρm_lt_r₁ := div_lt_div_of_pos_right hS.ρm_lt_r₁ hR
  r₂_lt_ρp := div_lt_div_of_pos_right hS.r₂_lt_ρp hR

/-- `ψ^{ω̄_R}_ℓ(ξ;λ,G) = ψ^{ω̄}_ℓ(ξ + log R;λ,R²G)`, and the same for `ψ'`. -/
theorem dilate_psi (hS : S.Valid) {R : ℝ} (hR : 0 < R) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (z : ℂ)
    (hz : 0 < z.re) (G ξ : ℝ) :
    (S.dilate R).psi ℓ z G ξ = S.psi ℓ z (R ^ 2 * G) (ξ + Real.log R) ∧
      (S.dilate R).dpsi ℓ z G ξ = S.dpsi ℓ z (R ^ 2 * G) (ξ + Real.log R) := by
  set t := Real.log R with ht
  have hSR := dilate_valid' S hS hR
  obtain ⟨hsol, h1, h1', -⟩ := psi_spec S hS ℓ hℓ z hz (R ^ 2 * G)
  obtain ⟨hsolR, h1R, h1R', -⟩ := psi_spec (S.dilate R) hSR ℓ hℓ z hz G
  have hV : (S.dilate R).Vric ℓ z G = fun ξ => S.Vric ℓ z (R ^ 2 * G) (ξ + t) :=
    funext (Vric_dilate S hR ℓ z G)
  have hcont : Continuous (fun ξ => S.Vric ℓ z (R ^ 2 * G) (ξ + t)) :=
    ((sector_riccati S hS ℓ hℓ (R ^ 2 * G)).2.1 z hz).continuous.comp (continuous_add_const t)
  have htr : LinODE.IsSolOn ((S.dilate R).Vric ℓ z G) univ
      (fun ξ => S.psi ℓ z (R ^ 2 * G) (ξ + t)) (fun ξ => S.dpsi ℓ z (R ^ 2 * G) (ξ + t)) := by
    rw [hV]
    rw [LinODE.isSolOn_univ_iff] at hsol ⊢
    exact ⟨fun ξ => (hsol.1 (ξ + t)).comp_add_const ξ t,
      fun ξ => (hsol.2 (ξ + t)).comp_add_const ξ t⟩
  have hξ : (S.dilate R).ξ₁ = S.ξ₁ - t := dilate_ξ₁ S hS.r₁_pos.ne' hR.ne'
  have hc' : ContinuousOn ((S.dilate R).Vric ℓ z G) univ := by
    rw [hV]
    exact hcont.continuousOn
  have key := LinODE.IsSolOn.eqOn ordConnected_univ hc' hsolR htr
    (mem_univ ((S.dilate R).ξ₁)) (by rw [h1R, hξ, sub_add_cancel, h1])
    (by rw [h1R', hξ, sub_add_cancel, h1'])
  exact ⟨key.1 (mem_univ ξ), key.2 (mem_univ ξ)⟩

/-- `E^{ω̄_R}_ℓ(λ;G) = E^{ω̄}_ℓ(λ;R²G)`. -/
theorem evans_dilate (hS : S.Valid) {R : ℝ} (hR : 0 < R) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (z : ℂ)
    (hz : 0 < z.re) (G : ℝ) :
    (S.dilate R).evans ℓ z G = S.evans ℓ z (R ^ 2 * G) := by
  have h₁ := dilate_ξ₁ S hS.r₁_pos.ne' hR.ne'
  have h₂ := dilate_ξ₂ S hS.r₂_pos.ne' hR.ne'
  have hp := dilate_psi S hS hR ℓ hℓ z hz G (S.ξ₂ - Real.log R)
  rw [sub_add_cancel] at hp
  rw [evans_def, evans_def, h₁, h₂, hp.1, hp.2, sub_sub_sub_cancel_right]

/-- The unnormalized eigenprofiles: `g^{ω̄_R}_*(r) = R² g^{ω̄}_*(Rr)` (every `r`). -/
theorem gStar_dilate (hS : S.Valid) {R : ℝ} (hR : 0 < R) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (z : ℂ)
    (hz : 0 < z.re) (G r : ℝ) :
    (S.dilate R).gStar ℓ z G r = ((R ^ 2 : ℝ) : ℂ) * S.gStar ℓ z (R ^ 2 * G) (R * r) := by
  simp only [gStar, Mres_dilate S hR, kcoef_dilate S hR]
  rcases eq_or_ne r 0 with rfl | hr
  · simp [kcoef]
  rw [(dilate_psi S hS hR ℓ hℓ z hz G (Real.log r)).1, ← Real.log_mul hr hR.ne', mul_comm r R]
  ring

theorem l2_const_mul (c : ℂ) (f : ℂ → ℂ) : Sob.l2 (fun x => c * f x) = ‖c‖ * Sob.l2 f := by
  unfold Sob.l2
  have h : (fun x => c * f x) = c • f := by
    funext x
    simp [smul_eq_mul]
  rw [h, eLpNorm_const_smul, ENNReal.toReal_mul]
  congr 1

theorem ofProfile_gStar_dilate (hS : S.Valid) {R : ℝ} (hR : 0 < R) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (z : ℂ) (hz : 0 < z.re) (G : ℝ) :
    Ang.ofProfile ℓ ((S.dilate R).gStar ℓ z G) =
      fun x => ((R ^ 2 : ℝ) : ℂ) * Ang.ofProfile ℓ (S.gStar ℓ z (R ^ 2 * G)) ((R : ℂ) * x) := by
  funext x
  have hR0 : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR.ne'
  have hn : ‖(R : ℂ) * x‖ = R * ‖x‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  simp only [Ang.ofProfile, Ang.angPhase, gStar_dilate S hS hR ℓ hℓ z hz G, hn]
  rw [Complex.ofReal_mul, mul_div_mul_left _ _ hR0]
  ring

end DilationH

end NonUniqueEuler
