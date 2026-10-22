import NonUniqueEuler.H.Sec4.Edge.Conclude
import NonUniqueEuler.I.Sec4.Sector
import NonUniqueEuler.I.Infra.Polar.Radial

/-!
# Helpers for `P/Sec4/Edge`: `lem:edge` for sector profiles

Manuscript `04_ring.tex:735-747`. For a profile `g ∈ Y^0_ℓ` (`S.IsProfileL2 g`), not a.e. zero,
with `L_ℓ(G) g = λ g` a.e. on `(0,∞)` and `Re λ > 0`:
* `ψ = 𝒢_ℓ g` is continuous (`green_bound`), and `g = M_λ k_ℓ ψ = ω̄' e` a.e.
  (`e = iℓψ/(r(λ+iℓΩ))`), so `g` vanishes off `{ω̄' ≠ 0}`;
* hence `ψ(r) = -(2n)⁻¹ ∫_{[r₁,r₂]} K0(r,ρ) ω̄'(ρ) e(ρ) ρ dρ`, and `‖g‖²_W = N > 0`;
* `core` (`H/Sec4/Edge/Conclude.lean`) gives `Re λ ≤ ½ Z_n^{1/2}` (`edge_profile`).

Also `ae_eq_of_ofProfile_ae_eq'`: sector functions `h₁(r)e^{iℓθ} = h₂(r)e^{iℓθ}` a.e. on the
plane have profiles equal a.e. on `(0,∞)` (polar coordinates; a copy of the argument of
`P/Sec4/SectorSetting.lean`, which this proof may not import).
-/

noncomputable section

open MeasureTheory Set ComplexConjugate

namespace NonUniqueEuler.EdgeH

open SectorSetting

variable {S : SectorSetting}

/-- If a nonnegative `φ` satisfies `φ(|x|) = 0` for a.e. `x ∈ ℂ`, then `φ = 0` a.e. on `(0,∞)`. -/
theorem ae_restrict_Ioi_of_comp_norm' {φ : ℝ → ℝ} (hφ : ∀ r, 0 ≤ φ r)
    (h : (fun x : ℂ => φ ‖x‖) =ᵐ[volume] 0) :
    ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), φ r = 0 := by
  have hint : Integrable (fun x : ℂ => φ ‖x‖) := (integrable_zero ℂ ℝ volume).congr h.symm
  have hint' := Polar.integrable_comp_norm_iff.1 hint
  have hI := Polar.integral_comp_norm φ
  have h0 : ∫ x : ℂ, φ ‖x‖ = 0 := by
    rw [integral_congr_ae h]
    simp
  rw [h0] at hI
  have hI0 : ∫ r in Ioi (0 : ℝ), r • φ r = 0 := by
    have := hI.symm
    rw [smul_eq_zero] at this
    exact this.resolve_left (by positivity)
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun r => r • φ r := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    exact mul_nonneg (le_of_lt hr) (hφ r)
  have hz := (integral_eq_zero_iff_of_nonneg_ae hnn hint').1 hI0
  filter_upwards [hz, self_mem_ae_restrict measurableSet_Ioi] with r hr hr0
  have : r * φ r = 0 := hr
  exact (mul_eq_zero.1 this).resolve_left (ne_of_gt hr0)

/-- Two sector functions that agree a.e. on the plane have profiles that agree a.e. on
`(0,∞)`. -/
theorem ae_eq_of_ofProfile_ae_eq' {ℓ : ℤ} {h₁ h₂ : ℝ → ℂ}
    (h : Ang.ofProfile ℓ h₁ =ᵐ[volume] Ang.ofProfile ℓ h₂) :
    h₁ =ᵐ[volume.restrict (Ioi 0)] h₂ := by
  have hne : ∀ᵐ x : ℂ ∂volume, x ≠ 0 := by
    rw [ae_iff]
    simp
  have hφ : (fun x : ℂ => ‖h₁ ‖x‖ - h₂ ‖x‖‖) =ᵐ[volume] 0 := by
    filter_upwards [h, hne] with x hx hx0
    have h1 : ‖h₁ ‖x‖ - h₂ ‖x‖‖ = ‖Ang.ofProfile ℓ h₁ x - Ang.ofProfile ℓ h₂ x‖ := by
      rw [Ang.ofProfile, Ang.ofProfile, ← sub_mul, norm_mul, Ang.norm_angPhase hx0, mul_one]
    simp [h1, hx]
  have := ae_restrict_Ioi_of_comp_norm' (φ := fun r => ‖h₁ r - h₂ r‖) (fun r => norm_nonneg _) hφ
  filter_upwards [this] with r hr
  exact sub_eq_zero.1 (norm_eq_zero.1 hr)

/-- `g = M_λ k_ℓ ψ = ω̄' e` at every `r > 0` where the eigen-equation holds. -/
theorem eq_dom_mul_efun {ℓ : ℤ} {z : ℂ} (hz : 0 < z.re) (G : ℝ) {h : ℝ → ℂ} {r : ℝ}
    (hr0 : 0 < r) (hr : S.LsecFn ℓ G h r = z * h r) :
    h r = ((S.dom r : ℝ) : ℂ) * efun S ℓ z G (green ℓ h) r := by
  have hmul := efun_mul (S := S) (ℓ := ℓ) hz G (green ℓ h) hr0.ne'
  have hm : mres S ℓ z G r ≠ 0 := mres_ne_zero hz G r
  have hr0' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr0.ne'
  rw [LsecFn_eq] at hr
  have h1 : mres S ℓ z G r * h r = S.kcoef ℓ r * green ℓ h r := by
    rw [mres]
    linear_combination (-1 : ℂ) * hr
  have hk : (r : ℂ) * S.kcoef ℓ r = Complex.I * (ℓ : ℂ) * ((S.dom r : ℝ) : ℂ) := by
    rw [kcoef]
    field_simp
  apply mul_left_cancel₀ (mul_ne_zero hr0' hm)
  linear_combination (r : ℂ) * h1 + green ℓ h r * hk - ((S.dom r : ℝ) : ℂ) * hmul

/-- `lem:edge` for sector profiles. -/
theorem edge_profile (hS : S.Valid) (hsplit : S.EdgeSplit) {ℓ : ℤ} (hℓ : ℓ ≠ 0) (G : ℝ)
    {z : ℂ} (hz : 0 < z.re) {h : ℝ → ℂ} (hh : S.IsProfileL2 h)
    (hne : ¬ (h =ᵐ[volume.restrict (Ioi 0)] 0))
    (heq : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), S.LsecFn ℓ G h r = z * h r) :
    z.re ≤ 1 / 2 * Real.sqrt (S.Zedge ℓ.natAbs) := by
  have hψc : ContinuousOn (green ℓ h) (Ioi 0) := (green_bound S hS hℓ hh).1
  have hec : ContinuousOn (efun S ℓ z G (green ℓ h)) (Icc S.r₁ S.r₂) :=
    (continuousOn_efun hS hz G hψc).mono (Icc_subset_Ioi hS)
  have hhe : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))),
      h r = ((S.dom r : ℝ) : ℂ) * efun S ℓ z G (green ℓ h) r := by
    filter_upwards [heq, self_mem_ae_restrict measurableSet_Ioi] with r hr hr0
    exact eq_dom_mul_efun hz G hr0 hr
  have hψI : ∀ r ∈ Icc S.r₁ S.r₂, green ℓ h r = -(((2 * |(ℓ : ℝ)|)⁻¹ : ℝ) : ℂ) *
      ∫ ρ in Icc S.r₁ S.r₂, (K0 ℓ.natAbs r ρ : ℂ) * fw S (efun S ℓ z G (green ℓ h)) ρ := by
    intro r _
    rw [green]
    congr 1
    calc ∫ ρ in Ioi (0 : ℝ), (((min r ρ / max r ρ) ^ ℓ.natAbs : ℝ) : ℂ) * h ρ * (ρ : ℂ)
        = ∫ ρ in Ioi (0 : ℝ), (K0 ℓ.natAbs r ρ : ℂ) * fw S (efun S ℓ z G (green ℓ h)) ρ := by
          refine integral_congr_ae ?_
          filter_upwards [hhe] with ρ hρ
          rw [hρ, fw, K0]
          ring
      _ = ∫ ρ in Icc S.r₁ S.r₂,
            (K0 ℓ.natAbs r ρ : ℂ) * fw S (efun S ℓ z G (green ℓ h)) ρ := by
          refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
            (Icc_subset_Ioi hS) fun ρ hρ => ?_
          have hd : S.dom ρ = 0 := hS.dom_eq_zero ρ hρ.1 hρ.2
          simp [fw, hd]
  have hu : ContinuousOn
      (fun r => |S.dom r| * ‖efun S ℓ z G (green ℓ h) r‖ ^ 2 * r ^ 2) (Icc S.r₁ S.r₂) :=
    ((continuous_dom hS).abs.continuousOn.mul (hec.norm.pow 2)).mul
      (continuous_pow 2).continuousOn
  have hN : 0 < ∫ r in Icc S.r₁ S.r₂,
      |S.dom r| * ‖efun S ℓ z G (green ℓ h) r‖ ^ 2 * r ^ 2 := by
    have hnn : 0 ≤ ∫ r in Icc S.r₁ S.r₂,
        |S.dom r| * ‖efun S ℓ z G (green ℓ h) r‖ ^ 2 * r ^ 2 :=
      setIntegral_nonneg measurableSet_Icc fun r _ => by positivity
    refine lt_of_le_of_ne hnn fun h0 => hne ?_
    have hz0 := (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun r => by positivity)
      (hu.integrableOn_compact isCompact_Icc)).1 h0.symm
    have hI : ∀ᵐ r ∂volume, r ∈ Icc S.r₁ S.r₂ →
        |S.dom r| * ‖efun S ℓ z G (green ℓ h) r‖ ^ 2 * r ^ 2 = 0 :=
      (ae_restrict_iff' measurableSet_Icc).1 hz0
    have hde : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))),
        ((S.dom r : ℝ) : ℂ) * efun S ℓ z G (green ℓ h) r = 0 := by
      rw [ae_restrict_iff' measurableSet_Ioi]
      filter_upwards [hI] with r hr hr0
      by_cases hrI : r ∈ Icc S.r₁ S.r₂
      · have h3 := hr hrI
        rcases mul_eq_zero.1 h3 with h4 | h4
        · rcases mul_eq_zero.1 h4 with h5 | h5
          · simp [abs_eq_zero.1 h5]
          · have : efun S ℓ z G (green ℓ h) r = 0 := by
              simpa using h5
            simp [this]
        · exact absurd ((pow_eq_zero_iff two_ne_zero).1 h4) (ne_of_gt hr0)
      · simp [hS.dom_eq_zero r hr0 hrI]
    filter_upwards [hhe, hde] with r h1 h2
    rw [h1, h2]
    rfl
  exact core hS hsplit hℓ hz G hψc hψI hN

end NonUniqueEuler.EdgeH
