import NonUniqueEuler.H.Sec4.Adjoint.Stream

/-!
# Helper for `lem:adjoint`(3): assembly

Helper of `P/Sec4/Adjoint.lean` (`04_ring.tex:620-629`): the statement `adjoint_stream`, proved
from `Stream.lean`. The manuscript's identification "the stream function of `g_*e^{iℓθ}` is
`(𝒢_ℓ g_*) e^{iℓθ}`" (`lem:sector`(1)) is an a.e. statement; the pointwise statement follows by
continuity of both sides on `ℂ \ {0}` and, at `0`, of the log potential.
-/

noncomputable section

open MeasureTheory Set Filter Topology ComplexConjugate Metric
open scoped ContDiff

namespace NonUniqueEuler.AdjointAux

open SectorSetting

theorem adjoint_stream_aux (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (z : ℂ)
    (hz : 0 < z.re) (G : ℝ) (hE : S.evans ℓ z G = 0) :
    (∀ x : ℂ, S.r₂ ≤ ‖x‖ →
        Multipole.logPotential (Ang.ofProfile ℓ (S.gStar ℓ z G)) x =
          Ang.ofProfile ℓ
            (fun r => -(S.poutStar ℓ z G / (2 * (ℓ : ℂ))) * (r : ℂ) ^ (-(ℓ : ℤ))) x) ∧
      (∀ x : ℂ, ‖x‖ ≤ S.r₁ →
        Multipole.logPotential (Ang.ofProfile ℓ (S.gStar ℓ z G)) x =
          Ang.ofProfile ℓ (fun r => -(S.pinStar ℓ z G / (2 * (ℓ : ℂ))) * (r : ℂ) ^ ℓ) x) ∧
      S.pinStar ℓ z G = -2 * (ℓ : ℂ) * ((Real.exp (-(ℓ * S.ξ₁)) : ℝ) : ℂ) ∧
      S.poutStar ℓ z G =
        -2 * (ℓ : ℂ) * ((Real.exp (ℓ * S.ξ₂) : ℝ) : ℂ) * S.psi ℓ z G S.ξ₂ ∧
      S.poutStar ℓ z G = BS.pout ℓ (Ang.ofProfile ℓ (S.gStar ℓ z G)) ∧
      S.pinStar ℓ z G = BS.pin ℓ (Ang.ofProfile ℓ (S.gStar ℓ z G)) := by
  obtain ⟨hcd, hsupp, -, hgreen, -⟩ := eigen_of_evans_eq_zero S hS ℓ hℓ z hz G hE
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast (show ℓ ≠ 0 by omega)
  have hℓC : (ℓ : ℂ) ≠ 0 := by exact_mod_cast (show ℓ ≠ 0 by omega)
  have hr₁ := hS.r₁_pos
  have hr₂ := hS.r₂_pos
  have hg0 : S.gStar ℓ z G 0 = 0 := by simp [gStar, kcoef]
  have hfc : Continuous (Ang.ofProfile (ℓ : ℤ) (S.gStar ℓ z G)) :=
    continuous_ofProfile_of_supp hr₁ hcd.continuousOn hsupp hg0 ℓ
  have hfs : HasCompactSupport (Ang.ofProfile (ℓ : ℤ) (S.gStar ℓ z G)) :=
    hasCompactSupport_ofProfile_of_supp hr₂.le hsupp ℓ
  have hLc : Continuous (Multipole.logPotential (Ang.ofProfile (ℓ : ℤ) (S.gStar ℓ z G))) :=
    continuous_logPotential hfc hfs
  have hgP := isProfileL2_gStar S hS ℓ hℓ hz G hE
  have hae := green_eq_logPotential S hS hℓ0 hgP
  have hGc : ContinuousOn (Ang.ofProfile (ℓ : ℤ) (green ℓ (S.gStar ℓ z G))) {0}ᶜ :=
    continuousOn_ofProfile (green_bound S hS hℓ0 hgP).1 ℓ
  have hEq : EqOn (Ang.ofProfile (ℓ : ℤ) (green ℓ (S.gStar ℓ z G)))
      (Multipole.logPotential (Ang.ofProfile (ℓ : ℤ) (S.gStar ℓ z G))) {0}ᶜ :=
    Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae hae) isOpen_compl_singleton hGc hLc.continuousOn
  have hext : ∀ r : ℝ, S.r₂ ≤ r → green ℓ (S.gStar ℓ z G) r =
      -(S.poutStar ℓ z G / (2 * (ℓ : ℂ))) * (r : ℂ) ^ (-(ℓ : ℤ)) := by
    intro r hr
    rw [green_eq_exterior ℓ hsupp (hr₂.trans_le hr) hr, poutStar]
    ring
  have hint : ∀ r : ℝ, 0 < r → r ≤ S.r₁ → green ℓ (S.gStar ℓ z G) r =
      -(S.pinStar ℓ z G / (2 * (ℓ : ℂ))) * (r : ℂ) ^ ℓ := by
    intro r hr0 hr
    rw [green_eq_interior ℓ hsupp hr0 hr, pinStar]
    ring
  have hoff : ∀ x : ℂ, x ≠ 0 →
      Multipole.logPotential (Ang.ofProfile (ℓ : ℤ) (S.gStar ℓ z G)) x =
        green ℓ (S.gStar ℓ z G) ‖x‖ * Ang.angPhase ℓ x :=
    fun x hx => (hEq (show x ∈ ({0}ᶜ : Set ℂ) from hx)).symm
  have hzero : Multipole.logPotential (Ang.ofProfile (ℓ : ℤ) (S.gStar ℓ z G)) 0 = 0 := by
    set c : ℂ := -(S.pinStar ℓ z G / (2 * (ℓ : ℂ))) with hc
    have hev : (fun x : ℂ => c * x ^ ℓ) =ᶠ[𝓝[≠] (0 : ℂ)]
        Multipole.logPotential (Ang.ofProfile (ℓ : ℤ) (S.gStar ℓ z G)) := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds (0 : ℂ) hr₁)]
        with x hx0 hxb
      have hx0' : x ≠ 0 := hx0
      have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0'
      have hxr : ‖x‖ ≤ S.r₁ := (mem_ball_zero_iff.1 hxb).le
      have hn : ((‖x‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hxn.ne'
      rw [hoff x hx0', hint ‖x‖ hxn hxr, Ang.angPhase, zpow_natCast, div_pow]
      field_simp
    have h1 : Tendsto (Multipole.logPotential (Ang.ofProfile (ℓ : ℤ) (S.gStar ℓ z G)))
        (𝓝[≠] (0 : ℂ))
        (𝓝 (Multipole.logPotential (Ang.ofProfile (ℓ : ℤ) (S.gStar ℓ z G)) 0)) :=
      (hLc.tendsto 0).mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (Multipole.logPotential (Ang.ofProfile (ℓ : ℤ) (S.gStar ℓ z G)))
        (𝓝[≠] (0 : ℂ)) (𝓝 (c * 0 ^ ℓ)) :=
      (((continuous_const.mul (continuous_pow ℓ)).tendsto 0).mono_left
        nhdsWithin_le_nhds).congr' hev
    rw [tendsto_nhds_unique h1 h2, zero_pow (show ℓ ≠ 0 by omega), mul_zero]
  have hpsi1 : S.psi ℓ z G S.ξ₁ = 1 := (psi_spec S hS ℓ hℓ z hz G).2.1
  have hr1C : ((S.r₁ : ℝ) : ℂ) ^ ℓ ≠ 0 := pow_ne_zero _ (by exact_mod_cast hr₁.ne')
  have hr2C : ((S.r₂ : ℝ) : ℂ) ^ ℓ ≠ 0 := pow_ne_zero _ (by exact_mod_cast hr₂.ne')
  have hexp1 : ((Real.exp (-(ℓ * S.ξ₁)) : ℝ) : ℂ) = (((S.r₁ : ℝ) : ℂ) ^ ℓ)⁻¹ := by
    rw [Real.exp_neg, Real.exp_nat_mul, ξ₁, Real.exp_log hr₁]
    norm_cast
  have hexp2 : ((Real.exp (ℓ * S.ξ₂) : ℝ) : ℂ) = ((S.r₂ : ℝ) : ℂ) ^ ℓ := by
    rw [Real.exp_nat_mul, ξ₂, Real.exp_log hr₂]
    norm_cast
  have hpin : S.pinStar ℓ z G = -2 * (ℓ : ℂ) * ((Real.exp (-(ℓ * S.ξ₁)) : ℝ) : ℂ) := by
    have h1 := hint S.r₁ hr₁ le_rfl
    rw [hgreen S.r₁ hr₁] at h1
    change S.psi ℓ z G S.ξ₁ = _ at h1
    rw [hpsi1] at h1
    rw [hexp1]
    calc S.pinStar ℓ z G
        = -2 * (ℓ : ℂ) * (((S.r₁ : ℝ) : ℂ) ^ ℓ)⁻¹ *
            (-(S.pinStar ℓ z G / (2 * (ℓ : ℂ))) * ((S.r₁ : ℝ) : ℂ) ^ ℓ) := by
          field_simp
      _ = -2 * (ℓ : ℂ) * (((S.r₁ : ℝ) : ℂ) ^ ℓ)⁻¹ := by rw [← h1, mul_one]
  have hpout : S.poutStar ℓ z G =
      -2 * (ℓ : ℂ) * ((Real.exp (ℓ * S.ξ₂) : ℝ) : ℂ) * S.psi ℓ z G S.ξ₂ := by
    have h2 := hext S.r₂ le_rfl
    rw [hgreen S.r₂ hr₂] at h2
    change S.psi ℓ z G S.ξ₂ = _ at h2
    rw [h2, hexp2, zpow_neg, zpow_natCast]
    field_simp
  refine ⟨?_, ?_, hpin, hpout, poutStar_eq_pout S ℓ hℓ z G, pinStar_eq_pin S ℓ hℓ z G⟩
  · intro x hx
    have hx0 : x ≠ 0 := by
      intro h
      rw [h, norm_zero] at hx
      linarith
    rw [hoff x hx0, hext ‖x‖ hx]
    rfl
  · intro x hx
    by_cases hx0 : x = 0
    · subst hx0
      rw [hzero]
      simp [Ang.ofProfile, angPhase_zero ℓ hℓ]
    · rw [hoff x hx0, hint ‖x‖ (norm_pos_iff.2 hx0) hx]
      rfl

end NonUniqueEuler.AdjointAux
