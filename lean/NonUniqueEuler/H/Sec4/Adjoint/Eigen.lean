import NonUniqueEuler.H.Sec4.Adjoint.Basic
import NonUniqueEuler.H.Sec4.Adjoint.Green
import NonUniqueEuler.I.Sec4.Sector
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Helper for `lem:adjoint`(1): the adjoint eigenfunction (weak form)

Helper of `P/Sec4/Adjoint.lean` (`04_ring.tex:602-612`). With `X = ψ_*(log r) M_*(r)` and
`g ∈ Y^0_ℓ`:
`∫ (L_ℓ g) X r dr = ∫ (-iℓΩ) g X r dr + ∫ (𝒢_ℓ g) g_* r dr`, and by the symmetry of the kernel
(`integral_green_mul_symm`) and `𝒢_ℓ g_* = ψ_*(log r) = (λ_* + iℓΩ) X`, the second term is
`∫ g (λ_* + iℓΩ) X r dr`; the transport terms cancel. `X ≠ 0` near `r₁` since `ψ_*(ξ₁) = 1`.
-/

noncomputable section

open MeasureTheory Set Filter Topology ComplexConjugate
open scoped ContDiff

namespace NonUniqueEuler.AdjointAux

open SectorSetting

/-- `lem:adjoint`(1), weak form, with `X = ψ_*(log r) M_*(r)`:
`∫ (L_ℓ g) X r dr = λ_* ∫ g X r dr` for `g ∈ Y^0_ℓ`. -/
theorem weak_eigen (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (z : ℂ)
    (hz : 0 < z.re) (G : ℝ) (hE : S.evans ℓ z G = 0) {g : ℝ → ℂ} (hg : S.IsProfileL2 g) :
    ∫ r in Ioi (0 : ℝ), S.LsecFn ℓ G g r * (S.psi ℓ z G (Real.log r) * S.Mres ℓ z G r) * (r : ℂ) =
      z * ∫ r in Ioi (0 : ℝ), g r * (S.psi ℓ z G (Real.log r) * S.Mres ℓ z G r) * (r : ℂ) := by
  obtain ⟨hcd, hsupp, -, hgreen, -⟩ := eigen_of_evans_eq_zero S hS ℓ hℓ z hz G hE
  set X : ℝ → ℂ := fun r => S.psi ℓ z G (Real.log r) * S.Mres ℓ z G r with hXdef
  set W : ℝ → ℂ := fun r => Complex.I * (ℓ : ℂ) * ((S.Omega G r : ℝ) : ℂ) with hWdef
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast (show ℓ ≠ 0 by omega)
  have hsub := Icc_subset_Ioi S hS
  have hXc : ContinuousOn X (Icc S.ρm S.ρp) := (continuousOn_X S hS ℓ hℓ hz G).mono hsub
  have hWc : ContinuousOn W (Icc S.ρm S.ρp) :=
    (continuousOn_const.mul (continuousOn_Omega_cast S hS G)).mono hsub
  have hrc : ContinuousOn (fun r : ℝ => (r : ℂ)) (Icc S.ρm S.ρp) :=
    Complex.continuous_ofReal.continuousOn
  have hsub₁ : Icc S.r₁ S.r₂ ⊆ Ioi 0 := (Icc_r_subset_Icc_ρ S hS).trans hsub
  have hgc : ContinuousOn (S.gStar ℓ z G) (Icc S.r₁ S.r₂) := hcd.continuousOn.mono hsub₁
  have hGc : ContinuousOn (green ℓ g) (Icc S.r₁ S.r₂) :=
    (green_bound S hS hℓ0 hg).1.mono hsub₁
  -- the pointwise decomposition of the integrand
  have hpt1 : ∀ r, S.LsecFn ℓ G g r * X r * (r : ℂ) =
      g r * (-(W r) * X r * (r : ℂ)) + green ℓ g r * S.gStar ℓ z G r * (r : ℂ) := by
    intro r
    rw [LsecFn_eq, ← kcoef_mul_X S ℓ z G r]
    simp only [hXdef, hWdef, Int.cast_natCast]
    ring
  have hA₁ : IntegrableOn (fun r => g r * (-(W r) * X r * (r : ℂ))) (Ioi 0) :=
    integrableOn_profile_mul S hg ((hWc.neg.mul hXc).mul hrc)
  have hA₂ : IntegrableOn (fun r => green ℓ g r * S.gStar ℓ z G r * (r : ℂ)) (Ioi 0) := by
    refine integrableOn_Ioi_of_continuousOn_Icc ((hGc.mul hgc).mul
      Complex.continuous_ofReal.continuousOn) ?_
    intro r hr hr'
    rw [hsupp r hr hr', mul_zero, zero_mul]
  have hgρ : IntegrableOn (fun ρ => g ρ * (ρ : ℂ)) (Ioi 0) := integrableOn_profile_mul S hg hrc
  have hg₁ : IntegrableOn (fun r => S.gStar ℓ z G r * (r : ℂ)) (Ioi 0) := by
    refine integrableOn_Ioi_of_continuousOn_Icc (hgc.mul Complex.continuous_ofReal.continuousOn) ?_
    intro r hr hr'
    rw [hsupp r hr hr', zero_mul]
  have hFub := integral_green_mul_symm (ℓ : ℤ) hgρ hg₁
  have hpt2 : ∀ ρ ∈ Ioi (0 : ℝ), g ρ * green ℓ (S.gStar ℓ z G) ρ * (ρ : ℂ) =
      g ρ * (z * X ρ * (ρ : ℂ)) + g ρ * (W ρ * X ρ * (ρ : ℂ)) := by
    intro ρ hρ
    rw [hgreen ρ hρ, psi_eq_denom_mul_X S hz ℓ G ρ]
    simp only [hXdef, hWdef]
    ring
  have hB₁ : IntegrableOn (fun ρ => g ρ * (z * X ρ * (ρ : ℂ))) (Ioi 0) :=
    integrableOn_profile_mul S hg ((continuousOn_const.mul hXc).mul hrc)
  have hB₂ : IntegrableOn (fun ρ => g ρ * (W ρ * X ρ * (ρ : ℂ))) (Ioi 0) :=
    integrableOn_profile_mul S hg ((hWc.mul hXc).mul hrc)
  have e1 : ∫ r in Ioi (0 : ℝ), S.LsecFn ℓ G g r * X r * (r : ℂ) =
      (∫ r in Ioi (0 : ℝ), g r * (-(W r) * X r * (r : ℂ))) +
        ∫ r in Ioi (0 : ℝ), green ℓ g r * S.gStar ℓ z G r * (r : ℂ) := by
    rw [← integral_add hA₁ hA₂]
    exact integral_congr_ae (Eventually.of_forall hpt1)
  have e2 : ∫ ρ in Ioi (0 : ℝ), g ρ * green ℓ (S.gStar ℓ z G) ρ * (ρ : ℂ) =
      (∫ ρ in Ioi (0 : ℝ), g ρ * (z * X ρ * (ρ : ℂ))) +
        ∫ ρ in Ioi (0 : ℝ), g ρ * (W ρ * X ρ * (ρ : ℂ)) := by
    rw [← integral_add hB₁ hB₂]
    exact setIntegral_congr_fun measurableSet_Ioi hpt2
  have e3 : ∫ r in Ioi (0 : ℝ), g r * (-(W r) * X r * (r : ℂ)) =
      -∫ r in Ioi (0 : ℝ), g r * (W r * X r * (r : ℂ)) := by
    rw [← integral_neg]
    congr 1
    funext r
    ring
  have e4 : ∫ ρ in Ioi (0 : ℝ), g ρ * (z * X ρ * (ρ : ℂ)) =
      z * ∫ ρ in Ioi (0 : ℝ), g ρ * X ρ * (ρ : ℂ) := by
    rw [← integral_const_mul]
    congr 1
    funext r
    ring
  rw [e1, hFub, e2, e3, e4]
  ring

/-- `lem:adjoint`(1), last assertion: `conj X` is not `0` in `L²([ρ₋,ρ₊])`. -/
theorem adjEig_not_ae_zero (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (z : ℂ)
    (hz : 0 < z.re) (G : ℝ) :
    ¬ (∀ᵐ r ∂(volume.restrict (Icc S.ρm S.ρp)), S.adjEig ℓ z G r = 0) := by
  intro h
  have h' : S.adjEig ℓ z G =ᵐ[volume.restrict (Ioo S.ρm S.ρp)] fun _ => (0 : ℂ) :=
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self h
  have hc : ContinuousOn (S.adjEig ℓ z G) (Ioo S.ρm S.ρp) :=
    (Complex.continuous_conj.comp_continuousOn (continuousOn_X S hS ℓ hℓ hz G)).mono
      (Ioo_subset_Icc_self.trans (Icc_subset_Ioi S hS))
  have hEq := Measure.eqOn_open_of_ae_eq h' isOpen_Ioo hc continuousOn_const
  have hr₁ : S.r₁ ∈ Ioo S.ρm S.ρp := ⟨hS.ρm_lt_r₁, lt_of_le_of_lt hS.r₁_le_r₂ hS.r₂_lt_ρp⟩
  have h1 := hEq hr₁
  have hψ : S.psi ℓ z G (Real.log S.r₁) = 1 := (psi_spec S hS ℓ hℓ z hz G).2.1
  simp only [adjEig, hψ, one_mul, map_eq_zero] at h1
  exact Mres_ne_zero S hz (ℓ : ℤ) G S.r₁ h1

end NonUniqueEuler.AdjointAux
