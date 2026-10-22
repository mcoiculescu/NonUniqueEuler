import NonUniqueEuler.Defs.Sec4.Evans
import NonUniqueEuler.Defs.Sec4.Extra1Sector
import NonUniqueEuler.I.Sec4.SectorSetting
import NonUniqueEuler.I.Sec4.EvansBasic
import NonUniqueEuler.I.Sec4.Resolvent
import NonUniqueEuler.I.Sec4.Sector
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Helper for `thm:evans-simple`: basic facts on the eigendata, and the adjoint eigenfunction

Helper of `P/Sec4/EvansSimple.lean` (fully proved). Namespace `NonUniqueEuler.EvansSimpleAux`.
Copied, with the namespace renamed, from `H/Sec4/Adjoint/Basic.lean`, `H/Sec4/Adjoint/Green.lean`
and `H/Sec4/Adjoint/Eigen.lean` (the proof of `lem:adjoint`), which this proof may
not import (import rules, `README.md`). With `X(r) = ψ_*(log r) M_*(r)`:
* `denom_ne_zero`, `Mres_ne_zero`, `psi_eq_denom_mul_X`, `kcoef_mul_X`, continuity on `(0,∞)`;
* `integrableOn_Ioi_of_continuousOn_Icc`, `integrableOn_profile_mul`, `isProfileL2_gStar`;
* `integral_green_mul_symm`: the symmetric kernel of `𝒢_ℓ` (Fubini);
* `weak_eigen`: `∫ (L_ℓ g) X r dr = λ_* ∫ g X r dr` for `g ∈ Y^0_ℓ` (`04_ring.tex:602-612`), the
  identity `ℓ_* ∘ L_ℓ = λ_* ℓ_*` used for `thm:evans-simple`(2) and the converse of (3).
-/

noncomputable section

open MeasureTheory Set Filter Topology ComplexConjugate
open scoped ContDiff

namespace NonUniqueEuler.EvansSimpleAux

open SectorSetting

/-- A function continuous on `[a,b]` and vanishing on `(0,∞) \ [a,b]` is integrable on `(0,∞)`. -/
theorem integrableOn_Ioi_of_continuousOn_Icc {F : ℝ → ℂ} {a b : ℝ}
    (hF : ContinuousOn F (Icc a b)) (hz : ∀ r : ℝ, 0 < r → r ∉ Icc a b → F r = 0) :
    IntegrableOn F (Ioi 0) :=
  (hF.integrableOn_compact isCompact_Icc).of_ae_sdiff_eq_zero measurableSet_Ioi.nullMeasurableSet
    (Eventually.of_forall fun r hr => hz r hr.1 hr.2)

/-- For `g ∈ Y^0_ℓ` (as a profile) and `F` continuous on `[ρ₋,ρ₊]`, `g F` is integrable on
`(0,∞)`. -/
theorem integrableOn_profile_mul (S : SectorSetting) {g : ℝ → ℂ} (hg : S.IsProfileL2 g)
    {F : ℝ → ℂ} (hF : ContinuousOn F (Icc S.ρm S.ρp)) :
    IntegrableOn (fun r => g r * F r) (Ioi 0) := by
  have hgi : IntegrableOn g (Icc S.ρm S.ρp) := hg.1.integrable one_le_two
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hF
  have h1 : IntegrableOn (fun r => g r * F r) (Icc S.ρm S.ρp) := by
    refine Integrable.mul_bdd (c := C) hgi (hF.aestronglyMeasurable measurableSet_Icc) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact hC r hr
  refine h1.of_ae_sdiff_eq_zero measurableSet_Ioi.nullMeasurableSet ?_
  have h2 := (ae_restrict_iff' measurableSet_Ioi).1 hg.2
  filter_upwards [h2] with r hr hr'
  rw [hr hr'.1 hr'.2, zero_mul]

/-- `λ + iℓΩ ≠ 0` when `Re λ > 0`. -/
theorem denom_ne_zero (S : SectorSetting) {z : ℂ} (hz : 0 < z.re) (ℓ : ℤ) (G r : ℝ) :
    z + Complex.I * (ℓ : ℂ) * ((S.Omega G r : ℝ) : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

theorem Mres_ne_zero (S : SectorSetting) {z : ℂ} (hz : 0 < z.re) (ℓ : ℤ) (G r : ℝ) :
    S.Mres ℓ z G r ≠ 0 :=
  inv_ne_zero (denom_ne_zero S hz ℓ G r)

/-- `ψ_*(log r) = (λ_* + iℓΩ(r)) ψ_*(log r) M_*(r)`. -/
theorem psi_eq_denom_mul_X (S : SectorSetting) {z : ℂ} (hz : 0 < z.re) (ℓ : ℕ) (G r : ℝ) :
    S.psi ℓ z G (Real.log r) =
      (z + Complex.I * (ℓ : ℂ) * ((S.Omega G r : ℝ) : ℂ)) *
        (S.psi ℓ z G (Real.log r) * S.Mres ℓ z G r) := by
  have h := denom_ne_zero S hz (ℓ : ℤ) G r
  simp only [Int.cast_natCast] at h
  rw [Mres]
  simp only [Int.cast_natCast]
  field_simp

/-- `k_ℓ X = g_*`, with `X = ψ_*(log r) M_*(r)`. -/
theorem kcoef_mul_X (S : SectorSetting) (ℓ : ℕ) (z : ℂ) (G r : ℝ) :
    S.kcoef ℓ r * (S.psi ℓ z G (Real.log r) * S.Mres ℓ z G r) = S.gStar ℓ z G r := by
  rw [gStar]
  ring

theorem continuousOn_Omega_cast (S : SectorSetting) (hS : S.Valid) (G : ℝ) :
    ContinuousOn (fun r => ((S.Omega G r : ℝ) : ℂ)) (Ioi 0) :=
  Complex.continuous_ofReal.comp_continuousOn (contDiffOn_Omega S hS G).continuousOn

theorem continuousOn_Mres (S : SectorSetting) (hS : S.Valid) {z : ℂ} (hz : 0 < z.re)
    (ℓ : ℤ) (G : ℝ) : ContinuousOn (S.Mres ℓ z G) (Ioi 0) := by
  have h : ContinuousOn (fun r => z + Complex.I * (ℓ : ℂ) * ((S.Omega G r : ℝ) : ℂ)) (Ioi 0) :=
    continuousOn_const.add (continuousOn_const.mul (continuousOn_Omega_cast S hS G))
  exact h.inv₀ fun r _ => denom_ne_zero S hz ℓ G r

theorem continuousOn_psi_log (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    {z : ℂ} (hz : 0 < z.re) (G : ℝ) :
    ContinuousOn (fun r => S.psi ℓ z G (Real.log r)) (Ioi 0) := by
  have hψ := (psi_spec S hS ℓ hℓ z hz G).2.2.2.1.continuous
  exact hψ.comp_continuousOn (Real.continuousOn_log.mono fun r hr => ne_of_gt hr)

/-- `X(r) = ψ_*(log r) M_*(r)` is continuous on `(0,∞)`. -/
theorem continuousOn_X (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    {z : ℂ} (hz : 0 < z.re) (G : ℝ) :
    ContinuousOn (fun r => S.psi ℓ z G (Real.log r) * S.Mres ℓ z G r) (Ioi 0) :=
  (continuousOn_psi_log S hS ℓ hℓ hz G).mul (continuousOn_Mres S hS hz (ℓ : ℤ) G)

theorem Icc_subset_Ioi (S : SectorSetting) (hS : S.Valid) : Icc S.ρm S.ρp ⊆ Ioi 0 :=
  fun _ hr => lt_of_lt_of_le hS.ρm_pos hr.1

theorem Icc_r_subset_Icc_ρ (S : SectorSetting) (hS : S.Valid) :
    Icc S.r₁ S.r₂ ⊆ Icc S.ρm S.ρp :=
  Icc_subset_Icc hS.ρm_lt_r₁.le hS.r₂_lt_ρp.le

/-- The eigenprofile `g_*` lies in `Y^0_ℓ` as a profile. -/
theorem isProfileL2_gStar (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {z : ℂ}
    (hz : 0 < z.re) (G : ℝ) (hE : S.evans ℓ z G = 0) : S.IsProfileL2 (S.gStar ℓ z G) := by
  obtain ⟨hcd, hsupp, -⟩ := eigen_of_evans_eq_zero S hS ℓ hℓ z hz G hE
  have hc : ContinuousOn (S.gStar ℓ z G) (Icc S.ρm S.ρp) :=
    hcd.continuousOn.mono (Icc_subset_Ioi S hS)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨MemLp.of_bound (hc.aestronglyMeasurable measurableSet_Icc) C ?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact hC r hr
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr hr'
    exact hsupp r hr fun h => hr' (Icc_r_subset_Icc_ρ S hS h)

/-- Symmetry of the Green kernel (Fubini): `∫ (𝒢_ℓ g) h r dr = ∫ g (𝒢_ℓ h) ρ dρ`. -/
theorem integral_green_mul_symm (ℓ : ℤ) {g h : ℝ → ℂ}
    (hg : IntegrableOn (fun ρ => g ρ * (ρ : ℂ)) (Ioi 0))
    (hh : IntegrableOn (fun r => h r * (r : ℂ)) (Ioi 0)) :
    ∫ r in Ioi (0 : ℝ), green ℓ g r * h r * (r : ℂ) =
      ∫ ρ in Ioi (0 : ℝ), g ρ * green ℓ h ρ * (ρ : ℂ) := by
  set μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμ
  let K : ℝ → ℝ → ℂ := fun r ρ => (((min r ρ / max r ρ) ^ ℓ.natAbs : ℝ) : ℂ)
  let c : ℂ := (((2 * |(ℓ : ℝ)|)⁻¹ : ℝ) : ℂ)
  let F : ℝ → ℝ → ℂ := fun r ρ => K r ρ * ((h r * r) * (g ρ * ρ))
  have hKs : ∀ r ρ, K ρ r = K r ρ := fun r ρ => by simp only [K, min_comm, max_comm]
  have hKm : Measurable (Function.uncurry K) := by
    apply Complex.measurable_ofReal.comp
    exact ((measurable_fst.min measurable_snd).div (measurable_fst.max measurable_snd)).pow_const _
  have hKb : ∀ᵐ p ∂(μ.prod μ), ‖Function.uncurry K p‖ ≤ 1 := by
    rw [hμ, Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
    obtain ⟨h1, h2⟩ := hp
    simp only [mem_Ioi] at h1 h2
    simp only [Function.uncurry, K, Complex.norm_real, Real.norm_eq_abs]
    have hmax : 0 < max p.1 p.2 := lt_max_of_lt_left h1
    have hmin : 0 < min p.1 p.2 := lt_min h1 h2
    rw [abs_of_nonneg (by positivity)]
    apply pow_le_one₀ (by positivity)
    rw [div_le_one hmax]
    exact min_le_max
  have hint : Integrable (Function.uncurry F) (μ.prod μ) := by
    have hP := hh.mul_prod hg
    exact hP.bdd_mul hKm.aestronglyMeasurable hKb
  have hL : ∀ r, green ℓ g r * h r * (r : ℂ) = -c * ∫ ρ in Ioi 0, F r ρ := by
    intro r
    have : ∫ ρ in Ioi 0, F r ρ = (∫ ρ in Ioi (0 : ℝ), K r ρ * g ρ * (ρ : ℂ)) * (h r * r) := by
      rw [← integral_mul_const]
      congr 1
      funext ρ
      simp only [F]
      ring
    rw [this, green]
    ring
  have hR : ∀ ρ, g ρ * green ℓ h ρ * (ρ : ℂ) = -c * ∫ r in Ioi 0, F r ρ := by
    intro ρ
    have : ∫ r in Ioi 0, F r ρ = (∫ r in Ioi (0 : ℝ), K ρ r * h r * (r : ℂ)) * (g ρ * ρ) := by
      rw [← integral_mul_const]
      congr 1
      funext r
      simp only [F, hKs r ρ]
      ring
    rw [this, green]
    ring
  simp_rw [hL, hR]
  rw [integral_const_mul, integral_const_mul, integral_integral_swap hint]

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

end NonUniqueEuler.EvansSimpleAux
