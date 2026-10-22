import NonUniqueEuler.Defs.Sec4.Evans
import NonUniqueEuler.Defs.Sec4.Extra1Sector
import NonUniqueEuler.I.Sec4.SectorSetting
import NonUniqueEuler.I.Sec4.EvansBasic
import NonUniqueEuler.I.Sec4.Resolvent
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Helper for `lem:adjoint`: basic facts on the eigendata of a sector setting

Helper of `P/Sec4/Adjoint.lean` (`04_ring.tex:602-651`). With `X(r) = ψ_*(log r) M_*(r)`:
* `denom_ne_zero`: `λ + iℓΩ ≠ 0` for `Re λ > 0` (`Ω` is real);
* `psi_eq_denom_mul_X`: `ψ_*(log r) = (λ_* + iℓΩ(r)) X(r)`;
* `kcoef_mul_X`: `k_ℓ X = g_*`;
* continuity on `(0,∞)` of `Ω`, `M_*`, `X`, `g_*`;
* `integrableOn_Ioi_of_continuousOn_Icc`, `integrableOn_profile_mul`: integrability on `(0,∞)` of
  functions vanishing off a compact interval, and of `g F` for `g ∈ Y^0_ℓ`.
-/

noncomputable section

open MeasureTheory Set Filter Topology ComplexConjugate
open scoped ContDiff

namespace NonUniqueEuler.AdjointAux

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

end NonUniqueEuler.AdjointAux
