import NonUniqueEuler.Defs.Sec4.Eigendata
import NonUniqueEuler.I.Sec4.Eigendata
import NonUniqueEuler.I.Infra.Polar.Fubini
import NonUniqueEuler.I.Infra.AngularFourier.Sector
import NonUniqueEuler.I.Infra.SectorSpace.Projection

/-!
# Helpers for `P/Sec4/PropSemigroup`: `ℓ_*(G)` only sees the sector `3`

`ℓ_*(G)(w) = n_* ℓ_*(w_3)` (`04_ring.tex:1313-1317`, `04_ring.tex:1499-1500`): on `Y^s(N)`,
`Eig.ell χ s G w = n_*(G) · ellStarY s 3 λ_* G (P_3 w)` (`ell_eq_ellStarY_secProj`).

* `angularSector_congr_ae`: the angular sectors of a.e. equal functions agree a.e. on `(0, ∞)`
  (Tonelli in polar coordinates, `Polar.lintegral_eq_lintegral_Ioi_circle`);
* `angularSector_sectorProj_self`: `(P_ℓ f)_ℓ = f_ℓ` on `(0, ∞)`
  (`Ang.sectorProj_eq_angularSector`).
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal ComplexConjugate

namespace NonUniqueEuler

namespace PropSemigroupH

open Sect RingData

/-- The angular sectors of a.e. equal functions agree a.e. on `(0, ∞)`. -/
theorem angularSector_congr_ae {f g : ℂ → ℂ} (h : f =ᵐ[volume] g) (ℓ : ℤ) :
    Polar.angularSector f ℓ =ᵐ[volume.restrict (Ioi (0 : ℝ))] Polar.angularSector g ℓ := by
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 h)
  have hmeas : Measurable (N.indicator (1 : ℂ → ℝ≥0∞)) := measurable_one.indicator hNm
  have htot := Polar.lintegral_eq_lintegral_Ioi_circle hmeas
  rw [lintegral_indicator_one hNm, hN0] at htot
  have hcm : Continuous fun p : ℝ × ℝ => circleMap 0 p.1 p.2 := by
    simp only [circleMap]
    fun_prop
  have hF : Measurable fun p : ℝ × ℝ => N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 p.1 p.2) :=
    hmeas.comp hcm.measurable
  have hinner : Measurable fun r : ℝ =>
      ∫⁻ θ in Ioc (0 : ℝ) (2 * π), N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 r θ) :=
    hF.lintegral_prod_right'
  have hprod : Measurable fun r : ℝ => ENNReal.ofReal r *
      ∫⁻ θ in Ioc (0 : ℝ) (2 * π), N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 r θ) :=
    (ENNReal.measurable_ofReal.comp measurable_id).mul hinner
  have hae := (lintegral_eq_zero_iff hprod).1 htot.symm
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioi] with r hr hr0
  simp only [Pi.zero_apply] at hr
  have hpos : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hr0).ne'
  have hinner0 :
      ∫⁻ θ in Ioc (0 : ℝ) (2 * π), N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 r θ) = 0 := by
    rcases mul_eq_zero.1 hr with h' | h'
    · exact absurd h' hpos
    · exact h'
  have hcθ : Continuous fun θ : ℝ => circleMap 0 r θ := continuous_circleMap 0 r
  have hθ := (lintegral_eq_zero_iff (hmeas.comp hcθ.measurable)).1 hinner0
  have hθ' := (ae_restrict_iff' measurableSet_Ioc).1 hθ
  unfold Polar.angularSector
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  rw [uIoc_of_le (by positivity)]
  filter_upwards [hθ'] with θ hθ1 hθmem
  have hnot : circleMap 0 r θ ∉ N := by
    intro hm
    have h1 := hθ1 hθmem
    simp [Set.indicator_of_mem hm] at h1
  have hfg : f (circleMap 0 r θ) = g (circleMap 0 r θ) := by
    by_contra hne
    exact hnot (hsub hne)
  simp only [circleMap, zero_add] at hfg
  rw [hfg]

/-- `(P_ℓ f)_ℓ = f_ℓ` at every radius `r > 0`. -/
theorem angularSector_sectorProj_self (ℓ : ℤ) (f : ℂ → ℂ) {r : ℝ} (hr : 0 < r) :
    Polar.angularSector (Ang.sectorProj ℓ f) ℓ r = Polar.angularSector f ℓ r := by
  have key : ∀ θ : ℝ, Ang.sectorProj ℓ f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
      Complex.exp (-((ℓ : ℂ) * θ * Complex.I)) = Polar.angularSector f ℓ r := by
    intro θ
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hx : (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero hr' (Complex.exp_ne_zero _)
    have hn : ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = r := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr]
    rw [Ang.sectorProj_eq_angularSector ℓ f hx, hn]
    have hph : Ang.angPhase ℓ ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
        Complex.exp ((ℓ : ℂ) * θ * Complex.I) := by
      simp only [Ang.angPhase]
      rw [hn, show (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) / (r : ℂ) =
          Complex.exp ((θ : ℂ) * Complex.I) by field_simp, ← Complex.exp_int_mul]
      ring_nf
    rw [hph, mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
  conv_lhs => unfold Polar.angularSector
  rw [intervalIntegral.integral_congr (g := fun _ => Polar.angularSector f ℓ r)
    (fun θ _ => key θ), intervalIntegral.integral_const, sub_zero, Complex.real_smul]
  have hπ : (2 * π : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  push_cast
  field_simp

/-- **`ℓ_*(G)` only sees the sector `3`**: `ℓ_*(G)(w) = n_*(G) ℓ_*((P_3 w)_3)` on `Y^s(N)`
(`04_ring.tex:1313-1317`). -/
theorem ell_eq_ellStarY_secProj (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ)
    (hN : NumericalHypothesis χ) {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) (s : ℕ) (w : Y s annN) :
    Eig.ell χ s G w = (Eig.nstar χ G : ℂ) *
      (ringPhiSetting χ).ellStarY s 3 (Eig.lam χ G) G (secProj s annN 3 w) := by
  have hn : (Eig.nstar χ G : ℂ) ≠ 0 := by
    exact_mod_cast (Eig.eigendata_phi χ hχ hN hG).1.ne'
  have hell := Eig.ell_spec_of_exists (Eig.exists_ell χ hχ hN hG s)
  have hTY : ∃ T : Ysec s (ringPhiSetting χ).Nstar ((3 : ℕ) : ℤ) →L[ℂ] ℂ,
      ∀ g : Ysec s (ringPhiSetting χ).Nstar ((3 : ℕ) : ℤ),
      T g = (ringPhiSetting χ).ellStar 3 (Eig.lam χ G) G
        (Polar.angularSector g.fn ((3 : ℕ) : ℤ)) := by
    refine ⟨((Eig.nstar χ G : ℂ))⁻¹ • (Eig.ell χ s G).comp (inclSec s annN 3), fun g => ?_⟩
    change (Eig.nstar χ G : ℂ)⁻¹ * Eig.ell χ s G (inclSec s annN 3 g) = _
    rw [hell]
    change (Eig.nstar χ G : ℂ)⁻¹ * ((Eig.nstar χ G : ℂ) *
      (ringPhiSetting χ).ellStar 3 (Eig.lam χ G) G (Polar.angularSector g.fn 3)) = _
    rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]
    rfl
  have h1 : (ringPhiSetting χ).ellStarY s 3 (Eig.lam χ G) G (secProj s annN 3 w) =
      (ringPhiSetting χ).ellStar 3 (Eig.lam χ G) G
        (Polar.angularSector (secProj s annN 3 w).fn 3) :=
    SectorSetting.ellStarY_spec_of_exists _ s 3 _ G hTY _
  rw [h1, hell]
  change (Eig.nstar χ G : ℂ) * (ringPhiSetting χ).ellStar 3 (Eig.lam χ G) G
    (Polar.angularSector w.fn 3) = _
  congr 1
  have hP : (secProj s annN 3 w).fn =ᵐ[volume] Ang.sectorProj 3 w.fn :=
    (secProj_spec isRotInvariant_annN 3).1 w
  unfold SectorSetting.ellStar
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [angularSector_congr_ae hP 3, ae_restrict_mem measurableSet_Ioi] with r h1 h2
  rw [h1, angularSector_sectorProj_self 3 _ h2]

end PropSemigroupH

end NonUniqueEuler
