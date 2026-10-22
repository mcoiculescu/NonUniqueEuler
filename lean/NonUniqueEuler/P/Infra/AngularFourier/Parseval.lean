import NonUniqueEuler.Defs.Infra.AngularFourier
import NonUniqueEuler.I.Infra.AngularFourier.Sector
import NonUniqueEuler.I.Infra.AngularFourier.SectorL2
import NonUniqueEuler.H.Infra.AngularFourier.Parseval.PolarSum
import NonUniqueEuler.H.Infra.AngularFourier.Parseval.Hilbert

/-!
# Proof: the angular Fourier series in `L²(ℂ)` and Parseval's identity (library I-ANG)

Proof of `NonUniqueEuler/I/Infra/AngularFourier/Parseval.lean` (`02_prelim.tex:33-34`,
`04_ring.tex:178-180`).

Structure.
1. *Parseval in polar form* (`hasSum_angularSector_sq`): reduce to a strongly measurable
   representative (`ParsevalH.ae_angularSector_eq`), then
   `ParsevalH.hasSum_angularSector_sq_of_stronglyMeasurable` (Tonelli in polar coordinates,
   Mathlib's `hasSum_sq_fourierCoeffOn` on almost every circle, monotone convergence).
2. `‖P_ℓ g‖²_{L²} = 2π ∫₀^∞ |g_ℓ|² r dr` (`l2_sectorProj_sq`): `P_ℓ g = g_ℓ(r) e^{iℓθ}` off the
   origin (`sectorProj_eq_angularSector`) and `memLp_ofProfile_iff`. With 1 this is the `L²`
   Parseval identity `hasSum_norm_sq_sectorProjL`.
3. `P_ℓ P_m = δ_{ℓm} P_m` on `L²` (`sectorProjL_comp`) from the pointwise identity
   `sectorProj_sectorProj`.
4. Self-adjointness, orthogonality and `f = ∑ P_ℓ f` follow abstractly from 2 and 3
   (`H/.../Parseval/Hilbert.lean`): the proof does not use Fubini for inner products; it derives
   orthogonality from Parseval.
5. Uniqueness from 1 and 2.
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace NonUniqueEuler.Ang

/-! ### Auxiliary facts -/

/-- `x ≠ 0` for almost every `x ∈ ℂ`. -/
private theorem ae_ne_zero : ∀ᵐ x : ℂ ∂volume, x ≠ 0 := by
  have h : volume ({0} : Set ℂ) = 0 := measure_singleton 0
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h] with x hx
  simpa using hx

/-- `P_ℓ g = g_ℓ(r) e^{iℓθ}` almost everywhere. -/
private theorem sectorProj_ae_eq_ofProfile (ℓ : ℤ) (g : ℂ → ℂ) :
    sectorProj ℓ g =ᵐ[volume] ofProfile ℓ (Polar.angularSector g ℓ) := by
  filter_upwards [ae_ne_zero] with x hx
  rw [sectorProj_eq_angularSector ℓ g hx, ofProfile]

/-- `‖P_ℓ g‖²_{L²} = 2π ∫₀^∞ |g_ℓ(r)|² r dr`. -/
private theorem l2_sectorProj_sq (ℓ : ℤ) {g : ℂ → ℂ} (hg : AEStronglyMeasurable g volume) :
    Sob.l2 (sectorProj ℓ g) ^ 2 =
      2 * π * ∫ r in Ioi 0, ‖Polar.angularSector g ℓ r‖ ^ 2 * r := by
  have h1 : Sob.l2 (sectorProj ℓ g) = Sob.l2 (ofProfile ℓ (Polar.angularSector g ℓ)) := by
    simp only [Sob.l2]
    rw [eLpNorm_congr_ae (sectorProj_ae_eq_ofProfile ℓ g)]
  rw [h1]
  exact (memLp_ofProfile_iff (ℓ := ℓ) (ParsevalH.aestronglyMeasurable_angularSector hg ℓ)).2

/-- The `L²` norm of an `Lp` element is `Sob.l2` of its representative. -/
private theorem norm_eq_l2 (f : Lp ℂ 2 (volume : Measure ℂ)) : ‖f‖ = Sob.l2 (f : ℂ → ℂ) := by
  rw [Lp.norm_def, Sob.l2]

private theorem norm_sectorProjL_sq (ℓ : ℤ) (f : Lp ℂ 2 (volume : Measure ℂ)) :
    ‖sectorProjL ℓ f‖ ^ 2 =
      2 * π * ∫ r in Ioi 0, ‖Polar.angularSector (f : ℂ → ℂ) ℓ r‖ ^ 2 * r := by
  rw [norm_eq_l2, ← l2_sectorProj_sq ℓ (Lp.aestronglyMeasurable f)]
  simp only [Sob.l2]
  rw [eLpNorm_congr_ae (sectorProjL_spec ℓ f)]

/-! ### Parseval in polar form -/

/-- Parseval in polar form: `‖g‖²_{L²} = 2π ∑_ℓ ∫₀^∞ |g_ℓ(r)|² r dr`. -/
theorem hasSum_angularSector_sq {g : ℂ → ℂ} (hg : MemLp g 2 volume) :
    HasSum (fun ℓ : ℤ => 2 * π * ∫ r in Ioi 0, ‖Polar.angularSector g ℓ r‖ ^ 2 * r)
      (Sob.l2 g ^ 2) := by
  set g' : ℂ → ℂ := hg.1.mk g with hg'
  have hae : g =ᵐ[volume] g' := hg.1.ae_eq_mk
  have hL2' : MemLp g' 2 volume := hg.ae_eq hae
  have h := ParsevalH.hasSum_angularSector_sq_of_stronglyMeasurable hg.1.stronglyMeasurable_mk
    hL2'
  have hl2 : Sob.l2 g = Sob.l2 g' := by
    simp only [Sob.l2]
    rw [eLpNorm_congr_ae hae]
  have hsec : ∀ ℓ : ℤ, ∫ r in Ioi 0, ‖Polar.angularSector g ℓ r‖ ^ 2 * r =
      ∫ r in Ioi 0, ‖Polar.angularSector g' ℓ r‖ ^ 2 * r := by
    intro ℓ
    refine integral_congr_ae ?_
    filter_upwards [ParsevalH.ae_angularSector_eq hae] with r hr
    rw [hr ℓ]
  rw [hl2]
  simp_rw [hsec]
  exact h

/-- Parseval: `‖f‖² = ∑_ℓ ‖P_ℓ f‖²`. -/
theorem hasSum_norm_sq_sectorProjL (f : Lp ℂ 2 (volume : Measure ℂ)) :
    HasSum (fun ℓ : ℤ => ‖sectorProjL ℓ f‖ ^ 2) (‖f‖ ^ 2) := by
  simp_rw [norm_sectorProjL_sq]
  rw [norm_eq_l2]
  exact hasSum_angularSector_sq (Lp.memLp f)

/-! ### Algebra of the projections -/

/-- `P_ℓ` is idempotent and `P_ℓ P_m = 0` for `ℓ ≠ m`. -/
theorem sectorProjL_comp (ℓ m : ℤ) :
    (sectorProjL ℓ).comp (sectorProjL m) = if ℓ = m then sectorProjL m else 0 := by
  refine ContinuousLinearMap.ext fun f => ?_
  rw [ContinuousLinearMap.comp_apply]
  refine Lp.ext ?_
  have h1 := sectorProjL_spec ℓ (sectorProjL m f)
  have h2 := sectorProj_congr_ae ℓ (sectorProjL_spec m f)
  by_cases hℓm : ℓ = m
  · subst hℓm
    rw [ite_eq_left rfl]
    filter_upwards [h1, h2, sectorProjL_spec ℓ f] with x hx1 hx2 hx3
    rw [hx1, hx2, congrFun (sectorProj_sectorProj ℓ ℓ f) x, ite_eq_left rfl, hx3]
  · rw [ite_eq_right hℓm]
    filter_upwards [h1, h2, Lp.coeFn_zero ℂ 2 (volume : Measure ℂ)] with x hx1 hx2 hx3
    rw [hx1, hx2, congrFun (sectorProj_sectorProj ℓ m f) x, ite_eq_right hℓm,
      zero_apply, hx3]

/-- `P_ℓ` is self-adjoint on `L²`. -/
theorem inner_sectorProjL (ℓ : ℤ) (f g : Lp ℂ 2 (volume : Measure ℂ)) :
    inner ℂ (sectorProjL ℓ f) g = inner ℂ f (sectorProjL ℓ g) :=
  ParsevalH.inner_apply_eq_of_parseval sectorProjL sectorProjL_comp hasSum_norm_sq_sectorProjL
    ℓ f g

/-- Orthogonality of different sectors. -/
theorem inner_sectorProjL_of_ne {ℓ m : ℤ} (h : ℓ ≠ m) (f g : Lp ℂ 2 (volume : Measure ℂ)) :
    inner ℂ (sectorProjL ℓ f) (sectorProjL m g) = 0 :=
  ParsevalH.inner_apply_apply_of_ne_of_parseval sectorProjL sectorProjL_comp
    hasSum_norm_sq_sectorProjL h f g

/-- The angular Fourier series converges in `L²`: `f = ∑_ℓ P_ℓ f`. -/
theorem hasSum_sectorProjL (f : Lp ℂ 2 (volume : Measure ℂ)) :
    HasSum (fun ℓ : ℤ => sectorProjL ℓ f) f :=
  ParsevalH.hasSum_apply_of_parseval sectorProjL sectorProjL_comp hasSum_norm_sq_sectorProjL f

/-! ### Uniqueness -/

/-- Uniqueness: a function in `L²` all of whose sectors vanish is `0` a.e. -/
theorem ae_eq_zero_of_sectorProj {g : ℂ → ℂ} (hg : MemLp g 2 volume)
    (h : ∀ ℓ : ℤ, sectorProj ℓ g =ᵐ[volume] 0) : g =ᵐ[volume] 0 := by
  have hzero : ∀ ℓ : ℤ, 2 * π * ∫ r in Ioi 0, ‖Polar.angularSector g ℓ r‖ ^ 2 * r = 0 := by
    intro ℓ
    rw [← l2_sectorProj_sq ℓ hg.1, Sob.l2, eLpNorm_congr_ae (h ℓ), eLpNorm_zero]
    simp
  have hs := hasSum_angularSector_sq hg
  simp_rw [hzero] at hs
  have hl2 : Sob.l2 g ^ 2 = 0 := hs.unique hasSum_zero
  have hl2' : (eLpNorm g 2 volume).toReal = 0 := by
    rw [Sob.l2] at hl2
    exact pow_eq_zero_iff (n := 2) two_ne_zero |>.1 hl2
  have hnorm : eLpNorm g 2 volume = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff _).1 hl2' with h0 | htop
    · exact h0
    · exact absurd htop hg.2.ne
  exact (eLpNorm_eq_zero_iff hg.1 two_ne_zero).1 hnorm

end NonUniqueEuler.Ang
