import Mathlib.Analysis.Normed.Algebra.Exponential
import NonUniqueEuler.Defs.Infra.SectorSpace
import NonUniqueEuler.I.Infra.Sobolev.Space
import NonUniqueEuler.I.Infra.Polar.Fubini
import NonUniqueEuler.I.Infra.AngularFourier.Sector
import NonUniqueEuler.I.Infra.SectorSpace.Projection
import NonUniqueEuler.I.Infra.SectorSpace.Decomposition

/-!
# Helpers for `P/Sec4/PropSU`: elements of the sector spaces and sector profiles

Generic facts about `Y s K`, `Ysec s K ℓ` and the sector profiles, used to identify the Riesz
projection `Eig.R` sector by sector.

* extensionality: an element of `Y s K` or `Ysec s K ℓ` is determined by the a.e. class of its
  function (`Sob.Hk.ext_fn`); functions of sums and scalar multiples;
* an element of `Y^s` on an annulus is determined by its sector projections (`hasSum_secProj`);
* `angularSector_congr_ae`: a.e. equal plane functions have a.e. (in `r > 0`) equal sector
  profiles (Tonelli in polar coordinates);
* `angularSector_secProj_ae`: the sector-`ℓ` profile of `P_ℓ w` is that of `w` (a.e. in `r > 0`);
* `conj_ofProfile`: `conj(h(|x|) e^{iℓθ}) = conj h(|x|) e^{-iℓθ}`.

The first group and `angularSector_congr_ae`, `angularSector_sectorProj` are copies of the
corresponding helpers of `H/Sec4/SemigroupLaw/Basic.lean` and `H/Sec4/SemigroupLaw/Profile.lean`,
which this proof may not import (import rules, `README.md`); they live in the separate namespace
`NonUniqueEuler.PropSUH` to avoid clashes.
-/

noncomputable section

open MeasureTheory Set Real ComplexConjugate
open scoped ENNReal

namespace NonUniqueEuler.PropSUH

open Sob Ang Sect

variable {s : ℕ} {K : Set ℂ}

/-! ### Tuples and their functions -/

theorem tupleFn_add (F G : SobTuple s) :
    tupleFn (F + G) =ᵐ[volume] tupleFn F + tupleFn G :=
  Lp.coeFn_add (F.ofLp (idx0 s)) (G.ofLp (idx0 s))

theorem tupleFn_smul (c : ℂ) (F : SobTuple s) :
    tupleFn (c • F) =ᵐ[volume] c • tupleFn F :=
  Lp.coeFn_smul c (F.ofLp (idx0 s))

theorem tupleFn_zero : tupleFn (0 : SobTuple s) =ᵐ[volume] 0 :=
  Lp.coeFn_zero ℂ 2 volume

/-- Two elements of `H^s` with a.e. equal functions are equal (as tuples). -/
theorem tuple_ext {F G : SobTuple s} (hF : F ∈ HkSub s) (hG : G ∈ HkSub s)
    (h : tupleFn F =ᵐ[volume] tupleFn G) : F = G := by
  have := Hk.ext_fn (F := (⟨F, hF⟩ : Hk s)) (G := ⟨G, hG⟩) h
  exact congrArg Subtype.val this

theorem Y_ext_fn {w v : Y s K} (h : w.fn =ᵐ[volume] v.fn) : w = v :=
  Subtype.ext (tuple_ext (YSub_le_HkSub s K w.2) (YSub_le_HkSub s K v.2) h)

theorem Ysec_ext_fn {ℓ : ℤ} {g h : Ysec s K ℓ} (hgh : g.fn =ᵐ[volume] h.fn) : g = h :=
  Subtype.ext (tuple_ext (YSub_le_HkSub s K (YsecSub_le_YSub s K ℓ g.2))
    (YSub_le_HkSub s K (YsecSub_le_YSub s K ℓ h.2)) hgh)

theorem Y_fn_add (w v : Y s K) : (w + v).fn =ᵐ[volume] w.fn + v.fn :=
  tupleFn_add (w : SobTuple s) v

theorem Y_fn_smul (c : ℂ) (w : Y s K) : (c • w).fn =ᵐ[volume] c • w.fn :=
  tupleFn_smul c (w : SobTuple s)

theorem Ysec_fn_smul {ℓ : ℤ} (c : ℂ) (g : Ysec s K ℓ) : (c • g).fn =ᵐ[volume] c • g.fn :=
  tupleFn_smul c (g : SobTuple s)

theorem Ysec_fn_zero {ℓ : ℤ} : (0 : Ysec s K ℓ).fn =ᵐ[volume] 0 :=
  tupleFn_zero

/-! ### Sector projections -/

/-- An element of `Y^s` on an annulus is determined by its sector projections. -/
theorem Y_ext_of_secProj {ρm ρp : ℝ} (hρm : 0 < ρm) (hρ : ρm < ρp)
    {a b : Y s (closedAnnulus ρm ρp)}
    (h : ∀ ℓ, secProj s _ ℓ a = secProj s _ ℓ b) : a = b := by
  have ha := hasSum_secProj hρm hρ a
  have hb := hasSum_secProj hρm hρ b
  simp only [h] at ha
  exact ha.unique hb

/-- `P_m (inclSec ℓ g) = g` if `m = ℓ`. -/
theorem secProj_inclSec_self (hK : IsRotInvariant K) (ℓ : ℤ) (g : Ysec s K ℓ) :
    secProj s K ℓ (inclSec s K ℓ g) = g := by
  apply Subtype.ext
  rw [secProj_inclSec hK ℓ ℓ g]
  simp

/-- `P_m (inclSec ℓ g) = 0` if `m ≠ ℓ`. -/
theorem secProj_inclSec_ne (hK : IsRotInvariant K) {ℓ m : ℤ} (hm : m ≠ ℓ) (g : Ysec s K ℓ) :
    secProj s K m (inclSec s K ℓ g) = 0 := by
  apply Subtype.ext
  rw [secProj_inclSec hK ℓ m g]
  simp [hm]

/-! ### Sector profiles -/

/-- A.e. equal plane functions have a.e. equal sector profiles on `(0, ∞)`. -/
theorem angularSector_congr_ae {f₁ f₂ : ℂ → ℂ} (h : f₁ =ᵐ[volume] f₂) (ℓ : ℤ) :
    Polar.angularSector f₁ ℓ =ᵐ[volume.restrict (Ioi (0 : ℝ))] Polar.angularSector f₂ ℓ := by
  set N := toMeasurable (volume : Measure ℂ) {x | f₁ x ≠ f₂ x} with hNdef
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : (volume : Measure ℂ) N = 0 := by
    rw [hNdef, measure_toMeasurable]
    exact h
  have hind : Measurable (N.indicator (1 : ℂ → ℝ≥0∞)) := measurable_one.indicator hNm
  have key := Polar.lintegral_eq_lintegral_Ioi_circle hind
  rw [lintegral_indicator_one hNm, hN0] at key
  have hcont : Continuous fun p : ℝ × ℝ => circleMap 0 p.1 p.2 := by
    unfold circleMap
    fun_prop
  have hF : Measurable fun p : ℝ × ℝ => N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 p.1 p.2) :=
    hind.comp hcont.measurable
  have hmeas : Measurable fun r : ℝ => ENNReal.ofReal r *
      ∫⁻ θ in Ioc (0 : ℝ) (2 * π), N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 r θ) :=
    ENNReal.measurable_ofReal.mul (hF.lintegral_prod_right' (ν := volume.restrict (Ioc 0 (2 * π))))
  have hae := (lintegral_eq_zero_iff hmeas).1 key.symm
  filter_upwards [hae, self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
    with r hr hr0
  have hint : ∫⁻ θ in Ioc (0 : ℝ) (2 * π), N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 r θ) = 0 := by
    rcases mul_eq_zero.1 hr with h1 | h1
    · exact absurd (ENNReal.ofReal_eq_zero.1 h1) (not_le.2 hr0)
    · exact h1
  have hm : Measurable fun θ : ℝ => N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 r θ) :=
    hind.comp (continuous_circleMap 0 r).measurable
  have hθ : ∀ᵐ θ ∂(volume.restrict (Ioc (0 : ℝ) (2 * π))), circleMap 0 r θ ∉ N := by
    filter_upwards [(lintegral_eq_zero_iff hm).1 hint] with θ hθ hmem
    simp only [Pi.zero_apply] at hθ
    rw [indicator_of_mem hmem] at hθ
    exact one_ne_zero hθ
  unfold Polar.angularSector
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  rw [uIoc_of_le (by positivity), ← ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hθ] with θ hθ
  have hx : (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) = circleMap 0 r θ := by
    simp [circleMap]
  have heq : f₁ (circleMap 0 r θ) = f₂ (circleMap 0 r θ) := by
    by_contra hne
    exact hθ (subset_toMeasurable _ _ hne)
  rw [hx, heq]

/-- `angPhase ℓ (r e^{iθ}) = e^{iℓθ}` for `r > 0`. -/
theorem angPhase_polar (ℓ : ℤ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    angPhase ℓ ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
      Complex.exp ((ℓ : ℂ) * θ * Complex.I) := by
  have hn : ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = r := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  unfold angPhase
  rw [hn, mul_div_cancel_left₀ _ (by exact_mod_cast hr.ne'), ← Complex.exp_int_mul]
  congr 1
  ring

theorem norm_polar {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = r := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
    Complex.norm_exp_ofReal_mul_I, mul_one]

/-- The sector-`ℓ` profile of `P_ℓ f` is that of `f` (on `r > 0`). -/
theorem angularSector_sectorProj (ℓ : ℤ) (f : ℂ → ℂ) {r : ℝ} (hr : 0 < r) :
    Polar.angularSector (sectorProj ℓ f) ℓ r = Polar.angularSector f ℓ r := by
  have hpt : ∀ θ : ℝ, sectorProj ℓ f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
      Complex.exp (-((ℓ : ℂ) * θ * Complex.I)) = Polar.angularSector f ℓ r := by
    intro θ
    have hx : (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hr.ne') (Complex.exp_ne_zero _)
    rw [sectorProj_eq_angularSector ℓ f hx, norm_polar hr θ, angPhase_polar ℓ hr θ, mul_assoc,
      ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
  conv_lhs => rw [Polar.angularSector]
  simp_rw [hpt]
  rw [intervalIntegral.integral_const, sub_zero, Complex.real_smul]
  have hπ : (2 * π : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  push_cast
  field_simp

/-- The sector-`ℓ` profile of `P_ℓ w` is that of `w`, a.e. on `(0, ∞)`. -/
theorem angularSector_secProj_ae (hK : IsRotInvariant K) (ℓ : ℤ) (w : Y s K) :
    Polar.angularSector (secProj s K ℓ w).fn ℓ =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      Polar.angularSector w.fn ℓ := by
  have h1 := angularSector_congr_ae ((secProj_spec hK ℓ).1 w) ℓ
  filter_upwards [h1, self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
    with r hr hr0
  rw [hr]
  exact angularSector_sectorProj ℓ w.fn hr0

/-! ### Conjugation of sector functions -/

theorem conj_angPhase (ℓ : ℤ) (x : ℂ) : conj (angPhase ℓ x) = angPhase (-ℓ) x := by
  unfold angPhase
  rw [map_zpow₀, zpow_neg, ← inv_zpow]
  congr 1
  by_cases hx : x = 0
  · simp [hx]
  · have hn : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hx
    have hu : ‖x / (‖x‖ : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 hx)]
    have hu0 : x / (‖x‖ : ℂ) ≠ 0 := div_ne_zero hx hn
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hu]
    simp

theorem conj_ofProfile (ℓ : ℤ) (h : ℝ → ℂ) (x : ℂ) :
    conj (ofProfile ℓ h x) = ofProfile (-ℓ) (fun r => conj (h r)) x := by
  unfold ofProfile
  rw [map_mul, conj_angPhase]

end NonUniqueEuler.PropSUH
