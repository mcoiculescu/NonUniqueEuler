import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import NonUniqueEuler.Defs.Infra.SobolevSpace
import NonUniqueEuler.Defs.Infra.AngularFourier
import NonUniqueEuler.I.Infra.AngularFourier.SectorL2

/-!
# Proof: the `H^k`-valued average is `P_ℓ g`

Proof of `NonUniqueEuler/I/Infra/AngularFourier/Derivatives/Average.lean` (same declaration,
statement copied verbatim). Manuscript: `04_ring.tex:181-185`
(`P_ℓ w = (2π)⁻¹ ∫₀^{2π} e^{-iℓφ} w ∘ O_φ dφ`, an `H^s`-valued average).

Method (as in the interface sketch).
1. The `0`-component map `L : Hk k →L[ℂ] L²` (`PiLp.proj` after the subtype inclusion)
   commutes with the interval integral (`ContinuousLinearMap.intervalIntegral_comp_comm`), so
   the function of the average is the `L²`-valued average of the continuous path `L ∘ F`.
2. `L²` level (`HkAverageAux.Lp_average_ae_eq`): test against `u ∈ L²` (`ext_inner_left`);
   `⟪u, ·⟫` commutes with the integral, `⟪u, f θ⟫ = ∫ conj(u x) g'(O_θ x) dx` for a strongly
   measurable representative `g'` of `g`, and Fubini on `(0, 2π] × ℂ`
   (`integral_integral_swap`) with the Tonelli–Hölder bound
   `∫∫ |u(x)| |g'(O_θ x)| ≤ 2π ‖u‖₂ ‖g‖₂` (`HkAverageAux.integrable_integrand`) turns the result
   into `⟪u, P_ℓ g⟫` (`sectorProj_congr_ae`, `memLp_sectorProj`,
   `I/Infra/AngularFourier/SectorL2.lean`).
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace NonUniqueEuler.Ang

namespace HkAverageAux

/-- The measure `dθ` on `(0, 2π]`. -/
abbrev μθ : Measure ℝ := (volume : Measure ℝ).restrict (Ioc (0 : ℝ) (2 * π))

/-- The phase `e^{-iℓθ}`. -/
abbrev phase (ℓ : ℤ) (θ : ℝ) : ℂ := Complex.exp (-((ℓ : ℂ) * θ * Complex.I))

theorem continuous_phase (ℓ : ℤ) : Continuous (phase ℓ) := by
  unfold phase; fun_prop

theorem enorm_phase (ℓ : ℤ) (θ : ℝ) : ‖phase ℓ θ‖ₑ = 1 := by
  rw [← ofReal_norm, phase, Complex.norm_exp]; simp

theorem continuous_rot_uncurry : Continuous (fun q : ℝ × ℂ => rot q.1 q.2) := by
  unfold rot; fun_prop

/-- Hölder in `L²`: `∫⁻ |u| |v| ≤ ‖u‖₂ ‖v‖₂`. -/
theorem lintegral_enorm_mul_le {u v : ℂ → ℂ} (hu : AEStronglyMeasurable u volume)
    (hv : AEStronglyMeasurable v volume) :
    ∫⁻ x, ‖u x‖ₑ * ‖v x‖ₑ ≤ eLpNorm u 2 volume * eLpNorm v 2 volume := by
  have h := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) hv hu
  rw [eLpNorm_one_eq_lintegral_enorm] at h
  simpa [enorm_mul] using h

/-- The Fubini integrand `(θ, x) ↦ conj(u x) e^{-iℓθ} g(O_θ x)` is integrable on
`(0, 2π] × ℂ`. -/
theorem integrable_integrand {u g : ℂ → ℂ} (hu : MemLp u 2 volume) (hus : StronglyMeasurable u)
    (hg : MemLp g 2 volume) (hgs : StronglyMeasurable g) (ℓ : ℤ) :
    Integrable (Function.uncurry fun (θ : ℝ) (x : ℂ) => star (u x) * (phase ℓ θ * g (rot θ x)))
      (μθ.prod volume) := by
  have hsm : StronglyMeasurable (Function.uncurry fun (θ : ℝ) (x : ℂ) =>
      star (u x) * (phase ℓ θ * g (rot θ x))) := by
    refine StronglyMeasurable.mul ?_ (StronglyMeasurable.mul ?_ ?_)
    · exact (hus.comp_measurable measurable_snd).star
    · exact ((continuous_phase ℓ).comp continuous_fst).stronglyMeasurable
    · exact hgs.comp_measurable continuous_rot_uncurry.measurable
  refine ⟨hsm.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, lintegral_prod _ hsm.measurable.enorm.aemeasurable]
  have hbound : ∀ θ : ℝ, ∫⁻ x, ‖Function.uncurry (fun (θ : ℝ) (x : ℂ) =>
      star (u x) * (phase ℓ θ * g (rot θ x))) (θ, x)‖ₑ ∂volume ≤
      eLpNorm u 2 volume * eLpNorm g 2 volume := by
    intro θ
    have heq : ∀ x, ‖Function.uncurry (fun (θ : ℝ) (x : ℂ) =>
        star (u x) * (phase ℓ θ * g (rot θ x))) (θ, x)‖ₑ = ‖u x‖ₑ * ‖g (rot θ x)‖ₑ := by
      intro x
      have hs : ‖star (u x)‖ₑ = ‖u x‖ₑ := by rw [← ofReal_norm, ← ofReal_norm, norm_star]
      simp only [Function.uncurry_apply_pair, enorm_mul, enorm_phase, one_mul, hs]
    simp_rw [heq]
    refine (lintegral_enorm_mul_le hu.1
      (hgs.comp_measurable (by unfold rot; fun_prop)).aestronglyMeasurable).trans_eq ?_
    rw [eLpNorm_comp_measurePreserving hg.1 (Polar.measurePreserving_rot θ)]
  calc ∫⁻ θ, ∫⁻ x, ‖Function.uncurry (fun (θ : ℝ) (x : ℂ) =>
          star (u x) * (phase ℓ θ * g (rot θ x))) (θ, x)‖ₑ ∂volume ∂μθ
      ≤ ∫⁻ _θ, eLpNorm u 2 volume * eLpNorm g 2 volume ∂μθ := lintegral_mono hbound
    _ < ∞ := by
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc]
      exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hu.2 hg.2) ENNReal.ofReal_lt_top

/-- Fubini: `∫_θ e^{-iℓθ} ∫_x conj(u x) g(O_θ x) = ∫_x conj(u x) ∫_θ e^{-iℓθ} g(O_θ x)`. -/
theorem fubini_identity {u g : ℂ → ℂ} (hu : MemLp u 2 volume) (hus : StronglyMeasurable u)
    (hg : MemLp g 2 volume) (hgs : StronglyMeasurable g) (ℓ : ℤ) :
    ∫ θ, phase ℓ θ * (∫ x, star (u x) * g (rot θ x)) ∂μθ =
      ∫ x, star (u x) * ∫ θ, phase ℓ θ * g (rot θ x) ∂μθ := by
  have h := integral_integral_swap (integrable_integrand hu hus hg hgs ℓ)
  calc ∫ θ, phase ℓ θ * (∫ x, star (u x) * g (rot θ x)) ∂μθ
      = ∫ θ, ∫ x, star (u x) * (phase ℓ θ * g (rot θ x)) ∂volume ∂μθ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
        simp only
        rw [← integral_const_mul]
        congr 1; funext x; ring
    _ = ∫ x, ∫ θ, star (u x) * (phase ℓ θ * g (rot θ x)) ∂μθ ∂volume := h
    _ = ∫ x, star (u x) * ∫ θ, phase ℓ θ * g (rot θ x) ∂μθ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only
        rw [← integral_const_mul]

/-- The `L²` version: the `L²`-valued average of a continuous path of rotated copies of `g`
is `P_ℓ g`. -/
theorem Lp_average_ae_eq {g : ℂ → ℂ} (hg : MemLp g 2 volume)
    {f : ℝ → Lp ℂ 2 (volume : Measure ℂ)} (hf : Continuous f)
    (hfg : ∀ θ : ℝ, (f θ : ℂ → ℂ) =ᵐ[volume] fun x => g (rot θ x)) (ℓ : ℤ) :
    (((2 * π : ℂ)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, phase ℓ θ • f θ :
        Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) =ᵐ[volume] sectorProj ℓ g := by
  set g' := hg.1.mk g with hg'def
  have hgg' : g =ᵐ[volume] g' := hg.1.ae_eq_mk
  have hgs : StronglyMeasurable g' := hg.1.stronglyMeasurable_mk
  have hg'L : MemLp g' 2 volume := hg.ae_eq hgg'
  have hP := memLp_sectorProj hg ℓ
  suffices hAP : ((2 * π : ℂ)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, phase ℓ θ • f θ) =
      hP.1.toLp (sectorProj ℓ g) by
    rw [hAP]; exact hP.1.coeFn_toLp
  refine ext_inner_left ℂ fun u => ?_
  have hint : IntervalIntegrable (fun θ => phase ℓ θ • f θ) volume 0 (2 * π) :=
    ((continuous_phase ℓ).smul hf).continuousOn.intervalIntegrable
  have hinner : ∀ θ : ℝ, inner ℂ u (f θ) = ∫ x, star (u x) * g' (rot θ x) := by
    intro θ
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    have h2 : (fun x => g (rot θ x)) =ᵐ[volume] fun x => g' (rot θ x) :=
      (Polar.measurePreserving_rot θ).quasiMeasurePreserving.ae_eq_comp hgg'
    filter_upwards [hfg θ, h2] with x hx1 hx2
    rw [RCLike.inner_apply', hx1, hx2]
    rfl
  have hinnerP : inner ℂ u (hP.1.toLp (sectorProj ℓ g)) =
      ∫ x, star (u x) * sectorProj ℓ g' x := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hP.1.coeFn_toLp, sectorProj_congr_ae ℓ hgg'] with x hx1 hx2
    rw [RCLike.inner_apply', hx1, hx2]
    rfl
  have hcomm : inner ℂ u (∫ θ in (0 : ℝ)..2 * π, phase ℓ θ • f θ) =
      ∫ θ in (0 : ℝ)..2 * π, phase ℓ θ * inner ℂ u (f θ) := by
    rw [← innerSL_apply_apply ℂ u, ← (innerSL ℂ u).intervalIntegral_comp_comm hint]
    congr 1; funext θ
    rw [map_smul, innerSL_apply_apply, smul_eq_mul]
  rw [inner_smul_right, hcomm, hinnerP]
  simp_rw [hinner]
  rw [intervalIntegral.integral_of_le (by positivity),
    fubini_identity (Lp.memLp u) (Lp.stronglyMeasurable u) hg'L hgs ℓ, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [sectorProj, intervalIntegral.integral_of_le (by positivity)]
  ring

end HkAverageAux

open HkAverageAux

/-- The function of the `Hk`-valued average `(2π)⁻¹ ∫₀^{2π} e^{-iℓθ} F(θ) dθ` of a continuous
path of rotated copies `F θ = g ∘ O_θ` is `P_ℓ g`. -/
theorem Hk_fn_average_ae_eq {k : ℕ} {g : ℂ → ℂ} (hg : MemLp g 2 volume) {F : ℝ → Sob.Hk k}
    (hF : Continuous F) (hFg : ∀ θ : ℝ, (F θ).fn =ᵐ[volume] fun x => g (rot θ x)) (ℓ : ℤ) :
    Sob.Hk.fn ((2 * π : ℂ)⁻¹ •
        ∫ θ in (0 : ℝ)..2 * π, Complex.exp (-((ℓ : ℂ) * θ * Complex.I)) • F θ) =ᵐ[volume]
      sectorProj ℓ g := by
  set L : Sob.Hk k →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
    (PiLp.proj 2 (fun _ : Sob.SobIdx k => Lp ℂ 2 (volume : Measure ℂ)) (Sob.idx0 k)).comp
      (Sob.HkSub k).subtypeL with hLdef
  have hL : ∀ G : Sob.Hk k, Sob.Hk.fn G = ((L G : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) :=
    fun G => rfl
  have hint : IntervalIntegrable (fun θ : ℝ => phase ℓ θ • F θ) volume 0 (2 * π) :=
    ((continuous_phase ℓ).smul hF).continuousOn.intervalIntegrable
  have hcomm : L ((2 * π : ℂ)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, phase ℓ θ • F θ) =
      (2 * π : ℂ)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, phase ℓ θ • L (F θ) := by
    rw [L.map_smul, ← L.intervalIntegral_comp_comm hint]
    simp_rw [L.map_smul]
  rw [hL]
  change ((L ((2 * π : ℂ)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, phase ℓ θ • F θ) :
    Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) =ᵐ[volume] sectorProj ℓ g
  rw [hcomm]
  exact Lp_average_ae_eq hg (L.continuous.comp hF) (fun θ => hFg θ) ℓ

end NonUniqueEuler.Ang
