import NonUniqueEuler.I.Sec4.PropU
import NonUniqueEuler.I.Sec4.Uniform
import NonUniqueEuler.I.Sec4.Eigendata
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.I.Infra.Polar.Fubini
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Helper for `constants_pos`: the signs of the eigendata constants

Helper of `P/Sec10/ConstantsPos.lean` (`lem:nonempty`, `10_parameters.tex:295-315`). For an
admissible cutoff with (N1)–(N3):
* `sigb_pos`, `sigma_zero_pos`, `z_norm_pos`: `σ_b > 211/2500 > 0`, `σ = σ(0) ≥ σ_b`,
  `|z| ≥ Re z = σ` (`prop:U`(a));
* `cN_pos`, `cout_pos` (`lem:uniform`), `CN_pos` (`C_N ≥ |β(0)||pout_*(0)| > 0`, `prop:U`(b));
* `ellNorm_pos`: `‖ℓ_*‖ ≥ ‖ℓ_*(0)‖ > 0`, since `ℓ_*(0)(φ_*(0)) = 1` (`def:eigendata`);
* `gradPhiL2_pos`: `‖∇Φ‖_{L²} > 0`, since `Φ` is smooth, compactly supported and `Φ ≢ 0`
  (`lem:ring-facts`);
* `Cls_pos`: `C_ls = ‖ℓ_*‖‖∇Φ‖_{L²} > 0`.

The lemmas `angularSector_congr_ae`, `ellFn_congr_ae` (`ℓ_*(G)` on functions only sees the a.e.
class) are copied from `H/Sec9/Handoff/Bridge.lean` (itself copied from other helpers), which
cannot be imported here (import rules, `README.md`).
-/

noncomputable section

open MeasureTheory Set Real Filter Topology
open scoped ENNReal

namespace NonUniqueEuler.Relay.ConstantsPosAux

open RingData

/-! ### `ℓ_*` only sees the a.e. class (copied) -/

/-- The polar parametrisation `(r, θ) ↦ r e^{iθ}` is continuous. -/
theorem continuous_polarParam :
    Continuous fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I) := by
  fun_prop

/-- a.e. equal functions on `ℂ` have a.e. equal angular sectors on `(0, ∞)`. -/
theorem angularSector_congr_ae {g g' : ℂ → ℂ} (h : g =ᵐ[volume] g') (ℓ : ℤ) :
    Polar.angularSector g ℓ =ᵐ[volume.restrict (Ioi 0)] Polar.angularSector g' ℓ := by
  have h0 : volume {x | ¬ g x = g' x} = 0 := ae_iff.1 h
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null h0
  have hmeasN : Measurable (N.indicator (1 : ℂ → ℝ≥0∞)) := measurable_one.indicator hNm
  have hT := Polar.lintegral_eq_lintegral_Ioi_circle hmeasN
  rw [lintegral_indicator_one hNm, hN0] at hT
  have hFm : Measurable fun p : ℝ × ℝ => N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 p.1 p.2) := by
    refine hmeasN.comp ?_
    have : (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) =
        fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I) := by
      funext p; simp [circleMap]
    rw [this]
    exact continuous_polarParam.measurable
  have hGm : Measurable fun r : ℝ => ENNReal.ofReal r *
      ∫⁻ θ in Ioc (0 : ℝ) (2 * π), N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 r θ) :=
    ENNReal.measurable_ofReal.mul
      (hFm.lintegral_prod_right' (ν := volume.restrict (Ioc 0 (2 * π))))
  have hae := (lintegral_eq_zero_iff hGm).1 hT.symm
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioi] with r hr hrpos
  have hrpos' : (0 : ℝ) < r := hrpos
  have hr' : ∫⁻ θ in Ioc (0 : ℝ) (2 * π), N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 r θ) = 0 := by
    have hr2 : ENNReal.ofReal r *
        ∫⁻ θ in Ioc (0 : ℝ) (2 * π), N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 r θ) = 0 := hr
    rcases mul_eq_zero.1 hr2 with h1 | h1
    · exact absurd h1 (ENNReal.ofReal_pos.2 hrpos').ne'
    · exact h1
  have hθm : Measurable fun θ : ℝ => N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 r θ) :=
    hFm.comp (measurable_const.prodMk measurable_id)
  have hθ := (lintegral_eq_zero_iff hθm).1 hr'
  unfold Polar.angularSector
  congr 1
  rw [intervalIntegral.integral_of_le (by positivity),
    intervalIntegral.integral_of_le (by positivity)]
  refine integral_congr_ae ?_
  filter_upwards [hθ] with θ hθ'
  have hnot : circleMap 0 r θ ∉ N := by
    intro hmem
    have : N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 r θ) = 1 := indicator_of_mem hmem _
    simp [this] at hθ'
  have hcm : circleMap 0 r θ = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    simp [circleMap]
  rw [hcm] at hnot
  have heq : g ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
      g' ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
    by_contra hne
    exact hnot (hNsub hne)
  simp only [heq]

/-- `ℓ_*(G)` on functions (`Eig.ellFn`) only depends on the a.e. class of the function. -/
theorem ellFn_congr_ae (χ : ℝ → ℝ) (G : ℝ) {f g : ℂ → ℂ} (hfg : f =ᵐ[volume] g) :
    Eig.ellFn χ G f = Eig.ellFn χ G g := by
  have hs := angularSector_congr_ae hfg 3
  unfold Eig.ellFn SectorSetting.ellStar
  congr 2
  refine integral_congr_ae ?_
  filter_upwards [hs] with r hr
  rw [hr]

/-! ### The signs of the eigendata constants -/

variable {χ : ℝ → ℝ}

/-- `0 ∈ [0, G₁]`. -/
theorem zero_mem_Icc_Gbar : (0 : ℝ) ∈ Icc (0 : ℝ) Gbar := by
  refine ⟨le_rfl, ?_⟩
  unfold Gbar
  positivity

/-- `σ_b > 0` (`prop:U`(a): `σ_b > 211/2500`). -/
theorem sigb_pos (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) : 0 < Eig.sigb χ := by
  have h := (Eig.propU_a χ hχ hN).2.2.2.1
  linarith

/-- `σ_b ≤ σ = σ(0)` (`prop:U`(a), `0 ∈ [0,G₁]`). -/
theorem sigb_le_sigma_zero (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) :
    Eig.sigb χ ≤ Eig.sigma χ 0 := by
  obtain ⟨-, -, ⟨G₀, -, hsigb, hmin⟩, -, -⟩ := Eig.propU_a χ hχ hN
  rw [hsigb]
  exact hmin 0 zero_mem_Icc_Gbar

/-- `σ = σ(0) > 0`. -/
theorem sigma_zero_pos (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) :
    0 < Eig.sigma χ 0 :=
  lt_of_lt_of_le (sigb_pos hχ hN) (sigb_le_sigma_zero hχ hN)

/-- `|z| ≥ Re z = σ > 0`. -/
theorem z_norm_pos (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) :
    0 < ‖Eig.z χ‖ := by
  have h1 : (Eig.z χ).re = Eig.sigma χ 0 := rfl
  have h2 := Complex.re_le_norm (Eig.z χ)
  linarith [sigma_zero_pos hχ hN]

/-- `c_N > 0` (`lem:uniform`). -/
theorem cN_pos (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) : 0 < Eig.cN χ :=
  (Eig.uniform_constants χ hχ hN).2.2.2.2.2.2.1

/-- `c_out > 0` (`lem:uniform`). -/
theorem cout_pos (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) : 0 < Eig.cout χ :=
  (Eig.uniform_constants χ hχ hN).2.2.2.2.2.2.2.1

/-- `C_N ≥ |β(0)||pout_*(0)| > 0` (`lem:uniform`, `prop:U`(b)). -/
theorem CN_pos (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) : 0 < Eig.CN χ := by
  have hle := ((Eig.uniform_constants χ hχ hN).2.2.2.2.2.2.2.2 0 zero_mem_Icc_Gbar).2.1
  obtain ⟨hp, -, -, hb⟩ := (Eig.propU_b χ hχ hN).2.2.2.2.2.2 0 zero_mem_Icc_Gbar
  exact lt_of_lt_of_le (mul_pos hb hp) hle

/-- `‖ℓ_*(0)‖_{(X^0)^*} > 0`, since `ℓ_*(0)(φ_*(0)) = 1` (`def:eigendata`). -/
theorem ell_zero_norm_pos (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) :
    0 < ‖Eig.ell χ 0 0‖ := by
  have hG := zero_mem_Icc_Gbar
  obtain ⟨-, -, hY, hone, -⟩ := Eig.eigendata_phi χ hχ hN hG
  have hspec := Eig.ell_spec_of_exists (Eig.exists_ell χ hχ hN hG 0) (Eig.phiY χ 0 0)
  have hval : Eig.ell χ 0 0 (Eig.phiY χ 0 0) = 1 := by
    rw [hspec, ellFn_congr_ae χ 0 (hY 0).1, hone]
  have hb := (Eig.ell χ 0 0).le_opNorm (Eig.phiY χ 0 0)
  rw [hval] at hb
  refine lt_of_le_of_ne (ContinuousLinearMap.opNorm_nonneg _) (fun h => ?_)
  rw [← h, zero_mul] at hb
  norm_num at hb

/-- `‖ℓ_*‖ ≥ ‖ℓ_*(0)‖ > 0`. -/
theorem ellNorm_pos (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) :
    0 < Eig.ellNorm χ := by
  have hle := ((Eig.uniform_constants χ hχ hN).2.2.2.2.2.2.2.2 0 zero_mem_Icc_Gbar).2.2.2.1
  exact lt_of_lt_of_le (ell_zero_norm_pos hχ hN) hle

/-- `‖∇Φ‖_{L²} > 0`: `|∇Φ|` is continuous and compactly supported, and it is not a.e. zero since
otherwise `Φ` would be constant, hence `0` (compact support), contradicting `Φ ≢ 0`. -/
theorem gradPhiL2_pos (hχ : IsAdmissibleCutoff χ) : 0 < Eig.gradPhiL2 χ := by
  obtain ⟨hsmooth, hcs, -, -, ⟨y₀, hy₀⟩, -⟩ := ringFacts_of_admissible hχ
  set f : ℂ → ℂ := fun y => ((‖fderiv ℝ (ringPhi χ) y‖ : ℝ) : ℂ) with hfdef
  have hcont : Continuous (fderiv ℝ (ringPhi χ)) := hsmooth.continuous_fderiv (by simp)
  have hfc : Continuous f := Complex.continuous_ofReal.comp (continuous_norm.comp hcont)
  have hfcs : HasCompactSupport f :=
    (hcs.fderiv (𝕜 := ℝ)).comp_left (g := fun L : ℂ →L[ℝ] ℝ => ((‖L‖ : ℝ) : ℂ)) (by simp)
  have hmem : MemLp f 2 (volume : Measure ℂ) := hfc.memLp_of_hasCompactSupport hfcs
  have hne_top : eLpNorm f 2 volume ≠ ⊤ := hmem.eLpNorm_ne_top
  have hne_zero : eLpNorm f 2 volume ≠ 0 := by
    intro h0
    have hae : f =ᵐ[volume] 0 :=
      (eLpNorm_eq_zero_iff hmem.aestronglyMeasurable (by norm_num)).1 h0
    have hf0 : f = 0 := (hfc.ae_eq_iff_eq volume continuous_const).1 hae
    have hder : ∀ x, fderiv ℝ (ringPhi χ) x = 0 := by
      intro x
      have hx := congrFun hf0 x
      simp only [hfdef, Pi.zero_apply, Complex.ofReal_eq_zero, norm_eq_zero] at hx
      exact hx
    have hdiff : Differentiable ℝ (ringPhi χ) := hsmooth.differentiable (by simp)
    have hconst := is_const_of_fderiv_eq_zero hdiff hder
    obtain ⟨y₁, hy₁⟩ := (ne_univ_iff_exists_notMem _).1 hcs.isCompact.ne_univ
    have hzero : ringPhi χ y₁ = 0 := image_eq_zero_of_notMem_tsupport hy₁
    exact hy₀ ((hconst y₀ y₁).trans hzero)
  unfold Eig.gradPhiL2 Sob.l2
  exact ENNReal.toReal_pos hne_zero hne_top

/-- `C_ls = ‖ℓ_*‖‖∇Φ‖_{L²} > 0`. -/
theorem Cls_pos (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) : 0 < Eig.Cls χ :=
  mul_pos (ellNorm_pos hχ hN) (gradPhiL2_pos hχ)

end NonUniqueEuler.Relay.ConstantsPosAux
