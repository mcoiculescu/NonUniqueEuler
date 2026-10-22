import NonUniqueEuler.Statement.MainTheorem
import NonUniqueEuler.Defs.Infra.Polar
import NonUniqueEuler.I.Infra.Polar.Newton
import NonUniqueEuler.I.Infra.Polar.Fubini
import NonUniqueEuler.I.Infra.Polar.AngularAverage
import NonUniqueEuler.I.Infra.Polar.RadialDeriv
import NonUniqueEuler.I.Infra.Equimeasurable.Lipschitz
import NonUniqueEuler.I.Sec2.WeakIntegrability
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Proof: `lem:radial-stationary`, radial data give stationary renormalized solutions

Proof of `NonUniqueEuler/I/Sec3/RadialStationary.lean` (same declarations, statements copied
verbatim). Manuscript: `lem:radial-stationary`, `03_compactness.tex:831-876`.

Structure (following the manuscript's proof).
1. `radial_velocity`: Newton's theorem, `Polar.velocity_of_isRadial` (I-POLAR).
2. `RadialStationaryAux.memX_stationary`: the constant function lies in `X_q(T)`.
3. `RadialStationaryAux.integral_space_piece_eq_zero`: for radial `g ∈ L¹` and a field
   `v = c(|x|) K(x)` a.e., `∫ g v·∇φ(t) = 0`. On a full-measure set, `g = ḡ(|x|)`
   (`Polar.ae_eq_angAvg_of_isRadial`) and `v·∇φ(t) = c(r)(2πr²)⁻¹ ∂_θ φ(t)`; polar Fubini
   (`Polar.integral_eq_integral_Ioi_intervalIntegral`) and `∫₀^{2π} ∂_θ φ dθ = 0`
   (`Polar.intervalIntegral_angular_deriv_eq_zero`) give `0`.
4. `RadialStationaryAux.integral_time_piece`: Fubini on `(0,T) × ℝ²` and the fundamental theorem
   of calculus, with `φ(T, ·) = 0`, give `∫₀ᵀ ∫ g ∂_tφ = -∫ g φ(0)`.
5. `radial_stationary`: the integrability conjuncts and the reduction to the identities are
   `isRenormalizedWeakSolution_iff_of_memX` and `integrableOn_transportIntegrand_of_memX`
   (the remark after `def:weak`); the identities follow from 3 and 4 with `g = Υ(f)`
   (`g = f` for `eq:weak`).

Deviation (inessential): the per-`t` splitting of `∫ g (∂_tφ + v·∇φ)` is done for a.e. `t`
(those `t` for which the slice of the slab-integrable integrand is integrable, by Fubini), which
suffices for the `t`-integral. The manuscript states the vanishing "for every `t`".
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler.Compact

namespace RadialStationaryAux

variable {T : ℝ} {φ : ℝ × ℂ → ℝ}

theorem contDiff_one (hφ : IsTestFunction T φ) : ContDiff ℝ 1 φ :=
  hφ.contDiff.of_le (by exact_mod_cast le_top)

theorem differentiable (hφ : IsTestFunction T φ) : Differentiable ℝ φ :=
  (contDiff_one hφ).differentiable one_ne_zero

theorem hasDerivAt_time (hφ : IsTestFunction T φ) (t : ℝ) (x : ℂ) :
    HasDerivAt (fun s => φ (s, x)) (fderiv ℝ φ (t, x) ((1 : ℝ), (0 : ℂ))) t := by
  have h : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : ℂ)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  exact ((differentiable hφ) (t, x)).hasFDerivAt.comp_hasDerivAt t h

theorem timeDeriv_eq (hφ : IsTestFunction T φ) (t : ℝ) (x : ℂ) :
    timeDeriv φ t x = fderiv ℝ φ (t, x) ((1 : ℝ), (0 : ℂ)) :=
  (hasDerivAt_time hφ t x).deriv

theorem continuous_timeDeriv (hφ : IsTestFunction T φ) :
    Continuous (fun p : ℝ × ℂ => timeDeriv φ p.1 p.2) := by
  simp_rw [timeDeriv_eq hφ]
  exact ((contDiff_one hφ).continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem exists_bound_timeDeriv (hφ : IsTestFunction T φ) :
    ∃ C, ∀ t x, |timeDeriv φ t x| ≤ C := by
  obtain ⟨C, hC⟩ := ((contDiff_one hφ).continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (hφ.hasCompactSupport.fderiv (𝕜 := ℝ))
  refine ⟨C, fun t x => ?_⟩
  have h1 : ‖((1 : ℝ), (0 : ℂ))‖ = 1 := by simp [Prod.norm_def]
  rw [timeDeriv_eq hφ, ← Real.norm_eq_abs]
  calc ‖fderiv ℝ φ (t, x) ((1 : ℝ), (0 : ℂ))‖
      ≤ ‖fderiv ℝ φ (t, x)‖ * ‖((1 : ℝ), (0 : ℂ))‖ := (fderiv ℝ φ (t, x)).le_opNorm _
    _ ≤ C := by rw [h1, mul_one]; exact hC _

/-- `∫₀ᵀ ∂_tφ(t, x) dt = -φ(0, x)`, since `φ(T, x) = 0`. -/
theorem integral_timeDeriv (hT : 0 < T) (hφ : IsTestFunction T φ) (x : ℂ) :
    ∫ t in Ioo (0 : ℝ) T, timeDeriv φ t x = -φ (0, x) := by
  have hcont : Continuous (fun t => timeDeriv φ t x) :=
    (continuous_timeDeriv hφ).comp (continuous_id.prodMk continuous_const)
  have hTx : φ (T, x) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact lt_irrefl _ (hφ.support_lt _ h)
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hT.le,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => φ (s, x))
      (fun s _ => by rw [timeDeriv_eq hφ]; exact hasDerivAt_time hφ s x)
      (hcont.intervalIntegrable _ _), hTx, zero_sub]

theorem integrable_mul_timeDeriv (hφ : IsTestFunction T φ) {g : ℂ → ℝ} (hg : Integrable g)
    (t : ℝ) : Integrable (fun x => g x * timeDeriv φ t x) := by
  obtain ⟨C, hC⟩ := exists_bound_timeDeriv hφ
  refine hg.mul_bdd (c := C) ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact ((continuous_timeDeriv hφ).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (Real.norm_eq_abs _).le.trans (hC t x)

/-- `∫₀ᵀ ∫ g ∂_tφ dx dt = -∫ g φ(0, ·) dx` for `g ∈ L¹` (Fubini and the fundamental theorem of
calculus; `03_compactness.tex:871-872`). -/
theorem integral_time_piece (hT : 0 < T) (hφ : IsTestFunction T φ) {g : ℂ → ℝ}
    (hg : Integrable g) :
    ∫ t in Ioo (0 : ℝ) T, ∫ x, g x * timeDeriv φ t x = -∫ x, g x * φ (0, x) := by
  obtain ⟨C, hC⟩ := exists_bound_timeDeriv hφ
  have hint : Integrable (Function.uncurry fun t x => g x * timeDeriv φ t x)
      ((volume.restrict (Ioo (0 : ℝ) T)).prod volume) := by
    refine (hg.comp_snd (volume.restrict (Ioo (0 : ℝ) T))).mul_bdd (c := C)
      (continuous_timeDeriv hφ).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => (Real.norm_eq_abs _).le.trans (hC p.1 p.2))
  rw [integral_integral_swap hint, ← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [integral_const_mul, integral_timeDeriv hT hφ x, mul_neg]

/-- The angular part (`03_compactness.tex:863-870`): for radial `g ∈ L¹` and a field
`v = c(|x|) x^⊥/(2π|x|²)` a.e., `∫ g v · ∇φ(t) = 0` whenever the integrand is integrable. -/
theorem integral_space_piece_eq_zero {g : ℂ → ℝ} (hg : Integrable g) (hgrad : IsRadial g)
    {v : ℂ → ℂ} {c : ℝ → ℝ} (hv : v =ᵐ[volume] fun x => (c ‖x‖ : ℂ) * biotSavartKernel x)
    (hφ : IsTestFunction T φ) (t : ℝ)
    (hint : Integrable (fun x => g x * spaceDeriv φ t x (v x))) :
    ∫ x, g x * spaceDeriv φ t x (v x) = 0 := by
  have hψ : ContDiff ℝ 1 (fun y : ℂ => φ (t, y)) :=
    (contDiff_one hφ).comp (contDiff_const.prodMk contDiff_id)
  let H : ℝ → ℝ := fun r => Real.circleAverage g 0 r * (c r / (2 * Real.pi * r ^ 2))
  let F : ℂ → ℝ := fun x => H ‖x‖ * fderiv ℝ (fun y : ℂ => φ (t, y)) x (Complex.I * x)
  have hae : (fun x => g x * spaceDeriv φ t x (v x)) =ᵐ[volume] F := by
    filter_upwards [Polar.ae_eq_angAvg_of_isRadial hgrad hg.aestronglyMeasurable, hv]
      with x hx1 hx2
    have hsm : (c ‖x‖ : ℂ) * biotSavartKernel x =
        (c ‖x‖ / (2 * Real.pi * ‖x‖ ^ 2)) • (Complex.I * x) := by
      rw [Complex.real_smul, biotSavartKernel]
      push_cast
      ring
    simp only [F, H, spaceDeriv]
    rw [hx1, hx2, hsm, ContinuousLinearMap.map_smul, smul_eq_mul]
    simp only [Polar.angAvg]
    ring
  rw [integral_congr_ae hae, Polar.integral_eq_integral_Ioi_intervalIntegral (hint.congr hae)]
  have hzero : ∀ r ∈ Ioi (0 : ℝ),
      r • ∫ θ in (0 : ℝ)..2 * Real.pi, F (circleMap 0 r θ) = (fun _ : ℝ => (0 : ℝ)) r := by
    intro r hr
    have hr' : |r| = r := abs_of_pos hr
    simp only [F, norm_circleMap_zero, hr']
    rw [intervalIntegral.integral_const_mul, Polar.intervalIntegral_angular_deriv_eq_zero hψ r,
      mul_zero, smul_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi hzero, integral_zero]

theorem volume_restrict_slab (T : ℝ) :
    volume.restrict (slab T) = (volume.restrict (Ioo (0 : ℝ) T)).prod (volume : Measure ℂ) := by
  rw [slab, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

/-- The constant function `ω(t) = f` lies in `X_q(T)`. -/
theorem memX_stationary {q T : ℝ} {f : ℂ → ℝ} (hf1 : MemLp f 1 volume)
    (hfq : MemLp f (ENNReal.ofReal q) volume) : MemX q T (stationary f) where
  aestronglyMeasurable := by
    rw [volume_restrict_slab]
    exact hf1.aestronglyMeasurable.comp_snd
  essBounded := ⟨(eLpNorm f 1 volume).toReal + (eLpNorm f (ENNReal.ofReal q) volume).toReal,
    Filter.Eventually.of_forall fun _ => ⟨hf1, hfq, le_rfl⟩⟩

/-- The transport identity for the stationary function, with a radial integrand `g ∈ L¹`
(`g = Υ(f)`) and the radial field `v_f = Circ_f(|x|) K(x)`. -/
theorem transport_identity (hT : 0 < T) {f g : ℂ → ℝ} (hg : Integrable g) (hgrad : IsRadial g)
    (hv : velocity f =ᵐ[volume] fun x => (Polar.circ f ‖x‖ : ℂ) * biotSavartKernel x)
    (hφ : IsTestFunction T φ)
    (hint : IntegrableOn (fun p : ℝ × ℂ =>
      g p.2 * (timeDeriv φ p.1 p.2 + spaceDeriv φ p.1 p.2 (velocity f p.2))) (slab T)) :
    (∫ t in Ioo (0 : ℝ) T, ∫ x : ℂ,
        g x * (timeDeriv φ t x + spaceDeriv φ t x (velocity f x))) +
      ∫ x, g x * φ (0, x) = 0 := by
  have hae_t : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)),
      Integrable (fun x => g x * (timeDeriv φ t x + spaceDeriv φ t x (velocity f x))) := by
    rw [IntegrableOn, volume_restrict_slab] at hint
    exact hint.prod_right_ae
  have key : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)),
      ∫ x, g x * (timeDeriv φ t x + spaceDeriv φ t x (velocity f x)) =
        ∫ x, g x * timeDeriv φ t x := by
    filter_upwards [hae_t] with t ht
    have hA := integrable_mul_timeDeriv hφ hg t
    have hB : Integrable (fun x => g x * spaceDeriv φ t x (velocity f x)) := by
      refine (ht.sub hA).congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.sub_apply]
      ring
    have hsplit : (fun x => g x * (timeDeriv φ t x + spaceDeriv φ t x (velocity f x))) =
        fun x => g x * timeDeriv φ t x + g x * spaceDeriv φ t x (velocity f x) :=
      funext fun x => mul_add _ _ _
    rw [hsplit, integral_add hA hB, integral_space_piece_eq_zero hg hgrad hv hφ t hB, add_zero]
  rw [integral_congr_ae key, integral_time_piece hT hφ hg, neg_add_cancel]

end RadialStationaryAux

open RadialStationaryAux

set_option linter.unusedVariables false in
/-- **`lem:radial-stationary`**, the velocity formula (`03_compactness.tex:833-834`): for
`4/3 < q < ∞` and radial `f ∈ L¹ ∩ L^q`, `K ∗ f(x) = Circ_f(|x|) x^⊥/(2π|x|²)` for a.e. `x`. -/
theorem radial_velocity {q : ℝ} {f : ℂ → ℝ} (hq : 4 / 3 < q) (hf1 : MemLp f 1 volume)
    (hfq : MemLp f (ENNReal.ofReal q) volume) (hrad : IsRadial f) :
    velocity f =ᵐ[volume] fun x => (Polar.circ f ‖x‖ : ℂ) * biotSavartKernel x := by
  exact Polar.velocity_of_isRadial hrad (memLp_one_iff_integrable.mp hf1)

/-- **`lem:radial-stationary`**, the stationary solution (`03_compactness.tex:834-836`): for
`4/3 < q < ∞`, `T > 0` and radial `f ∈ L¹ ∩ L^q`, the stationary function `ω(t) = f` is a
renormalized weak solution in `X_q(T)` with datum `f`. -/
theorem radial_stationary {q T : ℝ} {f : ℂ → ℝ} (hq : 4 / 3 < q) (hT : 0 < T)
    (hf1 : MemLp f 1 volume) (hfq : MemLp f (ENNReal.ofReal q) volume) (hrad : IsRadial f) :
    IsRenormalizedWeakSolution q T f (stationary f) := by
  have hX : MemX q T (stationary f) := memX_stationary hf1 hfq
  have hv := radial_velocity hq hf1 hfq hrad
  rw [isRenormalizedWeakSolution_iff_of_memX hq hT hf1 hfq hX]
  refine ⟨fun φ hφ => ?_, fun Υ hΥ φ hφ => ?_⟩
  · exact transport_identity hT (memLp_one_iff_integrable.mp hf1) hrad hv hφ
      (integrableOn_transportIntegrand_of_memX hq hT hX hφ).1
  · obtain ⟨⟨K, hK⟩, h0⟩ := hΥ.isLipO
    have hΥint : Integrable (fun x => Υ (f x)) :=
      memLp_one_iff_integrable.mp (hK.comp_memLp h0 hf1)
    have hΥrad : IsRadial (fun x => Υ (f x)) := fun θ => (hrad θ).fun_comp Υ
    exact transport_identity hT hΥint hΥrad hv hφ
      ((integrableOn_transportIntegrand_of_memX hq hT hX hφ).2 Υ hΥ)

end NonUniqueEuler.Compact
