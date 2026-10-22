import NonUniqueEuler.Defs.Sec2.BiotSavart
import NonUniqueEuler.Defs.Sec2.Spaces
import NonUniqueEuler.I.Sec2.Velocity
import NonUniqueEuler.I.Sec2.BSBasic
import NonUniqueEuler.I.Infra.ConvMinkowski.Measurable
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Proof: the integrals of the weak formulation converge (the remark after `def:weak`)

Proof of `I/Sec2/WeakIntegrability.lean` (`02_prelim.tex:545-550`). Same declarations, same
statements.

* `ae_ae_integrable_velocity_of_memX`: `lem:BS-basic`(e) (`BS.ae_integrable_biotSavart_of_L1`)
  for the a.e. `t` with `ω(t) ∈ L¹`.
* `exists_bound_convAbs_of_memX`: `lem:velocity`(a) (`BS.velocity_bounds` with `p = q`, `R = 1`)
  and `‖ω(t)‖_{L¹∩L^q} ≤ M`.
* `integrableOn_transportIntegrand_of_memX`: the generic estimate
  `WeakInt.integrableOn_transportIntegrand_of_abs_le` for any `u` with `|u| ≤ L |ω|`
  (`u = ω`, `L = 1`; `u = Υ(ω)`, `L = ‖Υ'‖_∞`, mean value theorem). The test function has a
  bounded derivative `‖Dφ‖ ≤ D` (continuous with compact support), `∂_tφ = Dφ (1, 0)`,
  `w·∇φ = Dφ (0, w)`; so `|u (∂_tφ + v·∇φ)| ≤ L D (|ω| + |ω| (|K| ∗ |ω|))`, and Tonelli
  (`lintegral_prod_le`, no measurability needed for the upper bound) gives
  `∫_slab ≤ L D (M + C M²) T`.
* `integrable_datum_mul_testFunction`: `φ(0, ·)` is bounded, `ω^in, Υ(ω^in) ∈ L¹`.
* The two equivalences: the fields of the structures from the previous lemmas.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace NonUniqueEuler

namespace WeakInt

/-! ### Derivatives of a test function -/

theorem timeDeriv_eq_fderiv {φ : ℝ × ℂ → ℝ} (hφ : Differentiable ℝ φ) (t : ℝ) (x : ℂ) :
    timeDeriv φ t x = fderiv ℝ φ (t, x) ((1 : ℝ), (0 : ℂ)) := by
  have h1 : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : ℂ)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  exact ((hφ (t, x)).hasFDerivAt.comp_hasDerivAt t h1).deriv

theorem fderiv_slice_eq {φ : ℝ × ℂ → ℝ} (hφ : Differentiable ℝ φ) (t : ℝ) (x : ℂ) :
    fderiv ℝ (fun y => φ (t, y)) x = (fderiv ℝ φ (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ ℂ) :=
  ((hφ (t, x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)).fderiv

theorem spaceDeriv_eq_fderiv {φ : ℝ × ℂ → ℝ} (hφ : Differentiable ℝ φ) (t : ℝ) (x w : ℂ) :
    spaceDeriv φ t x w = fderiv ℝ φ (t, x) ((0 : ℝ), w) := by
  simp only [spaceDeriv, fderiv_slice_eq hφ t x, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply]

theorem differentiable_of_isTestFunction {T : ℝ} {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) :
    Differentiable ℝ φ :=
  hφ.contDiff.differentiable (by simp)

theorem continuous_fderiv_of_isTestFunction {T : ℝ} {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) :
    Continuous (fderiv ℝ φ) :=
  hφ.contDiff.continuous_fderiv (by simp)

/-- A test function has a bounded derivative. -/
theorem exists_bound_fderiv_of_isTestFunction {T : ℝ} {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ p, ‖fderiv ℝ φ p‖ ≤ D := by
  obtain ⟨D, hD⟩ :=
    (continuous_fderiv_of_isTestFunction hφ).bounded_above_of_compact_support
      (hφ.hasCompactSupport.fderiv (𝕜 := ℝ))
  exact ⟨D, (norm_nonneg _).trans (hD 0), hD⟩

theorem abs_timeDeriv_le {T : ℝ} {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) {D : ℝ}
    (hD : ∀ p, ‖fderiv ℝ φ p‖ ≤ D) (t : ℝ) (x : ℂ) : |timeDeriv φ t x| ≤ D := by
  rw [timeDeriv_eq_fderiv (differentiable_of_isTestFunction hφ), ← Real.norm_eq_abs]
  refine ((fderiv ℝ φ (t, x)).le_opNorm _).trans ?_
  have h1 : ‖((1 : ℝ), (0 : ℂ))‖ = 1 := by simp [Prod.norm_def]
  rw [h1, mul_one]
  exact hD _

theorem abs_spaceDeriv_le {T : ℝ} {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) {D : ℝ}
    (hD : ∀ p, ‖fderiv ℝ φ p‖ ≤ D) (t : ℝ) (x w : ℂ) : |spaceDeriv φ t x w| ≤ D * ‖w‖ := by
  rw [spaceDeriv_eq_fderiv (differentiable_of_isTestFunction hφ), ← Real.norm_eq_abs]
  refine ((fderiv ℝ φ (t, x)).le_opNorm _).trans ?_
  have h1 : ‖((0 : ℝ), w)‖ = ‖w‖ := by simp [Prod.norm_def]
  rw [h1]
  exact mul_le_mul_of_nonneg_right (hD _) (norm_nonneg _)

theorem continuous_timeDeriv {T : ℝ} {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) :
    Continuous (fun p : ℝ × ℂ => timeDeriv φ p.1 p.2) := by
  have : (fun p : ℝ × ℂ => timeDeriv φ p.1 p.2) =
      fun p => fderiv ℝ φ p ((1 : ℝ), (0 : ℂ)) := by
    funext p
    rw [timeDeriv_eq_fderiv (differentiable_of_isTestFunction hφ)]
  rw [this]
  exact (continuous_fderiv_of_isTestFunction hφ).clm_apply continuous_const

theorem continuous_fderiv_slice {T : ℝ} {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) :
    Continuous (fun p : ℝ × ℂ => fderiv ℝ (fun y => φ (p.1, y)) p.2) := by
  have : (fun p : ℝ × ℂ => fderiv ℝ (fun y => φ (p.1, y)) p.2) =
      fun p => (fderiv ℝ φ p).comp (ContinuousLinearMap.inr ℝ ℝ ℂ) := by
    funext p
    rw [fderiv_slice_eq (differentiable_of_isTestFunction hφ)]
  rw [this]
  exact (continuous_fderiv_of_isTestFunction hφ).clm_comp continuous_const

/-- The integrand `u (∂_tφ + w·∇φ)` is a.e.-strongly measurable when `u` and `w` are. -/
theorem aestronglyMeasurable_transportIntegrand {T : ℝ} {φ : ℝ × ℂ → ℝ}
    (hφ : IsTestFunction T φ) {μ : Measure (ℝ × ℂ)} {u : ℝ → ℂ → ℝ} {w : ℝ → ℂ → ℂ}
    (hu : AEStronglyMeasurable (Function.uncurry u) μ)
    (hw : AEStronglyMeasurable (fun p : ℝ × ℂ => w p.1 p.2) μ) :
    AEStronglyMeasurable (transportIntegrand u w φ) μ := by
  have hsd : AEStronglyMeasurable (fun p : ℝ × ℂ => spaceDeriv φ p.1 p.2 (w p.1 p.2)) μ :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂
      (continuous_fderiv_slice hφ).aestronglyMeasurable hw
  exact hu.mul ((continuous_timeDeriv hφ).aestronglyMeasurable.add hsd)

/-! ### Renormalizations -/

theorem exists_abs_le_of_isRenormalization {Υ : ℝ → ℝ} (hΥ : IsRenormalization Υ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ s, |Υ s| ≤ L * |s| := by
  obtain ⟨C, hC⟩ := hΥ.deriv_bounded
  have hd : Differentiable ℝ Υ := hΥ.contDiff.differentiable one_ne_zero
  refine ⟨C, (abs_nonneg _).trans (hC 0), fun s => ?_⟩
  have h := convex_univ.norm_image_sub_le_of_norm_deriv_le (f := Υ) (fun x _ => hd x)
    (fun x _ => by rw [Real.norm_eq_abs]; exact hC x) (mem_univ (0 : ℝ)) (mem_univ s)
  simpa [hΥ.map_zero, Real.norm_eq_abs] using h

theorem continuous_of_isRenormalization {Υ : ℝ → ℝ} (hΥ : IsRenormalization Υ) : Continuous Υ :=
  hΥ.contDiff.continuous

/-! ### The slab as a product -/

theorem restrict_slab_eq_prod (T : ℝ) :
    volume.restrict (slab T) = (volume.restrict (Ioo (0 : ℝ) T)).prod (volume : Measure ℂ) := by
  rw [slab, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

/-- `‖g‖_{L¹} ≤ M` from `‖g‖_{L¹} + ‖g‖_{L^q} ≤ M`, as a bound for `∫⁻ |g|`. -/
theorem lintegral_enorm_le_of_normL1Lp_le {q M : ℝ} {g : ℂ → ℝ} (h1 : MemLp g 1 volume)
    (hle : Prelim.normL1Lp (ENNReal.ofReal q) g ≤ M) :
    ∫⁻ x, ‖g x‖ₑ ≤ ENNReal.ofReal M := by
  rw [← eLpNorm_one_eq_lintegral_enorm, ← ENNReal.ofReal_toReal h1.eLpNorm_ne_top]
  refine ENNReal.ofReal_le_ofReal (le_trans ?_ hle)
  exact le_add_of_nonneg_right ENNReal.toReal_nonneg

/-- The pointwise majorant of the transport integrand. -/
theorem enorm_transportIntegrand_le {T : ℝ} {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) {D : ℝ}
    (hD0 : 0 ≤ D) (hD : ∀ p, ‖fderiv ℝ φ p‖ ≤ D) {ω u : ℝ → ℂ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (huω : ∀ t x, |u t x| ≤ L * |ω t x|) (t : ℝ) (x : ℂ) :
    ‖transportIntegrand u (velocityField ω) φ (t, x)‖ₑ ≤
      ENNReal.ofReal (L * D) *
        (‖ω t x‖ₑ + ‖ω t x‖ₑ * Conv.convAbs biotSavartKernel (ω t) x) := by
  have hv : ‖velocityField ω t x‖ₑ ≤ Conv.convAbs biotSavartKernel (ω t) x :=
    Conv.enorm_velocity_le (ω t) x
  have hu : ‖u t x‖ₑ ≤ ENNReal.ofReal L * ‖ω t x‖ₑ := by
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul hL]
    exact ENNReal.ofReal_le_ofReal (huω t x)
  have ha : ‖timeDeriv φ t x‖ₑ ≤ ENNReal.ofReal D := by
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (abs_timeDeriv_le hφ hD t x)
  have hb : ‖spaceDeriv φ t x (velocityField ω t x)‖ₑ ≤
      ENNReal.ofReal D * Conv.convAbs biotSavartKernel (ω t) x := by
    rw [Real.enorm_eq_ofReal_abs]
    refine (ENNReal.ofReal_le_ofReal (abs_spaceDeriv_le hφ hD t x _)).trans ?_
    rw [ENNReal.ofReal_mul hD0, ofReal_norm]
    gcongr
  calc ‖transportIntegrand u (velocityField ω) φ (t, x)‖ₑ
      = ‖u t x‖ₑ * ‖timeDeriv φ t x + spaceDeriv φ t x (velocityField ω t x)‖ₑ := by
        simp only [transportIntegrand, enorm_mul]
    _ ≤ (ENNReal.ofReal L * ‖ω t x‖ₑ) *
          (ENNReal.ofReal D + ENNReal.ofReal D * Conv.convAbs biotSavartKernel (ω t) x) :=
        mul_le_mul' hu ((enorm_add_le _ _).trans (add_le_add ha hb))
    _ = ENNReal.ofReal (L * D) *
          (‖ω t x‖ₑ + ‖ω t x‖ₑ * Conv.convAbs biotSavartKernel (ω t) x) := by
        rw [ENNReal.ofReal_mul hL]
        ring

end WeakInt

open WeakInt

/-- For `ω ∈ X_q(T)` (`q ≥ 1` is not even needed), for a.e. `t ∈ (0,T)` the integral defining
`v(t, x) = K ∗ ω(t)(x)` converges absolutely for a.e. `x` (`lem:BS-basic`(e)). -/
theorem ae_ae_integrable_velocity_of_memX {q T : ℝ} {ω : ℝ → ℂ → ℝ} (hX : MemX q T ω) :
    ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)), ∀ᵐ x : ℂ,
      Integrable (fun y : ℂ => biotSavartKernel (x - y) * (ω t y : ℂ)) volume := by
  obtain ⟨M, hM⟩ := hX.essBounded
  filter_upwards [hM] with t ht
  exact BS.ae_integrable_biotSavart_of_L1 ht.1

/-- `02_prelim.tex:548-550`: for `4/3 < q < ∞` there is `C = C(q)` such that, whenever
`‖ω(t)‖_{L¹∩L^q} ≤ M` for a.e. `t ∈ (0,T)`, also `∫ |ω(t)| (|K| ∗ |ω(t)|) dx ≤ C M²` for a.e.
`t ∈ (0,T)` (in particular `‖ω(t) v(t)‖_{L¹} ≤ C M²`). -/
theorem exists_bound_convAbs_of_memX {q : ℝ} (hq : 4 / 3 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T M : ℝ) (ω : ℝ → ℂ → ℝ),
      (∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)),
        MemLp (ω t) 1 volume ∧ MemLp (ω t) (ENNReal.ofReal q) volume ∧
          Prelim.normL1Lp (ENNReal.ofReal q) (ω t) ≤ M) →
      ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)),
        ∫⁻ x, ‖ω t x‖ₑ * Conv.convAbs biotSavartKernel (ω t) x ≤ ENNReal.ofReal (C * M ^ 2) := by
  obtain ⟨C, hC, hCω⟩ := BS.velocity_bounds hq one_pos
  refine ⟨C, hC, fun T M ω hM => ?_⟩
  filter_upwards [hM] with t ht
  obtain ⟨h1, hqq, hle⟩ := ht
  refine ((hCω (ω t) h1 hqq).2.2.2.2.2).trans (ENNReal.ofReal_le_ofReal ?_)
  have h0 : 0 ≤ Prelim.normL1Lp (ENNReal.ofReal q) (ω t) :=
    add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have h2 : Prelim.normL1Lp (ENNReal.ofReal q) (ω t) ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ h0 hle 2
  exact mul_le_mul_of_nonneg_left h2 hC.le

namespace WeakInt

/-- The generic estimate: for `ω ∈ X_q(T)`, `4/3 < q`, a test function `φ`, and `u` a.e.-strongly
measurable on the slab with `|u| ≤ L |ω|`, the integrand `u (∂_tφ + v·∇φ)`, `v = K ∗ ω`, is
integrable on `(0,T) × ℝ²`. -/
theorem integrableOn_transportIntegrand_of_abs_le {q T : ℝ} (hq : 4 / 3 < q)
    {ω : ℝ → ℂ → ℝ} (hX : MemX q T ω) {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ)
    {u : ℝ → ℂ → ℝ} (hu : AEStronglyMeasurable (Function.uncurry u) (volume.restrict (slab T)))
    {L : ℝ} (hL : 0 ≤ L) (huω : ∀ t x, |u t x| ≤ L * |ω t x|) :
    IntegrableOn (transportIntegrand u (velocityField ω) φ) (slab T) volume := by
  obtain ⟨D, hD0, hD⟩ := exists_bound_fderiv_of_isTestFunction hφ
  obtain ⟨M, hM⟩ := hX.essBounded
  obtain ⟨C, -, hC⟩ := exists_bound_convAbs_of_memX hq
  have hM' : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)),
      MemLp (ω t) 1 volume ∧ MemLp (ω t) (ENNReal.ofReal q) volume ∧
        Prelim.normL1Lp (ENNReal.ofReal q) (ω t) ≤ M := hM
  have hCM := hC T M ω hM'
  refine ⟨aestronglyMeasurable_transportIntegrand hφ hu
    (Conv.aestronglyMeasurable_velocityField_slab hX.aestronglyMeasurable), ?_⟩
  show ∫⁻ p, ‖transportIntegrand u (velocityField ω) φ p‖ₑ ∂(volume.restrict (slab T)) < ∞
  rw [restrict_slab_eq_prod]
  set K : ℝ≥0∞ := ENNReal.ofReal (L * D) * (ENNReal.ofReal M + ENNReal.ofReal (C * M ^ 2))
    with hK
  calc ∫⁻ p, ‖transportIntegrand u (velocityField ω) φ p‖ₑ
          ∂((volume.restrict (Ioo (0 : ℝ) T)).prod volume)
      ≤ ∫⁻ t, ∫⁻ x, ‖transportIntegrand u (velocityField ω) φ (t, x)‖ₑ
          ∂volume ∂(volume.restrict (Ioo (0 : ℝ) T)) := lintegral_prod_le _
    _ ≤ ∫⁻ _t, K ∂(volume.restrict (Ioo (0 : ℝ) T)) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hM', hCM] with t ht htC
        calc ∫⁻ x, ‖transportIntegrand u (velocityField ω) φ (t, x)‖ₑ
            ≤ ∫⁻ x, ENNReal.ofReal (L * D) *
                (‖ω t x‖ₑ + ‖ω t x‖ₑ * Conv.convAbs biotSavartKernel (ω t) x) :=
              lintegral_mono fun x => enorm_transportIntegrand_le hφ hD0 hD hL huω t x
          _ = ENNReal.ofReal (L * D) * ((∫⁻ x, ‖ω t x‖ₑ) +
                ∫⁻ x, ‖ω t x‖ₑ * Conv.convAbs biotSavartKernel (ω t) x) := by
              rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
                lintegral_add_left' ht.1.aestronglyMeasurable.enorm]
          _ ≤ K := by
              rw [hK]
              gcongr _ * ?_
              exact add_le_add (lintegral_enorm_le_of_normL1Lp_le ht.1 ht.2.2) htC
    _ < ∞ := by
        rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo]
        exact ENNReal.mul_lt_top (by rw [hK]; finiteness) ENNReal.ofReal_lt_top

end WeakInt

-- `hT` is part of the interface statement; the proof does not need it (the slab is empty for
-- `T ≤ 0`).
set_option linter.unusedVariables false in
/-- `02_prelim.tex:545-547`: for `ω ∈ X_q(T)`, `4/3 < q`, and every test function `φ ∈ 𝒟_T`, the
integrands `ω (∂_tφ + v·∇φ)` and `Υ(ω) (∂_tφ + v·∇φ)` (`Υ` a renormalization) of `(eq:weak)` and
`(eq:renorm)` are integrable on `(0,T) × ℝ²`. -/
theorem integrableOn_transportIntegrand_of_memX {q T : ℝ} (hq : 4 / 3 < q) (hT : 0 < T)
    {ω : ℝ → ℂ → ℝ} (hX : MemX q T ω) {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) :
    IntegrableOn (transportIntegrand ω (velocityField ω) φ) (slab T) volume ∧
      ∀ Υ : ℝ → ℝ, IsRenormalization Υ →
        IntegrableOn (transportIntegrand (fun t x => Υ (ω t x)) (velocityField ω) φ) (slab T)
          volume := by
  refine ⟨integrableOn_transportIntegrand_of_abs_le hq hX hφ hX.aestronglyMeasurable zero_le_one
    (fun t x => by rw [one_mul]), fun Υ hΥ => ?_⟩
  obtain ⟨L, hL0, hL⟩ := exists_abs_le_of_isRenormalization hΥ
  exact integrableOn_transportIntegrand_of_abs_le hq hX hφ
    ((continuous_of_isRenormalization hΥ).comp_aestronglyMeasurable hX.aestronglyMeasurable) hL0
    (fun t x => hL (ω t x))

/-- The datum terms `ω^in φ(0, ·)` and `Υ(ω^in) φ(0, ·)` of `(eq:weak)` and `(eq:renorm)` are
integrable for `ω^in ∈ L¹`. -/
theorem integrable_datum_mul_testFunction {T : ℝ} {ωin : ℂ → ℝ} (hin : MemLp ωin 1 volume)
    {φ : ℝ × ℂ → ℝ} (hφ : IsTestFunction T φ) :
    Integrable (fun x : ℂ => ωin x * φ (0, x)) volume ∧
      ∀ Υ : ℝ → ℝ, IsRenormalization Υ → Integrable (fun x : ℂ => Υ (ωin x) * φ (0, x)) volume := by
  obtain ⟨B, hB⟩ := hφ.contDiff.continuous.bounded_above_of_compact_support hφ.hasCompactSupport
  have hcont : Continuous (fun x : ℂ => φ (0, x)) :=
    hφ.contDiff.continuous.comp (continuous_const.prodMk continuous_id)
  have hbdd : ∀ᵐ x : ℂ, ‖φ (0, x)‖ ≤ B := ae_of_all _ fun x => hB _
  have hint : Integrable ωin volume := memLp_one_iff_integrable.mp hin
  refine ⟨hint.mul_bdd hcont.aestronglyMeasurable hbdd, fun Υ hΥ => ?_⟩
  obtain ⟨L, -, hL⟩ := exists_abs_le_of_isRenormalization hΥ
  have hΥint : Integrable (fun x => Υ (ωin x)) volume := by
    refine (hint.norm.const_mul L).mono'
      ((continuous_of_isRenormalization hΥ).comp_aestronglyMeasurable hint.aestronglyMeasurable)
      (ae_of_all _ fun x => ?_)
    simpa [Real.norm_eq_abs] using hL (ωin x)
  exact hΥint.mul_bdd hcont.aestronglyMeasurable hbdd

/-- With the integrability fields supplied by the remark, a weak solution in `X_q(T)` is exactly
a function of `X_q(T)` satisfying the identity `(eq:weak)` for every `φ ∈ 𝒟_T`
(`def:weak` as written in the manuscript). -/
theorem isWeakSolution_iff_of_memX {q T : ℝ} {ωin : ℂ → ℝ} {ω : ℝ → ℂ → ℝ} (hq : 4 / 3 < q)
    (hT : 0 < T) (hin1 : MemLp ωin 1 volume) (hinq : MemLp ωin (ENNReal.ofReal q) volume)
    (hX : MemX q T ω) :
    IsWeakSolution q T ωin ω ↔
      ∀ φ : ℝ × ℂ → ℝ, IsTestFunction T φ →
        (∫ t in Ioo (0 : ℝ) T, ∫ x : ℂ, transportIntegrand ω (velocityField ω) φ (t, x)) +
          ∫ x : ℂ, ωin x * φ (0, x) = 0 := by
  constructor
  · intro h
    exact h.weak.identity
  · intro h
    exact ⟨hq, hT, hin1, hinq, hX, ae_ae_integrable_velocity_of_memX hX,
      ⟨fun φ hφ => (integrableOn_transportIntegrand_of_memX hq hT hX hφ).1,
        fun φ hφ => (integrable_datum_mul_testFunction hin1 hφ).1, h⟩⟩

/-- The renormalized version: a renormalized weak solution in `X_q(T)` is exactly a function of
`X_q(T)` satisfying `(eq:weak)` and, for every renormalization `Υ`, `(eq:renorm)`. -/
theorem isRenormalizedWeakSolution_iff_of_memX {q T : ℝ} {ωin : ℂ → ℝ} {ω : ℝ → ℂ → ℝ}
    (hq : 4 / 3 < q) (hT : 0 < T) (hin1 : MemLp ωin 1 volume)
    (hinq : MemLp ωin (ENNReal.ofReal q) volume) (hX : MemX q T ω) :
    IsRenormalizedWeakSolution q T ωin ω ↔
      (∀ φ : ℝ × ℂ → ℝ, IsTestFunction T φ →
        (∫ t in Ioo (0 : ℝ) T, ∫ x : ℂ, transportIntegrand ω (velocityField ω) φ (t, x)) +
          ∫ x : ℂ, ωin x * φ (0, x) = 0) ∧
      ∀ Υ : ℝ → ℝ, IsRenormalization Υ → ∀ φ : ℝ × ℂ → ℝ, IsTestFunction T φ →
        (∫ t in Ioo (0 : ℝ) T, ∫ x : ℂ,
            transportIntegrand (fun t x => Υ (ω t x)) (velocityField ω) φ (t, x)) +
          ∫ x : ℂ, Υ (ωin x) * φ (0, x) = 0 := by
  constructor
  · intro h
    exact ⟨h.weak.identity, fun Υ hΥ => (h.renormalized Υ hΥ).identity⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(isWeakSolution_iff_of_memX hq hT hin1 hinq hX).2 h1, fun Υ hΥ =>
      ⟨fun φ hφ => (integrableOn_transportIntegrand_of_memX hq hT hX hφ).2 Υ hΥ,
        fun φ hφ => (integrable_datum_mul_testFunction hin1 hφ).2 Υ hΥ, h2 Υ hΥ⟩⟩

end NonUniqueEuler
