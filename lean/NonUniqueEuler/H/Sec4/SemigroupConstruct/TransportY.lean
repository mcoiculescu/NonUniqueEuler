import NonUniqueEuler.H.Sec4.SemigroupConstruct.LinY
import NonUniqueEuler.I.Infra.SectorSpace.BanachExp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Helpers for `lem:semigroup-construct`(1): the transport group `e^{tL^tr}` on `Y^s`

Helper file of `P/Sec4/SemigroupConstruct.lean` (fully proved). Manuscript `04_ring.tex:963-981`
(R1 form: `e^{tL^tr} = S.transportY s G t = ⊕_ℓ exp(t(-iℓΩ))`).

* `measurePreserving_rot_radial`: `x ↦ O_{φ(|x|)} x` preserves Lebesgue measure (polar Fubini and
  the invariance of `∫_0^{2π}` of a periodic function under shifts), so the transport formula
  `w ↦ w(r, θ - Ω(r;G)t)` preserves `L²`.
* `exists_norm_exp_transSec_le`: `‖exp(t(-iℓΩ))‖_{Y^s_ℓ → Y^s_ℓ} ≤ K(1+|t|)^s` uniformly in `ℓ` and
  `|G| ≤ G₊` (the sector bound and `exists_norm_Ysec_equiv`).
* `sectorProj_transportFn`: `P_ℓ(w ∘ O_{-Ωt}) = e^{-iℓΩt} P_ℓ w` pointwise (substitution and
  periodicity in the angle).
* `transportY_spec`: the four statements of `semigroupConstruct_transportY`.
-/

noncomputable section

open MeasureTheory Set Real Filter Topology
open scoped ContDiff ENNReal

namespace NonUniqueEuler.SGC

open Sob Sect Ang SectorSetting

/-! ### Rotations by a radial angle preserve Lebesgue measure -/

theorem lintegral_Ioc_shift_of_periodic {T : ℝ} (hT : 0 < T) {g : ℝ → ℝ≥0∞}
    (hg : Function.Periodic g T) (c : ℝ) :
    ∫⁻ θ in Ioc 0 T, g (θ + c) = ∫⁻ θ in Ioc 0 T, g θ := by
  have : Fact (0 < T) := ⟨hT⟩
  have hA : MeasurableEmbedding fun x : ℝ => x + c :=
    (Homeomorph.addRight c).isClosedEmbedding.measurableEmbedding
  have h1 : ∫⁻ θ in Ioc 0 T, g (θ + c) = ∫⁻ θ in Ioc c (c + T), g θ := by
    have := (measurePreserving_add_right volume c).setLIntegral_comp_preimage_emb hA g
      (Ioc c (c + T))
    rw [preimage_add_const_Ioc, sub_self, add_sub_cancel_left] at this
    exact this
  have h2 := AddCircle.lintegral_preimage T c hg.lift
  have h3 := AddCircle.lintegral_preimage T 0 hg.lift
  simp only [Function.Periodic.lift_coe, zero_add] at h2 h3
  rw [h1, h2, h3]

theorem rot_circleMap {r : ℝ} (a θ : ℝ) :
    rot a (circleMap 0 r θ) = circleMap 0 r (θ + a) := by
  simp only [rot, circleMap, zero_add, Complex.ofReal_add, add_mul, Complex.exp_add]
  ring

/-- `x ↦ O_{φ(|x|)} x` preserves Lebesgue measure. -/
theorem measurePreserving_rot_radial {φ : ℝ → ℝ} (hφ : Measurable φ) :
    MeasurePreserving (fun x : ℂ => rot (φ ‖x‖) x) volume volume := by
  have hm : Measurable (fun x : ℂ => rot (φ ‖x‖) x) := by
    simp only [rot]
    exact (Complex.measurable_exp.comp
      ((Complex.measurable_ofReal.comp (hφ.comp measurable_norm)).mul_const _)).mul measurable_id
  refine ⟨hm, ?_⟩
  ext A hA
  rw [Measure.map_apply hm hA]
  have hF : Measurable (A.indicator (1 : ℂ → ℝ≥0∞)) := measurable_one.indicator hA
  have e1 : volume ((fun x : ℂ => rot (φ ‖x‖) x) ⁻¹' A) =
      ∫⁻ x, A.indicator (1 : ℂ → ℝ≥0∞) (rot (φ ‖x‖) x) := by
    rw [← lintegral_indicator_one (hm hA)]
    rfl
  have e2 : volume A = ∫⁻ x, A.indicator (1 : ℂ → ℝ≥0∞) x :=
    (lintegral_indicator_one hA).symm
  rw [e1, e2]
  refine (Polar.lintegral_eq_lintegral_Ioi_circle (hF.comp hm)).trans ?_
  rw [Polar.lintegral_eq_lintegral_Ioi_circle hF]
  refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hr0 : 0 < r := hr
  congr 1
  have hrot : ∀ θ, rot (φ ‖circleMap 0 r θ‖) (circleMap 0 r θ) = circleMap 0 r (θ + φ r) := by
    intro θ
    rw [norm_circleMap_zero, abs_of_pos hr0, rot_circleMap]
  simp only [Function.comp, hrot]
  exact lintegral_Ioc_shift_of_periodic (g := fun θ => A.indicator 1 (circleMap 0 r θ))
    two_pi_pos (fun θ => congrArg (A.indicator 1) (periodic_circleMap 0 r θ)) (φ r)

/-! ### Measurability of `Ω` -/

theorem measurable_circ (f : ℂ → ℝ) (hf : Measurable f) : Measurable (Polar.circ f) := by
  have h : StronglyMeasurable fun p : ℝ × ℂ => ({q : ℝ × ℂ | ‖q.2‖ < q.1}).indicator
      (fun q => f q.2) p :=
    ((hf.comp measurable_snd).indicator
      (measurableSet_lt (measurable_norm.comp measurable_snd) measurable_fst)).stronglyMeasurable
  have h2 := h.integral_prod_right' (ν := (volume : Measure ℂ))
  have h3 : Polar.circ f = fun r => ∫ y, ({q : ℝ × ℂ | ‖q.2‖ < q.1}).indicator
      (fun q => f q.2) (r, y) := by
    funext r
    rw [Polar.circ, ← integral_indicator Metric.isOpen_ball.measurableSet]
    congr 1
    funext y
    by_cases hy : ‖y‖ < r
    · rw [indicator_of_mem (by simpa using hy), indicator_of_mem (by simpa using hy)]
    · rw [indicator_of_notMem (by simpa using hy), indicator_of_notMem (by simpa using hy)]
  rw [h3]
  exact h2.measurable

theorem measurable_Omega (S : SectorSetting) (hS : S.Valid) (G : ℝ) : Measurable (S.Omega G) := by
  have hc := measurable_circ S.om hS.contDiff.continuous.measurable
  unfold SectorSetting.Omega
  exact ((measurable_id.pow_const 2).inv).mul ((hc.div_const _).add_const _)

/-! ### Uniform bounds of the sector exponentials -/

theorem exists_norm_exp_transSec_le (S : SectorSetting) (hS : S.Valid) (s : ℕ) {Gp : ℝ}
    (hGp : 0 ≤ Gp) :
    ∃ K : ℝ, 0 < K ∧ ∀ (ℓ : ℤ) (G : ℝ), |G| ≤ Gp → ∀ t : ℝ,
      ‖NormedSpace.exp ((t : ℂ) • S.transSec s ℓ G)‖ ≤ K * (1 + |t|) ^ s := by
  obtain ⟨Ct, hCt, hT⟩ := transport_sector S hS s hGp
  obtain ⟨c2, C2, hc2, hC2, h2⟩ := exists_norm_Ysec_equiv s hS.ρm_pos hS.ρm_lt_ρp
  refine ⟨Real.sqrt (C2 / c2) * Ct, by positivity, fun ℓ G hG t => ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun g => ?_
  set E := NormedSpace.exp ((t : ℂ) • S.transSec s ℓ G)
  have hsec : ∀ g' : Ysec s S.Nstar ℓ, S.secNormY s g' ^ 2 =
      Sob.secNormSq s ℓ (Icc S.ρm S.ρp) (Polar.angularSector g'.fn ℓ) := fun g' =>
    Real.sq_sqrt (secNormSq_nonneg s ℓ measurableSet_Icc
      (fun r hr => hS.ρm_pos.le.trans hr.1) _)
  have hb := hT ℓ G hG t g
  have hn0 : 0 ≤ S.secNormY s g := Real.sqrt_nonneg _
  have hnE : 0 ≤ S.secNormY s (E g) := Real.sqrt_nonneg _
  have hup : ‖E g‖ ^ 2 ≤ C2 * S.secNormY s (E g) ^ 2 := by
    rw [hsec]; exact (h2 ℓ (E g)).2
  have hlow : c2 * S.secNormY s g ^ 2 ≤ ‖g‖ ^ 2 := by
    rw [hsec]; exact (h2 ℓ g).1
  have hsq : ‖E g‖ ^ 2 ≤ (Real.sqrt (C2 / c2) * Ct * (1 + |t|) ^ s * ‖g‖) ^ 2 := by
    have h1 : S.secNormY s (E g) ^ 2 ≤ (Ct * (1 + |t|) ^ s * S.secNormY s g) ^ 2 :=
      pow_le_pow_left₀ hnE hb 2
    have h3 : S.secNormY s g ^ 2 ≤ ‖g‖ ^ 2 / c2 := by
      rw [le_div_iff₀ hc2]
      linarith
    calc ‖E g‖ ^ 2 ≤ C2 * S.secNormY s (E g) ^ 2 := hup
      _ ≤ C2 * (Ct * (1 + |t|) ^ s * S.secNormY s g) ^ 2 :=
          mul_le_mul_of_nonneg_left h1 hC2.le
      _ = C2 * (Ct * (1 + |t|) ^ s) ^ 2 * S.secNormY s g ^ 2 := by ring
      _ ≤ C2 * (Ct * (1 + |t|) ^ s) ^ 2 * (‖g‖ ^ 2 / c2) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = (Real.sqrt (C2 / c2) * Ct * (1 + |t|) ^ s * ‖g‖) ^ 2 := by
          rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
          field_simp
  exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hsq

/-! ### The transport formula on sector projections -/

theorem sectorProj_transportFn (S : SectorSetting) (G t : ℝ) (f : ℂ → ℂ) (ℓ : ℤ) (x : ℂ) :
    sectorProj ℓ (S.transportFn G t f) x =
      Complex.exp (-(Complex.I * (ℓ : ℂ) * ((S.Omega G ‖x‖ : ℝ) : ℂ) * (t : ℂ))) *
        sectorProj ℓ f x := by
  set c := S.Omega G ‖x‖ * t with hc
  have h1 : ∀ φ : ℝ, S.transportFn G t f (rot φ x) = f (rot (φ + -c) x) := by
    intro φ
    simp only [transportFn, Polar.norm_rot, hc]
    rw [← Polar.rot_add, add_comm]
  set F : ℝ → ℂ := fun ψ => Complex.exp (-((ℓ : ℂ) * ψ * Complex.I)) * f (rot ψ x) with hF
  have hper : Function.Periodic F (2 * π) := by
    intro ψ
    simp only [hF]
    have hr : rot (ψ + 2 * π) x = rot ψ x := by
      simp only [rot, Complex.ofReal_add, add_mul, Complex.exp_add]
      rw [show ((2 * π : ℝ) : ℂ) * Complex.I = 2 * π * Complex.I by push_cast; ring,
        Complex.exp_two_pi_mul_I, mul_one]
    rw [hr]
    congr 1
    have : -((ℓ : ℂ) * ((ψ + 2 * π : ℝ) : ℂ) * Complex.I) =
        -((ℓ : ℂ) * ψ * Complex.I) + (-(ℓ : ℤ)) * (2 * π * Complex.I) := by
      push_cast; ring
    have h1 : Complex.exp (-(ℓ : ℂ) * (2 * π * Complex.I)) = 1 := by
      have := Complex.exp_int_mul_two_pi_mul_I (-ℓ)
      push_cast at this
      exact this
    rw [this, Complex.exp_add, h1, mul_one]
  have h2 : ∫ φ in (0 : ℝ)..2 * π, Complex.exp (-((ℓ : ℂ) * φ * Complex.I)) *
      S.transportFn G t f (rot φ x) =
      Complex.exp (-((ℓ : ℂ) * c * Complex.I)) * ∫ ψ in (0 : ℝ)..2 * π, F ψ := by
    have e1 : ∀ φ : ℝ, Complex.exp (-((ℓ : ℂ) * φ * Complex.I)) * S.transportFn G t f (rot φ x) =
        Complex.exp (-((ℓ : ℂ) * c * Complex.I)) * F (φ + -c) := by
      intro φ
      rw [h1, hF]
      simp only
      rw [← mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    simp only [e1]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_add_right F (-c)]
    congr 1
    have := hper.intervalIntegral_add_eq (0 + -c) 0
    rw [zero_add] at this
    rw [zero_add, show 2 * π + -c = -c + 2 * π by ring, this, zero_add]
  simp only [sectorProj]
  rw [h2]
  simp only [hF]
  rw [← mul_assoc, mul_comm _ (Complex.exp _), mul_assoc]
  congr 2
  rw [hc]
  push_cast
  ring

theorem memLp_transportFn (S : SectorSetting) (hS : S.Valid) (G t : ℝ) {f : ℂ → ℂ}
    (hf : MemLp f 2 volume) : MemLp (S.transportFn G t f) 2 volume := by
  have hφ : Measurable fun r : ℝ => -(S.Omega G r * t) :=
    ((measurable_Omega S hS G).mul_const t).neg
  exact hf.comp_measurePreserving (measurePreserving_rot_radial hφ)

/-! ### The transport group -/

theorem continuous_exp_smul_gen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (A : E →L[ℂ] E) :
    Continuous fun τ : ℝ => NormedSpace.exp ((τ : ℂ) • A) :=
  continuous_iff_continuousAt.2 fun τ => (BanachExp.hasDerivAt_exp_smul A τ).1.continuousAt

theorem transportY_spec (S : SectorSetting) (hS : S.Valid) (s : ℕ) {Gp : ℝ}
    (hGp : 0 ≤ Gp) :
    ∃ C : ℝ, 0 < C ∧ ∀ G : ℝ, |G| ≤ Gp →
      (∀ t : ℝ, ‖S.transportY s G t‖ ≤ C * (1 + |t|) ^ s) ∧
      (∀ (t : ℝ) (w : Y s S.Nstar),
        (S.transportY s G t w).fn =ᵐ[volume] S.transportFn G t w.fn) ∧
      (∀ t t' : ℝ, S.transportY s G (t + t') = (S.transportY s G t).comp (S.transportY s G t')) ∧
      (∀ w : Y s S.Nstar, Continuous fun t => S.transportY s G t w) := by
  obtain ⟨K, hK, hKb⟩ := exists_norm_exp_transSec_le S hS s hGp
  obtain ⟨B, hB, hBs⟩ := exists_sectorSum_spec s hS.ρm_pos hS.ρm_lt_ρp
  refine ⟨B * K, by positivity, fun G hG => ⟨fun t => ?_, fun t w => ?_, fun t t' => ?_,
    fun w => ?_⟩⟩
  · have := (hBs (fun ℓ => NormedSpace.exp ((t : ℂ) • S.transSec s ℓ G)) (K * (1 + |t|) ^ s)
      fun ℓ => hKb ℓ G hG t).2
    calc ‖S.transportY s G t‖ ≤ B * (K * (1 + |t|) ^ s) := this
      _ = B * K * (1 + |t|) ^ s := by ring
  · refine ae_eq_of_sectorProj (y_memLp _) (memLp_transportFn S hS G t (y_memLp w)) fun ℓ => ?_
    have hP : secProj s S.Nstar ℓ (S.transportY s G t w) =
        NormedSpace.exp ((t : ℂ) • S.transSec s ℓ G) (secProj s S.Nstar ℓ w) :=
      secProj_sectorSum (A := fun ℓ => NormedSpace.exp ((t : ℂ) • S.transSec s ℓ G))
        hS.ρm_pos hS.ρm_lt_ρp (fun ℓ => hKb ℓ G hG t) ℓ w
    have h1 := (secProj_spec (s := s) S.isRotInvariant_Nstar ℓ).1 (S.transportY s G t w)
    rw [hP] at h1
    have h2 := exp_transSec_spec S hS s ℓ G t (secProj s S.Nstar ℓ w)
    have h3 := (secProj_spec (s := s) S.isRotInvariant_Nstar ℓ).1 w
    filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
    rw [← hx1, hx2, hx3, sectorProj_transportFn]
  · have hA : ∀ ℓ, ‖NormedSpace.exp ((t : ℂ) • S.transSec s ℓ G)‖ ≤ K * (1 + |t|) ^ s :=
      fun ℓ => hKb ℓ G hG t
    have hA' : ∀ ℓ, ‖NormedSpace.exp ((t' : ℂ) • S.transSec s ℓ G)‖ ≤ K * (1 + |t'|) ^ s :=
      fun ℓ => hKb ℓ G hG t'
    have h := sectorSum_comp hS.ρm_pos hS.ρm_lt_ρp hA hA'
    have he : (fun ℓ => NormedSpace.exp (((t + t' : ℝ) : ℂ) • S.transSec s ℓ G)) =
        fun ℓ => (NormedSpace.exp ((t : ℂ) • S.transSec s ℓ G)).comp
          (NormedSpace.exp ((t' : ℂ) • S.transSec s ℓ G)) := by
      funext ℓ
      rw [BanachExp.exp_smul_add]
      rfl
    show sectorSum s S.Nstar (fun ℓ => NormedSpace.exp (((t + t' : ℝ) : ℂ) • S.transSec s ℓ G)) =
      (sectorSum s S.Nstar fun ℓ => NormedSpace.exp ((t : ℂ) • S.transSec s ℓ G)).comp
        (sectorSum s S.Nstar fun ℓ => NormedSpace.exp ((t' : ℂ) • S.transSec s ℓ G))
    rw [he]
    exact h
  · rw [continuous_iff_continuousAt]
    intro t₀
    set T := |t₀| + 1
    have hJ : ∀ t ∈ Icc (-T) T, ∀ ℓ,
        ‖NormedSpace.exp ((t : ℂ) • S.transSec s ℓ G)‖ ≤ K * (1 + T) ^ s := by
      intro t ht ℓ
      refine (hKb ℓ G hG t).trans ?_
      have : |t| ≤ T := abs_le.2 ⟨ht.1, ht.2⟩
      gcongr
    have hc : ∀ (ℓ : ℤ) (g : Ysec s S.Nstar ℓ),
        ContinuousOn (fun t : ℝ => NormedSpace.exp ((t : ℂ) • S.transSec s ℓ G) g)
          (Icc (-T) T) := by
      intro ℓ g
      exact ((continuous_exp_smul_gen (S.transSec s ℓ G)).clm_apply continuous_const).continuousOn
    have hcon := continuousOn_sectorSum hS.ρm_pos hS.ρm_lt_ρp
      (A := fun t ℓ => NormedSpace.exp ((t : ℂ) • S.transSec s ℓ G)) hJ hc w
    have hmem : Icc (-T) T ∈ 𝓝 t₀ := Icc_mem_nhds (by
      have := neg_abs_le t₀; linarith) (by have := le_abs_self t₀; linarith)
    exact hcon.continuousAt hmem

end NonUniqueEuler.SGC
