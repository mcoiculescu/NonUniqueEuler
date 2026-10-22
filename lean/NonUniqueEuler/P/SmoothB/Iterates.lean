import NonUniqueEuler.Defs.SmoothB.Iteration
import NonUniqueEuler.I.Infra.BSParam.ContDiff
import NonUniqueEuler.I.Sec2.BSBasic
import NonUniqueEuler.I.Sec2.BSSmooth
import NonUniqueEuler.I.SmoothB.Flow
import NonUniqueEuler.I.SmoothB.FlowFacts
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Proof of `lem:iterates` (the iterates are defined, smooth, transported, norm-preserving)

Proof of the interface `I/SmoothB/Iterates.lean` (`lem:iterates`, `B_global_smooth.tex:208-260`).

The manuscript argues by induction on `j`. The induction predicate (`IterGood ω₀ j`, private)
is (i) together with (ii) for **every** `p ∈ [0, ∞]` (the measure-preservation argument does not
need `p ≥ 1`). From it:
* (iii) for `j` (`velocity_of_good`): space–time smoothness and slab bounds of the derivatives by
  the parametric Biot–Savart interface `I/Infra/BSParam/ContDiff.lean` (this is the manuscript's
  differentiation under the integral sign); `div v^{[j]} = 0` by `lem:BS-basic`(d) applied to
  the slice `ω^{[j]}(t) ∈ C_c^∞`; `|v^{[j]}| ≤ U_*` by `lem:BS-basic`(b) and (ii).
* (iv) for `j` (`flow_of_velocity`): `lem:flow` and `hasDerivAt_comp_flowOf`.
* (i), (ii) for `j + 1` (`good_succ`): `flowOf_disp_le` with the bound `U_*`, and
  `flowOf_measurePreserving` with `eLpNorm_comp_measurePreserving`.

The four declarations of the interface are then derived. The hypothesis `ω₀ ≠ 0` is not used.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace NonUniqueEuler.Smooth

variable {ω₀ : ℂ → ℝ} {R₀ : ℝ}

/-! ### The induction -/

/-- The induction predicate: `lem:iterates`(i) and (ii) (the latter for every exponent). -/
private def IterGood (ω₀ : ℂ → ℝ) (j : ℕ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry (iter ω₀ j)) ∧
    (∀ R₀' : ℝ, (∀ x : ℂ, R₀' < ‖x‖ → ω₀ x = 0) →
      ∀ t : ℝ, ∀ x : ℂ, R₀' + Ustar ω₀ * |t| < ‖x‖ → iter ω₀ j t x = 0) ∧
    ∀ (t : ℝ) (p : ℝ≥0∞), eLpNorm (iter ω₀ j t) p volume = eLpNorm ω₀ p volume

/-- `ω₀` vanishes outside `\bar B_{R₀}` (from `supp ω₀ ⊂ B_{R₀}`). -/
private theorem datum_eq_zero_of_lt (h : IsSmoothDatum ω₀ R₀) :
    ∀ x : ℂ, R₀ < ‖x‖ → ω₀ x = 0 := by
  intro x hx
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have := h.tsupport_subset hmem
  rw [Metric.mem_ball, dist_zero_right] at this
  linarith

/-- `ω₀ ∈ L^p` for every `p`. -/
private theorem datum_memLp (h : IsSmoothDatum ω₀ R₀) (p : ℝ≥0∞) : MemLp ω₀ p volume :=
  h.contDiff.continuous.memLp_of_hasCompactSupport h.hasCompactSupport

/-- The base case `j = 0`. -/
private theorem good_zero (h : IsSmoothDatum ω₀ R₀) : IterGood ω₀ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · exact h.contDiff.comp contDiff_snd
  · intro R₀' hR t x hx
    have : R₀' < ‖x‖ := lt_of_le_of_lt
      (le_add_of_nonneg_right (mul_nonneg (Ustar_nonneg ω₀) (abs_nonneg t))) hx
    exact hR x this
  · intro t p
    rfl

/-- The slab support bound of a good iterate, in the form of `I/Infra/BSParam/ContDiff.lean`. -/
private theorem good_slabSupport (h : IsSmoothDatum ω₀ R₀) {j : ℕ} (hj : IterGood ω₀ j) :
    ∀ T : ℝ, ∃ ρ : ℝ, ∀ t ∈ Icc (-T) T, ∀ x : ℂ, ρ < ‖x‖ → iter ω₀ j t x = 0 := by
  intro T
  refine ⟨R₀ + Ustar ω₀ * |T|, fun t ht x hx => ?_⟩
  apply hj.2.1 R₀ (datum_eq_zero_of_lt h) t x
  have htT : |t| ≤ |T| := by
    rw [abs_le]
    constructor
    · linarith [ht.1, le_abs_self T]
    · linarith [ht.2, le_abs_self T]
  have := mul_le_mul_of_nonneg_left htT (Ustar_nonneg ω₀)
  linarith

/-- The time slices of a good iterate are `C_c^∞`. -/
private theorem good_slice (h : IsSmoothDatum ω₀ R₀) {j : ℕ} (hj : IterGood ω₀ j) (t : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (iter ω₀ j t) ∧ HasCompactSupport (iter ω₀ j t) := by
  refine ⟨?_, ?_⟩
  · have := hj.1.comp ((contDiff_const (c := t)).prodMk contDiff_id)
    exact this
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (R₀ + Ustar ω₀ * |t|)) ?_
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
    exact hj.2.1 R₀ (datum_eq_zero_of_lt h) t x hx

/-- `lem:iterates`(iii) for `j`, from (i) and (ii) for `j`. -/
private theorem velocity_of_good (h : IsSmoothDatum ω₀ R₀) {j : ℕ} (hj : IterGood ω₀ j) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry (iterVel ω₀ j)) ∧
      (∀ T : ℝ, 0 < T → ∀ n : ℕ, ∃ C : ℝ, ∀ t ∈ Icc (-T) T, ∀ x : ℂ,
        ‖iteratedFDeriv ℝ n (Function.uncurry (iterVel ω₀ j)) (t, x)‖ ≤ C) ∧
      (∀ t : ℝ, ∀ x : ℂ, Prelim.divergence (iterVel ω₀ j t) x = 0) ∧
      (∀ t : ℝ, ∀ x : ℂ, ‖iterVel ω₀ j t x‖ ≤ Ustar ω₀) ∧
      IsSmoothBoundedField (iterVel ω₀ j) := by
  have hslab := good_slabSupport h hj
  have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry (iterVel ω₀ j)) :=
    BS.contDiff_velocityField_of_slabSupport (n := ⊤) hj.1 hslab
  have hbd : ∀ t : ℝ, ∀ x : ℂ, ‖iterVel ω₀ j t x‖ ≤ Ustar ω₀ := by
    intro t x
    obtain ⟨hsm, hcs⟩ := good_slice h hj t
    have hmem : ∀ p : ℝ≥0∞, MemLp (iter ω₀ j t) p volume := fun p =>
      ⟨hsm.continuous.aestronglyMeasurable, by rw [hj.2.2 t p]; exact (datum_memLp h p).2⟩
    have := (BS.integrable_and_norm_velocity_le_sqrt_L1_Linf (hmem 1) (hmem ⊤) x).2
    rw [hj.2.2 t 1, hj.2.2 t ⊤] at this
    refine le_of_le_of_eq this ?_
    simp only [Ustar, Amax, l1]
    ring_nf
  refine ⟨hcd, ?_, ?_, hbd, ⟨hcd, fun T _ => ⟨Ustar ω₀, fun t _ x => hbd t x⟩⟩⟩
  · intro T hT n
    exact BS.iteratedFDeriv_velocityField_bounded (n := ⊤) hj.1 hslab hT le_top
  · intro t x
    obtain ⟨hsm, hcs⟩ := good_slice h hj t
    exact (BS.divergence_curl_velocity_of_smooth hsm hcs).1 x

/-- `lem:iterates`(iv) for `j`, from (iii) for `j`. -/
private theorem flow_of_velocity (h : IsSmoothDatum ω₀ R₀) {j : ℕ}
    (hv : IsSmoothBoundedField (iterVel ω₀ j))
    (hdiv : ∀ t : ℝ, ∀ x : ℂ, Prelim.divergence (iterVel ω₀ j t) x = 0) :
    (∀ (s : ℝ) (y : ℂ), maxDomain (iterVel ω₀ j) univ s y = univ) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ × ℂ => iterFlow ω₀ j p.1 p.2.1 p.2.2) ∧
      (∀ (t s : ℝ) (y : ℂ), (fderiv ℝ (iterFlow ω₀ j t s) y).det = 1) ∧
      iter ω₀ (j + 1) 0 = ω₀ ∧
      ∀ t : ℝ, ∀ x : ℂ,
        deriv (fun τ => iter ω₀ (j + 1) τ x) t +
          fderiv ℝ (iter ω₀ (j + 1) t) x (iterVel ω₀ j t x) = 0 := by
  refine ⟨fun s y => (flowOf_global hv s y).1, flowOf_contDiff hv,
    fun t s y => det_fderiv_flowOf hv hdiv t s y, ?_, ?_⟩
  · funext x
    show ω₀ (flowOf (iterVel ω₀ j) 0 0 x) = ω₀ x
    rw [(flowOf_global hv 0 x).2.init]
  · intro t x
    have hg : ContDiff ℝ 1 ω₀ := h.contDiff.of_le (by exact_mod_cast le_top)
    have hd := hasDerivAt_comp_flowOf hv hg 0 t x
    have e1 : (fun τ => iter ω₀ (j + 1) τ x) =
        fun τ => ω₀ (flowOf (iterVel ω₀ j) 0 τ x) := rfl
    have e2 : iter ω₀ (j + 1) t = fun z => ω₀ (flowOf (iterVel ω₀ j) 0 t z) := rfl
    rw [e1, e2, hd.deriv]
    exact neg_add_cancel _

/-- (i) and (ii) for `j + 1`, from (iii) for `j`. -/
private theorem good_succ (h : IsSmoothDatum ω₀ R₀) {j : ℕ}
    (hv : IsSmoothBoundedField (iterVel ω₀ j))
    (hdiv : ∀ t : ℝ, ∀ x : ℂ, Prelim.divergence (iterVel ω₀ j t) x = 0)
    (hbd : ∀ t : ℝ, ∀ x : ℂ, ‖iterVel ω₀ j t x‖ ≤ Ustar ω₀) :
    IterGood ω₀ (j + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · have hF := flowOf_contDiff hv
    have hin : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℂ => ((0 : ℝ), p.1, p.2)) :=
      contDiff_const.prodMk (contDiff_fst.prodMk contDiff_snd)
    exact h.contDiff.comp (hF.comp hin)
  · intro R₀' hR t x hx
    show ω₀ (flowOf (iterVel ω₀ j) 0 t x) = 0
    by_contra hne
    set a := flowOf (iterVel ω₀ j) 0 t x with ha_def
    have ha : ‖a‖ ≤ R₀' := by
      by_contra hlt
      exact hne (hR a (lt_of_not_ge hlt))
    have hs : t ∈ Icc (-|t|) |t| := ⟨neg_abs_le t, le_abs_self t⟩
    have h0 : (0 : ℝ) ∈ Icc (-|t|) |t| := ⟨by linarith [abs_nonneg t], abs_nonneg t⟩
    have hdisp := flowOf_disp_le hv (T := |t|) (M := Ustar ω₀) (fun τ _ z => hbd τ z) hs h0 x
    rw [← ha_def, zero_sub, abs_neg] at hdisp
    have htri : ‖x‖ ≤ ‖a‖ + ‖a - x‖ := by
      have := norm_sub_le a (a - x)
      simp only [sub_sub_cancel] at this
      linarith [norm_sub_rev a (a - x), this]
    have : ‖x‖ ≤ R₀' + Ustar ω₀ * |t| := by
      rw [mul_comm] at hdisp
      linarith
    linarith
  · intro t p
    exact eLpNorm_comp_measurePreserving (p := p) h.contDiff.continuous.aestronglyMeasurable
      (flowOf_measurePreserving hv hdiv 0 t)

/-- Every iterate satisfies (i) and (ii) (`lem:iterates`, induction on `j`). -/
private theorem iterGood (h : IsSmoothDatum ω₀ R₀) : ∀ j : ℕ, IterGood ω₀ j
  | 0 => good_zero h
  | j + 1 => by
    have hv := velocity_of_good h (iterGood h j)
    exact good_succ h hv.2.2.2.2 hv.2.2.1 hv.2.2.2.1

/-! ### The interface declarations -/

/-- `lem:iterates`(i): `ω^{[j]} ∈ C^∞(ℝ × ℝ²)` is real, and `ω^{[j]}(t, x) = 0` for
`|x| > R₀' + U_*|t|`. -/
theorem iterates_smooth_support (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (j : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry (iter ω₀ j)) ∧
      ∀ R₀' : ℝ, (∀ x : ℂ, R₀' < ‖x‖ → ω₀ x = 0) →
        ∀ t : ℝ, ∀ x : ℂ, R₀' + Ustar ω₀ * |t| < ‖x‖ → iter ω₀ j t x = 0 :=
  ⟨(iterGood h j).1, (iterGood h j).2.1⟩

/-- `lem:iterates`(ii): `‖ω^{[j]}(t)‖_{L^p} = ‖ω₀‖_{L^p}` for every `t` and `p ∈ [1, ∞]`. -/
theorem iterates_eLpNorm (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (j : ℕ) (t : ℝ) {p : ℝ≥0∞}
    (hp : 1 ≤ p) :
    eLpNorm (iter ω₀ j t) p volume = eLpNorm ω₀ p volume :=
  (iterGood h j).2.2 t p

/-- `lem:iterates`(iii): `v^{[j]} ∈ C^∞(ℝ × ℝ²; ℝ²)`, every derivative of `v^{[j]}` is bounded on
`[-T, T] × ℝ²` for every `T > 0`, `div v^{[j]} = 0`, and `|v^{[j]}| ≤ U_*`; in particular
`v^{[j]}` satisfies the hypotheses of `lem:flow`. -/
theorem iterates_velocity (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (j : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry (iterVel ω₀ j)) ∧
      (∀ T : ℝ, 0 < T → ∀ n : ℕ, ∃ C : ℝ, ∀ t ∈ Icc (-T) T, ∀ x : ℂ,
        ‖iteratedFDeriv ℝ n (Function.uncurry (iterVel ω₀ j)) (t, x)‖ ≤ C) ∧
      (∀ t : ℝ, ∀ x : ℂ, Prelim.divergence (iterVel ω₀ j t) x = 0) ∧
      (∀ t : ℝ, ∀ x : ℂ, ‖iterVel ω₀ j t x‖ ≤ Ustar ω₀) ∧
      IsSmoothBoundedField (iterVel ω₀ j) :=
  velocity_of_good h (iterGood h j)

/-- `lem:iterates`(iv): `Φ^{[j]}` is defined and `C^∞` on `ℝ × ℝ × ℝ²`, `det D_y Φ^{[j]} ≡ 1`,
`ω^{[j+1]}(0) = ω₀`, and `∂_t ω^{[j+1]} + v^{[j]} · ∇ω^{[j+1]} = 0` on `ℝ × ℝ²`. -/
theorem iterates_flow (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (j : ℕ) :
    (∀ (s : ℝ) (y : ℂ), maxDomain (iterVel ω₀ j) univ s y = univ) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ × ℂ => iterFlow ω₀ j p.1 p.2.1 p.2.2) ∧
      (∀ (t s : ℝ) (y : ℂ), (fderiv ℝ (iterFlow ω₀ j t s) y).det = 1) ∧
      iter ω₀ (j + 1) 0 = ω₀ ∧
      ∀ t : ℝ, ∀ x : ℂ,
        deriv (fun τ => iter ω₀ (j + 1) τ x) t +
          fderiv ℝ (iter ω₀ (j + 1) t) x (iterVel ω₀ j t x) = 0 := by
  have hv := velocity_of_good h (iterGood h j)
  exact flow_of_velocity h hv.2.2.2.2 hv.2.2.1

end NonUniqueEuler.Smooth
