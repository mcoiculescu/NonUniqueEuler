import NonUniqueEuler.Defs.SmoothB.Solution
import NonUniqueEuler.Defs.Sec2.Spaces
import NonUniqueEuler.I.SmoothB.Smooth
import NonUniqueEuler.I.Sec2.WeakIntegrability
import NonUniqueEuler.H.SmoothB.SmoothWeak.LpCont
import NonUniqueEuler.H.SmoothB.SmoothWeak.TransportIdentity

/-!
# Proof: thm:smooth (7) (the smooth solution is a renormalized weak solution)

Proof of `NonUniqueEuler/I/SmoothB/SmoothWeak.lean` (same declarations, statements copied
verbatim). Manuscript: `thm:smooth`(7), `02_prelim.tex:588-591`, proof
`B_global_smooth.tex:547-565`.

Structure.
1. `SmoothWeakH.transport_identity` (helper): for `u ∈ C¹(ℝ × ℝ²)` solving
   `∂_t u + v·∇u = 0` with `v ∈ C¹`, `div v = 0`, and `φ ∈ 𝒟_T`,
   `∫₀ᵀ∫ u(∂_tφ + v·∇φ) + ∫ u(0)φ(0) = 0` (integration by parts in `t` and in `x`, Fubini).
   It is applied to `u = ω` and to `u = Υ(ω)` (`∂_tΥ(ω) + v·∇Υ(ω) = Υ'(ω)(∂_tω + v·∇ω) = 0`).
2. `SmoothWeakH.memLinfLp_of_continuous`, `SmoothWeakH.tendsto_eLpNorm_sub` (helper): `ω` is
   continuous and `ω(t)` vanishes outside `B_{R(T)}` for `|t| ≤ T`, hence
   `ω ∈ L^∞(0,T; L^p)` for every `p ∈ [1, ∞]` and `t ↦ ω(t)` is continuous into `L^p`.
3. The integrability fields of the weak formulation are the remark after `def:weak`
   (`isRenormalizedWeakSolution_iff_of_memX`).

Deviation (inessential): the bounds `‖ω(t)‖_{L^p} ≤ |B_{R(T)}|^{1/p} sup_{[0,T]×ℝ²} |ω|` are used
instead of the conservation laws `‖ω(t)‖_{L¹} = ‖ω₀‖_{L¹}`, `‖ω(t)‖_{L^∞} = ‖ω₀‖_{L^∞}` of the
manuscript; the conclusion (membership in `L^∞(0,T; L¹ ∩ L^∞)`) is the same.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace NonUniqueEuler.Smooth

variable {ω₀ : ℂ → ℝ} {R₀ : ℝ}

namespace SmoothWeakH

theorem continuous_sol (h : IsSmoothDatum ω₀ R₀) : Continuous (Function.uncurry (sol ω₀)) :=
  (sol_isSmoothSol h).contDiff.continuous

/-- `ω(t)` vanishes outside `B̄_ρ` whenever `R(t) ≤ ρ`. -/
theorem sol_eq_zero_of_notMem (h : IsSmoothDatum ω₀ R₀) {t ρ : ℝ}
    (hρ : suppRadius ω₀ R₀ t ≤ ρ) {x : ℂ} (hx : x ∉ Metric.closedBall (0 : ℂ) ρ) :
    sol ω₀ t x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hx'
  exact hx (Metric.ball_subset_closedBall
    (Metric.ball_subset_ball hρ ((sol_isSmoothSol h).tsupport_subset t hx')))

theorem memLinfLp_sol (h : IsSmoothDatum ω₀ R₀) {T : ℝ} (hT : 0 < T) (p : ℝ≥0∞) :
    Prelim.MemLinfLp (Ioo (0 : ℝ) T) univ p (sol ω₀) :=
  memLinfLp_of_continuous (continuous_sol h) (isCompact_closedBall (0 : ℂ) (suppRadius ω₀ R₀ T))
    (fun t ht x hx => sol_eq_zero_of_notMem h (suppRadius_mono_abs ω₀ R₀ (by
      rw [abs_of_nonneg ht.1, abs_of_pos hT]
      exact ht.2)) hx) p

theorem memLp_sol (h : IsSmoothDatum ω₀ R₀) (t : ℝ) (p : ℝ≥0∞) : MemLp (sol ω₀ t) p volume := by
  have hcs : HasCompactSupport (sol ω₀ t) :=
    HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (suppRadius ω₀ R₀ t))
      fun x hx => sol_eq_zero_of_notMem h le_rfl hx
  exact ((continuous_sol h).comp
    (continuous_const.prodMk continuous_id : Continuous fun x : ℂ => (t, x))).memLp_of_hasCompactSupport
    hcs

/-- `Υ(ω)` solves the transport equation: `∂_tΥ(ω) + v·∇Υ(ω) = Υ'(ω)(∂_tω + v·∇ω) = 0`. -/
theorem transport_comp {ω : ℝ → ℂ → ℝ} {v : ℝ → ℂ → ℂ}
    (hω : ContDiff ℝ 1 (Function.uncurry ω))
    (htr : ∀ t x, deriv (fun s => ω s x) t + fderiv ℝ (ω t) x (v t x) = 0)
    {Υ : ℝ → ℝ} (hΥ : Differentiable ℝ Υ) (t : ℝ) (x : ℂ) :
    deriv (fun s => Υ (ω s x)) t + fderiv ℝ (fun y => Υ (ω t y)) x (v t x) = 0 := by
  have hs : ContDiff ℝ 1 (fun s => ω s x) :=
    hω.comp (contDiff_id.prodMk contDiff_const : ContDiff ℝ 1 fun s : ℝ => (s, x))
  have hy : ContDiff ℝ 1 (ω t) := contDiff_slice hω t
  have h1 : HasDerivAt (fun s => ω s x) (deriv (fun s => ω s x) t) t :=
    ((hs.differentiable one_ne_zero) t).hasDerivAt
  have h2 : HasFDerivAt (ω t) (fderiv ℝ (ω t) x) x :=
    ((hy.differentiable one_ne_zero) x).hasFDerivAt
  have k1 : HasDerivAt (fun s => Υ (ω s x)) (deriv Υ (ω t x) * deriv (fun s => ω s x) t) t :=
    (hΥ _).hasDerivAt.comp t h1
  have k2 : HasFDerivAt (fun y => Υ (ω t y)) (deriv Υ (ω t x) • fderiv ℝ (ω t) x) x :=
    (hΥ _).hasDerivAt.comp_hasFDerivAt x h2
  rw [k1.deriv, k2.fderiv]
  simp only [smul_apply, smul_eq_mul]
  rw [← mul_add, htr t x, mul_zero]

end SmoothWeakH

open SmoothWeakH

/-- thm:smooth (7): for every `T > 0` and every `q ∈ (4/3, ∞)`, the restriction of `ω` to
`[0, T)` lies in `L^∞(0, T; L¹ ∩ L^∞(ℝ²))` and is a renormalized weak solution in `X_q(T)` with
datum `ω₀`. -/
theorem smooth_weak (h : IsSmoothDatum ω₀ R₀) {T q : ℝ} (hT : 0 < T) (hq : 4 / 3 < q) :
    Prelim.MemLinfLp (Ioo (0 : ℝ) T) univ 1 (sol ω₀) ∧
      Prelim.MemLinfLp (Ioo (0 : ℝ) T) univ ⊤ (sol ω₀) ∧
      IsRenormalizedWeakSolution q T ω₀ (sol ω₀) := by
  have hs := sol_isSmoothSol h
  have hX : MemX q T (sol ω₀) := Prelim.memX_iff.2 ⟨memLinfLp_sol h hT 1, memLinfLp_sol h hT _⟩
  have hin : ∀ p : ℝ≥0∞, MemLp ω₀ p volume := fun p =>
    h.contDiff.continuous.memLp_of_hasCompactSupport h.hasCompactSupport
  refine ⟨memLinfLp_sol h hT 1, memLinfLp_sol h hT ⊤, ?_⟩
  rw [isRenormalizedWeakSolution_iff_of_memX hq hT (hin 1) (hin _) hX]
  have hω1 : ContDiff ℝ 1 (Function.uncurry (sol ω₀)) :=
    hs.contDiff.of_le (by exact_mod_cast le_top)
  have hv1 : ContDiff ℝ 1 (Function.uncurry (velocityField (sol ω₀))) :=
    hs.velocity_contDiff.of_le (by exact_mod_cast le_top)
  refine ⟨fun φ hφ => ?_, fun Υ hΥ φ hφ => ?_⟩
  · have := transport_identity hω1 hv1 hs.divergence_eq_zero hs.transport hT hφ
    rwa [hs.init] at this
  · have hΥd : Differentiable ℝ Υ := hΥ.contDiff.differentiable one_ne_zero
    have hu1 : ContDiff ℝ 1 (Function.uncurry fun t x => Υ (sol ω₀ t x)) :=
      hΥ.contDiff.comp hω1
    have := transport_identity hu1 hv1 hs.divergence_eq_zero
      (transport_comp hω1 hs.transport hΥd) hT hφ
    rwa [hs.init] at this

/-- The claim in the proof of thm:smooth (7): `t ↦ ω(t)` is continuous into `L^p(ℝ²)` for every
`p ∈ [1, ∞]` (on `[0, ∞)`). -/
theorem sol_continuousIntoLp (h : IsSmoothDatum ω₀ R₀) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    ContinuousIntoLp p (sol ω₀) := by
  refine ⟨fun t _ => memLp_sol h t p, fun t₀ _ => tendsto_nhdsWithin_of_tendsto_nhds ?_⟩
  refine tendsto_eLpNorm_sub (continuous_sol h)
    (isCompact_closedBall (0 : ℂ) (suppRadius ω₀ R₀ (|t₀| + 1))) (fun t ht x hx => ?_) p
  refine sol_eq_zero_of_notMem h (suppRadius_mono_abs ω₀ R₀ ?_) hx
  have h1 : |t - t₀| ≤ 1 := abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ |t₀| + 1)]
  calc |t| = |t₀ + (t - t₀)| := by ring_nf
    _ ≤ |t₀| + |t - t₀| := abs_add_le _ _
    _ ≤ |t₀| + 1 := by linarith

end NonUniqueEuler.Smooth
