import NonUniqueEuler.H.Sec4.Eigendata.Setup
import NonUniqueEuler.I.Sec4.EvansBasic
import NonUniqueEuler.I.Sec4.SectorSetting
import NonUniqueEuler.I.Infra.AngularFourier.Derivatives.ProfileL2
import NonUniqueEuler.I.Infra.Sobolev.Norm

/-!
# Helpers for `def:eigendata`: the representer of `ℓ_*(G)` on `L²(N)`

Helper of `P/Sec4/Eigendata.lean` (fully proved). Namespace `NonUniqueEuler.Eig.EigendataH`.
Manuscript `04_ring.tex:1333-1338`.

* `continuousOn_adjEig`: `conj(ψ_*(log r)M_*(r))` is continuous on `(0,∞)`;
* `memLp_ellRep`, `memXFn_ellRep`: the representer lies in `L²` and in `X^0`;
* `ellFn_eq_integral`: for `f ∈ L²` vanishing a.e. off `N`,
  `ℓ_*(G)(f) = ∫ f conj(ellRep)` (Fubini in polar coordinates:
  `∫_0^{2π} f(re^{iθ})e^{-3iθ}dθ = 2π f_3(r)`, and `f_3 = 0` a.e. off `[a/2, 2]`).
-/

noncomputable section

open MeasureTheory Set Real Filter Topology ComplexConjugate
open scoped ENNReal ContDiff

namespace NonUniqueEuler.Eig.EigendataH

open RingData Sect Sob Ang

/-- `annN` is measurable. -/
theorem measurableSet_annN : MeasurableSet annN :=
  isCompact_annN.isClosed.measurableSet

/-- Points of `N` are not `0`. -/
theorem ne_zero_of_mem_annN {x : ℂ} (hx : x ∈ annN) : x ≠ 0 := by
  rw [RingData.mem_annN] at hx
  intro h
  rw [h, norm_zero] at hx
  linarith [a_pos, hx.1]

/-- `M_λ(r) = (λ + iℓΩ(r;G))⁻¹` is continuous on `(0,∞)` for `Re λ > 0`. -/
theorem continuousOn_Mres (S : SectorSetting) (hS : S.Valid) (ℓ : ℤ) {z : ℂ} (hz : 0 < z.re)
    (G : ℝ) : ContinuousOn (S.Mres ℓ z G) (Ioi 0) := by
  have hΩ : ContinuousOn (S.Omega G) (Ioi 0) := (SectorSetting.contDiffOn_Omega S hS G).continuousOn
  have hden : ContinuousOn (fun r => z + Complex.I * (ℓ : ℂ) * ((S.Omega G r : ℝ) : ℂ)) (Ioi 0) :=
    continuousOn_const.add (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hΩ))
  refine hden.inv₀ fun r _ h => ?_
  have h2 := congrArg Complex.re h
  simp at h2
  linarith

/-- `conj(ψ_*(log r) M_*(r))` is continuous on `(0,∞)`. -/
theorem continuousOn_adjEig (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {z : ℂ}
    (hz : 0 < z.re) (G : ℝ) : ContinuousOn (S.adjEig ℓ z G) (Ioi 0) := by
  have hψ : Continuous (S.psi ℓ z G) :=
    (SectorSetting.psi_spec S hS ℓ hℓ z hz G).2.2.2.1.continuous
  have hlog : ContinuousOn Real.log (Ioi 0) :=
    Real.continuousOn_log.mono fun r hr => ne_of_gt hr
  have h1 : ContinuousOn (fun r => S.psi ℓ z G (Real.log r)) (Ioi 0) :=
    hψ.comp_continuousOn hlog
  exact Complex.continuous_conj.comp_continuousOn (h1.mul (continuousOn_Mres S hS ℓ hz G))

/-- The function `c · h(|x|)e^{3iθ}` is continuous on `N` when `h` is continuous on `(0,∞)`. -/
theorem continuousOn_ofProfile_annN {h : ℝ → ℂ} (hh : ContinuousOn h (Ioi 0)) (c : ℂ) :
    ContinuousOn (fun x => c * ofProfile 3 h x) annN := by
  refine continuousOn_const.mul ?_
  have h1 : ContinuousOn (fun x : ℂ => h ‖x‖) annN :=
    hh.comp continuous_norm.continuousOn fun x hx => norm_pos_iff.2 (ne_zero_of_mem_annN hx)
  have h2 : ContinuousOn (angPhase 3) annN := fun x hx =>
    (contDiffAt_angPhase 3 (ne_zero_of_mem_annN hx)).continuousAt.continuousWithinAt
  exact h1.mul h2

/-- A function continuous on `N` and vanishing off `N` is in `L²`. -/
theorem memLp_indicator_annN {f : ℂ → ℂ} (hf : ContinuousOn f annN) :
    MemLp (annN.indicator f) 2 volume := by
  rw [memLp_indicator_iff_restrict measurableSet_annN]
  have : IsFiniteMeasure (volume.restrict annN) :=
    isFiniteMeasure_restrict.2 isCompact_annN.measure_lt_top.ne
  obtain ⟨C, hC⟩ := isCompact_annN.exists_bound_of_continuousOn hf
  exact MemLp.of_bound (hf.aestronglyMeasurable measurableSet_annN) C
    ((ae_restrict_iff' measurableSet_annN).2 (Eventually.of_forall hC))

/-- The representer `ellRep` is in `L²`. -/
theorem memLp_ellRep {χ : ℝ → ℝ} {G : ℝ} (hL : LamFacts χ G) :
    MemLp (ellRep χ G) 2 volume :=
  memLp_indicator_annN (continuousOn_ofProfile_annN
    (continuousOn_adjEig _ hL.valid 3 (by norm_num) hL.re_pos G) _)

/-- The representer lies in `X^0` (`04_ring.tex:1333-1338`). -/
theorem memXFn_ellRep {χ : ℝ → ℝ} {G : ℝ} (hL : LamFacts χ G) :
    Lin.MemXFn 0 (ellRep χ G) := by
  refine ⟨(normH_zero (memLp_ellRep hL)).1, Eventually.of_forall fun x hx => ?_, ?_⟩
  · exact Set.indicator_of_notMem hx _
  · refine Eventually.of_forall fun x => ?_
    have hmem : rot (2 * π / ((3 : ℕ) : ℝ)) x ∈ annN ↔ x ∈ annN := by
      unfold annN
      exact rot_mem_closedAnnulus
    simp only [ellRep]
    by_cases h : x ∈ annN
    · rw [Set.indicator_of_mem (hmem.2 h), Set.indicator_of_mem h, ofProfile_three_rot]
    · rw [Set.indicator_of_notMem (fun h' => h (hmem.1 h')), Set.indicator_of_notMem h]

/-- The polar integrand of `f · conj(ellRep)` on the circle of radius `r > 0`. -/
theorem ellRep_circle {χ : ℝ → ℝ} {G : ℝ} (f : ℂ → ℂ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    f (circleMap 0 r θ) * conj (ellRep χ G (circleMap 0 r θ)) =
      (Icc (a / 2) 2).indicator
          (fun r => conj (((nstar χ G : ℝ) : ℂ) / (2 * π * conj (J χ G))) *
            conj ((ringPhiSetting χ).adjEig 3 (lam χ G) G r)) r *
        (f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
          Complex.exp (-(((3 : ℤ) : ℂ) * θ * Complex.I))) := by
  have hn : ‖circleMap 0 r θ‖ = r := by rw [norm_circleMap_zero, abs_of_pos hr]
  have hc : circleMap 0 r θ = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    simp [circleMap]
  have hmem : circleMap 0 r θ ∈ annN ↔ r ∈ Icc (a / 2) 2 := by
    rw [RingData.mem_annN, hn]
    rfl
  by_cases hrI : r ∈ Icc (a / 2) 2
  · rw [ellRep, Set.indicator_of_mem (hmem.2 hrI), Set.indicator_of_mem hrI, ofProfile, hn,
      angPhase_circleMap 3 hr θ, ← hc]
    have he : conj (Complex.exp (((3 : ℤ) : ℂ) * ((θ : ℂ) * Complex.I))) =
        Complex.exp (-(((3 : ℤ) : ℂ) * θ * Complex.I)) := by
      rw [← Complex.exp_conj]
      congr 1
      simp only [map_mul, map_intCast, Complex.conj_ofReal, Complex.conj_I]
      ring
    simp only [map_mul]
    rw [he]
    ring
  · rw [ellRep, Set.indicator_of_notMem (fun h => hrI (hmem.1 h)), Set.indicator_of_notMem hrI]
    simp

/-- **The representer** (`04_ring.tex:1333-1338`): for `f ∈ L²` vanishing a.e. off `N`,
`ℓ_*(G)(f) = ∫ f conj(ellRep)`. -/
theorem ellFn_eq_integral {χ : ℝ → ℝ} {G : ℝ} (hL : LamFacts χ G) {f : ℂ → ℂ}
    (hf : MemLp f 2 volume) (hfK : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → f x = 0) :
    ellFn χ G f = ∫ x, f x * conj (ellRep χ G x) := by
  have hE : MemLp (fun x => conj (ellRep χ G x)) 2 volume := (memLp_ellRep hL).star
  have hint : Integrable (fun x => f x * conj (ellRep χ G x)) := hf.integrable_mul hE
  rw [Polar.integral_eq_integral_Ioi_intervalIntegral hint]
  have h2π : (2 * π : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  have hinner : ∀ r : ℝ, 0 < r →
      ∫ θ in (0 : ℝ)..2 * π, f (circleMap 0 r θ) * conj (ellRep χ G (circleMap 0 r θ)) =
        (Icc (a / 2) 2).indicator
            (fun r => conj (((nstar χ G : ℝ) : ℂ) / (2 * π * conj (J χ G))) *
              conj ((ringPhiSetting χ).adjEig 3 (lam χ G) G r)) r *
          (2 * π * Polar.angularSector f 3 r) := by
    intro r hr
    rw [intervalIntegral.integral_congr (fun θ _ => ellRep_circle (χ := χ) (G := G) f hr θ),
      intervalIntegral.integral_const_mul]
    congr 1
    unfold Polar.angularSector
    rw [← mul_assoc, mul_inv_cancel₀ h2π, one_mul]
  have hsec := (memLp_angularSector_of_support (by linarith [a_pos] : (0 : ℝ) < a / 2) hf
    hfK 3).2
  unfold ellFn SectorSetting.ellStar
  rw [← integral_const_mul, ← integral_const_mul]
  rw [ae_restrict_iff' measurableSet_Ioi] at hsec
  refine setIntegral_congr_ae measurableSet_Ioi ?_
  filter_upwards [hsec] with r hr0' hr
  have hr0 := hr0' hr
  rw [hinner r hr, Complex.real_smul]
  by_cases hrI : r ∈ Icc (a / 2) 2
  · rw [Set.indicator_of_mem hrI]
    simp only [SectorSetting.adjEig, map_div₀, map_mul, Complex.conj_conj, Complex.conj_ofReal,
      map_ofNat]
    have hJ : J χ G ≠ 0 := hL.J_ne
    have hJ' : (ringPhiSetting χ).J 3 (lam χ G) G ≠ 0 := hJ
    field_simp
    unfold J
    ring
  · rw [Set.indicator_of_notMem hrI, hr0 hrI]
    simp

end NonUniqueEuler.Eig.EigendataH
