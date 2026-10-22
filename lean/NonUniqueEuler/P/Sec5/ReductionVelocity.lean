import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Sec5.Setting
import NonUniqueEuler.I.SmoothB.SmoothFlow
import NonUniqueEuler.I.Sec2.BSBasic
import NonUniqueEuler.I.Sec2.BSSmooth
import NonUniqueEuler.I.Infra.Polar.Newton
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.I.Sec4.SectorSetting
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Proof: `lem:reduction`(2) (the velocity of one ring and the radial motion of trajectories)

Proof of `OneRing.reduction_velocity`, stated in `I/Sec5/Reduction.lean` (the statement is
copied verbatim). Manuscript `05_single_ring.tex:110-117` (statement), `:187-198` (proof).

**Proof.**
* `ω_r ∈ C^∞(ℝ × ℝ²)` is `RingConfig.setting_parts_smooth`.
* For every `t` and every `x ≠ 0`:
  `ω(t) = (ω_i + ω_o)(t) + (ω_r(t) - Φ) + Φ` (`setting_sol_eq_parts`); every summand is
  continuous with compact support, so every Biot–Savart integral converges absolutely
  (`BS.integrable_and_norm_velocity_le_sqrt_L1_Linf`) and `K_BS *` is additive at `x`.
  `K_BS * (ω_i + ω_o) = h + G x^⊥/|x|²` by the definition of `h`, and Newton's theorem gives
  `K_BS * Φ = Circ_Φ(|x|) K_BS(x)`; the bracket `G/|x|² + Circ_Φ(|x|)/(2π|x|²)` is `Ω(|x|;G)`.
  Newton's theorem is available almost everywhere (`Polar.velocity_of_isRadial`); both sides are
  continuous on `ℝ² ∖ {0}` (`BS.contDiff_velocity_of_smooth`, `SectorSetting.circ_eq_integral`),
  hence equal there (deviation: the manuscript computes the circle integrals directly).
* `∂_τ Φ_τ(y) = v(τ, Φ_τ(y))` (`Smooth.flow_global`), so `d/dτ |Φ_τ(y)| = (v·e_r)(τ, Φ_τ(y))`
  while `Φ_τ(y) ≠ 0`, and `Ω x^⊥ · e_r = 0`; the fundamental theorem of calculus on `[0,t]`
  (the integrand is continuous there) gives the integral formula.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology ComplexConjugate

namespace NonUniqueEuler

namespace OneRing

open RingData

namespace ReductionVelocity

/-! ### Elementary facts about the Biot–Savart integral -/

/-- The Biot–Savart integral converges absolutely at every point for a continuous compactly
supported vorticity. -/
theorem integrable_bs {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (x : ℂ) :
    Integrable (fun y => biotSavartKernel (x - y) * (f y : ℂ)) :=
  (BS.integrable_and_norm_velocity_le_sqrt_L1_Linf (hf.memLp_of_hasCompactSupport hfc)
    (hf.memLp_of_hasCompactSupport hfc) x).1

/-- Additivity of the Biot–Savart integral at a point where both integrals converge. -/
theorem velocity_add {f g : ℂ → ℝ} {x : ℂ}
    (hf : Integrable (fun y => biotSavartKernel (x - y) * (f y : ℂ)))
    (hg : Integrable (fun y => biotSavartKernel (x - y) * (g y : ℂ))) :
    velocity (fun y => f y + g y) x = velocity f x + velocity g x := by
  unfold velocity
  rw [← integral_add hf hg]
  congr 1
  funext y
  push_cast
  ring

/-- Pointwise Newton's theorem for the ring: `K_BS * Φ (x) = Circ_Φ(|x|) K_BS(x)` for `x ≠ 0`. -/
theorem velocity_ringPhi {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {x : ℂ} (hx : x ≠ 0) :
    velocity (ringPhi χ) x = (Polar.circ (ringPhi χ) ‖x‖ : ℂ) * biotSavartKernel x := by
  obtain ⟨hsm, hcs, hrad, -⟩ := ringFacts_of_admissible hχ
  have hS := ringPhiSetting_valid hχ
  have hint : Integrable (ringPhi χ) := hsm.continuous.integrable_of_hasCompactSupport hcs
  have hrad' : IsRadial (ringPhi χ) := fun θ => Filter.Eventually.of_forall fun z => hrad θ z
  have hae := Polar.velocity_of_isRadial hrad' hint
  -- continuity of both sides on `{0}ᶜ`
  have hvc : Continuous (velocity (ringPhi χ)) :=
    (BS.contDiff_velocity_of_smooth hsm hcs).1.continuous
  have hF : Continuous fun r : ℝ =>
      2 * Real.pi * ∫ ρ in (0 : ℝ)..r, (ringPhiSetting χ).omR ρ * ρ := by
    refine continuous_const.mul (intervalIntegral.continuous_primitive (fun _ _ => ?_) 0)
    refine Continuous.intervalIntegrable ?_ _ _
    exact (hsm.continuous.comp Complex.continuous_ofReal).mul continuous_id
  have hcirc : (fun z : ℂ => Polar.circ (ringPhi χ) ‖z‖) =
      fun z : ℂ => 2 * Real.pi * ∫ ρ in (0 : ℝ)..‖z‖, (ringPhiSetting χ).omR ρ * ρ := by
    funext z
    exact (ringPhiSetting χ).circ_eq_integral hS (norm_nonneg z)
  have hrc : ContinuousOn (fun z : ℂ => (Polar.circ (ringPhi χ) ‖z‖ : ℂ) * biotSavartKernel z)
      ({0}ᶜ : Set ℂ) := by
    refine ContinuousOn.mul ?_ BS.contDiffOn_biotSavartKernel.continuousOn
    refine (Complex.continuous_ofReal.comp ?_).continuousOn
    rw [hcirc]
    exact hF.comp continuous_norm
  exact Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae hae) isOpen_compl_singleton
    hvc.continuousOn hrc hx

/-- `Ω(|x|;G) x^⊥ = G x^⊥/|x|² + Circ_Φ(|x|) K_BS(x)` for `x ≠ 0`. -/
theorem omegaField_eq {χ : ℝ → ℝ} (G : ℝ) {x : ℂ} (hx : x ≠ 0) :
    omegaField χ G x = (G : ℂ) * (Complex.I * x) / (((‖x‖ ^ 2 : ℝ)) : ℂ) +
      (Polar.circ (ringPhi χ) ‖x‖ : ℂ) * biotSavartKernel x := by
  have hn : (‖x‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hx
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  simp only [omegaField, Lin.Omega, SectorSetting.Omega, ringPhiSetting_om, biotSavartKernel]
  push_cast
  field_simp
  ring

/-! ### The radial component -/

theorem radComp_apply (f : ℂ → ℂ) (x : ℂ) :
    radComp f x = (f x * conj (((‖x‖ : ℝ) : ℂ)⁻¹ * x)).re := rfl

/-- `Ω(|x|;G) x^⊥ · e_r = 0`. -/
theorem omegaField_mul_conj_re (χ : ℝ → ℝ) (G : ℝ) (x : ℂ) :
    (omegaField χ G x * conj (((‖x‖ : ℝ) : ℂ)⁻¹ * x)).re = 0 := by
  have h : omegaField χ G x * conj (((‖x‖ : ℝ) : ℂ)⁻¹ * x) =
      ((Lin.Omega χ G ‖x‖ * (‖x‖)⁻¹ * Complex.normSq x : ℝ) : ℂ) * Complex.I := by
    simp only [omegaField, map_mul, map_inv₀, Complex.conj_ofReal]
    rw [show ((Lin.Omega χ G ‖x‖ : ℝ) : ℂ) * (Complex.I * x) * (((‖x‖ : ℝ) : ℂ)⁻¹ * conj x) =
      ((Lin.Omega χ G ‖x‖ : ℝ) : ℂ) * (((‖x‖ : ℝ) : ℂ)⁻¹) * (x * conj x) * Complex.I by ring,
      Complex.mul_conj]
    push_cast
    ring
  rw [h]
  simp

/-- Derivative of `τ ↦ |γ(τ)|` where `γ(τ) ≠ 0`: `γ'·e_r`. -/
theorem hasDerivAt_norm {γ : ℝ → ℂ} {v : ℂ} {τ : ℝ} (hγ : HasDerivAt γ v τ) (h0 : γ τ ≠ 0) :
    HasDerivAt (fun s => ‖γ s‖) ((v * conj (((‖γ τ‖ : ℝ) : ℂ)⁻¹ * γ τ)).re) τ := by
  have hn : ‖γ τ‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  have h2 : ‖γ τ‖ ^ 2 ≠ 0 := pow_ne_zero 2 hn
  have hd := (hγ.norm_sq).sqrt h2
  have hfun : (fun s => Real.sqrt (‖γ s‖ ^ 2)) = fun s => ‖γ s‖ := by
    funext s
    exact Real.sqrt_sq (norm_nonneg _)
  rw [hfun] at hd
  convert hd using 1
  rw [Real.sqrt_sq (norm_nonneg _), Complex.inner]
  simp only [map_mul, map_inv₀, Complex.conj_ofReal]
  rw [show v * ((((‖γ τ‖ : ℝ) : ℂ))⁻¹ * conj (γ τ)) =
      ((((‖γ τ‖)⁻¹ : ℝ)) : ℂ) * (v * conj (γ τ)) by push_cast; ring, Complex.re_ofReal_mul]
  field_simp

/-! ### The configuration -/

variable {c : RingConfig} {T : ℝ}

theorem isSmoothDatum (hc : c.Hyp T) : ∃ R₀ : ℝ, Smooth.IsSmoothDatum c.datum R₀ := by
  obtain ⟨R₀, hR₀⟩ := hc.datum_hasCompactSupport.isCompact.isBounded.subset_ball 0
  exact ⟨R₀, ⟨hc.datum_contDiff, hR₀⟩⟩

/-- The flow solves `∂_τ Φ_τ(y) = v(τ, Φ_τ(y))`. -/
theorem hasDerivAt_flow (hc : c.Hyp T) (y : ℂ) (τ : ℝ) :
    HasDerivAt (fun s => c.flow s y) (velocity (c.sol τ) (c.flow τ y)) τ := by
  obtain ⟨R₀, hD⟩ := isSmoothDatum hc
  exact (Smooth.flow_global hD y).2.hasDerivAt τ (mem_univ τ)

theorem continuous_flow (hc : c.Hyp T) (t : ℝ) : Continuous (c.flow t) := by
  obtain ⟨R₀, hD⟩ := isSmoothDatum hc
  exact (Smooth.flow_diffeo hD t).2.2.1.continuous

/-- The velocity `(τ, x) ↦ v(τ, x)` is jointly continuous. -/
theorem continuous_vel (hc : c.Hyp T) :
    Continuous (fun p : ℝ × ℂ => velocity (c.sol p.1) p.2) := by
  obtain ⟨R₀, hD⟩ := isSmoothDatum hc
  exact (Smooth.vel_isSmoothBoundedField hD).continuous

theorem continuous_ringPart (hc : c.Hyp T) (t : ℝ) : Continuous (c.ringPart t) :=
  (RingConfig.setting_parts_smooth hc).2.2.2.1.continuous.comp
    (continuous_const.prodMk continuous_id)

theorem continuous_innerPart (hc : c.Hyp T) (t : ℝ) : Continuous (c.innerPart t) :=
  (RingConfig.setting_parts_smooth hc).2.2.2.2.1.continuous.comp
    (continuous_const.prodMk continuous_id)

theorem continuous_outerPart (hc : c.Hyp T) (t : ℝ) : Continuous (c.outerPart t) :=
  (RingConfig.setting_parts_smooth hc).2.2.2.2.2.continuous.comp
    (continuous_const.prodMk continuous_id)

theorem hasCompactSupport_ringPart (hc : c.Hyp T) (t : ℝ) : HasCompactSupport (c.ringPart t) := by
  rw [HasCompactSupport, (RingConfig.setting_tsupport_parts hc t).1]
  exact (RingConfig.setting_parts_smooth hc).1.2.isCompact.image (continuous_flow hc t)

theorem hasCompactSupport_innerPart (hc : c.Hyp T) (t : ℝ) :
    HasCompactSupport (c.innerPart t) := by
  rw [HasCompactSupport, (RingConfig.setting_tsupport_parts hc t).2.1]
  exact (RingConfig.setting_parts_smooth hc).2.1.2.isCompact.image (continuous_flow hc t)

theorem hasCompactSupport_outerPart (hc : c.Hyp T) (t : ℝ) :
    HasCompactSupport (c.outerPart t) := by
  rw [HasCompactSupport, (RingConfig.setting_tsupport_parts hc t).2.2]
  exact (RingConfig.setting_parts_smooth hc).2.2.1.2.isCompact.image (continuous_flow hc t)

/-- **The velocity decomposition** `v = Ω(|x|;G)x^⊥ + h + K_BS * (ω_r - Φ)`, for every `t` and
every `x ≠ 0`. -/
theorem velocity_sol_eq (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hc : c.Hyp T) (t : ℝ) {x : ℂ}
    (hx : x ≠ 0) :
    velocity (c.sol t) x = omegaField χ c.G x + c.h t x +
      velocity (fun y => c.ringPart t y - ringPhi χ y) x := by
  obtain ⟨hsm, hcs, -⟩ := ringFacts_of_admissible hχ
  have hsol : c.sol t = fun y => (c.innerPart t y + c.outerPart t y) +
      ((c.ringPart t y - ringPhi χ y) + ringPhi χ y) := by
    funext y
    rw [(RingConfig.setting_sol_eq_parts hc).1 t y]
    ring
  have hio_c : Continuous fun y => c.innerPart t y + c.outerPart t y :=
    (continuous_innerPart hc t).add (continuous_outerPart hc t)
  have hio_s : HasCompactSupport fun y => c.innerPart t y + c.outerPart t y :=
    (hasCompactSupport_innerPart hc t).add (hasCompactSupport_outerPart hc t)
  have hr_c : Continuous fun y => c.ringPart t y - ringPhi χ y :=
    (continuous_ringPart hc t).sub hsm.continuous
  have hr_s : HasCompactSupport fun y => c.ringPart t y - ringPhi χ y :=
    (hasCompactSupport_ringPart hc t).sub hcs
  have hrΦ_c : Continuous fun y => (c.ringPart t y - ringPhi χ y) + ringPhi χ y :=
    hr_c.add hsm.continuous
  have hrΦ_s : HasCompactSupport fun y => (c.ringPart t y - ringPhi χ y) + ringPhi χ y :=
    hr_s.add hcs
  rw [hsol, velocity_add (integrable_bs hio_c hio_s x) (integrable_bs hrΦ_c hrΦ_s x),
    velocity_add (integrable_bs hr_c hr_s x) (integrable_bs hsm.continuous hcs x),
    velocity_ringPhi hχ hx, omegaField_eq c.G hx]
  have hh : c.h t x = velocity (fun y => c.innerPart t y + c.outerPart t y) x -
      (c.G : ℂ) * (Complex.I * x) / (((‖x‖ ^ 2 : ℝ)) : ℂ) := rfl
  rw [hh]
  ring

/-- The radial component of `v` along a trajectory, with `Ω x^⊥ · e_r = 0` removed. -/
theorem radComp_velocity_sol (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hc : c.Hyp T) (t : ℝ)
    {x : ℂ} (hx : x ≠ 0) :
    (velocity (c.sol t) x * conj (((‖x‖ : ℝ) : ℂ)⁻¹ * x)).re =
      radComp (fun z => c.h t z + velocity (fun y => c.ringPart t y - ringPhi χ y) z) x := by
  rw [velocity_sol_eq χ hχ hc t hx, radComp_apply, add_assoc, add_mul, Complex.add_re,
    omegaField_mul_conj_re, zero_add]

theorem ne_zero_of_mem_annN' {x : ℂ} (hx : x ∈ annN') : x ≠ 0 := by
  intro h0
  have h1 : a / 4 ≤ ‖x‖ := hx.1
  rw [h0, norm_zero] at h1
  have ha : 0 < a := Real.exp_pos _
  linarith

end ReductionVelocity

open ReductionVelocity

/-- **`lem:reduction`(2)** (`05_single_ring.tex:110-117`). Under the hypotheses of
`lem:reduction` on `[0,T]`: `ω_r ∈ C^∞(ℝ × ℝ²)`; on `[0,T] × N'` the velocity is
`v = K_BS * ω = Ω(|x|;G)x^⊥ + h + K_BS * (ω_r - Φ)`; and if `t ∈ [0,T]` and `Φ_τ(y) ∈ N'` for
every `τ ∈ [0,t]`, then `|Φ_t(y)| - |y| = ∫₀ᵗ ((h + K_BS*(ω_r - Φ))·e_r)(τ, Φ_τ(y)) dτ`. -/
theorem reduction_velocity (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) {c : RingConfig} {T : ℝ}
    (hc : c.Hyp T) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℂ => c.ringPart p.1 p.2) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ annN',
        velocity (c.sol t) x = omegaField χ c.G x + c.h t x +
          velocity (fun y => c.ringPart t y - ringPhi χ y) x) ∧
      ∀ t ∈ Icc (0 : ℝ) T, ∀ y : ℂ, (∀ τ ∈ Icc (0 : ℝ) t, c.flow τ y ∈ annN') →
        ‖c.flow t y‖ - ‖y‖ = ∫ τ in (0 : ℝ)..t,
          radComp (fun x => c.h τ x + velocity (fun z => c.ringPart τ z - ringPhi χ z) x)
            (c.flow τ y) := by
  refine ⟨(RingConfig.setting_parts_smooth hc).2.2.2.1, fun t _ x hx =>
    velocity_sol_eq χ hχ hc t (ne_zero_of_mem_annN' hx), ?_⟩
  intro t ht y hpath
  have ht0 : 0 ≤ t := ht.1
  have hne : ∀ τ ∈ Icc (0 : ℝ) t, c.flow τ y ≠ 0 := fun τ hτ => ne_zero_of_mem_annN' (hpath τ hτ)
  -- the full radial velocity along the trajectory
  set k : ℝ → ℝ := fun τ => (velocity (c.sol τ) (c.flow τ y) *
    conj (((‖c.flow τ y‖ : ℝ) : ℂ)⁻¹ * c.flow τ y)).re with hk
  have hγc : Continuous fun τ => c.flow τ y :=
    continuous_iff_continuousAt.2 fun τ => (hasDerivAt_flow hc y τ).continuousAt
  have hderiv : ∀ τ ∈ uIcc (0 : ℝ) t, HasDerivAt (fun s => ‖c.flow s y‖) (k τ) τ := by
    intro τ hτ
    rw [uIcc_of_le ht0] at hτ
    exact hasDerivAt_norm (hasDerivAt_flow hc y τ) (hne τ hτ)
  have hkc : ContinuousOn k (uIcc (0 : ℝ) t) := by
    rw [uIcc_of_le ht0]
    have hv : Continuous fun τ => velocity (c.sol τ) (c.flow τ y) := by
      have h1 := (continuous_vel hc).comp (continuous_id.prodMk hγc)
      exact h1
    have hinv : ContinuousOn (fun τ => (((‖c.flow τ y‖ : ℝ) : ℂ))⁻¹) (Icc (0 : ℝ) t) := by
      refine ContinuousOn.inv₀ (Complex.continuous_ofReal.comp
        (continuous_norm.comp hγc)).continuousOn fun τ hτ => ?_
      simpa using hne τ hτ
    exact Complex.continuous_re.comp_continuousOn (hv.continuousOn.mul
      (Complex.continuous_conj.comp_continuousOn (hinv.mul hγc.continuousOn)))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hkc.intervalIntegrable
  have h0 : c.flow 0 y = y := (RingConfig.setting_sol_eq_parts hc).2.2.2.1 y
  rw [h0] at hftc
  rw [← hftc]
  refine intervalIntegral.integral_congr fun τ hτ => ?_
  rw [uIcc_of_le ht0] at hτ
  exact radComp_velocity_sol χ hχ hc τ (hne τ hτ)

end OneRing

end NonUniqueEuler
