import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Sec4.Eigendata
import NonUniqueEuler.I.Sec4.Uniform
import NonUniqueEuler.I.Infra.Sobolev.Norm
import NonUniqueEuler.I.Infra.Sobolev.NormDeriv
import NonUniqueEuler.I.Infra.Sobolev.ReIm

/-!
# Proof of the moment bound behind `cor:active-moment`

Proof of `NonUniqueEuler/I/Sec5/Active/Moment.lean` (`05_single_ring.tex:1112-1122`). Same
declaration, statement copied verbatim.

Proof (as in the manuscript).
* `2Re(Xφ_*) = Xφ_* + conj X conj φ_*` pointwise (`Complex.add_conj`).
* Sector orthogonality `∫ conj φ_* ȳ³ = conj (∫ φ_* y³) = 0`: the integrand `F(y) = φ_*(y) y³`
  is a sector-`6` function, `F(e^{iπ/6} y) = e^{iπ} F(y) = -F(y)` pointwise, and rotations
  preserve Lebesgue measure (`Polar.measurePreserving_rot`), so `∫ F = -∫ F`.
  No polar coordinates are needed.
* Integrability of `g ȳ³` for `g ∈ L²` vanishing a.e. off `N`: Hölder with the `L²` weight
  `1_N ȳ³` (bounded on the compact `N`).
* Linearity: `2π pout_3[f] - 2π pout_*(G) X = ∫ (f - 2Re(Xφ_*)) ȳ³`.
* `lem:uniform` (`Eig.uniform_inequalities`, second item) and `‖·‖_{L²} ≤ ‖·‖_{H^k}`
  (`Sob.MemH.l2_le`); `2Re(Xφ_*) ∈ H^k` by `Sob.MemH.const_smul` and `Sob.MemH.re_im`.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology ComplexConjugate

namespace NonUniqueEuler

namespace OneRing

open RingData

namespace ActiveMomentAux

/-- `N` is measurable. -/
theorem measurableSet_annN' : MeasurableSet annN := isCompact_annN.isClosed.measurableSet

/-- The weight `1_N ȳ³` is in `L²`. -/
theorem memLp_indicator_conj_pow :
    MemLp (annN.indicator fun w : ℂ => conj w ^ (3 : ℤ)) 2 volume := by
  rw [memLp_indicator_iff_restrict measurableSet_annN']
  have hfin : IsFiniteMeasure (volume.restrict annN) :=
    isFiniteMeasure_restrict.2 isCompact_annN.measure_lt_top.ne
  have hcont : Continuous fun w : ℂ => conj w ^ (3 : ℤ) := by
    simp only [zpow_ofNat]
    exact (Complex.continuous_conj).pow 3
  refine MemLp.of_bound hcont.aestronglyMeasurable 8 ?_
  refine (ae_restrict_iff' measurableSet_annN').2 (Eventually.of_forall fun x hx => ?_)
  have h2 : ‖x‖ ≤ 2 := hx.2
  rw [zpow_ofNat, norm_pow, Complex.norm_conj]
  calc ‖x‖ ^ 3 ≤ 2 ^ 3 := by gcongr
    _ = 8 := by norm_num

/-- For `g ∈ L²` vanishing a.e. off `N`, `g ȳ³` is integrable. -/
theorem integrable_mul_conj_pow {g : ℂ → ℂ} (hg : MemLp g 2 volume)
    (hgN : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → g x = 0) :
    Integrable (fun w => g w * conj w ^ (3 : ℤ)) volume := by
  have hae : (fun w => g w * annN.indicator (fun w : ℂ => conj w ^ (3 : ℤ)) w) =ᵐ[volume]
      fun w => g w * conj w ^ (3 : ℤ) := by
    filter_upwards [hgN] with x hx
    by_cases hxN : x ∈ annN
    · rw [indicator_of_mem hxN]
    · rw [hx hxN, zero_mul, zero_mul]
  have : ENNReal.HolderTriple 2 2 1 := ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩
  exact (hg.integrable_mul memLp_indicator_conj_pow).congr hae

/-- An integrand that changes sign under a rotation has integral `0`. -/
theorem integral_eq_zero_of_rot_neg {F : ℂ → ℂ} (θ : ℝ) (hF : ∀ y, F (rot θ y) = -F y) :
    ∫ y, F y = 0 := by
  have hemb : MeasurableEmbedding (rot θ) := by
    rw [Polar.rot_eq_rotation]
    exact (rotation (Circle.exp θ)).toHomeomorph.measurableEmbedding
  have h1 : ∫ y, F (rot θ y) = ∫ y, F y :=
    (Polar.measurePreserving_rot θ).integral_comp hemb F
  simp only [hF, integral_neg] at h1
  have h2 : (2 : ℂ) * ∫ y, F y = 0 := by linear_combination -h1
  simpa using h2

/-- `e^{iπ/6}` to the sixth power is `-1`. -/
theorem exp_pi_div_six_pow_six :
    Complex.exp (((Real.pi / 6 : ℝ) : ℂ) * Complex.I) ^ 6 = -1 := by
  rw [← Complex.exp_nat_mul]
  have : ((6 : ℕ) : ℂ) * (((Real.pi / 6 : ℝ) : ℂ) * Complex.I) = (Real.pi : ℂ) * Complex.I := by
    push_cast
    ring
  rw [this, Complex.exp_pi_mul_I]

/-- Sector orthogonality: `∫ c h(|y|) e^{3iθ} y³ dy = 0`. -/
theorem integral_ofProfile_three_mul_pow (c : ℂ) (h : ℝ → ℂ) :
    ∫ y, c * Ang.ofProfile 3 h y * y ^ (3 : ℤ) = 0 := by
  refine integral_eq_zero_of_rot_neg (Real.pi / 6) fun y => ?_
  set ζ : ℂ := Complex.exp (((Real.pi / 6 : ℝ) : ℂ) * Complex.I)
  have hrot : rot (Real.pi / 6) y = ζ * y := rfl
  have hnorm : ‖rot (Real.pi / 6) y‖ = ‖y‖ := Polar.norm_rot _ _
  simp only [Ang.ofProfile, Ang.angPhase, hnorm, zpow_ofNat]
  rw [hrot, mul_div_assoc, mul_pow, mul_pow]
  have h6 : ζ ^ 6 = -1 := exp_pi_div_six_pow_six
  linear_combination (c * h ‖y‖ * (y / (‖y‖ : ℂ)) ^ 3 * y ^ 3) * h6

/-- `∫ conj φ_* ȳ³ = 0`. -/
theorem conjMoment_conj_phi (χ : ℝ → ℝ) (G : ℝ) :
    Multipole.conjMoment (fun x => conj (Eig.phi χ G x)) 3 = 0 := by
  rw [Multipole.conjMoment]
  have : (fun w => conj (Eig.phi χ G w) * conj w ^ (3 : ℤ)) =
      fun w => conj (((Eig.nstar χ G : ℝ) : ℂ)⁻¹ * Ang.ofProfile 3 (Eig.gstar χ G) w *
        w ^ (3 : ℤ)) := by
    funext w
    simp only [Eig.phi, map_mul, map_zpow₀]
  rw [this, integral_conj, integral_ofProfile_three_mul_pow, map_zero]

/-- `2Re(Xφ) = Xφ + conj X conj φ`. -/
theorem modeFn_eq (χ : ℝ → ℝ) (G : ℝ) (X : ℂ) (x : ℂ) :
    modeFn χ G X x = X * Eig.phi χ G x + conj X * conj (Eig.phi χ G x) := by
  rw [modeFn, ← map_mul, Complex.add_conj]

/-- `2Re(Xφ_*) ∈ H^k` for `φ_* ∈ H^k`. -/
theorem memH_modeFn {χ : ℝ → ℝ} {G : ℝ} {k : ℕ} (hφ : Sob.MemH k (Eig.phi χ G)) (X : ℂ) :
    Sob.MemH k (modeFn χ G X) := by
  have h1 : Sob.MemH k (X • Eig.phi χ G) := (hφ.const_smul X).1
  have h2 := h1.re_im.1
  have h3 := (h2.const_smul (2 : ℂ)).1
  have heq : ((2 : ℂ) • fun x => (((X • Eig.phi χ G) x).re : ℂ)) = modeFn χ G X := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, modeFn]
    push_cast
    ring
  rwa [heq] at h3

end ActiveMomentAux

open ActiveMomentAux in
/-- **The moment bound behind `cor:active-moment`** (`05_single_ring.tex:1112-1122`): for
`G ∈ [0,G₁]`, `f ∈ H^k` vanishing a.e. off `N` and `X ∈ ℂ`,
`|2π pout_3[f] - 2π pout_*(G)X| ≤ 2π C_p ‖f - 2Re(Xφ_*(G))‖_{H^k}`. -/
theorem active_moment_bound (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ)
    (hN : NumericalHypothesis χ) {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) {k : ℕ} {f : ℂ → ℂ}
    (hf : Sob.MemH k f) (hfN : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → f x = 0) (X : ℂ) :
    ‖2 * Real.pi * BS.pout 3 f - 2 * Real.pi * Eig.pout χ G * X‖ ≤
      2 * Real.pi * Eig.Cp * Sob.normH k (f - modeFn χ G X) := by
  obtain ⟨-, hX, -, -, -⟩ := Eig.eigendata_phi χ hχ hN hG
  obtain ⟨hφH, hφN, -⟩ := hX k
  have hφL2 : MemLp (Eig.phi χ G) 2 volume := (Sob.memH_iff.1 hφH).1
  have hfL2 : MemLp f 2 volume := (Sob.memH_iff.1 hf).1
  have hcφL2 : MemLp (fun x => conj (Eig.phi χ G x)) 2 volume := hφL2.star
  have hcφN : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → conj (Eig.phi χ G x) = 0 := by
    filter_upwards [hφN] with x hx hxN
    rw [hx hxN, map_zero]
  have hmode := memH_modeFn hφH X
  have hmodeN : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → modeFn χ G X x = 0 := by
    filter_upwards [hφN] with x hx hxN
    rw [modeFn_eq, hx hxN, map_zero, mul_zero, mul_zero, add_zero]
  have hgH : Sob.MemH k (f - modeFn χ G X) := (hf.sub hmode).1
  have hgL2 : MemLp (f - modeFn χ G X) 2 volume := (Sob.memH_iff.1 hgH).1
  have hgN : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → (f - modeFn χ G X) x = 0 := by
    filter_upwards [hfN, hmodeN] with x hfx hmx hxN
    rw [Pi.sub_apply, hfx hxN, hmx hxN, sub_zero]
  have hbound := (Eig.uniform_inequalities χ hχ hN).2.1 _ hgL2 hgN
  have hIf := integrable_mul_conj_pow hfL2 hfN
  have hIφ := integrable_mul_conj_pow hφL2 hφN
  have hIcφ := integrable_mul_conj_pow hcφL2 hcφN
  have hIm := integrable_mul_conj_pow (Sob.memH_iff.1 hmode).1 hmodeN
  have hm : ∫ w, modeFn χ G X w * conj w ^ (3 : ℤ) =
      X * Multipole.conjMoment (Eig.phi χ G) 3 := by
    have : (fun w => modeFn χ G X w * conj w ^ (3 : ℤ)) = fun w =>
        X * (Eig.phi χ G w * conj w ^ (3 : ℤ)) +
          conj X * (conj (Eig.phi χ G w) * conj w ^ (3 : ℤ)) := by
      funext w
      rw [modeFn_eq]
      ring
    rw [this, integral_add (hIφ.const_mul X) (hIcφ.const_mul _), integral_const_mul,
      integral_const_mul]
    have h0 := conjMoment_conj_phi χ G
    rw [Multipole.conjMoment] at h0
    rw [h0, mul_zero, add_zero, Multipole.conjMoment]
  have hid : 2 * (Real.pi : ℂ) * BS.pout 3 f - 2 * Real.pi * Eig.pout χ G * X =
      Multipole.conjMoment (f - modeFn χ G X) 3 := by
    have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
      exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)
    rw [BS.pout_eq_conjMoment, Eig.pout, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hpi, one_mul,
      one_mul]
    rw [Multipole.conjMoment, Multipole.conjMoment, Multipole.conjMoment]
    simp only [Pi.sub_apply, sub_mul, Nat.cast_ofNat]
    rw [integral_sub hIf hIm, hm, Multipole.conjMoment]
    ring
  rw [hid]
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have hnorm : ‖(2 * (Real.pi : ℂ))⁻¹‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv]
    congr 1
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg h2π.le]
  rw [norm_mul, hnorm] at hbound
  have hCp : 0 ≤ Eig.Cp := by
    rw [Eig.Cp]
    positivity
  calc ‖Multipole.conjMoment (f - modeFn χ G X) 3‖
      = 2 * Real.pi * ((2 * Real.pi)⁻¹ * ‖Multipole.conjMoment (f - modeFn χ G X) 3‖) := by
        field_simp
    _ ≤ 2 * Real.pi * (Eig.Cp * Sob.l2 (f - modeFn χ G X)) := by gcongr
    _ ≤ 2 * Real.pi * (Eig.Cp * Sob.normH k (f - modeFn χ G X)) := by
        gcongr
        exact hgH.l2_le
    _ = 2 * Real.pi * Eig.Cp * Sob.normH k (f - modeFn χ G X) := by ring

end OneRing

end NonUniqueEuler
