import NonUniqueEuler.Defs.Sec2.BiotSavart
import NonUniqueEuler.I.Infra.Multipole.Moments
import NonUniqueEuler.I.Infra.Multipole.Laurent
import NonUniqueEuler.I.Infra.Multipole.Holomorphic
import NonUniqueEuler.H.Sec7.Transfer.PowerSeries
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Helper for `lem:transfer`: Laurent and power series forms of the fields

Helper of `P/Sec7/Transfer.lean` (`07_several_rings.tex:143-149`, `:176-182`, `:200-211`).
For a real `g ∈ L¹`, with `F = V₁ - iV₂` the complex form (`eq:complex-velocity`):
* exterior: if `g = 0` a.e. outside `\bar B_ϱ`, then on `|z| > ϱ` the non-monopole field is
  `E_g = conj F`, `F = Σ_l c_l z^{-l-1}` with `c_0 = 0`, `c_l = (2πi)⁻¹ ∫ g ζ^l`
  (`extField_eq_conj_laurentTail`), `|c_l| ≤ (2π)⁻¹‖g‖₁ ϱ^l` (`norm_extCoeff_le`) and `c_l = 0`
  unless `m ∣ l` for an `m`-fold symmetric `g` (`extCoeff_eq_zero_of_not_dvd`). This repeats the
  first step of the proof of `lem:ext-multipole` (`P/Sec2/ExtMultipole.lean`, namespace
  `BS.ExtMultipoleAux`, which a proof file may not import);
* interior: if `g = 0` a.e. on `B_R`, then on `B_R` the velocity is `K * g = conj F`,
  `F = Σ_l d_l z^l`, `d_l = -(2πi)⁻¹ ∫ g ζ^{-l-1}` (`velocity_eq_conj_powSer`),
  `|d_l| ≤ (2π)⁻¹‖g‖₁ R^{-l-1}` (`norm_intCoeff_le`), `d_l = 0` unless `m ∣ l + 1`
  (`intCoeff_eq_zero_of_not_dvd`);
* `eq:derivative-norm` in operator-norm form: if `V = conj F` on an open `U` with `F`
  holomorphic, then `‖D^q V(z)‖ = |F^{(q)}(z)|` on `U` (`norm_iteratedFDeriv_of_eqOn_conj`).
-/

noncomputable section

open MeasureTheory Set Metric ComplexConjugate Filter Topology
open scoped ContDiff

namespace NonUniqueEuler.Rings.TransferAux

/-- `∫ |g| = ‖g‖_{L¹}` for a real integrable `g`. -/
theorem integral_norm_ofReal_eq {g : ℂ → ℝ} (hg : Integrable g) :
    ∫ w, ‖(g w : ℂ)‖ = (eLpNorm g 1 volume).toReal := by
  rw [toReal_eLpNorm hg.aestronglyMeasurable,
    lpNorm_one_eq_integral_norm hg.aestronglyMeasurable]
  simp [Complex.norm_real]

/-! ### The exterior expansion -/

/-- The coefficients of `F = E₁ - iE₂`: `c_0 = 0` and `c_l = (2πi)⁻¹ Q_l` for `l ≥ 1`. -/
def extCoeff (g : ℂ → ℝ) (l : ℕ) : ℂ :=
  if l = 0 then 0 else (2 * Real.pi * Complex.I)⁻¹ * Multipole.moment (fun w => (g w : ℂ)) l

theorem norm_two_pi_I_inv : ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ = (2 * Real.pi)⁻¹ := by
  rw [norm_inv, norm_mul, Complex.norm_I, mul_one, norm_mul, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

theorem norm_extCoeff_le {ϱ : ℝ} (hϱ : 0 ≤ ϱ) {g : ℂ → ℝ} (hg : Integrable g)
    (hsupp : ∀ᵐ y, ϱ < ‖y‖ → g y = 0) (l : ℕ) :
    ‖extCoeff g l‖ ≤ ((2 * Real.pi)⁻¹ * ∫ w, ‖(g w : ℂ)‖) * ϱ ^ l := by
  have hA : 0 ≤ ∫ w, ‖(g w : ℂ)‖ := integral_nonneg fun _ => norm_nonneg _
  have hpi := Real.pi_pos
  unfold extCoeff
  split_ifs with hl
  · rw [norm_zero]
    positivity
  · have hGs : ∀ᵐ w, ϱ < ‖w‖ → (g w : ℂ) = 0 := by
      filter_upwards [hsupp] with w hw h
      simp [hw h]
    have hm := Multipole.norm_moment_le hg.ofReal hϱ hGs l
    rw [norm_mul, norm_two_pi_I_inv, mul_assoc]
    exact mul_le_mul_of_nonneg_left hm (by positivity)

theorem extCoeff_eq_zero_of_not_dvd {m : ℕ} (hm : 0 < m) {g : ℂ → ℝ}
    (hsym : IsMFoldSymmetric m g) {l : ℕ} (hl : ¬ m ∣ l) : extCoeff g l = 0 := by
  unfold extCoeff
  split_ifs with h0
  · rfl
  · rw [Multipole.moment_eq_zero_of_isMFoldSymmetric hm hsym
      (fun h => hl (Int.natCast_dvd_natCast.mp h)), mul_zero]

theorem extCoeff_zero (g : ℂ → ℝ) : extCoeff g 0 = 0 := by simp [extCoeff]

/-- For a `3`-fold symmetric `g`, `c_l = 0` for `l < 3`. -/
theorem extCoeff_eq_zero_of_lt_three {g : ℂ → ℝ} (hsym : IsMFoldSymmetric 3 g) {l : ℕ}
    (hl : l < 3) : extCoeff g l = 0 := by
  rcases Nat.eq_zero_or_pos l with rfl | hl0
  · exact extCoeff_zero g
  · exact extCoeff_eq_zero_of_not_dvd (by norm_num) hsym fun h =>
      absurd (Nat.le_of_dvd hl0 h) (by omega)

/-- `∫ g = Q_0`. -/
theorem moment_zero_ofReal (g : ℂ → ℝ) :
    Multipole.moment (fun w => (g w : ℂ)) ((0 : ℕ) : ℤ) = ((∫ y, g y : ℝ) : ℂ) := by
  simp only [Multipole.moment, Nat.cast_zero, zpow_zero, mul_one]
  exact integral_complex_ofReal

/-- On `{|z| > ϱ}`, `E_g = conj F` with `F = laurentTail (extCoeff g)`. -/
theorem extField_eq_conj_laurentTail {ϱ : ℝ} {g : ℂ → ℝ} (hg : Integrable g)
    (hsupp : ∀ᵐ y, ϱ < ‖y‖ → g y = 0) {z : ℂ} (hz : ϱ < ‖z‖) :
    BS.extField g z = conj (Multipole.laurentTail (extCoeff g) z) := by
  set G : ℂ → ℂ := fun w => (g w : ℂ) with hG
  set c : ℂ := (2 * Real.pi * Complex.I)⁻¹ with hc
  have hGs : ∀ᵐ w, ϱ < ‖w‖ → G w = 0 := by
    filter_upwards [hsupp] with w hw h
    simp [hG, hw h]
  have hs := (Multipole.hasSum_cauchyTransform_exterior hg.ofReal hGs hz).mul_left c
  have h0 := hasSum_ite_eq (0 : ℕ) (c * (Multipole.moment G ((0 : ℕ) : ℤ) * (z ^ (0 + 1))⁻¹))
  have hs2 := hs.sub h0
  have hfun : (fun l : ℕ => c * (Multipole.moment G l * (z ^ (l + 1))⁻¹) -
      (if l = 0 then c * (Multipole.moment G ((0 : ℕ) : ℤ) * (z ^ (0 + 1))⁻¹) else 0)) =
      fun l => extCoeff g l * (z ^ (l + 1))⁻¹ := by
    funext l
    rcases eq_or_ne l 0 with rfl | hl
    · simp [extCoeff]
    · simp only [extCoeff, hl, ite_false, sub_zero, ← hG, ← hc]
      ring
  have hs3 : HasSum (fun l : ℕ => extCoeff g l * (z ^ (l + 1))⁻¹)
      (c * Multipole.cauchyTransform G z -
        c * (Multipole.moment G ((0 : ℕ) : ℤ) * (z ^ (0 + 1))⁻¹)) := by
    rw [← hfun]
    exact hs2
  have hlt : Multipole.laurentTail (extCoeff g) z =
      c * Multipole.cauchyTransform G z -
        c * (Multipole.moment G ((0 : ℕ) : ℤ) * (z ^ (0 + 1))⁻¹) := hs3.tsum_eq
  rw [BS.extField, Multipole.velocity_eq_conj_cauchyTransform, BS.monopole, hlt, map_sub, ← hG,
    ← hc]
  congr 1
  rw [← Complex.conj_conj (((∫ y, g y : ℝ) : ℂ) * biotSavartKernel z)]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Multipole.conj_biotSavartKernel, moment_zero_ofReal, hc,
    zero_add, pow_one, mul_inv, mul_inv]
  ring

/-! ### The interior expansion -/

/-- The coefficients of the interior expansion `F = Σ_l d_l z^l` of `V₁ - iV₂`:
`d_l = -(2πi)⁻¹ ∫ g ζ^{-l-1}`. -/
def intCoeff (g : ℂ → ℝ) (l : ℕ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ * -Multipole.moment (fun w => (g w : ℂ)) (-((l : ℤ) + 1))

theorem norm_intCoeff_le {R : ℝ} (hR : 0 < R) {g : ℂ → ℝ} (hg : Integrable g)
    (hsupp : ∀ᵐ y, ‖y‖ < R → g y = 0) (l : ℕ) :
    ‖intCoeff g l‖ ≤ ((2 * Real.pi)⁻¹ * (∫ w, ‖(g w : ℂ)‖) * R⁻¹) * (R ^ l)⁻¹ := by
  have hA : 0 ≤ ∫ w, ‖(g w : ℂ)‖ := integral_nonneg fun _ => norm_nonneg _
  have hGs : ∀ᵐ w, ‖w‖ < R → (g w : ℂ) = 0 := by
    filter_upwards [hsupp] with w hw h
    simp [hw h]
  have hm := Multipole.norm_moment_neg_le hg.ofReal hR hGs (l + 1)
  have he : (-((l : ℤ) + 1)) = -(((l + 1 : ℕ) : ℤ)) := by push_cast; ring
  rw [intCoeff, he, norm_mul, norm_neg, norm_two_pi_I_inv]
  calc (2 * Real.pi)⁻¹ * ‖Multipole.moment (fun w => (g w : ℂ)) (-(((l + 1 : ℕ) : ℤ)))‖
      ≤ (2 * Real.pi)⁻¹ * ((∫ w, ‖(g w : ℂ)‖) * (R ^ (l + 1))⁻¹) := by
        gcongr
        exact hm
    _ = ((2 * Real.pi)⁻¹ * (∫ w, ‖(g w : ℂ)‖) * R⁻¹) * (R ^ l)⁻¹ := by
        rw [pow_succ, mul_inv]
        ring

theorem intCoeff_eq_zero_of_not_dvd {m : ℕ} (hm : 0 < m) {g : ℂ → ℝ}
    (hsym : IsMFoldSymmetric m g) {l : ℕ} (hl : ¬ m ∣ l + 1) : intCoeff g l = 0 := by
  have hl' : ¬ (m : ℤ) ∣ -((l : ℤ) + 1) := by
    rw [Int.dvd_neg]
    intro h
    apply hl
    have : ((l : ℤ) + 1) = ((l + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this] at h
    exact Int.natCast_dvd_natCast.mp h
  rw [intCoeff, Multipole.moment_eq_zero_of_isMFoldSymmetric hm hsym hl', neg_zero, mul_zero]

/-- For a `3`-fold symmetric `g`, `d_0 = d_1 = 0`. -/
theorem intCoeff_eq_zero_of_lt_two {g : ℂ → ℝ} (hsym : IsMFoldSymmetric 3 g) {l : ℕ}
    (hl : l < 2) : intCoeff g l = 0 :=
  intCoeff_eq_zero_of_not_dvd (by norm_num) hsym fun h =>
    absurd (Nat.le_of_dvd (by omega) h) (by omega)

/-- On `B_R`, where `g` vanishes, `K * g = conj F` with `F = powSer (intCoeff g)`. -/
theorem velocity_eq_conj_powSer {R : ℝ} {g : ℂ → ℝ} (hg : Integrable g)
    (hsupp : ∀ᵐ y, ‖y‖ < R → g y = 0) {z : ℂ} (hz : ‖z‖ < R) :
    velocity g z = conj (powSer (intCoeff g) z) := by
  have hGs : ∀ᵐ w, ‖w‖ < R → (fun w => (g w : ℂ)) w = 0 := by
    filter_upwards [hsupp] with w hw h
    simp [hw h]
  have hfun : ∀ l : ℕ, (2 * Real.pi * Complex.I)⁻¹ *
      -(Multipole.moment (fun w => (g w : ℂ)) (-((l : ℤ) + 1)) * z ^ l) =
        intCoeff g l * z ^ l := by
    intro l
    simp only [intCoeff]
    ring
  have hint : HasSum (fun l : ℕ => -(Multipole.moment (fun w => (g w : ℂ)) (-((l : ℤ) + 1)) *
      z ^ l)) (Multipole.cauchyTransform (fun w => (g w : ℂ)) z) :=
    Multipole.hasSum_cauchyTransform_interior hg.ofReal hGs hz
  rw [Multipole.velocity_eq_conj_cauchyTransform, powSer]
  congr 1
  rw [← hint.tsum_eq, ← tsum_mul_left]
  exact tsum_congr fun l => hfun l

/-! ### Derivatives of `conj F` -/

/-- `eq:derivative-norm`, operator-norm form: if `V = conj F` on an open `U` and `F` is
holomorphic there, then `‖D^q V(z)‖ = |F^{(q)}(z)|` on `U`. -/
theorem norm_iteratedFDeriv_of_eqOn_conj {V F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) (hV : ∀ z ∈ U, V z = conj (F z)) (q : ℕ) {z : ℂ}
    (hz : z ∈ U) : ‖iteratedFDeriv ℝ q V z‖ = ‖iteratedDeriv q F z‖ := by
  have hloc : V =ᶠ[𝓝 z] fun x => conj (F x) :=
    Filter.eventually_of_mem (hU.mem_nhds hz) hV
  rw [(hloc.iteratedFDeriv ℝ q).eq_of_nhds]
  exact Multipole.norm_iteratedFDeriv_real_conj_eq hU hF hz q

theorem contDiffOn_of_eqOn_conj {V F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) (hV : ∀ z ∈ U, V z = conj (F z)) : ContDiffOn ℝ ∞ V U :=
  (Multipole.contDiffOn_real_of_differentiableOn hU hF).2.congr hV

end NonUniqueEuler.Rings.TransferAux
