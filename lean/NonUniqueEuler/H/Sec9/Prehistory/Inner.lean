import NonUniqueEuler.Defs.Sec9.All
import NonUniqueEuler.I.Sec8.Coupling
import NonUniqueEuler.I.Sec6.FieldContinuity

/-!
# Helpers for `P/Sec9/Prehistory`: the inner part `|2π pout_3[ν^in_j(t)]| ≤ 4π η^in_j(A_jt)`

Helper file of `P/Sec9/Prehistory.lean` (`lem:prehistory`, `09_relay.tex:1070-1085`).
`lem:coupling`(1) at `r = 1` reads `(2π)⁻¹∫₀^{2π} h^in_j(A_jt)(e^{iθ})·e_r e^{-3iθ}dθ = (i/2)p_3`,
`p_3 = pout_3[ν^in_j(t)]`, so `|p_3| ≤ 2 max_{|y|=1}|h^in_j(A_jt)| ≤ 2η^in_j(A_jt)` (the unit circle
lies in `N'`).

* `norm_angularSector_le`: `|g_ℓ(r)| ≤ C` if `|g| ≤ C` on the circle of radius `r`;
* `abs_radComp_le`: `|h·e_r| ≤ |h|`;
* `norm_two_pi_pout_nuIn_le`: `|2π pout_3[ν^in_j(t)]| ≤ 4π η^in_j(A_jt)` (with `M_h` arbitrary).
Everything here is proved.
-/

noncomputable section

open MeasureTheory Set Metric ComplexConjugate

namespace NonUniqueEuler

namespace Relay

namespace PrehistoryAux

open RingData Datum

/-- `|g_ℓ(r)| ≤ C` when `|g(re^{iθ})| ≤ C` for every `θ` (no integrability needed). -/
theorem norm_angularSector_le {g : ℂ → ℂ} (ℓ : ℤ) (r : ℝ) {C : ℝ}
    (hg : ∀ θ : ℝ, ‖g ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ≤ C) :
    ‖Polar.angularSector g ℓ r‖ ≤ C := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hg 0)
  have hint : ‖∫ θ in (0 : ℝ)..2 * Real.pi,
      g ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
        Complex.exp (-((ℓ : ℂ) * θ * Complex.I))‖ ≤ C * |2 * Real.pi - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ => ?_
    rw [norm_mul]
    have he : ‖Complex.exp (-((ℓ : ℂ) * θ * Complex.I))‖ = 1 := by
      rw [show -((ℓ : ℂ) * θ * Complex.I) = ((-(ℓ * θ) : ℝ) : ℂ) * Complex.I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [he, mul_one]
    exact hg θ
  have hpi := Real.pi_pos
  rw [sub_zero, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hint
  unfold Polar.angularSector
  rw [norm_mul]
  have h2 : ‖(2 * (Real.pi : ℂ))⁻¹‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv, show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [h2]
  calc (2 * Real.pi)⁻¹ * _ ≤ (2 * Real.pi)⁻¹ * (C * (2 * Real.pi)) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = C := by field_simp

/-- `|h·e_r| ≤ |h|` (`e_r = x/|x|`, and `0` at `x = 0`). -/
theorem abs_radComp_le (h : ℂ → ℂ) (x : ℂ) : |OneRing.radComp h x| ≤ ‖h x‖ := by
  unfold OneRing.radComp
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, Complex.norm_conj]
  have he : ‖((‖x‖ : ℝ) : ℂ)⁻¹ * x‖ ≤ 1 := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm]
    by_cases hx : x = 0
    · simp [hx]
    · have : 0 < ‖x‖ := norm_pos_iff.2 hx
      rw [inv_mul_cancel₀ this.ne']
  calc ‖h x‖ * ‖((‖x‖ : ℝ) : ℂ)⁻¹ * x‖ ≤ ‖h x‖ * 1 :=
        mul_le_mul_of_nonneg_left he (norm_nonneg _)
    _ = ‖h x‖ := mul_one _

/-- **`|2π pout_3[ν^in_j(t)]| ≤ 4π η^in_j(A_jt)`** for `1 ≤ j < n`, `t ≥ 0` with
`D_{j+1}(t) ⊂ B_{ar_j/8}` (`09_relay.tex:1070-1085`: `lem:coupling`(1) at `r = 1`; the unit circle
lies in `N'`, where `|h^in_j(A_jt)| ≤ ‖h^in_j(A_jt)‖_{C^{M_h}(N')}`). -/
theorem norm_two_pi_pout_nuIn_le (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ)
    {j : ℕ} (hj : 1 ≤ j) (hjn : j < P.n) {t : ℝ} (ht : 0 ≤ t) (hin : P.HInDefined j t)
    (Mh : ℕ) :
    ‖2 * Real.pi * BS.pout 3 (fun y => ((P.nuIn j t y : ℝ) : ℂ))‖ ≤
      4 * Real.pi * P.etaIn Mh j (P.A j * t) := by
  have ha := zero_lt_a
  have ha1 := a_lt_one
  obtain ⟨-, -, hsec⟩ := Kick.coupling_one P hP hN hj hjn ht hin
  have h1 : (1 : ℝ) ∈ Icc (a / 4) 3 := ⟨by linarith, by norm_num⟩
  have hsec1 := hsec 1 h1
  simp only [Complex.ofReal_one, one_zpow, mul_one] at hsec1
  -- `h^in_j(A_jt) ∈ C^{M_h}(N')`
  have hpath := Approx.hIn_continuous P hP hN hj hjn.le ht
    (t₂ := t) (fun t' ht' => by rwa [show t' = t from le_antisymm ht'.2 ht'.1]) Mh
  have hmem : MemCk Mh annN' (P.hIn j (P.A j * t)) := hpath.1 _ ⟨le_rfl, le_rfl⟩
  have hbd : ∀ θ : ℝ, ‖(fun y => ((OneRing.radComp (P.hIn j (P.A j * t)) y : ℝ) : ℂ))
      (((1 : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ≤ P.etaIn Mh j (P.A j * t) := by
    intro θ
    set y : ℂ := ((1 : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) with hy
    have hy1 : ‖y‖ = 1 := by
      rw [hy, Complex.ofReal_one, one_mul]
      exact Complex.norm_exp_ofReal_mul_I _
    have hyN : y ∈ annN' := by
      show a / 4 ≤ ‖y‖ ∧ ‖y‖ ≤ 3
      rw [hy1]
      exact ⟨by linarith, by norm_num⟩
    simp only [Complex.norm_real, Real.norm_eq_abs]
    exact (abs_radComp_le _ _).trans (norm_le_normCk hmem hyN)
  have hA := norm_angularSector_le
    (g := fun y => ((OneRing.radComp (P.hIn j (P.A j * t)) y : ℝ) : ℂ)) 3 1 hbd
  rw [hsec1, norm_mul] at hA
  have hI2 : ‖Complex.I / 2‖ = 1 / 2 := by
    rw [norm_div, Complex.norm_I, Complex.norm_two]
  rw [hI2] at hA
  have hpi := Real.pi_pos
  rw [norm_mul, norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hpi]
  nlinarith [norm_nonneg (BS.pout 3 (fun y => ((P.nuIn j t y : ℝ) : ℂ)))]

end PrehistoryAux

end Relay

end NonUniqueEuler
