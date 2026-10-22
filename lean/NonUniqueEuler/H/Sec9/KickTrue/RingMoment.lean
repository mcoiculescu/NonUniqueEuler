import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import NonUniqueEuler.Defs.Sec9.All
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.I.Infra.Multipole.Moments

/-!
# Helpers for `P/Sec9/KickTrue`: the ring moment `q^ring = 2π pout_3[w_{k+1}]`

Helper file of `P/Sec9/KickTrue.lean` (`lem:kicktrue`, step (Q1), `09_relay.tex:1290-1296`):
"in ring-`(k+1)` units the function `ω^{(n)}(t)1_{S_{k+1}(t)}` is `A_{k+1}(Φ + w_{k+1}(t))`. Since `Φ` is
radial and `w_{k+1}(t)` is real, `q^ring(τ) = conj Q_m[w_{k+1}(t)] = 2π pout_3[w_{k+1}(t)]`".

* `integral_sub_of_integral_eq_zero`: `∫(f - g) = ∫f` if `g` is integrable with `∫g = 0` (no
  integrability of `f` needed: both sides vanish otherwise);
* `Qm_Phi_eq_zero`: `Q_3[Φ] = 0` (`Φ` radial) and integrability of `Φ(y)y³`;
* `Qm_unitsVort`: `Q_3[A⁻¹g(r·)] = A⁻¹r⁻⁵Q_3[g]` (scaling, `r > 0`);
* `conjQm_omegaRing_eq`: `conj Q_3[ω(t)1_{S_j(t)}]/(A_j r_j⁵) = 2π pout_3[w_j(t)]` for every `j`, `t`;
* `qRing_eq`: `q^ring(τ_K) = 2π pout_3[w_{k+1}(T_{k+1} + τ_K/A_{k+1})]`.
Everything here is proved.
-/

noncomputable section

open MeasureTheory Set ComplexConjugate

namespace NonUniqueEuler

namespace Relay

namespace KickTrueAux

open RingData Datum

/-- `∫(f - g) = ∫f` when `g` is integrable with `∫g = 0`. -/
theorem integral_sub_of_integral_eq_zero {f g : ℂ → ℂ} (hg : Integrable g)
    (hg0 : ∫ y, g y = 0) : ∫ y, (f y - g y) = ∫ y, f y := by
  by_cases hf : Integrable f
  · rw [integral_sub hf hg, hg0, sub_zero]
  · have hfg : ¬ Integrable (fun y => f y - g y) := by
      intro h
      apply hf
      have h2 := h.add hg
      have he : (fun y => f y - g y) + g = f := by funext y; simp
      rwa [he] at h2
    rw [integral_undef hf, integral_undef hfg]

/-- `Q_3[Φ] = 0` and `Φ(y)y³` is integrable (`Φ ∈ C_c^∞` radial, `lem:ring-facts`). -/
theorem Qm_Phi_eq_zero {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) :
    Integrable (fun y : ℂ => ((ringPhi χ y : ℝ) : ℂ) * y ^ 3) ∧
      ∫ y : ℂ, ((ringPhi χ y : ℝ) : ℂ) * y ^ 3 = 0 := by
  obtain ⟨hcd, hcs, hrad, -⟩ := ringFacts_of_admissible hχ
  have hc : Continuous (ringPhi χ) := hcd.continuous
  constructor
  · have hc' : Continuous (fun y : ℂ => ((ringPhi χ y : ℝ) : ℂ) * y ^ 3) := by fun_prop
    refine hc'.integrable_of_hasCompactSupport ?_
    have h : HasCompactSupport (fun y : ℂ => ((ringPhi χ y : ℝ) : ℂ)) :=
      hcs.comp_left Complex.ofReal_zero
    exact h.mul_right
  · have hrot : ∀ θ : ℝ, (fun x => ((ringPhi χ (rot θ x) : ℝ) : ℂ)) =ᵐ[volume]
        fun x => ((ringPhi χ x : ℝ) : ℂ) := by
      intro θ
      exact Filter.Eventually.of_forall fun x => by simp only [hrad θ x]
    have h := Multipole.moment_eq_zero_of_rot_invariant
      (g := fun x => ((ringPhi χ x : ℝ) : ℂ)) hrot (l := (3 : ℤ)) (by norm_num)
    have h2 := BS.Qm_eq_moment 3 (fun y => ((ringPhi χ y : ℝ) : ℂ))
    simp only [BS.Qm] at h2
    rw [h2]
    exact_mod_cast h

/-- Scaling of `Q_3`: `Q_3[A⁻¹ g(r ·)] = A⁻¹ r⁻⁵ Q_3[g]` for `r > 0`. -/
theorem Qm_scaleVort (A r : ℝ) (hr : 0 < r) (g : ℂ → ℝ) :
    ∫ y : ℂ, ((scaleVort A r g y : ℝ) : ℂ) * y ^ 3 =
      ((A⁻¹ * (r ^ 5)⁻¹ : ℝ) : ℂ) * ∫ x : ℂ, ((g x : ℝ) : ℂ) * x ^ 3 := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hpt : ∀ y : ℂ, ((scaleVort A r g y : ℝ) : ℂ) * y ^ 3 =
      ((A⁻¹ * (r ^ 3)⁻¹ : ℝ) : ℂ) *
        ((fun x : ℂ => ((g x : ℝ) : ℂ) * x ^ 3) (r • y)) := by
    intro y
    simp only [scaleVort, Complex.real_smul]
    push_cast
    field_simp
  have hsc : ∫ x : ℂ, ((g (r • x) : ℝ) : ℂ) * (r • x) ^ 3 =
      |((r ^ 2)⁻¹)| • ∫ x : ℂ, ((g x : ℝ) : ℂ) * x ^ 3 := by
    have := Measure.integral_comp_smul (volume : Measure ℂ)
      (fun x : ℂ => ((g x : ℝ) : ℂ) * x ^ 3) r
    rwa [Complex.finrank_real_complex] at this
  simp_rw [hpt]
  rw [integral_const_mul, hsc]
  rw [abs_of_pos (by positivity : (0 : ℝ) < (r ^ 2)⁻¹), Complex.real_smul, ← mul_assoc]
  congr 1
  push_cast
  field_simp

/-- **`conj Q_3[ω(t)1_{S_j(t)}]/(A_j r_j⁵) = 2π pout_3[w_j(t)]`** for a valid approximation and every
level `j` and time `t` (`09_relay.tex:1290-1296`; `Φ` radial, `w_j(t)` real). -/
theorem conjQm_omegaRing_eq (P : Approx) (hP : P.Valid) (j : ℕ) (t : ℝ) :
    conj (BS.Qm 3 fun x => ((P.omegaRing j t x : ℝ) : ℂ)) /
        ((P.A j * P.r j ^ (3 + 2) : ℝ) : ℂ) =
      2 * Real.pi * BS.pout 3 (P.w j t) := by
  have hA := hP.A_pos j
  have hr := hP.r_pos j
  obtain ⟨hΦi, hΦ0⟩ := Qm_Phi_eq_zero hP.admissible
  have hw : P.w j t = fun y => ((P.wR j t y : ℝ) : ℂ) := rfl
  have hsplit : (fun y : ℂ => ((P.wR j t y : ℝ) : ℂ) * y ^ 3) = fun y =>
      ((P.unitsVort j (P.omegaRing j t) y : ℝ) : ℂ) * y ^ 3 -
        ((ringPhi P.χ y : ℝ) : ℂ) * y ^ 3 := by
    funext y
    simp only [Approx.wR]
    push_cast
    ring
  have hQ : BS.Qm 3 (fun y => ((P.wR j t y : ℝ) : ℂ)) =
      (((P.A j)⁻¹ * (P.r j ^ 5)⁻¹ : ℝ) : ℂ) *
        BS.Qm 3 (fun x => ((P.omegaRing j t x : ℝ) : ℂ)) := by
    unfold BS.Qm
    rw [hsplit, integral_sub_of_integral_eq_zero hΦi hΦ0]
    exact Qm_scaleVort _ _ hr _
  rw [hw, BS.two_pi_mul_pout_ofReal, hQ, map_mul, Complex.conj_ofReal, div_eq_inv_mul]
  congr 1
  simp only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow]
  ring

/-- **`q^ring(τ_K) = 2π pout_3[w_{k+1}(t)]`**, `t = T_{k+1} + τ_K/A_{k+1}` (`09_relay.tex:1290-1296`). -/
theorem qRing_eq (P : Approx) (hP : P.Valid) (k : ℕ) (τK : ℝ) :
    P.qRing k τK = 2 * Real.pi * BS.pout 3 (P.w (k + 1) (P.T (k + 1) + τK / P.A (k + 1))) :=
  conjQm_omegaRing_eq P hP (k + 1) _

end KickTrueAux

end Relay

end NonUniqueEuler
