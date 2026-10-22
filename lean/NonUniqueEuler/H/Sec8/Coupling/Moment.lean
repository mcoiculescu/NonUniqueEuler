import NonUniqueEuler.Defs.Sec8.All
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Helper for `lem:coupling`(1): `pout_3[ν^in_k] = μ s_k⁵ q_{k+1}(t)/(2π)`

Helper of `P/Sec8/Coupling.lean` (fully proved). Manuscript `08_kick.tex:104-109`: "the change of
variables `x = r_k y` and the reality of `ω_{≥k+1}(t)` give
`p_3 = (2πA_k)⁻¹∫ω_{≥k+1}(t, r_ky) ȳ³ dy = conj(Q_m[ω_{≥k+1}(t)])/(2πA_kr_k⁵)
= A_{k+1}r_{k+1}⁵/(2πA_kr_k⁵) q_{k+1}(t) = μs_k⁵/(2π) q_{k+1}(t)`."

* `pout_nuIn`: the identity (no integrability needed: `∫ f(r·) = r⁻² ∫ f` and
  `∫ conj f = conj ∫ f` hold for every `f`).
-/

noncomputable section

open MeasureTheory Set ComplexConjugate

namespace NonUniqueEuler.CouplingAux

open RingData Datum

/-- **`pout_3[ν^in_k(t)] = μ s_k⁵ q_{k+1}(t)/(2π)`** (`08_kick.tex:104-109`), for `k ≥ 1`. -/
theorem pout_nuIn (P : Approx) (hP : P.Valid) {k : ℕ} (hk : 1 ≤ k) (t : ℝ) :
    BS.pout 3 (fun y => ((P.nuIn k t y : ℝ) : ℂ)) =
      ((P.μ * P.s k ^ 5 / (2 * Real.pi) : ℝ) : ℂ) * P.q (k + 1) t := by
  have hA : 0 < P.A k := hP.A_pos k
  have hr : 0 < P.r k := hP.r_pos k
  have hs : 0 < P.s k := hP.s_pos k
  have hμ : 0 < P.μ := by linarith [hP.datumParams.one_lt_μ]
  have hA' : P.A (k + 1) = P.μ * P.A k := amp_succ _ _ hk
  have hr' : P.r (k + 1) = P.s k * P.r k := radius_succ _ _ hk
  set F : ℂ → ℂ := fun x => ((P.omegaGe (k + 1) t x : ℝ) : ℂ) * conj x ^ 3 with hF
  have h1 : ∀ y : ℂ, ((P.nuIn k t y : ℝ) : ℂ) * conj y ^ 3 =
      (((P.A k)⁻¹ / P.r k ^ 3 : ℝ) : ℂ) * F ((P.r k : ℝ) • y) := by
    intro y
    have hr0 : ((P.r k : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
    simp only [hF, Complex.real_smul, map_mul, Complex.conj_ofReal]
    show (((P.A k)⁻¹ * P.omegaGe (k + 1) t (((P.r k : ℝ) : ℂ) * y) : ℝ) : ℂ) * conj y ^ 3 = _
    push_cast
    field_simp
  have h2 : ∫ x, F x = conj (BS.Qm 3 fun x => ((P.omegaGe (k + 1) t x : ℝ) : ℂ)) := by
    unfold BS.Qm
    rw [← integral_conj]
    congr 1
    funext x
    simp [hF, map_mul, map_pow]
  have hq : conj (BS.Qm 3 fun x => ((P.omegaGe (k + 1) t x : ℝ) : ℂ)) =
      P.q (k + 1) t * ((P.A (k + 1) * P.r (k + 1) ^ (3 + 2) : ℝ) : ℂ) := by
    have hne : ((P.A (k + 1) * P.r (k + 1) ^ (3 + 2) : ℝ) : ℂ) ≠ 0 := by
      have := hP.A_pos (k + 1)
      have := hP.r_pos (k + 1)
      exact_mod_cast (by positivity : P.A (k + 1) * P.r (k + 1) ^ (3 + 2) ≠ 0)
    unfold Approx.q
    rw [div_mul_cancel₀ _ hne]
  unfold BS.pout
  simp_rw [h1]
  rw [integral_const_mul, Measure.integral_comp_smul, h2, hq, Complex.finrank_real_complex, hA',
    hr']
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_pos.ne'
  rw [abs_of_pos (by positivity : (0 : ℝ) < (P.r k ^ 2)⁻¹), Complex.real_smul]
  push_cast
  have hr0 : ((P.r k : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  have hA0 : ((P.A k : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hA.ne'
  field_simp

end NonUniqueEuler.CouplingAux
