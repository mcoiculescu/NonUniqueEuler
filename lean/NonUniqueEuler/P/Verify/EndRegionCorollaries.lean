import NonUniqueEuler.Defs.Verify.Profile
import NonUniqueEuler.I.Verify.EndRegions
import NonUniqueEuler.I.Verify.Comparison
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Proof: Lemma A.1(2) in the form used by steps (ii) and (iv) of the enclosure procedure

Proof of `NonUniqueEuler/I/Verify/EndRegionCorollaries.lean` (same declarations, statements
copied verbatim). Manuscript: proof of Proposition A.3, steps (ii) and (iv)
(`A_verification.tex:385-392`, `:436-447`).

Used black boxes: `endRegion_comparison` (`I/Verify/EndRegions.lean`), `cmpSol_one_ell` and
`cmpSol'_add_mul_cmpSol` (`I/Verify/Comparison.lean`).
-/

noncomputable section

open Set

namespace NonUniqueEuler

namespace AppA

open RingData

theorem exp_sub_one_le_two_mul {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    Real.exp ε - 1 ≤ 2 * ε := by
  have h := Real.abs_exp_sub_one_sub_id_le (x := ε) (by rw [abs_of_nonneg h0]; exact h1)
  have h2 := (abs_le.mp h).2
  nlinarith

/-- `0 ≤ ε_end` and `e^{ε_end} - 1 ≤ 2ε` for `ε_end ≤ ε ≤ 1` (private helper). -/
private theorem epsEnd_aux {z : ℂ} (hz : 0 < z.re) {ε : ℝ} (hε : epsEnd z ≤ ε)
    (hε1 : ε ≤ 1) :
    0 ≤ Real.exp (epsEnd z) - 1 ∧ Real.exp (epsEnd z) - 1 ≤ 2 * ε := by
  have h0 : 0 ≤ epsEnd z := div_nonneg (by positivity) hz.le
  refine ⟨by linarith [Real.add_one_le_exp (epsEnd z)], ?_⟩
  calc Real.exp (epsEnd z) - 1 ≤ Real.exp ε - 1 := by gcongr
    _ ≤ 2 * ε := exp_sub_one_le_two_mul (h0.trans hε) hε1

/-- Step (ii): the enclosure of `(ψ(ξa), ψ'(ξa))`. -/
theorem leftEnd_bound {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {z : ℂ}
    (hz : 0 < z.re) {G : ℝ} {ψ ψ' : ℝ → ℂ} (hsol : IsEvansSolution χ ℓ z G ψ ψ') {ε : ℝ}
    (hε : epsEnd z ≤ ε) (hε1 : ε ≤ 1) :
    ‖ψ ξa - ((Real.exp (ℓ * endL) : ℝ) : ℂ)‖ ≤ 2 * ε * Real.exp (ℓ * endL) ∧
      ‖ψ' ξa - (ℓ : ℂ) * ((Real.exp (ℓ * endL) : ℝ) : ℂ)‖ ≤
        2 * ℓ * ε * Real.exp (ℓ * endL) := by
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hLa : ξL ≤ ξa := by norm_num [ξL, ξa]
  have hcmp := endRegion_comparison hχ hℓ hz hsol (Or.inl ⟨rfl, rfl⟩) ξa ⟨hLa, le_rfl⟩
  rw [hsol.init, hsol.init'] at hcmp
  have hc := cmpSol_one_ell hℓpos.ne' ξL ξa
  simp only [Complex.ofReal_natCast] at hc
  rw [hc.1, hc.2, show ξa - ξL = endL from rfl] at hcmp
  have hw : wnorm (ℓ : ℝ) 1 (ℓ : ℂ) = ℓ := by
    simp [wnorm]
  rw [hw] at hcmp
  obtain ⟨hA, hB⟩ := max_le_iff.mp hcmp
  obtain ⟨_, he⟩ := epsEnd_aux hz hε hε1
  have hE : 0 ≤ Real.exp (ℓ * endL) * ℓ := by positivity
  have hmul := mul_le_mul_of_nonneg_left he hE
  refine ⟨?_, ?_⟩
  · have h1 : (ℓ : ℝ) * ‖ψ ξa - ((Real.exp (ℓ * endL) : ℝ) : ℂ)‖ ≤
        (ℓ : ℝ) * (2 * ε * Real.exp (ℓ * endL)) := by
      calc _ ≤ _ := hA
        _ ≤ _ := hmul
        _ = _ := by ring
    exact le_of_mul_le_mul_left h1 hℓpos
  · calc _ ≤ _ := hB
      _ ≤ _ := hmul
      _ = _ := by ring

/-- Step (iv): the enclosure of `(ψ' + ℓψ)(ξR)` from `(ψ, ψ')(ξb)`. -/
theorem rightEnd_bound {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {z : ℂ}
    (hz : 0 < z.re) {G : ℝ} {ψ ψ' : ℝ → ℂ} (hsol : IsEvansSolution χ ℓ z G ψ ψ') {ε : ℝ}
    (hε : epsEnd z ≤ ε) (hε1 : ε ≤ 1) {W : ℝ} (hW : wnorm ℓ (ψ ξb) (ψ' ξb) ≤ W) :
    ‖(ψ' ξR + (ℓ : ℂ) * ψ ξR) - ((Real.exp (ℓ * endR) : ℝ) : ℂ) * (ψ' ξb + (ℓ : ℂ) * ψ ξb)‖ ≤
      4 * ε * W * Real.exp (ℓ * endR) := by
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hbR : ξb ≤ ξR := by norm_num [ξb, ξR]
  have hcmp := endRegion_comparison hχ hℓ hz hsol (Or.inr ⟨rfl, rfl⟩) ξR ⟨hbR, le_rfl⟩
  have hc := cmpSol'_add_mul_cmpSol hℓpos.ne' ξb (ψ ξb) (ψ' ξb) ξR
  simp only [Complex.ofReal_natCast] at hc
  rw [show ξR - ξb = endR from rfl] at hcmp hc
  set c := cmpSol (ℓ : ℝ) ξb (ψ ξb) (ψ' ξb) ξR with hc_def
  set c' := cmpSol' (ℓ : ℝ) ξb (ψ ξb) (ψ' ξb) ξR with hc'_def
  set E := Real.exp (ℓ * endR) with hE_def
  have key : (ψ' ξR + (ℓ : ℂ) * ψ ξR) - (E : ℂ) * (ψ' ξb + (ℓ : ℂ) * ψ ξb) =
      (ψ' ξR - c') + (ℓ : ℂ) * (ψ ξR - c) := by
    rw [← hc]; ring
  rw [key]
  obtain ⟨he0, he⟩ := epsEnd_aux hz hε hε1
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hw0 : 0 ≤ wnorm ℓ (ψ ξb) (ψ' ξb) := le_max_of_le_right (norm_nonneg _)
  have hW0 : 0 ≤ W := hw0.trans hW
  have hsplit : ‖(ψ' ξR - c') + (ℓ : ℂ) * (ψ ξR - c)‖ ≤
      2 * wnorm ℓ (ψ ξR - c) (ψ' ξR - c') := by
    have h1 := norm_add_le (ψ' ξR - c') ((ℓ : ℂ) * (ψ ξR - c))
    rw [norm_mul, Complex.norm_natCast] at h1
    have h2 : (ℓ : ℝ) * ‖ψ ξR - c‖ ≤ wnorm ℓ (ψ ξR - c) (ψ' ξR - c') := le_max_left _ _
    have h3 : ‖ψ' ξR - c'‖ ≤ wnorm ℓ (ψ ξR - c) (ψ' ξR - c') := le_max_right _ _
    linarith
  calc _ ≤ 2 * wnorm ℓ (ψ ξR - c) (ψ' ξR - c') := hsplit
    _ ≤ 2 * (E * wnorm ℓ (ψ ξb) (ψ' ξb) * (Real.exp (epsEnd z) - 1)) := by
      gcongr
    _ ≤ 2 * (E * W * (2 * ε)) := by
      gcongr 2 * ?_
      exact mul_le_mul (mul_le_mul_of_nonneg_left hW hE0) he he0 (mul_nonneg hE0 hW0)
    _ = 4 * ε * W * E := by ring

end AppA

end NonUniqueEuler
