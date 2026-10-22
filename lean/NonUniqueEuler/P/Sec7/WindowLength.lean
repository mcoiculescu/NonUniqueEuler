import NonUniqueEuler.Defs.Sec7.All
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

/-!
# Proof: `lem:window-length` (the length of a window in kick time)

Proof of the interface `NonUniqueEuler/I/Sec7/WindowLength.lean`, following
`07_several_rings.tex:402-414`:
1. `A_{k+1}(t - T_{k+1}) = A_{k+1}(t - t♯_k) + T_pin` (`tsh_eq_T_add`), which gives the first claim.
2. `t ≤ T_k = t♯_k + T̂_k/A_k` and `A_{k+1} = μA_k` give `A_{k+1}(t - T_{k+1}) ≤ T_pin + μT̂_k`.
3. `κ♯_k ∈ (0,δ₀)`, `σ_k ≥ σ' > 0`, `κ♯_k ≥ K_lo s_k^5` give
   `T̂_k ≤ σ'⁻¹ log(δ₀/(K_lo s_k^5)) ≤ σ'⁻¹(5 log(1/s_k) + log₊(δ₀/K_lo))`.
4. `T_pin ≤ μ(T_pin + 1)` since `μ > 1`, `T_pin > 0`.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Rings

open RingData Datum

namespace WindowLengthAux

/-- Step 3, over named real variables: if `0 < κ < δ`, `0 < σ' ≤ σ`, `0 < K`, `0 < s` and
`K s^5 ≤ κ`, then `σ⁻¹ log(δ/κ) ≤ σ'⁻¹(5 log(1/s) + log₊(δ/K))`. -/
theorem that_le {σ σ' δ κ K s : ℝ} (hκ : 0 < κ) (hκδ : κ < δ) (hσ' : 0 < σ') (hσ : σ' ≤ σ)
    (hK : 0 < K) (hs : 0 < s) (hKs : K * s ^ (3 + 2) ≤ κ) :
    σ⁻¹ * Real.log (δ / κ) ≤
      1 / σ' * ((3 + 2) * Real.log (1 / s) + Real.posLog (δ / K)) := by
  have hδ : 0 < δ := hκ.trans hκδ
  have hs5 : 0 < s ^ (3 + 2) := pow_pos hs _
  have hKs5 : 0 < K * s ^ (3 + 2) := mul_pos hK hs5
  -- `log(δ/κ) > 0`
  have hL : 0 < Real.log (δ / κ) := Real.log_pos ((one_lt_div hκ).2 hκδ)
  -- `σ⁻¹ ≤ σ'⁻¹`
  have hinv : σ⁻¹ ≤ σ'⁻¹ := inv_anti₀ hσ' hσ
  have h1 : σ⁻¹ * Real.log (δ / κ) ≤ σ'⁻¹ * Real.log (δ / κ) :=
    mul_le_mul_of_nonneg_right hinv hL.le
  -- `log(δ/κ) ≤ log(δ/(K s^5))`
  have h2 : Real.log (δ / κ) ≤ Real.log (δ / (K * s ^ (3 + 2))) :=
    Real.log_le_log (div_pos hδ hκ) (div_le_div_of_nonneg_left hδ.le hKs5 hKs)
  -- `log(δ/(K s^5)) = log(δ/K) + 5 log(1/s)`
  have h3 : Real.log (δ / (K * s ^ (3 + 2))) = Real.log (δ / K) + (3 + 2) * Real.log (1 / s) := by
    have hsplit : δ / (K * s ^ (3 + 2)) = (δ / K) * (1 / s) ^ (3 + 2) := by
      rw [one_div_pow]
      field_simp
    rw [hsplit, Real.log_mul (div_pos hδ hK).ne' (pow_pos (one_div_pos.2 hs) _).ne',
      Real.log_pow]
    push_cast
    ring
  have h4 : Real.log (δ / K) ≤ Real.posLog (δ / K) := by
    rw [Real.posLog_apply]
    exact le_max_right _ _
  have hσ'inv : 0 ≤ σ'⁻¹ := inv_nonneg.2 hσ'.le
  calc σ⁻¹ * Real.log (δ / κ) ≤ σ'⁻¹ * Real.log (δ / κ) := h1
    _ ≤ σ'⁻¹ * ((3 + 2) * Real.log (1 / s) + Real.posLog (δ / K)) := by
        apply mul_le_mul_of_nonneg_left _ hσ'inv
        linarith
    _ = 1 / σ' * ((3 + 2) * Real.log (1 / s) + Real.posLog (δ / K)) := by
        rw [one_div σ']

end WindowLengthAux

/-- **`lem:window-length`** (`07_several_rings.tex:392-400`). Let `1 ≤ k < n`, the clock defined
up to level `k`, and `t ∈ W_k`. If `t ≤ t♯_k`, then `A_{k+1}(t - T_{k+1}) ≤ T_pin`. If `t ≥ t♯_k`,
`σ', K_lo > 0`, `σ_k ≥ σ'` and `κ♯_k ≥ K_lo s_k^{m+2}`, then
`A_{k+1}(t - T_{k+1}) ≤ T_pin + μT̂_k ≤ μ[T_pin + 1 + σ'⁻¹((m+2)log(1/s_k) + log₊(δ₀/K_lo))]`. -/
theorem window_length (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) (hG : P.GSmall)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k < P.n) (hc : P.ClockUpTo k) {t : ℝ} (ht : t ∈ P.W k) :
    (t ≤ P.tsh k → P.kickTime k t ≤ P.Tpin) ∧
    ∀ σ' Klo : ℝ, P.tsh k ≤ t → 0 < σ' → 0 < Klo → σ' ≤ P.sigma k →
      Klo * P.s k ^ (3 + 2) ≤ P.ksh k →
      P.kickTime k t ≤ P.Tpin + P.μ * P.That k ∧
      P.Tpin + P.μ * P.That k ≤ P.μ * (P.Tpin + 1 + 1 / σ' *
        ((3 + 2) * Real.log (1 / P.s k) + Real.posLog (P.δ₀ / Klo))) := by
  have hkne : k ≠ P.n + 1 := by omega
  have hA : 0 < P.A k := hP.A_pos k
  have hA1 : 0 < P.A (k + 1) := hP.A_pos (k + 1)
  have hμ : 1 < P.μ := hP.datumParams.one_lt_μ
  have hAμ : P.A (k + 1) = P.μ * P.A k := by
    rw [Approx.A_def, Approx.A_def]
    exact amp_succ _ _ hk
  have htsh := P.tsh_eq_T_add hkn
  have hT := P.T_of_ne hkne
  obtain ⟨_, ht2⟩ := ht
  -- Step 1: `A_{k+1}(u - T_{k+1}) = A_{k+1}(u - t♯_k) + T_pin`.
  have hkick : ∀ u : ℝ, P.kickTime k u = P.A (k + 1) * (u - P.tsh k) + P.Tpin := by
    intro u
    simp only [Approx.kickTime]
    rw [htsh]
    field_simp
    ring
  -- Step 2: `A_{k+1}(t - T_{k+1}) ≤ T_pin + μT̂_k`.
  have hstep2 : P.kickTime k t ≤ P.Tpin + P.μ * P.That k := by
    rw [hkick]
    have hle : t - P.tsh k ≤ P.That k / P.A k := by
      rw [hT] at ht2
      linarith
    have hmul : P.A (k + 1) * (t - P.tsh k) ≤ P.A (k + 1) * (P.That k / P.A k) :=
      mul_le_mul_of_nonneg_left hle hA1.le
    have heq : P.A (k + 1) * (P.That k / P.A k) = P.μ * P.That k := by
      rw [hAμ]
      field_simp
    linarith
  refine ⟨fun h => ?_, fun σ' Klo _ hσ' hKlo hσ hksh => ⟨hstep2, ?_⟩⟩
  · rw [hkick]
    have : P.A (k + 1) * (t - P.tsh k) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hA1.le (by linarith)
    linarith
  · -- Step 3: the bound on `T̂_k`.
    have hmem := hc.ksh_mem (le_refl k) hkn.le
    set B : ℝ := 1 / σ' * ((3 + 2) * Real.log (1 / P.s k) + Real.posLog (P.δ₀ / Klo)) with hB
    have hThat : P.That k ≤ B :=
      WindowLengthAux.that_le hmem.1 hmem.2 hσ' hσ hKlo (hP.s_pos k) hksh
    -- Step 4: `T_pin ≤ μ(T_pin + 1)`.
    have hμ0 : 0 < P.μ := by linarith
    have h1 : P.μ * P.That k ≤ P.μ * B := mul_le_mul_of_nonneg_left hThat hμ0.le
    have h2 : P.Tpin ≤ P.μ * P.Tpin := le_mul_of_one_le_left hP.Tpin_pos.le hμ.le
    have h3 : P.μ * (P.Tpin + 1 + B) = P.μ * P.Tpin + P.μ + P.μ * B := by ring
    rw [h3]
    linarith

end Rings

end NonUniqueEuler
