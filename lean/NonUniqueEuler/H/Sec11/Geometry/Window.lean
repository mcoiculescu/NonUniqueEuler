import NonUniqueEuler.H.Sec11.Geometry.Basic
import NonUniqueEuler.I.Sec7.WindowLength
import NonUniqueEuler.I.Sec9.Detuning

/-!
# Helper for `P/Sec11/Geometry.lean`: the length of the confinement window

Helper of the proof of `lem:geometry`, hypothesis (iv) of `prop:confine` (`11_bootstrap.tex:176-189`):
for a level `j < n` with `T_{j+1}` defined and `t₁ ∈ [T_{j+1}, min(t, e_j)]`,
`A_{j+1}(t₁ - T_{j+1}) < μ[T_pin + 1 + σ'⁻¹((m+2) log(1/s_j) + log₊(δ₀/K_lo))]`, hence
`Λ = 2 + 2C_*A_{j+1}(t₁ - T_{j+1}) < Λ^conf_j` (strictly, as in the manuscript; the strict
inequality gives `\bar B_{ϱ_j(t')} ⊂ B_{ar_j/8}` with the open ball). Uses `lem:window-length`
(`Rings.window_length`, first bound only), `lem:detuning` (`σ_j ≥ 15σ/16 > σ'`) and the bound
`T̂_j ≤ σ'⁻¹((m+2) log(1/s_j) + log₊(δ₀/K_lo))` (proved here, `11_bootstrap.tex:182-183`). All
proved.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

namespace GeometryH

open RingData Datum

variable {S : Standing}

/-- `(m+2) log(1/s_j) + log₊(δ₀/K_lo) ≥ 0`. -/
theorem logTerm_nonneg (hS : S.Holds) {j : ℕ} (hj : 1 ≤ j) :
    0 ≤ (3 + 2) * Real.log (1 / S.P.s j) + Real.posLog (S.P.δ₀ / S.Klo) := by
  have hs := s_pos hS j
  have hs1 : S.P.s j ≤ 1 := by
    have := s_le hS hj
    have := a_lt_one
    linarith
  have h1 : 1 ≤ 1 / S.P.s j := by rw [le_div_iff₀ hs]; linarith
  have h2 := Real.log_nonneg h1
  have h3 : 0 ≤ Real.posLog (S.P.δ₀ / S.Klo) := Real.posLog_nonneg
  positivity

/-- `T̂_j = σ_j⁻¹ log(δ₀/κ♯_j) ≤ σ'⁻¹((m+2) log(1/s_j) + log₊(δ₀/K_lo))` when `σ_j ≥ σ'`,
`κ♯_j ≥ K_lo s_j^{m+2}` and `T_j` is defined (`11_bootstrap.tex:182-183`). -/
theorem That_le (hS : S.Holds) (hpos : S.ConstPos) {j : ℕ} (hj : j ∈ Finset.Icc 1 S.P.n)
    (hc : S.P.ClockUpTo j) (hσ : S.σ' ≤ S.P.sigma j)
    (hamp : S.Klo * S.P.s j ^ (3 + 2) ≤ S.P.ksh j) :
    S.P.That j ≤ 1 / S.σ' * ((3 + 2) * Real.log (1 / S.P.s j) + Real.posLog (S.P.δ₀ / S.Klo)) := by
  have hjn := (Finset.mem_Icc.1 hj).2
  have hκ := hc.ksh_mem le_rfl hjn
  have hσ' := σ'_pos hS
  have hs := s_pos hS j
  have hK := hpos.Klo_pos
  have hδ := hS.δ₀_pos
  have hL0 : 0 ≤ Real.log (S.P.δ₀ / S.P.ksh j) :=
    Real.log_nonneg (by rw [le_div_iff₀ hκ.1]; linarith [hκ.2])
  have hLle : Real.log (S.P.δ₀ / S.P.ksh j) ≤
      (3 + 2) * Real.log (1 / S.P.s j) + Real.posLog (S.P.δ₀ / S.Klo) := by
    have hKs : 0 < S.Klo * S.P.s j ^ (3 + 2) := by positivity
    have h1 : S.P.δ₀ / S.P.ksh j ≤ S.P.δ₀ / (S.Klo * S.P.s j ^ (3 + 2)) :=
      div_le_div_of_nonneg_left hδ.le hKs hamp
    have h2 : Real.log (S.P.δ₀ / S.P.ksh j) ≤ Real.log (S.P.δ₀ / (S.Klo * S.P.s j ^ (3 + 2))) :=
      Real.log_le_log (div_pos hδ hκ.1) h1
    have h3 : S.P.δ₀ / (S.Klo * S.P.s j ^ (3 + 2)) = (S.P.δ₀ / S.Klo) * (1 / S.P.s j) ^ (3 + 2) := by
      rw [one_div_pow, mul_one_div, div_div]
    have h4 : Real.log ((S.P.δ₀ / S.Klo) * (1 / S.P.s j) ^ (3 + 2)) =
        Real.log (S.P.δ₀ / S.Klo) + (3 + 2) * Real.log (1 / S.P.s j) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
      push_cast
      ring
    have h5 : Real.log (S.P.δ₀ / S.Klo) ≤ Real.posLog (S.P.δ₀ / S.Klo) := by
      rw [Real.posLog_apply]
      exact le_max_right _ _
    rw [h3, h4] at h2
    linarith
  show (S.P.sigma j)⁻¹ * Real.log (S.P.δ₀ / S.P.ksh j) ≤ _
  have hinv : (S.P.sigma j)⁻¹ ≤ S.σ'⁻¹ := inv_anti₀ hσ' hσ
  calc (S.P.sigma j)⁻¹ * Real.log (S.P.δ₀ / S.P.ksh j)
      ≤ S.σ'⁻¹ * Real.log (S.P.δ₀ / S.P.ksh j) := mul_le_mul_of_nonneg_right hinv hL0
    _ ≤ S.σ'⁻¹ * ((3 + 2) * Real.log (1 / S.P.s j) + Real.posLog (S.P.δ₀ / S.Klo)) :=
        mul_le_mul_of_nonneg_left hLle (inv_nonneg.2 hσ'.le)
    _ = _ := by rw [one_div S.σ']

/-- **The length of the window** (`11_bootstrap.tex:176-187`): for `j < n` with `T_{j+1}` defined
and `t₁ ∈ [T_{j+1}, min(t, e_j)]`, under the hypotheses of `lem:geometry`,
`A_{j+1}(t₁ - T_{j+1}) < μ[T_pin + 1 + σ'⁻¹((m+2) log(1/s_j) + log₊(δ₀/K_lo))]`. -/
theorem kickTime_lt (hS : S.Holds) (hL : S.ParamLists) {t : ℝ} (h : S.GeometryHyp t) {j : ℕ}
    (hj1 : 1 ≤ j) (hjn : j < S.P.n) (hc : S.P.ClockUpTo (j + 1)) {t₁ : ℝ}
    (hT : S.P.T (j + 1) ≤ t₁) (he : t₁ ≤ S.P.endW j) (ht : t₁ ≤ t) :
    S.P.kickTime j t₁ < S.P.μ * (S.P.Tpin + 1 + 1 / S.σ' *
      ((3 + 2) * Real.log (1 / S.P.s j) + Real.posLog (S.P.δ₀ / S.Klo))) := by
  have hX := logTerm_nonneg hS hj1
  have hσ' := σ'_pos hS
  have hμ := hS.one_lt_μ
  have hTp := hS.Tpin_pos
  set Y := 1 / S.σ' * ((3 + 2) * Real.log (1 / S.P.s j) + Real.posLog (S.P.δ₀ / S.Klo)) with hY
  have hY0 : 0 ≤ Y := mul_nonneg (by positivity) hX
  have hμY : 0 ≤ S.P.μ * Y := mul_nonneg (by linarith) hY0
  have hlt : S.P.Tpin < S.P.μ * (S.P.Tpin + 1) := by nlinarith
  have hexp : S.P.μ * (S.P.Tpin + 1 + Y) = S.P.μ * (S.P.Tpin + 1) + S.P.μ * Y := by ring
  rw [hexp]
  by_cases h1 : t₁ ≤ S.P.tsh j
  · have := kickTime_le_Tpin hS hjn h1
    linarith
  · replace h1 := lt_of_not_ge h1
    have hcj : S.P.ClockUpTo j := by
      by_contra hcj
      rw [Approx.endW_of_not_clockUpTo hcj] at he
      linarith
    rw [Approx.endW_of_clockUpTo hcj] at he
    have hjmem : j ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.2 ⟨hj1, hjn.le⟩
    have hdet := (detuning S hS hL.det).2.2 j hjmem
    have hσ : S.σ' ≤ S.P.sigma j := (hdet.2.2.1.trans_le hdet.2.1).le
    have hamp := h.amp j (Finset.mem_Ico.2 ⟨hj1, hjn⟩) hc (h1.trans_le ht)
    have hpos := constPos hS
    have hWL := (Rings.window_length S.P hS.valid hS.hN (gsmall hS) hj1 hjn hcj ⟨hT, he⟩).2
      S.σ' S.Klo h1.le hσ' hpos.Klo_pos hσ hamp
    have hTh := That_le hS hpos hjmem hcj hσ hamp
    have h2 : S.P.μ * S.P.That j ≤ S.P.μ * Y := mul_le_mul_of_nonneg_left hTh (by linarith)
    linarith [hWL.1]

/-- `A_{j+1}(t - T_{j+1}) ≥ 0` for `t ≥ T_{j+1}`. -/
theorem kickTime_nonneg (hS : S.Holds) {j : ℕ} {t : ℝ} (ht : S.P.T (j + 1) ≤ t) :
    0 ≤ S.P.kickTime j t :=
  mul_nonneg (A_pos hS (j + 1)).le (sub_nonneg.2 ht)

/-- The kick time increases with `t`. -/
theorem kickTime_mono (hS : S.Holds) (j : ℕ) {t t' : ℝ} (ht : t ≤ t') :
    S.P.kickTime j t ≤ S.P.kickTime j t' :=
  mul_le_mul_of_nonneg_left (by linarith) (A_pos hS (j + 1)).le

/-- `Λ = 2 + 2C_*A_{j+1}(t₁ - T_{j+1}) < Λ^conf_j` (`11_bootstrap.tex:188`). -/
theorem confLambda_lt (hS : S.Holds) (hL : S.ParamLists) {t : ℝ} (h : S.GeometryHyp t) {j : ℕ}
    (hj1 : 1 ≤ j) (hjn : j < S.P.n) (hc : S.P.ClockUpTo (j + 1)) {t₁ : ℝ}
    (hT : S.P.T (j + 1) ≤ t₁) (he : t₁ ≤ S.P.endW j) (ht : t₁ ≤ t) :
    S.P.confLambda j t₁ < S.Lconf j := by
  have hk := kickTime_lt hS hL h hj1 hjn hc hT he ht
  have hC : 0 < 2 * Cstar := by have := Cstar_pos; positivity
  have := mul_lt_mul_of_pos_left hk hC
  simp only [Approx.confLambda, Standing.Lconf]
  linarith

/-- `Λ ≥ 0` for `t₁ ≥ T_{j+1}`. -/
theorem confLambda_nonneg (hS : S.Holds) {j : ℕ} {t₁ : ℝ} (hT : S.P.T (j + 1) ≤ t₁) :
    0 ≤ S.P.confLambda j t₁ := by
  have := kickTime_nonneg hS hT
  have := Cstar_pos
  simp only [Approx.confLambda]
  positivity

end GeometryH

end Relay

end NonUniqueEuler
