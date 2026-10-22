import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import NonUniqueEuler.Defs.Sec4.RingSetting
import NonUniqueEuler.Defs.Sec4.Operators
import NonUniqueEuler.I.Sec4.Sectors9
import NonUniqueEuler.I.Sec4.Edge
import NonUniqueEuler.I.Sec4.ClosedForm
import NonUniqueEuler.I.Sec4.RingFacts

/-!
# Proof: `cor:sector-6` (no unstable eigenvalue with `Re λ ≥ 9/200` in the sectors `±6`)

Proof of `I/Sec4/Sector6.lean` (`04_ring.tex:1192-1197`, proof `:1198-1203`). Same declaration,
statement copied verbatim.

Proof (as in the manuscript). Both settings are valid (`ringRefSetting_valid`,
`ringPhiSetting_valid`) and satisfy `EdgeSplit` (`ringRefSetting_edgeSplit`,
`ringPhiSetting_edgeSplit`). By `edge_bound` with `|ℓ| = 6`, `Zedge_ringPhi` and
`closedForm_Zedge` (`6d < 1`):
`Re λ ≤ ½Z_6^{1/2} = ½(Z^a_6Z^b_6)^{1/2} ≤ ½(e^{6a₀}Θ_6 + ε_*) < 9/200` by (N3) with `ℓ = 6`.
The step `(Z^a_6Z^b_6)^{1/2} ≤ e^{6a₀}Θ_6 + ε_*` uses `Z^a_6, Z^b_6 ≥ 0` (integrals of
nonnegative functions: `zedgeA_nonneg`, `zedgeB_nonneg`).
-/

noncomputable section

open Set MeasureTheory

namespace NonUniqueEuler

open RingData Sect

/-- `Z^a_ℓ ≥ 0`: the integrand `e^{2ℓ(ξ-ξ_c)}ϖ'(ξ)` is positive on `{ϖ' > 0}`. -/
private lemma zedgeA_nonneg (χ : ℝ → ℝ) (ℓ : ℕ) : 0 ≤ ZedgeA χ ℓ := by
  unfold ZedgeA
  have hmeas : MeasurableSet {ξ : ℝ | 0 < deriv (prof χ) ξ} :=
    measurableSet_lt measurable_const (measurable_deriv (prof χ))
  refine setIntegral_nonneg hmeas fun ξ hξ => ?_
  exact mul_nonneg (Real.exp_pos _).le (le_of_lt hξ)

/-- `Z^b_ℓ ≥ 0`: the integrand `e^{-2ℓ(ξ-ξ_c)}|ϖ'(ξ)|` is nonnegative. -/
private lemma zedgeB_nonneg (χ : ℝ → ℝ) (ℓ : ℕ) : 0 ≤ ZedgeB χ ℓ := by
  unfold ZedgeB
  exact integral_nonneg fun ξ => mul_nonneg (Real.exp_pos _).le (abs_nonneg _)

/-- `½ Z_6^{1/2} < 9/200` for the ring in reference units, under (N3). -/
private lemma half_sqrt_Zedge6_lt {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (h3 : N3) :
    1 / 2 * Real.sqrt ((ringRefSetting χ).Zedge 6) < 9 / 200 := by
  have hd : ((6 : ℕ) : ℝ) * d < 1 := by
    have := (ringData_order).2.2.2.2.2.2.1 6 (by norm_num) (by norm_num)
    exact this
  obtain ⟨hZ, hA, hB⟩ := closedForm_Zedge hχ (ℓ := 6) (by norm_num) hd
  set M : ℝ := Real.exp ((6 : ℕ) * a₀) * Θ 6 + εstar with hM
  have hN3 : M < 9 / 100 := h3 6 (by simp)
  have hA0 : 0 ≤ ZedgeA χ 6 := zedgeA_nonneg χ 6
  have hB0 : 0 ≤ ZedgeB χ 6 := zedgeB_nonneg χ 6
  have hM0 : 0 ≤ M := le_trans hA0 hA
  have hprod : ZedgeA χ 6 * ZedgeB χ 6 ≤ M * M := mul_le_mul hA hB hB0 hM0
  have hsqrt : Real.sqrt ((ringRefSetting χ).Zedge 6) ≤ M := by
    rw [hZ]
    calc Real.sqrt (ZedgeA χ 6 * ZedgeB χ 6) ≤ Real.sqrt (M * M) := Real.sqrt_le_sqrt hprod
      _ = M := Real.sqrt_mul_self hM0
  linarith

/-- `cor:sector-6`: assume (N3). For the ring in reference or ring units, every `G ∈ ℝ` and
`ℓ ∈ {6, -6}`, every eigenvalue `λ` of `L_ℓ(G)` on `Y^0_ℓ` with `Re λ > 0` satisfies
`Re λ < 9/200`. -/
theorem sector_six {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (h3 : N3) (S : SectorSetting)
    (hS : S = ringRefSetting χ ∨ S = ringPhiSetting χ) (G : ℝ) (ℓ : ℤ) (hℓ : ℓ = 6 ∨ ℓ = -6)
    (g : Ysec 0 S.Nstar ℓ) (z : ℂ) (hg : g ≠ 0) (hgz : S.Lsec 0 ℓ G g = z • g)
    (hz : 0 < z.re) : z.re < 9 / 200 := by
  have hℓ0 : ℓ ≠ 0 := by rcases hℓ with rfl | rfl <;> norm_num
  have hnat : ℓ.natAbs = 6 := by rcases hℓ with rfl | rfl <;> rfl
  -- the setting is valid, satisfies `EdgeSplit`, and has `Z_6` equal to that of `ω̄_c`
  have hdata : S.Valid ∧ S.EdgeSplit ∧ S.Zedge 6 = (ringRefSetting χ).Zedge 6 := by
    rcases hS with rfl | rfl
    · exact ⟨ringRefSetting_valid hχ, ringRefSetting_edgeSplit hχ, rfl⟩
    · exact ⟨ringPhiSetting_valid hχ, ringPhiSetting_edgeSplit hχ, Zedge_ringPhi hχ 6⟩
  obtain ⟨hV, hsplit, hZ⟩ := hdata
  have hedge := SectorSetting.edge_bound S hV hsplit hℓ0 G z hz g hg hgz
  rw [hnat, hZ] at hedge
  exact lt_of_le_of_lt hedge (half_sqrt_Zedge6_lt hχ h3)

end NonUniqueEuler
