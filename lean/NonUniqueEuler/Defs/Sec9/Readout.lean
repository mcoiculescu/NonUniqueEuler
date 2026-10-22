import NonUniqueEuler.Defs.Sec9.KickTrue
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

/-!
# Section 9.5: readout and time — `lem:readout`, `lem:time`, `lem:quiet-time` (definitions)

Manuscript `09_relay.tex:1399-1554`.

* `lem:readout` (`:1409-1423`): the readout cutoffs `χ_out ∈ C_c^∞((a/4,3))`, `0 ≤ χ_out ≤ 1`,
  `χ_out = 1` on `[a/2,2]` (`Relay.IsReadoutCutoff`), the test function
  `Ψ₁(x) = χ_out(|x|) x̄^m` (`Relay.readoutTest χ_out`), a concrete readout cutoff `Relay.chiOut`
  (a `ContDiffBump`, `isReadoutCutoff_chiOut`), and `c₀ = ½ A₁ c_out δ₀` (`S.c0`);
* `lem:time` (`:1465-1474`): `T_z` (`S.Tz`) and `T_*` (`S.Tstar`);
* `lem:quiet-time` (`:1496-1509`): `τ̄♯_j` (`S.tauBarSh j`) and `C_τ` (`S.Ctau`).

Here `m = 3`. All lemmas here are fully proved.
-/

noncomputable section

open MeasureTheory Set Metric ComplexConjugate

namespace NonUniqueEuler

namespace Relay

open RingData Datum

/-! ### `lem:readout` (`09_relay.tex:1409-1423`) -/

/-- **A readout cutoff** (`lem:readout`, `09_relay.tex:1411-1412`): `χ_out ∈ C_c^∞((a/4, 3))` with
`0 ≤ χ_out ≤ 1` and `χ_out = 1` on `[a/2, 2]` (smoothness `C^∞`, D15; compact support in the open
interval is `tsupport χ_out ⊆ (a/4, 3)`, `IsReadoutCutoff.hasCompactSupport`). -/
structure IsReadoutCutoff (χo : ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χo
  tsupport_subset : tsupport χo ⊆ Ioo (a / 4) 3
  nonneg : ∀ r, 0 ≤ χo r
  le_one : ∀ r, χo r ≤ 1
  eq_one : ∀ r ∈ Icc (a / 2) 2, χo r = 1

/-- The readout test function `Ψ₁(x) = χ_out(|x|) x̄^m`, `m = 3` (`lem:readout`,
`09_relay.tex:1413`); the readout is `∫ ω^{(n)}(T₁) Ψ₁` (`‖∫ x, (ω x : ℂ) * readoutTest χo x‖`). -/
def readoutTest (χo : ℝ → ℝ) (x : ℂ) : ℂ := ((χo ‖x‖ : ℝ) : ℂ) * conj x ^ 3

theorem zero_lt_a : 0 < a := Real.exp_pos _

theorem a_lt_one : a < 1 := by
  unfold a
  rw [Real.exp_lt_one_iff]
  norm_num [ξL, ξR]

/-- The bump behind `chiOut`: centre `1 + a/4`, equal to `1` on `[a/2, 2]` (radius `1 - a/4`),
support `[3a/8, 2 + a/8]` (radius `1 - a/8`). -/
def chiOutBump : ContDiffBump (1 + a / 4 : ℝ) where
  rIn := 1 - a / 4
  rOut := 1 - a / 8
  rIn_pos := by linarith [a_lt_one]
  rIn_lt_rOut := by linarith [zero_lt_a]

/-- A concrete readout cutoff (`IsReadoutCutoff chiOut`, `isReadoutCutoff_chiOut`); the manuscript
fixes some `χ_out` (`09_relay.tex:1411`), and every statement holds for every readout cutoff. -/
def chiOut : ℝ → ℝ := ⇑chiOutBump

theorem IsReadoutCutoff.hasCompactSupport {χo : ℝ → ℝ} (h : IsReadoutCutoff χo) :
    HasCompactSupport χo :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport χo)
    ((Metric.isBounded_Ioo (a / 4) 3).subset h.tsupport_subset)

theorem isReadoutCutoff_chiOut : IsReadoutCutoff chiOut where
  contDiff := chiOutBump.contDiff
  tsupport_subset := by
    have ha := zero_lt_a
    have ha1 := a_lt_one
    intro r hr
    have hr' : r ∈ closedBall (1 + a / 4 : ℝ) (1 - a / 8) := by
      have h := chiOutBump.tsupport_eq
      simp only [chiOut] at hr
      rw [h] at hr
      exact hr
    rw [Real.closedBall_eq_Icc] at hr'
    exact ⟨by linarith [hr'.1], by linarith [hr'.2]⟩
  nonneg r := chiOutBump.nonneg
  le_one r := chiOutBump.le_one
  eq_one r hr := by
    apply chiOutBump.one_of_mem_closedBall
    show r ∈ closedBall (1 + a / 4 : ℝ) (1 - a / 4)
    rw [Real.closedBall_eq_Icc]
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩

namespace Standing

variable (S : Standing)

/-- `c₀ = ½ A₁ c_out δ₀` (`lem:readout`, `09_relay.tex:1421`). -/
def c0 : ℝ := 1 / 2 * S.P.A₁ * Eig.cout S.P.χ * S.P.δ₀

/-! ### `lem:time` (`09_relay.tex:1465-1474`) -/

/-- `T_z = T_pin + 1 + σ'⁻¹ log₊(δ₀/K_lo)` (`lem:time`, `09_relay.tex:1467`). -/
def Tz : ℝ := S.P.Tpin + 1 + S.σ'⁻¹ * Real.posLog (S.P.δ₀ / S.Klo)

/-- `T_* = A₁⁻¹[μ/(μ-1)(T_z + ((m+2)/σ') log(1/s̄)) + ((m+2) log(2μ)/σ') μ²/(μ-1)² + 1
 + σ'⁻¹ log(2δ₀/κ_seed)]` (`lem:time`, `09_relay.tex:1468-1471`); it does not involve `n`. -/
def Tstar : ℝ :=
  S.P.A₁⁻¹ * (S.P.μ / (S.P.μ - 1) * (S.Tz + (3 + 2) / S.σ' * Real.log (1 / S.P.sbar)) +
    (3 + 2) * Real.log (2 * S.P.μ) / S.σ' * (S.P.μ ^ 2 / (S.P.μ - 1) ^ 2) + 1 +
    1 / S.σ' * Real.log (2 * S.P.δ₀ / S.P.κs))

/-! ### `lem:quiet-time` (`09_relay.tex:1496-1509`) -/

/-- `τ̄♯_j = (3T_z + (2m+5)σ'⁻¹ log(1/s_j))/(μ-1) + (m+2)μ log(2μ)/(σ'(μ-1)²)`
(`lem:quiet-time`, `09_relay.tex:1500-1501`). -/
def tauBarSh (j : ℕ) : ℝ :=
  (3 * S.Tz + (2 * 3 + 5) * S.σ'⁻¹ * Real.log (1 / S.P.s j)) / (S.P.μ - 1) +
    (3 + 2) * S.P.μ * Real.log (2 * S.P.μ) / (S.σ' * (S.P.μ - 1) ^ 2)

/-- `C_τ = max{3, (2m+5)/σ', 3(m+2)/σ'}` (`lem:quiet-time`, `09_relay.tex:1508`). -/
def Ctau : ℝ := max 3 (max ((2 * 3 + 5) / S.σ') (3 * (3 + 2) / S.σ'))

/-! ### Basic lemmas (fully proved) -/

theorem c0_def : S.c0 = 1 / 2 * S.P.A₁ * Eig.cout S.P.χ * S.P.δ₀ := rfl

theorem Tz_def : S.Tz = S.P.Tpin + 1 + S.σ'⁻¹ * Real.posLog (S.P.δ₀ / S.Klo) := rfl

theorem tauBarSh_def (j : ℕ) : S.tauBarSh j =
    (3 * S.Tz + (2 * 3 + 5) * S.σ'⁻¹ * Real.log (1 / S.P.s j)) / (S.P.μ - 1) +
      (3 + 2) * S.P.μ * Real.log (2 * S.P.μ) / (S.σ' * (S.P.μ - 1) ^ 2) := rfl

theorem three_le_Ctau : 3 ≤ S.Ctau := le_max_left _ _

end Standing

end Relay

end NonUniqueEuler
