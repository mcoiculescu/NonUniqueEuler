import NonUniqueEuler.Defs.Sec10.Lists
import NonUniqueEuler.I.Sec10.ConstantsPos
import NonUniqueEuler.I.Infra.Ip.Ip

/-!
# Proof: the uses of (P1) and (P2) (remark after `def:P0-P4`)

Proof of `I/Sec10/P0P4Uses.lean` (`10_parameters.tex:51-53`, `:73-79`). The three statements are
the conditional forms proved in `Defs/Sec10/Lists.lean` (`CondP1.kickIneqA`,
`CondP1.Cp_C2_mul_le`, `CondP2.kickIneqB`) with the signs discharged by `constants_pos`
(`I/Sec10/ConstantsPos.lean`), `Rings.Cmom_pos` and `Ip_pos` (`I/Infra/Ip/Ip.lean`).
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

open RingData Datum

/-- **(P1) gives hypothesis (a) of `lem:kicktrue`** (`10_parameters.tex:51-52`, `:73-74`):
`(16/15)(2πC₃δ₀²/σ) ≤ (1/4)(15/16) c_out δ₀/(20|z|)`. -/
theorem p1_kickIneqA (S : Standing) (hχ : IsAdmissibleCutoff S.P.χ)
    (hN : NumericalHypothesis S.P.χ) (hL : S.StructuralList) : S.kickIneqA := by
  have hpos : S.ConstPos := constants_pos S hχ hN hL.p0.σ'_gt hL.p0.σ'_lt_sigma
    hL.p1.δ₀_pos hL.p2.one_lt_μ hL.p3.Tpin_pos
  exact hL.p1.kickIneqA hpos.sigma0_pos hpos.z_norm_pos hpos.C3_pos

/-- **(P1) gives the first smallness hypothesis of `lem:readout`** (`10_parameters.tex:52-53`,
`:74-75`): `C_p C₂ δ₀ ≤ c_out/(16π)`. -/
theorem p1_readout (S : Standing) (hχ : IsAdmissibleCutoff S.P.χ)
    (hN : NumericalHypothesis S.P.χ) (hL : S.StructuralList) :
    Eig.Cp * S.C2 * S.P.δ₀ ≤ Eig.cout S.P.χ / (16 * Real.pi) := by
  have hpos : S.ConstPos := constants_pos S hχ hN hL.p0.σ'_gt hL.p0.σ'_lt_sigma
    hL.p1.δ₀_pos hL.p2.one_lt_μ hL.p3.Tpin_pos
  exact hL.p1.Cp_C2_mul_le hpos.Cp_C2_pos

/-- **(P2) gives the last inequality of hypothesis (ii) of `lem:drift`** (`10_parameters.tex:75-77`):
if `|q'| ≥ (15/16) c_out δ₀`, then `μ - 1 ≤ |q'|/(10|z| C_mom I_m(σ/4))`. -/
theorem p2_drift (S : Standing) (hχ : IsAdmissibleCutoff S.P.χ)
    (hN : NumericalHypothesis S.P.χ) (hL : S.StructuralList) {q' : ℂ}
    (hq : 15 / 16 * Eig.cout S.P.χ * S.P.δ₀ ≤ ‖q'‖) :
    S.P.μ - 1 ≤ ‖q'‖ / (10 * ‖S.z‖ * Rings.Cmom * Ip 3 (S.sigma0 / 4)) := by
  have hpos : S.ConstPos := constants_pos S hχ hN hL.p0.σ'_gt hL.p0.σ'_lt_sigma
    hL.p1.δ₀_pos hL.p2.one_lt_μ hL.p3.Tpin_pos
  have hIp : 0 < Ip 3 (S.sigma0 / 4) := Ip_pos 3 (by linarith [hpos.sigma0_pos])
  have hden : 0 ≤ 10 * ‖S.z‖ * Rings.Cmom * Ip 3 (S.sigma0 / 4) := by
    have := hpos.z_norm_pos
    have := Rings.Cmom_pos
    positivity
  have hB : S.kickIneqB := hL.p2.kickIneqB
  unfold Standing.kickIneqB at hB
  exact hB.trans (div_le_div_of_nonneg_right hq hden)

end Relay

end NonUniqueEuler
