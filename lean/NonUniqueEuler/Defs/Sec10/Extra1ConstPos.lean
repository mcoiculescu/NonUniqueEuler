import NonUniqueEuler.Defs.Sec10.Lists

/-!
# Section 10: the positivity of the constants of (P0)–(P4) (definition)

Manuscript: `lem:nonempty`
(`10_parameters.tex:278-290`), the clause "with all quantities finite and positive" (`:281`), proved
at `:295-315`.

* `Relay.Standing.ConstPos S`: the signs of the constants of the structural list (P0)–(P4) that the
  later proofs use (a structure of Props with named fields, so that consumers write
  `hpos.K1_pos`, `hpos.CF_pos`, …). The claim that these hold is the interface
  `Relay.constants_pos` (`I/Sec10/ConstantsPos.lean`).

Every field reads only the parameters `χ, s, σ', δ₀, μ, T_pin` of `S` (not `A₁`, `n`, `ω^{(n)}`,
`κ_seed`, `s̄`). `C₀ ≥ 1` and `C_F ≤ C₀` are not fields: they are proved for every `S`
(`Standing.one_le_C0`, `Standing.CF_le_C0`, `Defs/Sec10/Lists.lean`).

Here `C_Q` (`S.CQ`) and `C_hand = K₁C_Q` (`S.Chand`) are only nonnegative: the constant of
`thm:quiet` is specified with `0 ≤ C_Q` (`OneRing.IsQuietConst`, junk `0`), and positivity of the
chosen constant is not derivable from its specification.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

open RingData Datum

namespace Standing

variable (S : Standing)

/-- **The constants of (P0)–(P4) are positive** (`lem:nonempty`, `10_parameters.tex:281`,
`:295-315`): the eigendata `σ = σ(0)`, `σ_b`, `|z|`; `c_γ` of (P0.2); `C₂ ≥ 1`, `C₃`, `κ_L` of
(P0.3), `c_N`, `C_N`, `c_out`, `‖ℓ_*‖`, `C_ls` of `lem:uniform`; `maj_*` (and `C_Q ≥ 0`) of (P0.4);
`C_M`, `C_O`, `C_in` of (P0.5); `δ_kick`, `δ_rd` of (P1); `c'` and `μ_max > 1` of (P2), `C_Duh`,
`K_O`; `c_K`, `K₁`, `Ā`, `K_lo`, `K_up`, `C_hand ≥ 0`, `C_F`, `C_deep`, `T_z` of (P3); `κ₀(C₀)` of
(P4). -/
structure ConstPos : Prop where
  sigma0_pos : 0 < S.sigma0
  sigb_pos : 0 < S.sigb
  z_norm_pos : 0 < ‖S.z‖
  cgamma_pos : 0 < S.cgamma
  one_le_C2 : 1 ≤ S.C2
  C3_pos : 0 < S.C3
  kL_pos : 0 < OneRing.kL S.P.χ
  cN_pos : 0 < Eig.cN S.P.χ
  CN_pos : 0 < Eig.CN S.P.χ
  cout_pos : 0 < Eig.cout S.P.χ
  ellNorm_pos : 0 < Eig.ellNorm S.P.χ
  Cls_pos : 0 < Eig.Cls S.P.χ
  majst_pos : 0 < S.majst
  CQ_nonneg : 0 ≤ S.CQ
  CM_pos : 0 < S.CM
  CO_pos : 0 < S.CO
  Cin_pos : 0 < S.Cin
  deltaKick_pos : 0 < S.deltaKick
  deltaRd_pos : 0 < S.deltaRd
  cPrime_pos : 0 < S.cPrime
  one_lt_muMax : 1 < S.muMax
  CDuh_pos : 0 < S.CDuh
  KO_pos : 0 < S.KO
  cK_pos : 0 < S.cK
  K1_pos : 0 < S.K1
  Abar_pos : 0 < S.Abar
  Klo_pos : 0 < S.Klo
  Kup_pos : 0 < S.Kup
  Chand_nonneg : 0 ≤ S.Chand
  CF_pos : 0 < S.CF
  Cdeep_pos : 0 < S.Cdeep
  Tz_pos : 0 < S.Tz
  kappa0_pos : 0 < S.kappa0 S.C0

variable {S}

/-- `C_F ∈ (0, C₀]`, the hypothesis on `C_F` of `lem:Oprime` (`10_parameters.tex:311-312`). -/
theorem ConstPos.CF_mem (h : S.ConstPos) : S.CF ∈ Ioc 0 S.C0 := ⟨h.CF_pos, S.CF_le_C0⟩

/-- `C_p C₂ > 0` (`C_p = 4/√π`), the positivity used with (P1) for `lem:readout`. -/
theorem ConstPos.Cp_C2_pos (h : S.ConstPos) : 0 < Eig.Cp * S.C2 := by
  have hCp : 0 < Eig.Cp := by
    unfold Eig.Cp
    have : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
    positivity
  exact mul_pos hCp (lt_of_lt_of_le one_pos h.one_le_C2)

end Standing

end Relay

end NonUniqueEuler
