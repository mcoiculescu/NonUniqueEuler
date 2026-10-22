import NonUniqueEuler.Defs.Sec10.Extra1ConstPos
import NonUniqueEuler.I.Infra.Ip.Ip
import NonUniqueEuler.H.Sec10.ConstantsPos.Eigen

/-!
# Proof: the constants of (P0)–(P4) are positive (part of `lem:nonempty`)

Proof of `I/Sec10/ConstantsPos.lean` (`lem:nonempty`, `10_parameters.tex:281`, `:295-315`).

* The eigendata signs (`σ_b, σ, |z|, c_N, C_N, c_out, ‖ℓ_*‖, C_ls`) are in the helper
  `H/Sec10/ConstantsPos/Eigen.lean` (from `prop:U`, `lem:uniform`, `def:eigendata`,
  `lem:ring-facts`).
* The chosen constants of Sections 5 and 7 have the signs of their specifications in both branches
  of the choice (`activeConsts_signs`, `kL_pos`, `quietConsts_signs`, `transferConsts_pos`,
  `Cin_pos`).
* `C_* > 0` (`Cstar_pos`: `c₄ = (2π/(2 - 4/3))^{3/4} > 0`, `M_vort > 0`), `C_D(T_pin) > 0`.
* The explicit formulas of (P1)–(P4) are then positive.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

namespace ConstantsPosAux

open RingData Datum

/-! ### The chosen constants of Sections 5 and 7 (both branches of the choice) -/

/-- `C₂ ≥ 1`, `C₃ > 0` and `κ₀(C₀) > 0` for `C₀ ≥ 1` (`thm:active`; junk `(1/2, 1, 1, 1)`). -/
theorem activeConsts_signs (χ : ℝ → ℝ) (s : ℕ) (σ' : ℝ) :
    1 ≤ OneRing.C2 χ s σ' ∧ 0 < OneRing.C3 χ s σ' ∧
      ∀ C₀ : ℝ, 1 ≤ C₀ → 0 < OneRing.kappa0 χ s σ' C₀ := by
  unfold OneRing.C2 OneRing.C3 OneRing.kappa0 OneRing.activeConsts
  split_ifs with h
  · obtain ⟨-, h2, h3, hk, -⟩ := h.choose_spec
    exact ⟨h2, h3, hk⟩
  · exact ⟨le_rfl, one_pos, fun _ _ => one_pos⟩

/-- `κ_L > 0` (`lem:seed`; junk `1`). -/
theorem kL_pos (χ : ℝ → ℝ) : 0 < OneRing.kL χ := by
  unfold OneRing.kL OneRing.seedData
  split_ifs with h
  · exact h.choose_spec.kL_pos
  · exact one_pos

/-- `maj_* ∈ (0,1]` and `C_Q ≥ 0` (`thm:quiet`; junk `(1, 0, 0)`). -/
theorem quietConsts_signs (χ : ℝ → ℝ) (sh NQ : ℕ) :
    0 < OneRing.majst χ sh NQ ∧ 0 ≤ OneRing.CQ χ sh NQ := by
  unfold OneRing.majst OneRing.CQ OneRing.quietConsts
  split_ifs with h
  · obtain ⟨hm, hq, -⟩ := h.choose_spec
    exact ⟨hm.1, hq⟩
  · exact ⟨one_pos, le_rfl⟩

/-- `C^T_M > 0` and `C^T_O > 0` (`lem:transfer`; junk `(1, 1)`). -/
theorem transferConsts_pos (χ : ℝ → ℝ) (Mh : ℕ) :
    0 < Rings.CTM χ Mh ∧ 0 < Rings.CTO χ Mh := by
  unfold Rings.CTM Rings.CTO Rings.transferConsts
  split_ifs with h
  · exact ⟨h.choose_spec.CTM_pos, h.choose_spec.CTO_pos⟩
  · exact ⟨one_pos, one_pos⟩

/-- `C_in > 0` (`lem:inner-field`; junk `1`). -/
theorem Cin_pos (χ : ℝ → ℝ) (Mh : ℕ) : 0 < Rings.Cin χ Mh := by
  unfold Rings.Cin
  split_ifs with h
  · exact h.choose_spec.pos
  · exact one_pos

/-- `C_M = C^T_M max(1, C_{L1}) > 0`. -/
theorem CM_pos (χ : ℝ → ℝ) (Mh : ℕ) : 0 < Rings.CM χ Mh :=
  mul_pos (transferConsts_pos χ Mh).1 (lt_of_lt_of_le one_pos (le_max_left _ _))

/-- `C_O = C^T_O max(1, C_{L1}) > 0`. -/
theorem CO_pos (χ : ℝ → ℝ) (Mh : ℕ) : 0 < Rings.CO χ Mh :=
  mul_pos (transferConsts_pos χ Mh).2 (lt_of_lt_of_le one_pos (le_max_left _ _))

/-! ### Explicit constants -/

/-- `c₄ = (2π/(2 - 4/3))^{3/4} > 0` (`lem:LpLinf` with `p = 4`). -/
theorem cLpLinf_four_pos : 0 < BS.cLpLinf 4 := by
  unfold BS.cLpLinf
  have hce : Real.conjExponent 4 = 4 / 3 := by
    unfold Real.conjExponent
    norm_num
  rw [hce]
  have hbase : 0 < 2 * Real.pi / (2 - 4 / 3) := by
    have := Real.pi_pos
    have h : (0 : ℝ) < 2 - 4 / 3 := by norm_num
    positivity
  exact Real.rpow_pos_of_pos hbase _

/-- `C_* = (1 + c₄)/(2π) · M_vort^{1/2} > 0` (`lem:speed`). -/
theorem Cstar_pos : 0 < Cstar := by
  unfold Cstar
  have h1 : 0 < 1 + BS.cLpLinf 4 := by linarith [cLpLinf_four_pos]
  have h2 : 0 < Real.sqrt Mvort := Real.sqrt_pos.2 Mvort_pos
  have h3 := Real.pi_pos
  positivity

/-- `C_D(T) = (2 + 2C_*T)^3 T > 0` for `T > 0`. -/
theorem CD_pos {T : ℝ} (hT : 0 < T) : 0 < CD T := by
  unfold CD
  have h := Cstar_pos
  positivity

/-- `C_p = 4/√π > 0`. -/
theorem Cp_pos : 0 < Eig.Cp := by
  unfold Eig.Cp
  have : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  positivity

end ConstantsPosAux

open RingData Datum ConstantsPosAux

/-- **The constants of (P0)–(P4) are finite and positive** (`lem:nonempty`,
`10_parameters.tex:281`, `:295-315`): for an admissible cutoff with (N1)–(N3) and parameters with
`σ' ∈ (9/200, 3σ/4)`, `δ₀ > 0`, `μ > 1` and `T_pin > 0`, all the signs of `Standing.ConstPos`
hold. -/
theorem constants_pos (S : Standing) (hχ : IsAdmissibleCutoff S.P.χ)
    (hN : NumericalHypothesis S.P.χ) (hσ' : 9 / 200 < S.σ')
    (hσ'σ : S.σ' < 3 / 4 * Eig.sigma S.P.χ 0) (hδ₀ : 0 < S.P.δ₀) (hμ : 1 < S.P.μ)
    (hT : 0 < S.P.Tpin) : S.ConstPos := by
  -- eigendata
  have hσ : 0 < S.sigma0 := sigma_zero_pos hχ hN
  have hσb : 0 < S.sigb := sigb_pos hχ hN
  have hz : 0 < ‖S.z‖ := z_norm_pos hχ hN
  have hcN : 0 < Eig.cN S.P.χ := cN_pos hχ hN
  have hCN : 0 < Eig.CN S.P.χ := CN_pos hχ hN
  have hcout : 0 < Eig.cout S.P.χ := cout_pos hχ hN
  have hell : 0 < Eig.ellNorm S.P.χ := ellNorm_pos hχ hN
  have hCls : 0 < Eig.Cls S.P.χ := Cls_pos hχ hN
  -- chosen constants
  obtain ⟨hC2, hC3, hk0⟩ := activeConsts_signs S.P.χ S.s S.σ'
  have hC2' : 1 ≤ S.C2 := hC2
  have hC3' : 0 < S.C3 := hC3
  have hkL : 0 < OneRing.kL S.P.χ := kL_pos S.P.χ
  obtain ⟨hmaj, hCQ⟩ := quietConsts_signs S.P.χ S.sh S.NQ
  have hmaj' : 0 < S.majst := hmaj
  have hCQ' : 0 ≤ S.CQ := hCQ
  have hCM : 0 < S.CM := CM_pos S.P.χ S.Mh
  have hCO : 0 < S.CO := CO_pos S.P.χ S.Mh
  have hCin : 0 < S.Cin := Cin_pos S.P.χ S.Mh
  -- explicit constants
  have hμ0 : 0 < S.P.μ := by linarith
  have hμ1 : 0 < S.P.μ - 1 := by linarith
  have hσ'0 : 0 < S.σ' := by linarith
  have hpi := Real.pi_pos
  have hCp := Cp_pos
  have hCstar := Cstar_pos
  have hCmom := Rings.Cmom_pos
  have hCD : 0 < CD S.P.Tpin := CD_pos hT
  have hIp : 0 < Ip 3 (S.sigma0 / 4) := Ip_pos 3 (by positivity)
  have hcgamma : 0 < S.cgamma := by
    unfold Standing.cgamma
    have h1 : 16 * S.σ' < 15 * S.sigma0 := by
      have : S.sigma0 = Eig.sigma S.P.χ 0 := rfl
      linarith
    have h2 : 16 * S.σ' / (15 * S.sigma0) < 1 := (div_lt_one (by positivity)).2 h1
    linarith
  have hkick : 0 < S.deltaKick := by
    unfold Standing.deltaKick
    positivity
  have hrd : 0 < S.deltaRd := by
    unfold Standing.deltaRd
    positivity
  have hcP : 0 < S.cPrime := by
    unfold Standing.cPrime
    positivity
  have hmuMax : 1 < S.muMax := by
    unfold Standing.muMax
    have : 0 < min (S.cPrime * S.P.δ₀) (1 / 16) := lt_min (mul_pos hcP hδ₀) (by norm_num)
    linarith
  have hCDuh : 0 < S.CDuh := by
    unfold Standing.CDuh
    positivity
  have hKO : 0 < S.KO := by
    unfold Standing.KO
    positivity
  have hcK : 0 < S.cK := by
    unfold Standing.cK
    positivity
  have hK1 : 0 < S.K1 := by
    unfold Standing.K1
    have h4 : 0 < 4 * S.C2 + 1 := by linarith
    positivity
  have hAbar : 0 < S.Abar := by
    unfold Standing.Abar
    have h4 : 0 < 4 * S.C2 + 1 := by linarith
    positivity
  have hKlo : 0 < S.Klo := by
    unfold Standing.Klo
    positivity
  have hKup : 0 < S.Kup := by
    unfold Standing.Kup
    positivity
  have hChand : 0 ≤ S.Chand := by
    unfold Standing.Chand
    positivity
  have hCF : 0 < S.CF := by
    unfold Standing.CF
    positivity
  have hCdeep : 0 < S.Cdeep := by
    unfold Standing.Cdeep
    positivity
  have hTz : 0 < S.Tz := by
    unfold Standing.Tz
    have : 0 ≤ S.σ'⁻¹ * Real.posLog (S.P.δ₀ / S.Klo) :=
      mul_nonneg (inv_nonneg.2 hσ'0.le) Real.posLog_nonneg
    linarith
  have hkappa0 : 0 < S.kappa0 S.C0 := hk0 S.C0 S.one_le_C0
  exact
    { sigma0_pos := hσ
      sigb_pos := hσb
      z_norm_pos := hz
      cgamma_pos := hcgamma
      one_le_C2 := hC2'
      C3_pos := hC3'
      kL_pos := hkL
      cN_pos := hcN
      CN_pos := hCN
      cout_pos := hcout
      ellNorm_pos := hell
      Cls_pos := hCls
      majst_pos := hmaj'
      CQ_nonneg := hCQ'
      CM_pos := hCM
      CO_pos := hCO
      Cin_pos := hCin
      deltaKick_pos := hkick
      deltaRd_pos := hrd
      cPrime_pos := hcP
      one_lt_muMax := hmuMax
      CDuh_pos := hCDuh
      KO_pos := hKO
      cK_pos := hcK
      K1_pos := hK1
      Abar_pos := hAbar
      Klo_pos := hKlo
      Kup_pos := hKup
      Chand_nonneg := hChand
      CF_pos := hCF
      Cdeep_pos := hCdeep
      Tz_pos := hTz
      kappa0_pos := hkappa0 }

end Relay

end NonUniqueEuler
