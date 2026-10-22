import NonUniqueEuler.H.Sec9.Relay.Setup
import NonUniqueEuler.I.Sec9.TransferStep
import NonUniqueEuler.I.Sec5.ActiveT1
import NonUniqueEuler.I.Sec7.Transfer
import NonUniqueEuler.I.Sec7.InnerField
import NonUniqueEuler.I.Sec7.FieldUnits

/-!
# Helpers for `prop:relay`: the inner field of ring `j` on the active and debris phases of `j+1`

Helper file of `P/Sec9/Relay.lean` (`09_relay.tex:517-574`). Everything here is proved.

* `hIn_eq_extField`: on a time with `D_{j+1}(t) ⊂ B_{ar_j/8}`, `h^in_j(A_jt)` is the non-monopole
  field of `ω_{≥j+1}(t)` in ring-`j` units, as functions on `ℂ` (copied, with its proof, from
  `FieldBoundProof.hIn_eq_unitsField_extField` of `P/Sec7/FieldBound.lean`; it follows from
  `lem:inner-field`'s identity `Rings.inner_field_eq` at the point `y = 1 ∈ N'` and
  `Rings.fields_scaleVort`);
* `active_pointwise` (`09_relay.tex:519-531`): on `I₂ = [τ^act, min(τ, τ^sat)]`,
  `η^in_j(v) ≤ C_Mε_j(2C₂κe^{σ_{j+1}u} + 2C₂C(C₀)κ⟨u⟩^me^{σ'u} + C₀κ⟨u⟩^m)`, `u = μ(v - τ^act)`
  (`lem:transfer-step`(1) with `s' = s`, the bounds of (H4), `thm:active`'s last assertion);
* `debris_pointwise` (`09_relay.tex:563-574`): on `I₃ = [τ^sat, τ]`,
  `η^in_j(v) ≤ C_Mε_j(2 + 2C_*T_pin)^m` (`lem:transfer`(3) with
  `R = min(ϱ_j(t), ar_j/8)`, `D_{j+1}(t) ⊂ \bar B_R` by (Loc)(2)).

Deviation (minor): the manuscript takes `R = R_t = max{|x| : x ∈ D_{j+1}(t)}`; we take
`R = min(ϱ_j(t), ar_j/8) > 0`, which avoids the compactness of `D_{j+1}(t)` and the case
`R_t = 0`, and gives the same bound `R ≤ ϱ_j(t) ≤ (2 + 2C_*T_pin)r_{j+1}`.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

namespace RelayH

open RingData Datum

theorem one_mem_annN' : (1 : ℂ) ∈ annN' := by
  have h := Relay.a_lt_one
  show a / 4 ≤ ‖(1 : ℂ)‖ ∧ ‖(1 : ℂ)‖ ≤ 3
  rw [norm_one]
  constructor <;> linarith

/-- The inner field is the non-monopole field of `ω_{≥j+1}(t)` in ring-`j` units, as functions
on `ℂ`. Copied from `Rings.FieldBoundProof.hIn_eq_unitsField_extField` (`P/Sec7/FieldBound.lean`). -/
theorem hIn_eq_extField {P : Approx} (hP : P.Valid) (hN : NumericalHypothesis P.χ)
    {j : ℕ} (hj : 1 ≤ j) (hjn : j < P.n) {t : ℝ} (ht : 0 ≤ t) (hin : P.HInDefined j t) :
    P.hIn j (P.A j * t) = P.unitsField j (BS.extField (P.omegaGe (j + 1) t)) := by
  have hA := hP.A_pos j
  have hr := hP.r_pos j
  have hτ : P.A j * t / P.A j = t := by field_simp
  have hE : ∀ y, P.unitsField j (BS.extField (P.omegaGe (j + 1) t)) y =
      velocity (P.nuIn j t) y - BS.monopole (P.nuIn j t) y := by
    intro y
    have h3 := (Rings.fields_scaleVort hA hr (P.omegaGe (j + 1) t)).2.2 y
    rw [Approx.unitsField, ← h3]
    rfl
  have hH : ∀ y, P.hIn j (P.A j * t) y =
      velocity (P.nuIn j t) y - (P.G j : ℂ) * (Complex.I * y) / ((‖y‖ ^ 2 : ℝ) : ℂ) := by
    intro y
    simp only [Approx.hIn, hτ]
  set α : ℝ := ∫ x, P.nuIn j t x with hα
  have hdiff : ∀ y, P.hIn j (P.A j * t) y - P.unitsField j (BS.extField (P.omegaGe (j + 1) t)) y =
      ((α / (2 * Real.pi) - P.G j : ℝ) : ℂ) * (Complex.I * y / ((‖y‖ ^ 2 : ℝ) : ℂ)) := by
    intro y
    rw [hH, hE, BS.monopole, biotSavartKernel]
    by_cases hy : y = 0
    · simp [hy]
    · have hy' : ((‖y‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
        have : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
        exact_mod_cast pow_ne_zero 2 this
      have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
      push_cast at hy' ⊢
      field_simp
      ring
  have h1 := Rings.inner_field_eq P hP hN hj hjn ht hin 1 one_mem_annN'
  have hc : α / (2 * Real.pi) - P.G j = 0 := by
    have h0 := hdiff 1
    rw [← h1, sub_self] at h0
    simp only [norm_one, one_pow, Complex.ofReal_one, div_one, mul_one] at h0
    have h0' := h0.symm
    rcases mul_eq_zero.1 h0' with h | h
    · exact_mod_cast h
    · exact absurd h Complex.I_ne_zero
  funext y
  have := hdiff y
  rw [hc, Complex.ofReal_zero, zero_mul, sub_eq_zero] at this
  exact this

variable {S : Standing} {C₀ K₁ : ℝ} {j : ℕ} {τ : ℝ}

theorem T_succ_nonneg (h : S.RelayHyp C₀ K₁ j τ) (hS : S.Holds) : 0 ≤ S.P.T (j + 1) := by
  rw [T_succ h]
  have := tsh_succ_nonneg h hS
  have := div_nonneg (That_nonneg h hS) (hS.valid.A_pos (j + 1)).le
  linarith

/-- **The debris phase of ring `j+1`** (`09_relay.tex:563-574`): for `v ∈ [τ^sat, τ]`,
`η^in_j(v) ≤ C_Mε_j(2 + 2C_*T_pin)^m`. -/
theorem debris_pointwise (h : S.RelayHyp C₀ K₁ j τ) (hS : S.Holds) {v : ℝ}
    (hv : v ∈ Icc (S.P.A j * S.P.T (j + 1)) τ) :
    S.etaIn j v ≤ S.CM * S.P.eps j * (2 + 2 * Cstar * S.P.Tpin) ^ 3 := by
  have hA := hS.valid.A_pos j
  have hA1 := hS.valid.A_pos (j + 1)
  set t := v / S.P.A j with ht
  have hTt : S.P.T (j + 1) ≤ t := by
    rw [ht, le_div_iff₀ hA, mul_comm]
    exact hv.1
  have ht0 : 0 ≤ t := (T_succ_nonneg h hS).trans hTt
  have htτ : t ≤ τ / S.P.A j := div_le_div_of_nonneg_right hv.2 hA.le
  have htI : t ∈ Icc (0 : ℝ) (τ / S.P.A j) := ⟨ht0, htτ⟩
  have hloc := loc_j h hS htI
  have hconf := hloc.2.2 h.clock hTt
  have hin := hloc.2.1
  -- the kick time `τ_K = A_{j+1}(t - T_{j+1}) ∈ [0, T_pin]`
  have hK0 : 0 ≤ S.P.kickTime j t := mul_nonneg hA1.le (by linarith)
  have hKle : S.P.kickTime j t ≤ S.P.Tpin := by
    unfold Approx.kickTime
    have h1 : t ≤ S.P.tsh j := htτ.trans (div_le_tsh h hS)
    rw [tsh_j h] at h1
    have h2 := mul_le_mul_of_nonneg_left
      (by linarith : t - S.P.T (j + 1) ≤ S.P.Tpin / S.P.A (j + 1)) hA1.le
    rwa [mul_div_cancel₀ _ hA1.ne'] at h2
  have hr1 := hS.valid.r_pos (j + 1)
  have hrj := hS.valid.r_pos j
  have hCs := Cstar_nonneg
  have ha := Relay.zero_lt_a
  set ρ := S.P.confRadius j t with hρ
  have hρpos : 0 < ρ := by
    rw [hρ, Approx.confRadius]
    have : 0 ≤ 2 * Cstar * S.P.kickTime j t := by positivity
    exact mul_pos (by linarith) hr1
  set R := min ρ (a * S.P.r j / 8) with hR
  have hRpos : 0 < R := lt_min hρpos (by positivity)
  have hDR : S.P.D (j + 1) t ⊆ closedBall 0 R := by
    intro x hx
    have h1 := hconf hx
    have h2 := hin hx
    rw [mem_closedBall_zero_iff] at h1 ⊢
    rw [mem_ball_zero_iff] at h2
    exact le_min h1 h2.le
  obtain ⟨CTM, CTO, hT⟩ := Rings.transfer S.P.χ hS.admissible hS.hN S.Mh (one_le_Mh S)
  have hTc := Rings.transferConsts_spec ⟨CTM, CTO, hT⟩
  have hb := (hTc.inner_region S.P rfl hS.valid j h.one_le h.lt_n t ht0 R hRpos
    (min_le_right _ _) hDR).2
  have heq := hIn_eq_extField hS.valid hS.hN h.one_le h.lt_n ht0 hin
  have hAt : S.P.A j * t = v := mul_div_A hS j v
  show S.P.etaIn S.Mh j v ≤ _
  rw [Approx.etaIn, ← hAt, heq]
  refine hb.trans ?_
  have hRr : R / S.P.r (j + 1) ≤ 2 + 2 * Cstar * S.P.Tpin := by
    rw [div_le_iff₀ hr1]
    calc R ≤ ρ := min_le_left _ _
      _ = (2 + 2 * Cstar * S.P.kickTime j t) * S.P.r (j + 1) := rfl
      _ ≤ (2 + 2 * Cstar * S.P.Tpin) * S.P.r (j + 1) := by gcongr
  have hRr0 : 0 ≤ R / S.P.r (j + 1) := div_nonneg hRpos.le hr1.le
  have hCM : Rings.CTM S.P.χ S.Mh * max 1 Rings.CL1 = S.CM := rfl
  rw [hCM]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hRr0 hRr 3)
    (mul_nonneg (CM_pos S).le (hS.valid.eps_pos j).le)

/-- **The active phase of ring `j+1`** (`09_relay.tex:519-531`): for
`v ∈ [τ^act, min(τ, τ^sat)]` and `u = μ(v - τ^act)`,
`η^in_j(v) ≤ C_Mε_j(2C₂κe^{σ_{j+1}u} + 2C₂C(C₀)κ⟨u⟩^me^{σ'u} + C₀κ⟨u⟩^m)`. -/
theorem active_pointwise (h : S.RelayHyp C₀ K₁ j τ) (hS : S.Holds) (hC₀ : 1 ≤ C₀)
    (hact : S.P.A j * S.P.tsh (j + 1) < τ) {v : ℝ}
    (hv : v ∈ Icc (S.P.A j * S.P.tsh (j + 1)) (min τ (S.P.A j * S.P.T (j + 1)))) :
    S.etaIn j v ≤ S.CM * S.P.eps j *
      (2 * S.C2 * (S.P.ksh (j + 1) *
          Real.exp (S.P.sigma (j + 1) * (S.P.μ * (v - S.P.A j * S.P.tsh (j + 1))))) +
        2 * S.C2 * (S.Cact C₀ * S.P.ksh (j + 1) *
          Prelim.jap (S.P.μ * (v - S.P.A j * S.P.tsh (j + 1))) ^ 3 *
          Real.exp (S.σ' * (S.P.μ * (v - S.P.A j * S.P.tsh (j + 1))))) +
        C₀ * S.P.ksh (j + 1) * Prelim.jap (S.P.μ * (v - S.P.A j * S.P.tsh (j + 1))) ^ 3) := by
  have hA := hS.valid.A_pos j
  have hA1 := hS.valid.A_pos (j + 1)
  set t := v / S.P.A j with ht
  have hts : S.P.tsh (j + 1) ≤ t := by
    rw [ht, le_div_iff₀ hA, mul_comm]
    exact hv.1
  have ht0 : 0 ≤ t := (tsh_succ_nonneg h hS).trans hts
  have htτ : t ≤ τ / S.P.A j :=
    div_le_div_of_nonneg_right (hv.2.trans (min_le_left _ _)) hA.le
  have htT : t ≤ S.P.T (j + 1) := by
    rw [ht, div_le_iff₀ hA, mul_comm]
    exact hv.2.trans (min_le_right _ _)
  have htI : t ∈ Icc (0 : ℝ) (τ / S.P.A j) := ⟨ht0, htτ⟩
  have hact' : S.P.tsh (j + 1) < τ / S.P.A j := by
    rw [lt_div_iff₀ hA, mul_comm]
    exact hact
  obtain ⟨hIn1, hw, hetaIn1⟩ := (h.h4 hact').2 t ⟨hts, le_min htτ htT⟩
  -- the active time
  set u := S.P.μ * (v - S.P.A j * S.P.tsh (j + 1)) with hu
  have hut : S.P.activeTime (j + 1) t = u := by
    rw [Approx.activeTime, A_succ S.P h.one_le, hu, ht]
    field_simp
  have hu0 : 0 ≤ u := by
    rw [← hut, Approx.activeTime]
    exact mul_nonneg hA1.le (by linarith)
  rw [hut] at hw hetaIn1
  -- `lem:transfer-step`(1) with `s' = s`
  have hts1 := (transfer_step_one S hS h.one_le h.lt_n ht0 (pertDefined_succ h htI htT)
    (hDefined_j h hS htI) ⟨hIn1, hOutDefined_succ h hS htI⟩ S.s).2
  have hAt : S.P.A j * t = v := mul_div_A hS j v
  rw [hAt] at hts1
  -- the last assertion of `thm:active`
  have hκ := (ksh_mem h).1
  have hat := (OneRing.active_tOne S.P.χ hS.admissible hS.hN hS.σ'_mem hC₀
    (G_mem S hS (succ_mem h)) hκ).2 u hu0
  have hat' : S.ahatK (j + 1) u * S.rhoHatK C₀ (j + 1) u ≤
      S.Cact C₀ * S.P.ksh (j + 1) * Prelim.jap u ^ 3 * Real.exp (S.σ' * u) := hat
  have hahat : S.ahatK (j + 1) u = S.P.ksh (j + 1) * Real.exp (S.P.sigma (j + 1) * u) :=
    S.ahatK_def _ _
  have hC2 := one_le_C2 S
  have hCMe : 0 ≤ S.CM * S.P.eps j := mul_nonneg (CM_pos S).le (hS.valid.eps_pos j).le
  have hw' : Sob.normH S.s (S.P.w (j + 1) t) ≤
      2 * S.C2 * (S.P.ksh (j + 1) * Real.exp (S.P.sigma (j + 1) * u)) +
        2 * S.C2 * (S.Cact C₀ * S.P.ksh (j + 1) * Prelim.jap u ^ 3 * Real.exp (S.σ' * u)) := by
    calc Sob.normH S.s (S.P.w (j + 1) t)
        ≤ 2 * S.C2 * S.ahatK (j + 1) u * (1 + S.rhoHatK C₀ (j + 1) u) := hw
      _ = 2 * S.C2 * S.ahatK (j + 1) u +
            2 * S.C2 * (S.ahatK (j + 1) u * S.rhoHatK C₀ (j + 1) u) := by ring
      _ ≤ _ := by
          rw [hahat]
          have : 0 ≤ 2 * S.C2 := by linarith
          have := mul_le_mul_of_nonneg_left hat' this
          rw [← hahat]
          linarith
  calc S.etaIn j v
      ≤ S.CM * S.P.eps j * (Sob.normH S.s (S.P.w (j + 1) t) +
          S.etaIn (j + 1) (S.P.A (j + 1) * t)) := hts1
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hCMe

end RelayH

end Relay

end NonUniqueEuler
