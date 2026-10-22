import NonUniqueEuler.H.Sec9.O.Algebra
import NonUniqueEuler.I.Sec9.TransferStep

/-!
# Helpers for `P/Sec9/O`: the transfer chain and the pointwise bound on `η_i`

The bounds of `lem:O` at a fixed real time `s` (`09_relay.tex:323-350`):
* `OProof.inner_chain`: `lem:transfer-step`(1) applied at the levels `i, i+1, …, j-1` (with
  `s' = s_h`) gives, by induction,
  `η^in_i(A_is) ≤ Σ_{l=i+1}^{j} Π_{i,l}‖w_l(s)‖_{H^{s_h}} + Π_{i,j} η^in_j(A_js)`,
  `Π_{i,l} = ∏_{p=i}^{l-1} C_Mε_p`;
* `OProof.eta_pointwise`: with `lem:transfer-step`(2), `eq:O-Q` and `eq:O-BH` at time `s`
  (`‖w_l(s)‖ ≤ C_Q P̃_{l,j} m` for `i < l ≤ j` and `l < i`),
  `η_i(A_is) ≤ P̃_{i,j}(a₁m + a₂η^in_j(A_js))`, `a₁ = (8/7)(C_M/K_O)C_Q + (4/3)C_OC_QK_Os̄^{2m}`,
  `a₂ = C_M/K_O` (the three groups of terms of `09_relay.tex:330-350`).
-/

noncomputable section

open Set

namespace NonUniqueEuler.Relay.OProof

open RingData Datum

/-- **The inner transfer chain** (`09_relay.tex:325-329`): `lem:transfer-step`(1) at the levels
`i, …, j-1` with `s' = s_h`. -/
theorem inner_chain (S : Standing) (hS : S.Holds) {j : ℕ} (hjn : j < S.P.n) {s : ℝ} (hs : 0 ≤ s)
    (hdef : ∀ p ∈ Finset.Icc 1 j, S.P.HDefined p s)
    (hpert : ∀ p ∈ Finset.Icc 1 j, S.P.PertDefined p s) {i : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) :
    S.etaIn i (S.P.A i * s) ≤
      ∑ l ∈ Finset.Ico (i + 1) (j + 1),
          (∏ p ∈ Finset.Ico i l, S.CM * S.P.eps p) * Sob.normH S.sh (S.P.w l s) +
        (∏ p ∈ Finset.Ico i j, S.CM * S.P.eps p) * S.etaIn j (S.P.A j * s) := by
  have key : ∀ d : ℕ, ∀ i : ℕ, 1 ≤ i → i + d = j →
      S.etaIn i (S.P.A i * s) ≤
        ∑ l ∈ Finset.Ico (i + 1) (j + 1),
            (∏ p ∈ Finset.Ico i l, S.CM * S.P.eps p) * Sob.normH S.sh (S.P.w l s) +
          (∏ p ∈ Finset.Ico i j, S.CM * S.P.eps p) * S.etaIn j (S.P.A j * s) := by
    intro d
    induction d with
    | zero =>
      intro i _ hij
      subst hij
      simp
    | succ d ih =>
      intro i hi hij
      have h1 := ih (i + 1) (by omega) (by omega)
      have hT := (transfer_step_one S hS hi (by omega : i < S.P.n) hs
        (hpert (i + 1) (by simp only [Finset.mem_Icc]; omega))
        (hdef i (by simp only [Finset.mem_Icc]; omega))
        (hdef (i + 1) (by simp only [Finset.mem_Icc]; omega)) S.sh).2
      have hc : 0 ≤ S.CM * S.P.eps i := (mul_pos (CM_pos S) (hS.valid.eps_pos i)).le
      have hsum : ∑ l ∈ Finset.Ico (i + 1) (j + 1),
            (∏ p ∈ Finset.Ico i l, S.CM * S.P.eps p) * Sob.normH S.sh (S.P.w l s) =
          S.CM * S.P.eps i * (Sob.normH S.sh (S.P.w (i + 1) s) +
            ∑ l ∈ Finset.Ico (i + 1 + 1) (j + 1),
              (∏ p ∈ Finset.Ico (i + 1) l, S.CM * S.P.eps p) * Sob.normH S.sh (S.P.w l s)) := by
        rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : i + 1 < j + 1), Nat.Ico_succ_singleton,
          Finset.prod_singleton, mul_add, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun l hl => ?_
        rw [Finset.mem_Ico] at hl
        rw [Finset.prod_eq_prod_Ico_succ_bot (by omega : i < l)]
        ring
      have hprod : ∏ p ∈ Finset.Ico i j, S.CM * S.P.eps p =
          S.CM * S.P.eps i * ∏ p ∈ Finset.Ico (i + 1) j, S.CM * S.P.eps p :=
        Finset.prod_eq_prod_Ico_succ_bot (by omega : i < j) _
      rw [hsum, hprod]
      calc S.etaIn i (S.P.A i * s)
          ≤ S.CM * S.P.eps i *
              (Sob.normH S.sh (S.P.w (i + 1) s) + S.etaIn (i + 1) (S.P.A (i + 1) * s)) := hT
        _ ≤ S.CM * S.P.eps i * (Sob.normH S.sh (S.P.w (i + 1) s) +
              (∑ l ∈ Finset.Ico (i + 1 + 1) (j + 1),
                  (∏ p ∈ Finset.Ico (i + 1) l, S.CM * S.P.eps p) * Sob.normH S.sh (S.P.w l s) +
                (∏ p ∈ Finset.Ico (i + 1) j, S.CM * S.P.eps p) *
                  S.etaIn j (S.P.A j * s))) := by gcongr
        _ = _ := by ring
  exact key (j - i) i hi (by omega)

/-- **The pointwise bound on `η_i`** (`09_relay.tex:323-350`), at a real time `s ≥ 0`, under the
geometric hypotheses for the rings `p ≤ j`, `S_p(s) ⊂ N_p`, `eq:O-Q` and `eq:O-BH` at `s`
(`m` is the regularized majorant `maj^ε_j(A_js)`, `maj_j(A_js) ≤ m`). -/
theorem eta_pointwise (S : Standing) (hS : S.Holds) (hsm : S.OSmall) {i j : ℕ} (hi : 1 ≤ i)
    (hij : i < j) (hjn : j < S.P.n) {s m : ℝ} (hs : 0 ≤ s) (hm0 : 0 ≤ m)
    (hdef : ∀ p ∈ Finset.Icc 1 j, S.P.HDefined p s)
    (hpert : ∀ p ∈ Finset.Icc 1 j, S.P.PertDefined p s)
    (hw : ∀ p ∈ Finset.Icc 1 j, Sob.normH S.sh (S.P.w p s) ≤ S.CQ * S.maj p (S.P.A p * s))
    (hBH : ∀ p ∈ Finset.Ico 1 j, S.maj p (S.P.A p * s) ≤ S.Ptil p j * m)
    (hmj : S.maj j (S.P.A j * s) ≤ m) :
    S.eta i (S.P.A i * s) ≤ S.Ptil i j *
      ((8 / 7 * (S.CM / S.KO) * S.CQ + 4 / 3 * (S.CO * S.CQ * S.KO * S.P.sbar ^ 6)) * m +
        S.CM / S.KO * S.etaIn j (S.P.A j * s)) := by
  have hQ := CQ_nonneg S
  obtain ⟨hX0, hX8, -⟩ := CM_div_KO_le S hS
  set X := S.CM / S.KO with hXdef
  have hPij := Ptil_nonneg S hS i j
  -- `eq:O-Q` + `eq:O-BH`: `‖w_l(s)‖ ≤ C_Q P̃_{l,j} m` for `1 ≤ l ≤ j`
  have hwl : ∀ l ∈ Finset.Icc 1 j, Sob.normH S.sh (S.P.w l s) ≤ S.CQ * (S.Ptil l j * m) := by
    intro l hl
    have hl' := Finset.mem_Icc.mp hl
    refine (hw l hl).trans (mul_le_mul_of_nonneg_left ?_ hQ)
    rcases Nat.lt_or_ge l j with hlj | hlj
    · exact hBH l (Finset.mem_Ico.mpr ⟨hl'.1, hlj⟩)
    · have : l = j := le_antisymm hl'.2 hlj
      subst this
      rw [Standing.Ptil_self, one_mul]
      exact hmj
  -- the inner field
  have hin := inner_chain S hS hjn hs hdef hpert hi hij.le
  have hin1 : ∑ l ∈ Finset.Ico (i + 1) (j + 1),
        (∏ p ∈ Finset.Ico i l, S.CM * S.P.eps p) * Sob.normH S.sh (S.P.w l s) ≤
      S.CQ * m * S.Ptil i j * (8 / 7 * X) := by
    calc ∑ l ∈ Finset.Ico (i + 1) (j + 1),
          (∏ p ∈ Finset.Ico i l, S.CM * S.P.eps p) * Sob.normH S.sh (S.P.w l s)
        ≤ ∑ l ∈ Finset.Ico (i + 1) (j + 1), S.CQ * m * S.Ptil i j * X ^ (l - i) := by
          refine Finset.sum_le_sum fun l hl => ?_
          have hl' := Finset.mem_Ico.mp hl
          rw [prod_CM_eps_eq S hS i l]
          have hXl : 0 ≤ X ^ (l - i) * S.Ptil i l := mul_nonneg (pow_nonneg hX0 _) (Ptil_nonneg S hS i l)
          calc X ^ (l - i) * S.Ptil i l * Sob.normH S.sh (S.P.w l s)
              ≤ X ^ (l - i) * S.Ptil i l * (S.CQ * (S.Ptil l j * m)) :=
                mul_le_mul_of_nonneg_left (hwl l (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)) hXl
            _ = S.CQ * m * (S.Ptil i l * S.Ptil l j) * X ^ (l - i) := by ring
            _ = S.CQ * m * S.Ptil i j * X ^ (l - i) := by
                rw [S.Ptil_mul (by omega : i ≤ l) (by omega : l ≤ j)]
      _ = S.CQ * m * S.Ptil i j * ∑ l ∈ Finset.Ico (i + 1) (j + 1), X ^ (l - i) := by
          rw [Finset.mul_sum]
      _ ≤ S.CQ * m * S.Ptil i j * (8 / 7 * X) := by
          have : 0 ≤ S.CQ * m * S.Ptil i j := by positivity
          exact mul_le_mul_of_nonneg_left (geom_inner_le hX0 hX8 i j) this
  have hin2 : (∏ p ∈ Finset.Ico i j, S.CM * S.P.eps p) * S.etaIn j (S.P.A j * s) ≤
      X * S.Ptil i j * S.etaIn j (S.P.A j * s) := by
    rw [prod_CM_eps_eq S hS i j]
    have hpow : X ^ (j - i) ≤ X := pow_le_of_le_one hX0 (by linarith) (by omega)
    have he := S.etaIn_nonneg j (S.P.A j * s)
    have : X ^ (j - i) * S.Ptil i j ≤ X * S.Ptil i j := mul_le_mul_of_nonneg_right hpow hPij
    exact mul_le_mul_of_nonneg_right this he
  -- the outer field
  have hout := (transfer_step_two S hS (k := i) hi (by omega) hs
    (hdef i (Finset.mem_Icc.mpr ⟨hi, hij.le⟩))
    (fun l hl => hpert l (by
      have := Finset.mem_Ico.mp hl
      exact Finset.mem_Icc.mpr ⟨this.1, by omega⟩)) S.sh).2
  have hq0 : 0 ≤ S.KO * S.P.sbar ^ 6 := by
    have := (KO_pos S hS).le
    positivity
  have hq : S.KO * S.P.sbar ^ 6 ≤ 1 / 4 := hsm.KO_sbar
  have hout1 : S.CO * ∑ l ∈ Finset.Ico 1 i, S.P.b l i * Sob.normH S.sh (S.P.w l s) ≤
      S.CO * (S.CQ * m * S.Ptil i j * (4 / 3 * (S.KO * S.P.sbar ^ 6))) := by
    refine mul_le_mul_of_nonneg_left ?_ (CO_pos S).le
    calc ∑ l ∈ Finset.Ico 1 i, S.P.b l i * Sob.normH S.sh (S.P.w l s)
        ≤ ∑ l ∈ Finset.Ico 1 i, S.CQ * m * S.Ptil i j * (S.KO * S.P.sbar ^ 6) ^ (i - l) := by
          refine Finset.sum_le_sum fun l hl => ?_
          have hl' := Finset.mem_Ico.mp hl
          have hb := b_nonneg S.P hS.valid l i
          calc S.P.b l i * Sob.normH S.sh (S.P.w l s)
              ≤ S.P.b l i * (S.CQ * (S.Ptil l j * m)) :=
                mul_le_mul_of_nonneg_left (hwl l (Finset.mem_Icc.mpr ⟨hl'.1, by omega⟩)) hb
            _ = S.CQ * m * S.Ptil i j * (S.P.b l i * S.Ptil l i) := by
                rw [← S.Ptil_mul (by omega : l ≤ i) hij.le]
                ring
            _ ≤ S.CQ * m * S.Ptil i j * (S.KO * S.P.sbar ^ 6) ^ (i - l) := by
                have : 0 ≤ S.CQ * m * S.Ptil i j := by positivity
                refine mul_le_mul_of_nonneg_left ?_ this
                rw [b_mul_Ptil S hS hl'.1 hl'.2.le]
                exact prod_KO_s6_le S hS l i
      _ = S.CQ * m * S.Ptil i j * ∑ l ∈ Finset.Ico 1 i, (S.KO * S.P.sbar ^ 6) ^ (i - l) := by
          rw [Finset.mul_sum]
      _ ≤ S.CQ * m * S.Ptil i j * (4 / 3 * (S.KO * S.P.sbar ^ 6)) := by
          have : 0 ≤ S.CQ * m * S.Ptil i j := by positivity
          exact mul_le_mul_of_nonneg_left (geom_outer_le hq0 hq i) this
  rw [Standing.eta_eq_add]
  have hfinal : S.etaIn i (S.P.A i * s) + S.etaOut i (S.P.A i * s) ≤
      S.CQ * m * S.Ptil i j * (8 / 7 * X) + X * S.Ptil i j * S.etaIn j (S.P.A j * s) +
        S.CO * (S.CQ * m * S.Ptil i j * (4 / 3 * (S.KO * S.P.sbar ^ 6))) := by
    linarith
  calc _ ≤ _ := hfinal
    _ = _ := by ring

end NonUniqueEuler.Relay.OProof
