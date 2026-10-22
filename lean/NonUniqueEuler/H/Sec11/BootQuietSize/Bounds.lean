import NonUniqueEuler.H.Sec11.BootQuietSize.Basic

/-!
# Helper for `P/Sec11/BootQuietSize.lean`: the three final estimates of Step 5

Helper of the proof of Step 5 of `prop:bootstrap` (`11_bootstrap.tex:486-530`). The arithmetic
that turns the conclusions of `prop:relay` and `lem:O` into `maj_j(A_jt') ≤ Āε_j`:
* `b10_bound` (`:512-516`): `2C_M(2C_Q/(σ_b(μ-1)) + 1)ε_j · 2Āε_{j+1} ≤ Āε_j` by (B10) and
  `ε_{j+1} ≤ μs̄^{m+2}`;
* `XiNext_le` (`:519-520`, as in Step 3, `:362-365`): `Ξ_{j+1} ≤ δ₀/(σ_b(μ-1))` from
  `1 - γ_j ≥ γ'_μ` (`lem:gamma`), `κ♯_{j+1}/δ₀ ∈ (0, 1)` and (κ7) at `κ♯_{j+1}`;
* `relayBound_le_Abar` (`:520-523`): with `x_j ≤ 17σ/16` (`lem:detuning`) the right side of
  `eq:relay` with `Ξ = δ₀/(σ_b(μ-1))` is at most `Āε_j` (the definition of `Ā`);
* `Ptil_mul_le` (`:525-530`): `¾P̃_{j,k}Āε_k ≤ ⅜Āε_j ≤ Āε_j` for `j < k`, since
  `K_Oε_p ≤ K_Oμs̄^{m+2} ≤ ½` ((B7)).
All proved.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

namespace BootQuietSizeH

open RingData Datum

variable {S : Standing}

/-- **(B10) in Step 5** (`11_bootstrap.tex:512-516`): if `M ≤ 2Āε_{j+1}`, then
`2C_M(2C_Q/(σ_b(μ-1)) + 1)ε_j M ≤ Āε_j`. -/
theorem b10_bound (hpos : S.ConstPos) (hS : S.Holds)
    (hb10 : 4 * S.Crelay * S.P.μ * S.P.sbar ^ (3 + 2) ≤ 1 / 2) {j : ℕ} {M : ℝ}
    (hM : M ≤ 2 * S.Abar * S.P.eps (j + 1)) :
    2 * S.Crelay * S.P.eps j * M ≤ S.Abar * S.P.eps j := by
  have hC := Crelay_nonneg hpos hS
  have hej := eps_nonneg hS j
  have hA := hpos.Abar_pos.le
  have h1 : 0 ≤ 2 * S.Crelay * S.P.eps j := by positivity
  have h2 : 4 * S.Crelay * S.P.eps (j + 1) ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left (eps_le hS (j + 1)) (by positivity : 0 ≤ 4 * S.Crelay)
    generalize S.P.sbar ^ (3 + 2) = X at this hb10
    linarith
  have hX : 0 ≤ S.Abar * S.P.eps j := mul_nonneg hA hej
  calc 2 * S.Crelay * S.P.eps j * M ≤ 2 * S.Crelay * S.P.eps j * (2 * S.Abar * S.P.eps (j + 1)) :=
        mul_le_mul_of_nonneg_left hM h1
    _ = (4 * S.Crelay * S.P.eps (j + 1)) * (S.Abar * S.P.eps j) := by ring
    _ ≤ 1 / 2 * (S.Abar * S.P.eps j) := mul_le_mul_of_nonneg_right h2 hX
    _ ≤ S.Abar * S.P.eps j := by linarith

/-- **`Ξ_{j+1} ≤ δ₀/(σ_b(μ-1))`** (`11_bootstrap.tex:362-365`, `:519-520`): from `γ'_μ ≤ 1 - γ_j`
(`lem:gamma`), `κ♯_{j+1} ∈ (0, δ₀)` and (κ7) at `κ = κ♯_{j+1}`. -/
theorem XiNext_le (hS : S.Holds) (hsb : 0 < S.sigb) {j : ℕ} (hγ : S.gammaMu' ≤ 1 - S.gammaJ j)
    (hκ : S.P.ksh (j + 1) ∈ Ioo (0 : ℝ) S.P.δ₀)
    (h7 : S.CXi S.C0 S.K1 * (1 + 1 / (S.sigb * (S.P.μ - 1))) *
        (S.P.ksh (j + 1) / S.P.δ₀) ^ S.gammaMu' *
        Prelim.jap (Real.log (S.P.δ₀ / S.P.ksh (j + 1))) ^ (3 + 1) ≤
      1 / (S.sigb * (S.P.μ - 1))) :
    S.XiNext S.C0 S.K1 j ≤ S.P.δ₀ / (S.sigb * (S.P.μ - 1)) := by
  have hδ := hS.δ₀_pos
  have hμ : 0 < S.P.μ - 1 := by linarith [hS.one_lt_μ]
  have hD : 0 < S.sigb * (S.P.μ - 1) := mul_pos hsb hμ
  set c := S.CXi S.C0 S.K1 * (1 + 1 / (S.sigb * (S.P.μ - 1))) with hc
  set x := S.P.ksh (j + 1) / S.P.δ₀ with hx
  set J := Prelim.jap (Real.log (S.P.δ₀ / S.P.ksh (j + 1))) ^ (3 + 1) with hJ
  have hx0 : 0 < x := div_pos hκ.1 hδ
  have hx1 : x ≤ 1 := (div_le_one hδ).2 hκ.2.le
  have hab : x ^ (1 - S.gammaJ j) ≤ x ^ S.gammaMu' :=
    Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hγ
  have ha0 : 0 ≤ x ^ (1 - S.gammaJ j) := Real.rpow_nonneg hx0.le _
  have hJ0 : 0 ≤ J := pow_nonneg (Prelim.jap_nonneg _) _
  have hR : 0 ≤ 1 / (S.sigb * (S.P.μ - 1)) := by positivity
  have hkey : c * x ^ (1 - S.gammaJ j) * J ≤ 1 / (S.sigb * (S.P.μ - 1)) := by
    rcases le_or_gt 0 c with hc0 | hc0
    · calc c * x ^ (1 - S.gammaJ j) * J ≤ c * x ^ S.gammaMu' * J :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hab hc0) hJ0
        _ ≤ 1 / (S.sigb * (S.P.μ - 1)) := h7
    · have : c * x ^ (1 - S.gammaJ j) * J ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hc0.le ha0) hJ0
      linarith
  have heq : S.XiNext S.C0 S.K1 j = S.P.δ₀ * (c * x ^ (1 - S.gammaJ j) * J) := by
    simp only [Standing.XiNext, hc, hx, hJ]
    ring
  rw [heq]
  calc S.P.δ₀ * (c * x ^ (1 - S.gammaJ j) * J) ≤ S.P.δ₀ * (1 / (S.sigb * (S.P.μ - 1))) :=
        mul_le_mul_of_nonneg_left hkey hδ.le
    _ = S.P.δ₀ / (S.sigb * (S.P.μ - 1)) := by ring

/-- **The right side of `eq:relay` is at most `Āε_j`** (`11_bootstrap.tex:520-523`): with
`Ξ = δ₀/(σ_b(μ-1))` and `x_j ≤ 17σ/16` (`lem:detuning`),
`2C_Mε_je^{x_jT_pin}[4C₂δ₀/(σ_b(μ-1)) + C_D(T_pin) + Ξ] ≤ Āε_j`. -/
theorem relayBound_le_Abar (hpos : S.ConstPos) (hS : S.Holds) {j : ℕ}
    (hx : S.P.xk j ≤ 17 / 16 * S.sigma0) :
    S.relayBound j (S.P.δ₀ / (S.sigb * (S.P.μ - 1))) ≤ S.Abar * S.P.eps j := by
  have hδ := hS.δ₀_pos
  have hT := hS.Tpin_pos
  have hμ : 0 < S.P.μ - 1 := by linarith [hS.one_lt_μ]
  have hD : 0 < S.sigb * (S.P.μ - 1) := mul_pos hpos.sigb_pos hμ
  have hC2 : 0 ≤ S.C2 := le_trans zero_le_one hpos.one_le_C2
  have hCD := CD_nonneg hT.le
  have hB : 0 ≤ (4 * S.C2 + 1) * S.P.δ₀ / (S.sigb * (S.P.μ - 1)) + CD S.P.Tpin := by
    positivity
  have hCM := hpos.CM_pos
  have hej := eps_nonneg hS j
  have hexp : Real.exp (S.P.xk j * S.P.Tpin) ≤ Real.exp (17 * S.sigma0 * S.P.Tpin / 16) := by
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_right hx hT.le
    linarith
  have hsum : 4 * S.C2 * S.P.δ₀ / (S.sigb * (S.P.μ - 1)) + CD S.P.Tpin +
      S.P.δ₀ / (S.sigb * (S.P.μ - 1)) =
      (4 * S.C2 + 1) * S.P.δ₀ / (S.sigb * (S.P.μ - 1)) + CD S.P.Tpin := by ring
  rw [S.relayBound_def, hsum, S.Abar_def]
  have h2 : 0 ≤ 2 * S.CM * S.P.eps j := by positivity
  calc 2 * S.CM * S.P.eps j * Real.exp (S.P.xk j * S.P.Tpin) *
        ((4 * S.C2 + 1) * S.P.δ₀ / (S.sigb * (S.P.μ - 1)) + CD S.P.Tpin) ≤
      2 * S.CM * S.P.eps j * Real.exp (17 * S.sigma0 * S.P.Tpin / 16) *
        ((4 * S.C2 + 1) * S.P.δ₀ / (S.sigb * (S.P.μ - 1)) + CD S.P.Tpin) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp h2) hB
    _ = 2 * S.CM * Real.exp (17 * S.sigma0 * S.P.Tpin / 16) *
        ((4 * S.C2 + 1) * S.P.δ₀ / (S.sigb * (S.P.μ - 1)) + CD S.P.Tpin) * S.P.eps j := by ring

/-- `P̃_{i,k} ∈ [0, 1]` when every factor `K_Oε_p` is in `[0, ½]`. -/
theorem Ptil_mem (hpos : S.ConstPos) (hS : S.Holds) (hsmall : S.OSmall) (i k : ℕ) :
    0 ≤ S.Ptil i k ∧ S.Ptil i k ≤ 1 := by
  have hKO := hpos.KO_pos.le
  have hfac : ∀ p, 0 ≤ S.KO * S.P.eps p ∧ S.KO * S.P.eps p ≤ 1 / 2 := by
    intro p
    refine ⟨mul_nonneg hKO (eps_nonneg hS p), ?_⟩
    have := mul_le_mul_of_nonneg_left (eps_le hS p) hKO
    have h2 := hsmall.KO_mu_sbar
    generalize S.P.sbar ^ (3 + 2) = X at this h2
    linarith
  rw [S.Ptil_def]
  refine ⟨Finset.prod_nonneg fun p _ => (hfac p).1, ?_⟩
  exact Finset.prod_le_one (fun p _ => (hfac p).1) fun p _ => by linarith [(hfac p).2]

/-- **The stopped case of Step 5** (`11_bootstrap.tex:525-530`): for `j < k` and `M ≤ Āε_k`,
`¾P̃_{j,k}M ≤ ¾ĀK_Oε_jε_k∏_{p=j+1}^{k-1}K_Oε_p ≤ ⅜Āε_j ≤ Āε_j`. -/
theorem Ptil_mul_le (hpos : S.ConstPos) (hS : S.Holds) (hsmall : S.OSmall) {j k : ℕ}
    (hjk : j < k) {M : ℝ} (hM : M ≤ S.Abar * S.P.eps k) :
    3 / 4 * S.Ptil j k * M ≤ S.Abar * S.P.eps j := by
  have hKO := hpos.KO_pos.le
  have hA := hpos.Abar_pos.le
  have hej := eps_nonneg hS j
  have hek := eps_nonneg hS k
  have hsplit : S.Ptil j k = S.KO * S.P.eps j * S.Ptil (j + 1) k := by
    rw [S.Ptil_def, S.Ptil_def, Finset.prod_eq_prod_Ico_succ_bot hjk]
  obtain ⟨hP0, hP1⟩ := Ptil_mem hpos hS hsmall (j + 1) k
  have hy : S.KO * S.P.eps k ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left (eps_le hS k) hKO
    have h2 := hsmall.KO_mu_sbar
    generalize S.P.sbar ^ (3 + 2) = X at this h2
    linarith
  have hy0 : 0 ≤ S.KO * S.P.eps k := mul_nonneg hKO hek
  have hPjk : 0 ≤ S.Ptil j k := (Ptil_mem hpos hS hsmall j k).1
  have hX : 0 ≤ S.Abar * S.P.eps j := mul_nonneg hA hej
  calc 3 / 4 * S.Ptil j k * M ≤ 3 / 4 * S.Ptil j k * (S.Abar * S.P.eps k) :=
        mul_le_mul_of_nonneg_left hM (by positivity)
    _ = 3 / 4 * (S.Abar * S.P.eps j) * (S.Ptil (j + 1) k * (S.KO * S.P.eps k)) := by
        rw [hsplit]; ring
    _ ≤ 3 / 4 * (S.Abar * S.P.eps j) * (1 * (1 / 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul hP1 hy hy0 zero_le_one
    _ ≤ S.Abar * S.P.eps j := by linarith

end BootQuietSizeH

end Relay

end NonUniqueEuler
