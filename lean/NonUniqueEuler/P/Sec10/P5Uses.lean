import NonUniqueEuler.Defs.Sec10.Lists
import NonUniqueEuler.I.Sec9.Gamma
import NonUniqueEuler.I.Sec10.ConstantsPos

/-!
# Proof: (κ7) bounds the term `Ξ_{j+1}` (remark after `def:P5`)

Proof of `I/Sec10/P5Uses.lean` (`10_parameters.tex:122-130`, `:224-225`; the computation of
`11_bootstrap.tex:364-367`): same declarations, same statements.

With `κ = κ♯_{j+1}` and `x = κ/δ₀ ∈ (0, 1]` (`κ ≤ 2κ_seed < δ₀`, `KappaList.two_lt_δ₀`):
* `lem:gamma` (`gamma`) gives `γ'_μ ≤ 1 - γ_j`, so `x^{1-γ_j} ≤ x^{γ'_μ}`
  (`Real.rpow_le_rpow_of_exponent_ge`);
* the prefactor `C_Ξ(C₀,K₁)(1 + 1/(σ_b(μ-1)))` and `⟨log(δ₀/κ)⟩^{m+1}` are nonnegative
  (`constants_pos`: `K₁ > 0`, `σ_b > 0`, `C₂ ≥ 1`; `C(C₀) ≥ C₀ ≥ 1`);
* (κ7) at `κ` bounds the result by `δ₀ · 1/(σ_b(μ-1))`.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

open RingData Datum

/-- `C_Ξ(C₀,K₁) ≥ 0` for `C₀ = S.C0` under the signs of `constants_pos`. -/
private theorem CXi_nonneg_P5 (S : Standing) (hpos : S.ConstPos) :
    0 ≤ S.CXi S.C0 S.K1 := by
  have hK1 := hpos.K1_pos
  have hsb := hpos.sigb_pos
  have hC2 := hpos.one_le_C2
  have hC0 := S.one_le_C0
  have hCact : S.C0 ≤ S.Cact S.C0 := by
    unfold Standing.Cact OneRing.Cact
    exact le_max_left _ _
  have hmax : 1 ≤ max 1 (2 * S.CQ) := le_max_left _ _
  have hmin : 0 < min 1 S.sigb := lt_min one_pos hsb
  have hden : 0 < S.sigb * min 1 S.sigb ^ 3 := by positivity
  have hnum : 0 ≤ 2 * S.C2 * S.Cact S.C0 + S.C0 := by nlinarith
  unfold Standing.CXi
  have h1 : 0 ≤ max 1 (2 * S.CQ) * S.K1 := by nlinarith
  have h2 : 0 ≤ (2 * S.C2 * S.Cact S.C0 + S.C0) / (S.sigb * min 1 S.sigb ^ 3) :=
    div_nonneg hnum hden.le
  linarith

/-- **(κ7) bounds `Ξ_{j+1}`** (remark after `def:P5`, `10_parameters.tex:127-129`, `:224-225`;
the computation of `11_bootstrap.tex:364-367`): under (SA), (Det) and the κ-list for `κ_seed`,
for every level `1 ≤ j < n` with `κ♯_{j+1} ∈ (0, 2κ_seed]`,
`Ξ_{j+1} ≤ δ₀/(σ_b(μ-1))` (with `C₀`, `K₁` of (P4), `def:K1`). -/
theorem kappa7_XiNext (S : Standing) (hS : S.Holds) (hDet : S.Det)
    (hK : S.KappaList S.P.κs) {j : ℕ} (hj : 1 ≤ j) (hjn : j < S.P.n)
    (hκ : S.P.ksh (j + 1) ∈ Ioc (0 : ℝ) (2 * S.P.κs)) :
    S.XiNext S.C0 S.K1 j ≤ S.P.δ₀ / (S.sigb * (S.P.μ - 1)) := by
  have hpos := constants_pos S hS.admissible hS.hN hS.σ'_gt hS.σ'_lt_sigma hS.δ₀_pos
    hS.one_lt_μ hS.Tpin_pos
  have hδ : 0 < S.P.δ₀ := hS.δ₀_pos
  have hμ : 1 < S.P.μ := hS.one_lt_μ
  have hsb : 0 < S.sigb := hpos.sigb_pos
  set κ := S.P.ksh (j + 1) with hκdef
  have hκpos : 0 < κ := hκ.1
  have hκδ : κ < S.P.δ₀ := lt_of_le_of_lt hκ.2 (hK.two_lt_δ₀ hδ hμ)
  -- `x = κ/δ₀ ∈ (0, 1]`
  have hx0 : 0 < κ / S.P.δ₀ := div_pos hκpos hδ
  have hx1 : κ / S.P.δ₀ ≤ 1 := (div_le_one hδ).2 hκδ.le
  -- `lem:gamma`
  have hγ := (gamma S hS hDet j (Finset.mem_Ico.2 ⟨hj, hjn⟩)).1
  have hrpow : (κ / S.P.δ₀) ^ (1 - S.gammaJ j) ≤ (κ / S.P.δ₀) ^ S.gammaMu' :=
    Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hγ
  -- (κ7) at `κ`
  have h7 := (hK.cond hκpos hκ.2).k7
  -- signs
  have hσμ : 0 < S.sigb * (S.P.μ - 1) := mul_pos hsb (by linarith)
  have hpref : 0 ≤ S.CXi S.C0 S.K1 * (1 + 1 / (S.sigb * (S.P.μ - 1))) := by
    have : 0 ≤ 1 + 1 / (S.sigb * (S.P.μ - 1)) := by
      have := one_div_pos.2 hσμ
      linarith
    exact mul_nonneg (CXi_nonneg_P5 S hpos) this
  have hjap : 0 ≤ Prelim.jap (Real.log (S.P.δ₀ / κ)) ^ (3 + 1) := by
    unfold Prelim.jap
    positivity
  set A := S.CXi S.C0 S.K1 * (1 + 1 / (S.sigb * (S.P.μ - 1))) with hA
  set B := Prelim.jap (Real.log (S.P.δ₀ / κ)) ^ (3 + 1) with hB
  have hstep : A * (κ / S.P.δ₀) ^ (1 - S.gammaJ j) * B ≤ 1 / (S.sigb * (S.P.μ - 1)) := by
    calc A * (κ / S.P.δ₀) ^ (1 - S.gammaJ j) * B
        ≤ A * (κ / S.P.δ₀) ^ S.gammaMu' * B := by
          gcongr
      _ ≤ 1 / (S.sigb * (S.P.μ - 1)) := h7
  have hXi : S.XiNext S.C0 S.K1 j = S.P.δ₀ * (A * (κ / S.P.δ₀) ^ (1 - S.gammaJ j) * B) := by
    unfold Standing.XiNext
    rw [hA, hB, hκdef]
    ring
  rw [hXi]
  calc S.P.δ₀ * (A * (κ / S.P.δ₀) ^ (1 - S.gammaJ j) * B)
      ≤ S.P.δ₀ * (1 / (S.sigb * (S.P.μ - 1))) := mul_le_mul_of_nonneg_left hstep hδ.le
    _ = S.P.δ₀ / (S.sigb * (S.P.μ - 1)) := by ring

end Relay

end NonUniqueEuler
