import NonUniqueEuler.Defs.Sec8.All
import NonUniqueEuler.I.Sec8.KickLower
import NonUniqueEuler.I.Infra.Ip.Ip

/-!
# Proof: `prop:kick` (two-sided bound on a near-resonant kick)

Proof of `NonUniqueEuler/I/Sec8/Kick.lean` (`08_kick.tex:229-255`, proof `:256-291`).

Uses `lem:kick-lower` (`I/Sec8/KickLower.lean`: `Kick.kick_lower`) and `eq:Ip`
(`I/Infra/Ip/Ip.lean`: `Ip_pos`, `Ip_antitoneOn`).

Deviation (minor): the manuscript takes `σ > 0` from `prop:U`(a) (`σ ≥ σ_b > 211/2500`). Here
`σ > 0` is derived directly from the hypotheses: `x = Re λ_*(G)/μ > 0` (the setting) and
`|λ_*(G) - z| ≤ σ(μ-1)/(8μ)` give `0 < Re λ_*(G) ≤ σ + σ(μ-1)/(8μ)`, hence `σ > 0`. So the
hypotheses `hχ`, `hN` are not needed by the proof (they are kept in the statement).

The proof follows the manuscript: with `a = (μ-1)/μ`, `w = λ_*(G') - λ_*(G)/μ = z a + D` where
`D = (λ_*(G') - z) - (λ_*(G) - z)/μ`, `|D| ≤ σ a/4`; then `Re w ≥ (3/4)σ a`,
`(3/4)|z| a ≤ |w| ≤ (5/4)|z| a`, `x ≥ σ/4`. With `B = |β||q_s|/(|z|(μ-1))`:
`(2/5)μB ≤ |𝖪| ≤ 2μB` and `𝖱 ≤ B/5`, so `B/10 ≤ B/5 ≤ |A| ≤ 3μB`.
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler

namespace Kick

open RingData

/-- `‖𝖪‖ = |β||q_s||1 - e^{-wT_g}|/|w|`. -/
private theorem norm_kickK (β qs w : ℂ) (Tg : ℝ) :
    ‖kickK β qs w Tg‖ = ‖β‖ * ‖qs‖ * ‖1 - Complex.exp (-(w * Tg))‖ / ‖w‖ := by
  simp only [kickK, norm_div, norm_mul]

/-- `|1 - e^{-wT_g}| ≤ 1 + e^{-Re w T_g}`. -/
private theorem norm_one_sub_exp_le (w : ℂ) (Tg : ℝ) :
    ‖1 - Complex.exp (-(w * Tg))‖ ≤ 1 + Real.exp (-(w.re * Tg)) := by
  calc ‖1 - Complex.exp (-(w * Tg))‖ ≤ ‖(1 : ℂ)‖ + ‖Complex.exp (-(w * Tg))‖ := norm_sub_le _ _
    _ = 1 + Real.exp (-(w.re * Tg)) := by
      rw [norm_one, Complex.norm_exp, Complex.neg_re, Complex.re_mul_ofReal]

set_option linter.unusedVariables false in
/-- **`prop:kick`** (`08_kick.tex:229-255`). Assume (N1)–(N3) and the hypotheses of the
proposition (`Kick.KickHyp`: the setting with `ζ₀ = λ_*(G)/μ`, `1 < μ ≤ 2`, `G, G' ∈ [0,G₁]`
detuned, `T_g > 0`, `τ₀ < -T_g`, `τ₁ > 0`, `Q̄ > 0`, (Q1)–(Q3), (Kick1)–(Kick4)). Then
`Re w ≥ (3/4)σ(μ-1)/μ` (`w = λ_*(G') - ζ₀`), `x = Re ζ₀ ≥ σ/4`, and for every `τ ∈ I ∩ [0,∞)`:
`|β||q_s|/(10|z|(μ-1)) ≤ |A(τ)| ≤ 3|β||q_s|μ/(|z|(μ-1))`.
(`hχ`, `hN` are not used by the proof; see the module docstring.) -/
theorem kick (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {μ G G' : ℝ} {β : ℂ} {τ₀ : ℝ} {τ₁ : EReal} {q : ℝ → ℂ} {Tg Qbar : ℝ} {p : ℕ} {qs : ℂ}
    {err Qpre : ℝ → ℝ} (h : KickHyp χ μ G G' β τ₀ τ₁ q Tg Qbar p qs err Qpre) :
    3 / 4 * Eig.sigma χ 0 * ((μ - 1) / μ) ≤ (Eig.lam χ G' - Eig.lam χ G / μ).re ∧
    Eig.sigma χ 0 / 4 ≤ (Eig.lam χ G / μ).re ∧
    ∀ τ ∈ interval τ₀ τ₁, 0 ≤ τ →
      ‖β‖ * ‖qs‖ / (10 * ‖Eig.z χ‖ * (μ - 1)) ≤ ‖amp (Eig.lam χ G / μ) β τ₀ q τ‖ ∧
      ‖amp (Eig.lam χ G / μ) β τ₀ q τ‖ ≤ 3 * ‖β‖ * ‖qs‖ * μ / (‖Eig.z χ‖ * (μ - 1)) := by
  -- Notation.
  have hzre : (Eig.z χ).re = Eig.sigma χ 0 := rfl
  have hdet : ‖Eig.lam χ G - Eig.z χ‖ ≤ Eig.sigma χ 0 * (μ - 1) / (8 * μ) := h.detuned
  have hdet' : ‖Eig.lam χ G' - Eig.z χ‖ ≤ Eig.sigma χ 0 * (μ - 1) / (8 * μ) := h.detuned'
  have hrepos : 0 < (Eig.lam χ G / μ).re := h.setting.re_pos
  have hk1 := h.kick1
  have hk2 := h.kick2
  have hk3 := h.kick3
  have hk4 := h.kick4
  set σ := Eig.sigma χ 0 with hσdef
  set z := Eig.z χ with hzdef
  set l := Eig.lam χ G with hldef
  set l' := Eig.lam χ G' with hl'def
  have hμ1 : 1 < μ := h.one_lt_μ
  have hμ2 : μ ≤ 2 := h.μ_le_two
  have hμpos : 0 < μ := by linarith
  have hμne : (μ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hμpos.ne'
  set a : ℝ := (μ - 1) / μ with hadef
  have hapos : 0 < a := div_pos (by linarith) hμpos
  have hale : a ≤ 1 / 2 := by
    rw [hadef, div_le_iff₀ hμpos]
    linarith
  have hea : σ * (μ - 1) / (8 * μ) = σ * a / 8 := by
    rw [hadef]
    field_simp
  rw [hea] at hdet hdet'
  -- Step 0: `σ > 0`.
  have hlre_eq : (l / (μ : ℂ)).re = l.re / μ := Complex.div_ofReal_re l μ
  have hlre_pos : 0 < l.re := by
    rw [hlre_eq] at hrepos
    exact (div_pos_iff_of_pos_right hμpos).mp hrepos
  have hlre_bounds : σ - ‖l - z‖ ≤ l.re ∧ l.re ≤ σ + ‖l - z‖ := by
    have h1 := abs_le.mp (Complex.abs_re_le_norm (l - z))
    rw [Complex.sub_re, hzre] at h1
    constructor <;> linarith [h1.1, h1.2]
  have hσpos : 0 < σ := by
    by_contra hσ
    rw [not_lt] at hσ
    have hσa : σ * a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hσ hapos.le
    linarith [hlre_bounds.2]
  have hσa_nonneg : 0 ≤ σ * a := (mul_pos hσpos hapos).le
  have hσz : σ ≤ ‖z‖ := hzre ▸ Complex.re_le_norm z
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hσpos hσz
  -- Step 1: locate `w`.
  set D : ℂ := (l' - z) - (l - z) / (μ : ℂ) with hDdef
  have hw : l' - l / (μ : ℂ) = z * (a : ℂ) + D := by
    rw [hDdef, hadef]
    push_cast
    field_simp
    ring
  have hD : ‖D‖ ≤ σ * a / 4 := by
    have h1 : ‖(l - z) / (μ : ℂ)‖ = ‖l - z‖ / μ := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hμpos.le]
    have h2 : ‖l - z‖ / μ ≤ ‖l - z‖ := div_le_self (norm_nonneg _) hμ1.le
    calc ‖D‖ ≤ ‖l' - z‖ + ‖(l - z) / (μ : ℂ)‖ := norm_sub_le _ _
      _ ≤ σ * a / 8 + σ * a / 8 := by rw [h1]; linarith
      _ = σ * a / 4 := by ring
  have hDre : -(σ * a / 4) ≤ D.re := by
    have := (abs_le.mp ((Complex.abs_re_le_norm D).trans hD)).1
    exact this
  have hza : ‖z * (a : ℂ)‖ = ‖z‖ * a := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hapos.le]
  have hσza : σ * a ≤ ‖z‖ * a := mul_le_mul_of_nonneg_right hσz hapos.le
  have hwre : 3 / 4 * σ * a ≤ (l' - l / (μ : ℂ)).re := by
    rw [hw, Complex.add_re, Complex.re_mul_ofReal, hzre]
    linarith
  have hwlow : 3 / 4 * (‖z‖ * a) ≤ ‖l' - l / (μ : ℂ)‖ := by
    have := norm_sub_le (z * (a : ℂ) + D) D
    rw [add_sub_cancel_right, hza, ← hw] at this
    linarith
  have hwup : ‖l' - l / (μ : ℂ)‖ ≤ 5 / 4 * (‖z‖ * a) := by
    have := norm_add_le (z * (a : ℂ)) D
    rw [hza, ← hw] at this
    linarith
  have hzapos : 0 < ‖z‖ * a := mul_pos hzpos hapos
  have hwpos : 0 < ‖l' - l / (μ : ℂ)‖ := by linarith
  -- Step 2: `x ≥ σ/4` and `I_p(x) ≤ I_p(σ/4)`.
  have hx : σ / 4 ≤ (l / (μ : ℂ)).re := by
    rw [hlre_eq]
    have hσa2 : σ * a ≤ σ * (1 / 2) := mul_le_mul_of_nonneg_left hale hσpos.le
    have hl1 : 15 / 16 * σ ≤ l.re := by linarith [hlre_bounds.1]
    have hl2 : l.re / 2 ≤ l.re / μ := div_le_div_of_nonneg_left hlre_pos.le hμpos hμ2
    linarith
  have hσ4 : 0 < σ / 4 := by linarith
  have hIppos : 0 < Ip p (σ / 4) := Ip_pos p hσ4
  have hIp : Ip p (l / (μ : ℂ)).re ≤ Ip p (σ / 4) :=
    Ip_antitoneOn p (mem_Ioi.mpr hσ4) (mem_Ioi.mpr (lt_of_lt_of_le hσ4 hx)) hx
  refine ⟨?_, hx, ?_⟩
  · -- `Re w ≥ (3/4)σ(μ-1)/μ`.
    simpa only [hadef] using hwre
  intro τ hτ hτ0
  -- Step 3: the kick lemma.
  obtain ⟨hKlow, hAK⟩ := kick_lower h.setting (lt_of_lt_of_le (by positivity) hwre) h.Tg_pos
    h.τ₀_lt h.τ₁_pos h.Qbar_pos h.q1 h.q2 h.q3
  have hAK := hAK τ hτ hτ0
  set w : ℂ := l' - l / (μ : ℂ) with hwdef
  set K : ℂ := kickK β qs w Tg with hKdef
  set A : ℂ := amp (l / (μ : ℂ)) β τ₀ q τ with hAdef
  set x : ℝ := (l / (μ : ℂ)).re with hxdef
  have hμ1pos : 0 < μ - 1 := by linarith
  set B : ℝ := ‖β‖ * ‖qs‖ / (‖z‖ * (μ - 1)) with hBdef
  have hB : 0 ≤ B :=
    div_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (mul_pos hzpos hμ1pos).le
  have hβ := norm_nonneg β
  have hqs := norm_nonneg qs
  -- Bounds on `|𝖪|`.
  have hKlow' : 2 / 5 * μ * B ≤ ‖K‖ := by
    have hnum : ‖β‖ * ‖qs‖ * (1 / 2) ≤ ‖β‖ * ‖qs‖ * (1 - Real.exp (-(w.re * Tg))) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hβ hqs)
      linarith
    have hfrac : ‖β‖ * ‖qs‖ * (1 / 2) / (5 / 4 * (‖z‖ * a)) ≤
        ‖β‖ * ‖qs‖ * (1 - Real.exp (-(w.re * Tg))) / ‖w‖ :=
      div_le_div₀ (by linarith [mul_nonneg hβ hqs]) hnum hwpos hwup
    have heq : ‖β‖ * ‖qs‖ * (1 / 2) / (5 / 4 * (‖z‖ * a)) = 2 / 5 * μ * B := by
      rw [hBdef, hadef]
      field_simp
      ring
    linarith
  have hKup : ‖K‖ ≤ 2 * μ * B := by
    rw [hKdef, norm_kickK]
    have hnum : ‖β‖ * ‖qs‖ * ‖1 - Complex.exp (-(w * Tg))‖ ≤ ‖β‖ * ‖qs‖ * (3 / 2) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hβ hqs)
      linarith [norm_one_sub_exp_le w Tg]
    have hfrac : ‖β‖ * ‖qs‖ * ‖1 - Complex.exp (-(w * Tg))‖ / ‖w‖ ≤
        ‖β‖ * ‖qs‖ * (3 / 2) / (3 / 4 * (‖z‖ * a)) :=
      div_le_div₀ (by positivity) hnum (by linarith) hwlow
    have heq : ‖β‖ * ‖qs‖ * (3 / 2) / (3 / 4 * (‖z‖ * a)) = 2 * μ * B := by
      rw [hBdef, hadef]
      field_simp
      ring
    linarith
  -- Bound on `𝖱`.
  have hR : kickR β x τ₀ Tg err Qpre Qbar p ≤ B / 5 := by
    have hQI : Qbar * Ip p x ≤ ‖qs‖ / (10 * ‖z‖ * (μ - 1)) := by
      have h1 : Qbar * Ip p x ≤ Qbar * Ip p (σ / 4) :=
        mul_le_mul_of_nonneg_left hIp h.Qbar_pos.le
      have h2 : (μ - 1) * (10 * ‖z‖ * Qbar * Ip p (σ / 4)) ≤ ‖qs‖ :=
        (le_div_iff₀ (mul_pos (mul_pos (by linarith) h.Qbar_pos) hIppos)).mp hk1
      have h3 : Qbar * Ip p (σ / 4) ≤ ‖qs‖ / (10 * ‖z‖ * (μ - 1)) := by
        rw [le_div_iff₀ (mul_pos (by linarith) hμ1pos)]
        nlinarith [h2]
      linarith
    have hsum : errG x Tg err + errPre x τ₀ Tg Qpre + Qbar * Ip p x ≤
        ‖qs‖ / (‖z‖ * (μ - 1)) / 5 := by
      have e1 : ‖qs‖ / (20 * ‖z‖ * (μ - 1)) = ‖qs‖ / (‖z‖ * (μ - 1)) / 20 := by
        field_simp
      have e2 : ‖qs‖ / (10 * ‖z‖ * (μ - 1)) = ‖qs‖ / (‖z‖ * (μ - 1)) / 10 := by
        field_simp
      rw [e1] at hk3 hk4
      rw [e2] at hQI
      linarith
    have hB5 : B / 5 = ‖β‖ * (‖qs‖ / (‖z‖ * (μ - 1)) / 5) := by
      rw [hBdef]
      ring
    rw [kickR, hB5]
    exact mul_le_mul_of_nonneg_left hsum hβ
  have hμB : B ≤ μ * B := le_mul_of_one_le_left hB hμ1.le
  constructor
  · -- Lower bound.
    have h1 : ‖K‖ - ‖A‖ ≤ ‖A - K‖ := by
      rw [norm_sub_rev]
      exact norm_sub_norm_le K A
    have heq : ‖β‖ * ‖qs‖ / (10 * ‖z‖ * (μ - 1)) = B / 10 := by
      rw [hBdef]
      field_simp
    rw [heq]
    linarith
  · -- Upper bound.
    have h1 : ‖A‖ ≤ ‖K‖ + ‖A - K‖ := by
      calc ‖A‖ = ‖K + (A - K)‖ := by rw [add_sub_cancel]
        _ ≤ ‖K‖ + ‖A - K‖ := norm_add_le _ _
    have heq : 3 * ‖β‖ * ‖qs‖ * μ / (‖z‖ * (μ - 1)) = 3 * μ * B := by
      rw [hBdef]
      ring
    rw [heq]
    linarith

end Kick

end NonUniqueEuler
