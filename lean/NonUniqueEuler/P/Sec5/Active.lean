import NonUniqueEuler.H.Sec5.Active.WindowCase

/-!
# Proof of `thm:active` (an active ring) and of `cor:active-moment`

Proof of `NonUniqueEuler/I/Sec5/Active.lean` (`05_single_ring.tex:863-1122`). Same declaration
(`active`), statement copied verbatim. The facts on `t₁` (`tOneOf_spec`, `active_tOne`) are in
`I/Sec5/ActiveT1.lean` (a separate proof) and are used as black boxes by the helpers.

* `active` (`:913-1094`, with `cor:active-moment`, `:1112-1122`). The constants: `C_L ≥ 0` of the
  initial layer (`I/Sec5/Active/Layer.lean`, it is `C_lin(M-2)`), `C_φ = max_G ‖φ_*(G)‖_{H^{M-2}}`,
  `C♮ = max(4, 6C_φ + 2C_L + 1)`, `(δ_W, κ_W, C_W)` of `lem:window` for `C♮`,
  `C₂ = 6C_φ + 3(C_W + C_L + 1)`, `C₃ = (1 + C_p)C₂`, `d_H = min(δ_W, a/(32C₂))`; for `C₀ ≥ 1`,
  `κ₀(C₀)` is *some* `x > 0` such that every `κ ∈ (0,x]` satisfies the smallness conditions (the
  layer's `κ_L`, `C₄κ ≤ ½κ^{1/2}`, `2C_φC₄κ ≤ ½κ^{1/2}`, `κ ≤ (a/32)²`,
  `e^{σ_max t̄₁}κ ≤ κ_W`, `C_We^{σ_max t̄₁}κς(κ)^{N_W} ≤ ½κ^{1/2}`), chosen with
  `Classical.choose`. The case `u ≤ t₁` is `ActiveH.concl_layer`, the case `u > t₁` (restart,
  `lem:window`) is `ActiveH.concl_window` (`H/Sec5/Active/Core.lean`, `WindowCase.lean`).

Deviations: `κ₀(C₀)` is an admissible value, not
the largest one (the statement is existential, so this is immaterial); the constants `C♮`, `C₂`
use `C_L = C_lin(M-2)` and `C_φ` at level `M-2` (the manuscript's `C_lin`, `C_φ` are maxima over
levels, which only makes them larger); the bound of `(1-R)wlin` and `eq:A-layer` are packaged in
the interface `active_layer`, and the coefficient bound `|c(u)e^{λu}| ≤ â(3 + ρ̂)` is used in both
cases (the manuscript uses `â(2 + ρ̂)` and `3â` separately).
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace OneRing

open RingData

/-- **`thm:active`** (`05_single_ring.tex:863-900`). Assume (N1)–(N3). Fix an integer `s ≥ 3`
and `σ' ∈ (9/200, σ_b)`; `p = 3`, `N_G`, `M = s + N_G + 2`, `η_max = 1`. There are
`d_H ∈ (0,1)`, `C₂ ≥ 1` and `C₃ > 0`, depending only on `(Φ, G₁, s, σ')`, and for every
`C₀ ≥ 1` a number `κ₀(C₀) > 0`, depending only on `C₀` and `(Φ, G₁, s, σ')`, such that: for
`G ∈ [0,G₁]`, `κ > 0`, `η_b ∈ [0,η_max]`, `δ₀ ∈ (0,d_H]`, `ū > 0` and a configuration of
`lem:reduction` on `[0,ū]` with this `G` satisfying (Init), (Field), (Coef) and (Small)
`κ ≤ κ₀(C₀)`, for every `u ∈ [0, min(ū, T̂)]`:
(a) every trajectory of `ω_r` moves radially by at most `C₂δ₀ + κ^{1/2}` on `[0,u]`, and
`supp(Φ + w(u)) ⊂ 𝒩`;
(b) `‖w(u) - 2Re(c(u)e^{λu}φ_*)‖_{H^s} ≤ C₂â(u)[ρ̂(u) + â(u) + κ^{1/2} + η_b]` and
`‖w(u)‖_{H^s} ≤ C₂â(u)(1 + ρ̂(u))`;
and the bound of `cor:active-moment` with `C₃`. All of this is
`IsActiveConst χ s σ' d_H C₂ C₃ κ₀` (D11). -/
theorem active (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {s : ℕ} (hs : 3 ≤ s) {σ' : ℝ} (hσ' : σ' ∈ Ioo (9 / 200 : ℝ) (Eig.sigb χ)) :
    ∃ (δH C₂ C₃ : ℝ) (κ₀ : ℝ → ℝ), IsActiveConst χ s σ' δH C₂ C₃ κ₀ := by
  classical
  obtain ⟨CL, hCL, hLayer⟩ := active_layer χ hχ hN hs hσ'
  set Cφ := Eig.phiNormMax χ (Mact χ s - 2) with hCφ
  have hCφ0 : 0 ≤ Cφ := ActiveH.phiNormMax_nonneg χ hχ hN _
  set Cn := max 4 (6 * Cφ + 2 * CL + 1) with hCn
  have hCn4 : 4 ≤ Cn := le_max_left _ _
  have hCn' : 6 * Cφ + 2 * CL + 1 ≤ Cn := le_max_right _ _
  have hCn1 : 1 ≤ Cn := by linarith
  obtain ⟨δW, κW, CW, hδW, hκW, hCW, hWin⟩ := window χ hχ hN hs hσ' hCn1
  set C₂ := 6 * Cφ + 3 * (CW + CL + 1) with hC₂
  set C₃ := (1 + Eig.Cp) * C₂ with hC₃
  have hC₂1 : 1 ≤ C₂ := by linarith
  have hC₂0 : 0 < C₂ := by linarith
  obtain ⟨ha0, ha1⟩ := ActiveH.a_facts hχ
  have hσb : 0 < Eig.sigb χ := by linarith [hσ'.1, hσ'.2]
  set dH := min δW (a / (32 * C₂)) with hdH
  have hdH0 : 0 < dH := lt_min hδW.1 (by positivity)
  have hdH1 : dH < 1 := lt_of_le_of_lt (min_le_left _ _) (by linarith [hδW.2])
  -- the smallness conditions defining `κ₀(C₀)`
  have hex : ∀ C₀ : ℝ, 1 ≤ C₀ → ∃ k : ℝ, 0 < k ∧ ∃ κL C₄ : ℝ, 0 ≤ C₄ ∧
      ActiveH.LayerProp χ s σ' CL C₀ κL C₄ ∧
      ∀ κ : ℝ, 0 < κ → κ ≤ k →
        κ ≤ κL ∧ C₄ * κ ≤ Real.sqrt κ / 2 ∧ 2 * Cφ * C₄ * κ ≤ Real.sqrt κ / 2 ∧
          Real.sqrt κ ≤ a / 32 ∧ Real.exp (sigmaMax χ * tOneBar χ σ' C₀) * κ ≤ κW ∧
          CW * (Real.exp (sigmaMax χ * tOneBar χ σ' C₀) * κ) * varsigma χ κ ^ NW χ s ≤
            Real.sqrt κ / 2 := by
    intro C₀ hC₀
    obtain ⟨κL, C₄, hκL, hC₄, hLay⟩ := hLayer C₀ hC₀
    set E := Real.exp (sigmaMax χ * tOneBar χ σ' C₀) with hE
    have hE0 : 0 < E := Real.exp_pos _
    obtain ⟨ε₁, hε₁, -, h1⟩ := ActiveH.small_sqrt hC₄
    obtain ⟨ε₂, hε₂, -, h2⟩ := ActiveH.small_sqrt (A := 2 * Cφ * C₄) (by positivity)
    obtain ⟨ε₃, hε₃, -, h3⟩ := ActiveH.small_varsigma (B := CW * E) (by positivity) hσb (NW χ s)
    refine ⟨min (min (min κL ε₁) (min ε₂ ε₃)) (min ((a / 32) ^ 2) (κW / E)), ?_, κL, C₄, hC₄,
      hLay, fun κ hκ hk => ?_⟩
    · have : 0 < κW / E := div_pos hκW.1 hE0
      positivity
    · have hk1 := hk.trans (min_le_left _ _)
      have hk2 := hk.trans (min_le_right _ _)
      have hkL : κ ≤ κL := hk1.trans ((min_le_left _ _).trans (min_le_left _ _))
      have hk₁ : κ ≤ ε₁ := hk1.trans ((min_le_left _ _).trans (min_le_right _ _))
      have hk₂ : κ ≤ ε₂ := hk1.trans ((min_le_right _ _).trans (min_le_left _ _))
      have hk₃ : κ ≤ ε₃ := hk1.trans ((min_le_right _ _).trans (min_le_right _ _))
      have hka : κ ≤ (a / 32) ^ 2 := hk2.trans (min_le_left _ _)
      have hkW : κ ≤ κW / E := hk2.trans (min_le_right _ _)
      refine ⟨hkL, h1 κ hκ hk₁, h2 κ hκ hk₂, ?_, ?_, ?_⟩
      · calc Real.sqrt κ ≤ Real.sqrt ((a / 32) ^ 2) := Real.sqrt_le_sqrt hka
          _ = a / 32 := Real.sqrt_sq (by positivity)
      · rw [le_div_iff₀ hE0] at hkW
        linarith
      · have := h3 κ hκ hk₃
        calc CW * (E * κ) * varsigma χ κ ^ NW χ s
            = CW * E * κ * (1 + (Eig.sigb χ)⁻¹ * Real.log (1 / κ)) ^ NW χ s := by
              rw [varsigma]; ring
          _ ≤ Real.sqrt κ / 2 := this
  -- `κ₀`
  let κ₀ : ℝ → ℝ := fun C₀ => if h : 1 ≤ C₀ then Classical.choose (hex C₀ h) else 1
  have hκ₀ : ∀ C₀ (h : 1 ≤ C₀), κ₀ C₀ = Classical.choose (hex C₀ h) := fun C₀ h => dite_eq_left h
  refine ⟨dH, C₂, C₃, κ₀, ⟨hdH0, hdH1⟩, hC₂1, ?_, ?_, ?_⟩
  · have := ActiveH.Cp_pos
    positivity
  · intro C₀ hC₀
    rw [hκ₀ C₀ hC₀]
    exact (Classical.choose_spec (hex C₀ hC₀)).1
  intro C₀ hC₀ c ubar hc hG κ ηb δ₀ hκ hηb hδ₀ hInit hField hCoef hSmall u hu
  rw [hκ₀ C₀ hC₀] at hSmall
  obtain ⟨-, κL, C₄, hC₄, hLay, hsmall⟩ := Classical.choose_spec (hex C₀ hC₀)
  obtain ⟨hκL, hs1, hs2, hs3, hs4, hs5⟩ := hsmall κ hκ hSmall
  have hδ₀W : δ₀ ≤ δW := hδ₀.2.trans (min_le_left _ _)
  have hC₂δ : C₂ * δ₀ ≤ a / 32 := by
    have h1 : δ₀ ≤ a / (32 * C₂) := hδ₀.2.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    linarith
  by_cases hut : u ≤ tOne χ σ' C₀ c.G
  · exact ActiveH.concl_layer χ hχ hN hσ' hCL hC₀ hC₄ hLay (by linarith) rfl hc hG hκ hηb
      hδ₀.1 (by linarith [hdH1, hδ₀.2]) hInit hField hCoef hκL hs1 hs3 hC₂δ hu hut
  · exact ActiveH.concl_window χ hχ hN hσ' hCL hC₀ hC₄ hLay hWin hCW hκW.2 hCn' hCn4
      (by linarith) rfl hc hG hκ hηb hδ₀.1 hδ₀W (by linarith [hδW.2]) hInit hField hCoef hκL
      hs1 hs2 hs3 hC₂δ hs4 hs5 hu (lt_of_not_ge hut)

end OneRing

end NonUniqueEuler
