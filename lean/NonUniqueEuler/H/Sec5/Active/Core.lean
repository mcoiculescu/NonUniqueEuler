import NonUniqueEuler.H.Sec5.Active.Tools
import NonUniqueEuler.H.Sec5.Active.Elem
import NonUniqueEuler.I.Sec5.Active.Layer
import NonUniqueEuler.I.Sec5.Active.Moment

/-!
# Helpers for `thm:active`: the final step and the case `u ≤ t₁`

Helper of `P/Sec5/Active.lean` (fully proved, modulo the interface files it imports).

* `LayerProp`: the property of the layer constants (`I/Sec5/Active/Layer.lean`);
* `concl_of_core`: from the displacement bound (a), the bound (b) on `w - 2Re(ce^{λu}φ_*)` with
  some constant `K` (`6C_φ + 3K ≤ C₂`) and `|c(u)e^{λu}| ≤ â(3 + ρ̂)`, all conclusions of
  `thm:active` and `cor:active-moment` follow (`05_single_ring.tex:1015-1020`, `:1078-1094`,
  `:1112-1122`);
* `concl_layer`: the case `u ≤ t₁` (`05_single_ring.tex:1001-1020`).
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace NonUniqueEuler.OneRing.ActiveH

open RingData

/-- The property of the constants `(C_L; κ_L, C₄)` of the initial layer, for `C₀`
(`I/Sec5/Active/Layer.lean`). -/
def LayerProp (χ : ℝ → ℝ) (s : ℕ) (σ' CL C₀ κL C₄ : ℝ) : Prop :=
  ∀ (c : RingConfig) (ubar κ ηb : ℝ), c.Hyp ubar → c.G ∈ Icc (0 : ℝ) Gbar →
    0 < κ → κ ≤ κL → ηb ∈ Icc (0 : ℝ) etaMax →
    c.ActiveInit χ s C₀ κ → c.ActiveField χ s ubar C₀ κ ηb →
    ∀ u ∈ Icc (0 : ℝ) (min ubar (tOne χ σ' C₀ c.G)),
      c.MovesRadially u (C₄ * κ) ∧
        Sob.normH (Mact χ s - 2) (c.w χ u - modeFn χ c.G
            (runCoef χ c.G (c.pert0 χ) c.h u * Complex.exp (Eig.lam χ c.G * u))) ≤
          CL * (C₀ * κ * Prelim.jap u ^ pW * Real.exp (σ' * u) +
            ηb * ahat κ (Eig.sigma χ c.G) u) + C₄ * κ ^ 2 ∧
        ‖Eig.ellFn χ c.G (c.w χ u) -
            runCoef χ c.G (c.pert0 χ) c.h u * Complex.exp (Eig.lam χ c.G * u)‖ ≤
          C₄ * κ ^ 2

theorem Cp_pos : 0 < Eig.Cp := by
  unfold Eig.Cp
  have := Real.pi_pos
  positivity

theorem sqrt_le_one_of {κ : ℝ} (hκ1 : κ ≤ 1) : Real.sqrt κ ≤ 1 := by
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_le_sqrt hκ1

/-- **The final step** (`05_single_ring.tex:1015-1020`, `:1078-1094`, `:1112-1122`). -/
theorem concl_of_core (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {s : ℕ} {σ' C₀ : ℝ} (hC₀ : 0 ≤ C₀) {c : RingConfig} {ubar : ℝ}
    (hc : c.Hyp ubar) (hG : c.G ∈ Icc (0 : ℝ) Gbar) (h0 : tsupport c.ring0 ⊆ annNm)
    {κ ηb δ₀ C₂ C₃ K u T' : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hηb : ηb ∈ Icc (0 : ℝ) 1)
    (hu : 0 ≤ u) (huT : u ≤ T') (hT' : 0 < T') (hT'u : T' ≤ ubar)
    (hmoveT : c.MovesRadially T' (a / 16))
    (hmove : c.MovesRadially u (C₂ * δ₀ + Real.sqrt κ))
    (hδsmall : C₂ * δ₀ + Real.sqrt κ ≤ a / 16)
    (hK : 0 ≤ K) (hKC : 6 * Eig.phiNormMax χ (Mact χ s - 2) + 3 * K ≤ C₂)
    (hC₃ : C₃ = (1 + Eig.Cp) * C₂)
    (hb1 : Sob.normH s (c.w χ u - modeFn χ c.G
        (runCoef χ c.G (c.pert0 χ) c.h u * Complex.exp (Eig.lam χ c.G * u))) ≤
      K * ahat κ (Eig.sigma χ c.G) u *
        (rhoHatOf (Eig.sigma χ c.G) σ' C₀ u + ahat κ (Eig.sigma χ c.G) u + Real.sqrt κ + ηb))
    (hX : ‖runCoef χ c.G (c.pert0 χ) c.h u * Complex.exp (Eig.lam χ c.G * u)‖ ≤
      ahat κ (Eig.sigma χ c.G) u * (3 + rhoHatOf (Eig.sigma χ c.G) σ' C₀ u))
    (hâ1 : ahat κ (Eig.sigma χ c.G) u ≤ 1) :
    c.ActiveConcl χ s σ' C₀ κ ηb δ₀ C₂ C₃ u := by
  set σ := Eig.sigma χ c.G with hσ
  set X := runCoef χ c.G (c.pert0 χ) c.h u * Complex.exp (Eig.lam χ c.G * u) with hXdef
  set A := ahat κ σ u with hA
  set R := rhoHatOf σ σ' C₀ u with hR
  set Cφ := Eig.phiNormMax χ (Mact χ s - 2) with hCφ
  have hA0 : 0 ≤ A := (ahat_pos hκ σ u).le
  have hR0 : 0 ≤ R := rhoHatOf_nonneg hC₀ u
  have hCφ0 : 0 ≤ Cφ := phiNormMax_nonneg χ hχ hN _
  have hsM : s ≤ Mact χ s - 2 := by have := add_four_le_Mact χ s; omega
  have hsq0 := Real.sqrt_nonneg κ
  have hsq1 : Real.sqrt κ ≤ 1 := sqrt_le_one_of hκ1
  have hB0 : 0 ≤ R + A + Real.sqrt κ + ηb := by linarith [hηb.1]
  have hKC2 : K ≤ C₂ := by linarith
  have hC₂0 : 0 ≤ C₂ := by linarith
  have hwX : Lin.MemXFn s (c.w χ u) :=
    memXFn_w_of_moves χ hχ hc hT' hT'u h0 hmoveT le_rfl s u ⟨hu, huT⟩
  have hb1' : Sob.normH s (c.w χ u - modeFn χ c.G X) ≤ C₂ * A * (R + A + Real.sqrt κ + ηb) :=
    hb1.trans (by gcongr)
  refine ⟨hmove, tsupport_ringPart_of_moves hc h0 hmove hδsmall u ⟨hu, le_rfl⟩, hb1', ?_, ?_⟩
  · have h1 := normH_le_modeFn χ hχ hN hG hsM hwX.1 X
    have e1 : K * A * (R + A + Real.sqrt κ + ηb) ≤ K * A * (R + 3) :=
      mul_le_mul_of_nonneg_left (by linarith [hηb.2]) (mul_nonneg hK hA0)
    have e2 : 2 * Cφ * ‖X‖ ≤ 2 * Cφ * (A * (3 + R)) :=
      mul_le_mul_of_nonneg_left hX (by positivity)
    have e3 : (K + 2 * Cφ) * (A * (3 + R)) ≤ (3 * K + 6 * Cφ) * (A * (1 + R)) := by
      have : 0 ≤ (K + 2 * Cφ) * (A * R) := by positivity
      nlinarith
    have e4 : (3 * K + 6 * Cφ) * (A * (1 + R)) ≤ C₂ * (A * (1 + R)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    calc Sob.normH s (c.w χ u) ≤ Sob.normH s (c.w χ u - modeFn χ c.G X) + 2 * Cφ * ‖X‖ := h1
      _ ≤ K * A * (R + A + Real.sqrt κ + ηb) + 2 * Cφ * (A * (3 + R)) := add_le_add hb1 e2
      _ ≤ C₂ * A * (1 + R) := by nlinarith
  · have hm := active_moment_bound χ hχ hN hG hwX.1 hwX.2.1 X
    have hCK : Eig.Cp * K ≤ (1 + Eig.Cp) * C₂ := by
      have := Cp_pos
      nlinarith
    have hAB : 0 ≤ A * (R + A + Real.sqrt κ + ηb) := mul_nonneg hA0 hB0
    have hpi := Real.pi_pos
    calc ‖2 * Real.pi * BS.pout 3 (c.w χ u) - 2 * Real.pi * Eig.pout χ c.G * X‖
        ≤ 2 * Real.pi * Eig.Cp * Sob.normH s (c.w χ u - modeFn χ c.G X) := hm
      _ ≤ 2 * Real.pi * Eig.Cp * (K * A * (R + A + Real.sqrt κ + ηb)) := by
          have := Cp_pos
          gcongr
      _ = 2 * Real.pi * (A * (R + A + Real.sqrt κ + ηb)) * (Eig.Cp * K) := by ring
      _ ≤ 2 * Real.pi * (A * (R + A + Real.sqrt κ + ηb)) * ((1 + Eig.Cp) * C₂) := by gcongr
      _ = 2 * Real.pi * C₃ * A * (R + A + Real.sqrt κ + ηb) := by rw [hC₃]; ring

/-- `‖c(u)e^{λu}‖ = ‖c(u)‖e^{σu}`. -/
theorem norm_coef_exp (χ : ℝ → ℝ) (G : ℝ) (z : ℂ) (u : ℝ) :
    ‖z * Complex.exp (Eig.lam χ G * u)‖ = ‖z‖ * Real.exp (Eig.sigma χ G * u) := by
  rw [norm_mul, norm_exp_lam]

/-- **The case `u ≤ t₁`** (`05_single_ring.tex:1001-1020`). -/
theorem concl_layer (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {s : ℕ} {σ' : ℝ} (hσ' : σ' ∈ Ioo (9 / 200 : ℝ) (Eig.sigb χ))
    {CL C₀ κL C₄ C₂ C₃ : ℝ} (hCL : 0 ≤ CL) (hC₀ : 1 ≤ C₀) (hC₄ : 0 ≤ C₄)
    (hLay : LayerProp χ s σ' CL C₀ κL C₄)
    (hC₂ : 6 * Eig.phiNormMax χ (Mact χ s - 2) + 3 * (CL + 1) ≤ C₂)
    (hC₃ : C₃ = (1 + Eig.Cp) * C₂)
    {c : RingConfig} {ubar : ℝ} (hc : c.Hyp ubar) (hG : c.G ∈ Icc (0 : ℝ) Gbar)
    {κ ηb δ₀ : ℝ} (hκ : 0 < κ) (hηb : ηb ∈ Icc (0 : ℝ) etaMax) (hδ₀ : 0 < δ₀) (hδ₀1 : δ₀ ≤ 1)
    (hInit : c.ActiveInit χ s C₀ κ) (hField : c.ActiveField χ s ubar C₀ κ ηb)
    (hCoef : c.ActiveCoef χ ubar C₀ κ)
    (hκL : κ ≤ κL) (hsm : C₄ * κ ≤ Real.sqrt κ / 2) (hsqa : Real.sqrt κ ≤ a / 32)
    (hC₂δ : C₂ * δ₀ ≤ a / 32)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) (min ubar (That (Eig.sigma χ c.G) δ₀ κ)))
    (hut : u ≤ tOne χ σ' C₀ c.G) :
    c.ActiveConcl χ s σ' C₀ κ ηb δ₀ C₂ C₃ u := by
  obtain ⟨hσb, hσbσ, -⟩ := sigma_facts χ hχ hN hG
  set σ := Eig.sigma χ c.G with hσ
  have hσ'σ : σ' < σ := hσ'.2.trans_le hσbσ
  have hσ'0 : 0 < σ' := by linarith [hσ'.1]
  have hσ0 : 0 < σ := by linarith
  obtain ⟨ha0, ha1⟩ := a_facts hχ
  have hηb' : ηb ∈ Icc (0 : ℝ) 1 := hηb
  have hu0 := hu.1
  have huU : u ≤ ubar := hu.2.trans (min_le_left _ _)
  have huT : u ≤ That σ δ₀ κ := hu.2.trans (min_le_right _ _)
  have ht1pos : 0 < tOne χ σ' C₀ c.G := (tOneOf_spec hσ'σ hC₀).1
  have hU0 : 0 < ubar := hc.T_pos
  have hT'0 : 0 < min ubar (tOne χ σ' C₀ c.G) := lt_min hU0 ht1pos
  have huT' : u ≤ min ubar (tOne χ σ' C₀ c.G) := le_min huU hut
  obtain ⟨hmv, hb, -⟩ := hLay c ubar κ ηb hc hG hκ hκL hηb hInit hField u ⟨hu0, huT'⟩
  obtain ⟨hmvT, -, -⟩ := hLay c ubar κ ηb hc hG hκ hκL hηb hInit hField _ ⟨hT'0.le, le_rfl⟩
  have hsq0 := Real.sqrt_nonneg κ
  have hC4a : C₄ * κ ≤ a / 16 := by linarith
  have hκ1 : κ ≤ 1 := by
    have h1 : Real.sqrt κ ≤ 1 := by linarith
    nlinarith [Real.sq_sqrt hκ.le]
  have hâ1 : ahat κ σ u ≤ 1 := (ahat_le_of_le_That hσ0 hδ₀ hκ huT).trans hδ₀1
  have hκâ : κ ≤ ahat κ σ u := by
    unfold ahat
    have : 1 ≤ Real.exp (σ * u) := Real.one_le_exp (by positivity)
    nlinarith
  have hC₂0 : 0 ≤ C₂ := by
    have := phiNormMax_nonneg χ hχ hN (Mact χ s - 2); linarith
  have hρ := rho_layer hσ'σ hC₀ hκ hu0 hut
  have hR0 : 0 ≤ rhoHatOf σ σ' C₀ u := rhoHatOf_nonneg (by linarith) u
  have hA0 : 0 ≤ ahat κ σ u := (ahat_pos hκ σ u).le
  apply concl_of_core χ hχ hN (by linarith : (0 : ℝ) ≤ C₀) hc hG hInit.2 hκ hκ1 hηb' hu0 huT'
    hT'0 (min_le_left _ _) (hmvT.mono hC4a) (hmv.mono ?_) (by linarith)
    (by linarith : (0 : ℝ) ≤ CL + 1) hC₂ hC₃ ?_ ?_ hâ1
  · have : 0 ≤ C₂ * δ₀ := mul_nonneg hC₂0 hδ₀.le
    linarith
  · have hsM : s ≤ Mact χ s - 2 := by have := add_four_le_Mact χ s; omega
    have hk2 : C₄ * κ ^ 2 ≤ Real.sqrt κ * ahat κ σ u := by
      calc C₄ * κ ^ 2 = (C₄ * κ) * κ := by ring
        _ ≤ (Real.sqrt κ / 2) * ahat κ σ u := by gcongr
        _ ≤ Real.sqrt κ * ahat κ σ u := by nlinarith
    calc Sob.normH s (c.w χ u - modeFn χ c.G
          (runCoef χ c.G (c.pert0 χ) c.h u * Complex.exp (Eig.lam χ c.G * u)))
        ≤ Sob.normH (Mact χ s - 2) (c.w χ u - modeFn χ c.G
          (runCoef χ c.G (c.pert0 χ) c.h u * Complex.exp (Eig.lam χ c.G * u))) :=
          normH_mono_order' hsM _
      _ ≤ CL * (C₀ * κ * Prelim.jap u ^ pW * Real.exp (σ' * u) + ηb * ahat κ σ u) +
            C₄ * κ ^ 2 := hb
      _ ≤ CL * (ahat κ σ u * rhoHatOf σ σ' C₀ u + ηb * ahat κ σ u) +
            Real.sqrt κ * ahat κ σ u := by gcongr
      _ ≤ (CL + 1) * ahat κ σ u *
            (rhoHatOf σ σ' C₀ u + ahat κ σ u + Real.sqrt κ + ηb) := by
          have : 0 ≤ ηb := hηb'.1
          nlinarith [mul_nonneg hA0 hR0, mul_nonneg hA0 hA0, mul_nonneg hA0 this,
            mul_nonneg hA0 hsq0, mul_nonneg hCL (mul_nonneg hA0 hA0),
            mul_nonneg hCL (mul_nonneg hA0 hsq0)]
  · have hcoef := hCoef u ⟨hu0, huU⟩
    rw [norm_coef_exp]
    have he : Real.exp (-(σ * u)) * Real.exp (σ * u) = 1 := by
      rw [← Real.exp_add]; simp
    have he' : 1 ≤ Real.exp (σ' * u) := Real.one_le_exp (by positivity)
    have hj := Prelim.jap_nonneg u
    have hCj : C₀ * κ * Prelim.jap u ^ pW ≤ ahat κ σ u * rhoHatOf σ σ' C₀ u := by
      refine le_trans ?_ hρ
      have : 0 ≤ C₀ * κ * Prelim.jap u ^ pW := by positivity
      nlinarith
    calc ‖runCoef χ c.G (c.pert0 χ) c.h u‖ * Real.exp (σ * u)
        ≤ κ * (2 + C₀ * Prelim.jap u ^ pW * Real.exp (-(σ * u))) * Real.exp (σ * u) := by
          gcongr
      _ = 2 * ahat κ σ u + C₀ * κ * Prelim.jap u ^ pW *
            (Real.exp (-(σ * u)) * Real.exp (σ * u)) := by unfold ahat; ring
      _ ≤ ahat κ σ u * (3 + rhoHatOf σ σ' C₀ u) := by
          rw [he, mul_one, mul_add]
          linarith

end NonUniqueEuler.OneRing.ActiveH
