import NonUniqueEuler.H.Sec5.Active.Core
import NonUniqueEuler.I.Sec5.Window
import NonUniqueEuler.I.Sec5.ReductionField
import NonUniqueEuler.I.Sec5.Active.Restart
import NonUniqueEuler.I.Sec5.Active.RunCoefShift

/-!
# Helpers for `thm:active`: the case `u > t₁` (restart and `lem:window`)

Helper of `P/Sec5/Active.lean` (fully proved, modulo the interface files it imports).
Manuscript `05_single_ring.tex:1022-1094`.

* `WindowProp`: the property of the constants of `lem:window` (`I/Sec5/Window.lean`);
* `moves_compose`: displacements add over the restart;
* `restart_field_bound`: the field hypothesis of `lem:window` for the restarted problem
  (Peetre's inequality and the definition of `t₁`, `05_single_ring.tex:1039-1045`);
* `coef_after`: `|c(v)| ≤ 3κ` for `v ≥ t₁` (`eq:A-t1` and (Coef));
* `concl_window`: the case `u > t₁`.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace NonUniqueEuler.OneRing.ActiveH

open RingData

/-- The property of the constants `(δ_W, κ_W, C_W)` of `lem:window` for `C♮ = Cn`. -/
def WindowProp (χ : ℝ → ℝ) (s : ℕ) (σ' Cn δW κW CW : ℝ) : Prop :=
  ∀ (c : RingConfig) (ubar κ₁ δ₀ ηb : ℝ), c.G ∈ Icc (0 : ℝ) Gbar →
    κ₁ ∈ Ioc (0 : ℝ) κW → δ₀ ∈ Ioc (0 : ℝ) δW → ηb ∈ Icc (0 : ℝ) 1 →
    ubar ∈ Ioc (0 : ℝ) (That (Eig.sigma χ c.G) δ₀ κ₁) → c.Hyp ubar →
    Sob.normH (Mact χ s - 2) (c.pert0 χ) ≤ Cn * κ₁ →
    tsupport c.ring0 ⊆ Sect.closedAnnulus ((7 / 8 - 1 / 64) * a) (5 / 4 + a / 64) →
    (∀ u ∈ Icc (0 : ℝ) ubar, normCk (Mact χ s) annN' (c.h u) ≤
      Cn * κ₁ * Prelim.jap u ^ pW + ηb * ahat κ₁ (Eig.sigma χ c.G) u) →
    (∀ u ∈ Icc (0 : ℝ) ubar, ‖runCoef χ c.G (c.pert0 χ) c.h u‖ ≤ Cn * κ₁) →
    ∀ u ∈ Icc (0 : ℝ) ubar,
      c.MovesRadially u (CW * δ₀ + CW * κ₁ * varsigma χ κ₁ ^ NW χ s) ∧
        CW * δ₀ + CW * κ₁ * varsigma χ κ₁ ^ NW χ s ≤ a / 32 ∧
        Sob.normH s (c.w χ u - modeFn χ c.G
            (runCoef χ c.G (c.pert0 χ) c.h u * Complex.exp (Eig.lam χ c.G * u))) ≤
          CW * ahat κ₁ (Eig.sigma χ c.G) u *
            (rhoOne (Eig.sigma χ c.G) σ' u + ahat κ₁ (Eig.sigma χ c.G) u +
              κ₁ * varsigma χ κ₁ ^ NW χ s + ηb)

/-- Radial displacements add over a restart at `t₁` (`05_single_ring.tex:1085-1090`). -/
theorem moves_compose {c c' : RingConfig} {T t₁ u δ₁ δ₂ : ℝ} (hc : c.Hyp T) (ht₁ : 0 ≤ t₁)
    (hring' : c'.ring0 = c.ringPart t₁)
    (hflow' : ∀ (τ : ℝ) (y : ℂ), c'.flow τ (c.flow t₁ y) = c.flow (t₁ + τ) y)
    (h1 : c.MovesRadially t₁ δ₁) (h2 : c'.MovesRadially (u - t₁) δ₂) (hδ₂ : 0 ≤ δ₂) :
    c.MovesRadially u (δ₂ + δ₁) := by
  intro y hy τ hτ
  by_cases hτt : τ ≤ t₁
  · exact (h1 y hy τ ⟨hτ.1, hτt⟩).trans (by linarith)
  · rw [not_le] at hτt
    have hz : c.flow t₁ y ∈ tsupport c'.ring0 := by
      rw [hring', (RingConfig.setting_tsupport_parts hc t₁).1]
      exact ⟨y, hy, rfl⟩
    have hflowτ : c.flow τ y = c'.flow (τ - t₁) (c.flow t₁ y) := by
      rw [hflow']; congr 1; ring
    have e2 := h2 _ hz (τ - t₁) ⟨by linarith, by linarith [hτ.2]⟩
    have e1 := h1 y hy t₁ ⟨ht₁, le_rfl⟩
    rw [hflowτ]
    calc |‖c'.flow (τ - t₁) (c.flow t₁ y)‖ - ‖y‖|
        = |(‖c'.flow (τ - t₁) (c.flow t₁ y)‖ - ‖c.flow t₁ y‖) + (‖c.flow t₁ y‖ - ‖y‖)| := by
          ring_nf
      _ ≤ |‖c'.flow (τ - t₁) (c.flow t₁ y)‖ - ‖c.flow t₁ y‖| + |‖c.flow t₁ y‖ - ‖y‖| :=
          abs_add_le _ _
      _ ≤ δ₂ + δ₁ := add_le_add e2 e1

/-- `â(t + v) = â₁(v)` with `κ₁ = â(t)`. -/
theorem ahat_add (κ σ t v : ℝ) : ahat κ σ (t + v) = ahat (ahat κ σ t) σ v := by
  unfold ahat
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- **The field of the restarted problem** (`05_single_ring.tex:1039-1045`): from
`‖h(t₁+v)‖ ≤ C₀κ⟨t₁+v⟩^p + η_b â(t₁+v)` one gets `‖h̃(v)‖ ≤ C♮κ₁⟨v⟩^p + η_b κ₁e^{σv}`,
`κ₁ = â(t₁)`. -/
theorem restart_field_bound {σ σ' C₀ κ ηb v Cn B : ℝ} (hσ : σ' < σ) (hσ'0 : 0 ≤ σ')
    (hC₀ : 1 ≤ C₀) (hκ : 0 < κ) (hCn : 1 ≤ Cn)
    (hB : B ≤ C₀ * κ * Prelim.jap (tOneOf σ σ' C₀ + v) ^ pW +
      ηb * ahat κ σ (tOneOf σ σ' C₀ + v)) :
    B ≤ Cn * ahat κ σ (tOneOf σ σ' C₀) * Prelim.jap v ^ pW +
      ηb * ahat (ahat κ σ (tOneOf σ σ' C₀)) σ v := by
  obtain ⟨htpos, hprop, -⟩ := tOneOf_spec hσ hC₀
  set t := tOneOf σ σ' C₀ with ht
  have hP := hprop t le_rfl
  have hpe := jap_add_pow_le t v
  have hjt := Prelim.jap_nonneg t
  have hjv := Prelim.jap_nonneg v
  have h2 := one_lt_two_rpow
  have hQ : (2 : ℝ) ^ ((pW : ℝ) / 2) * C₀ * Prelim.jap t ^ pW ≤ Real.exp (σ * t) := by
    have heq : (2 : ℝ) ^ ((pW : ℝ) / 2) * C₀ * Prelim.jap t ^ pW =
        ((2 : ℝ) ^ ((pW : ℝ) / 2) * C₀ * Prelim.jap t ^ pW * Real.exp (-((σ - σ') * t))) *
          Real.exp ((σ - σ') * t) := by
      rw [mul_assoc _ (Real.exp _), ← Real.exp_add]; simp
    rw [heq]
    calc _ ≤ 1 * Real.exp ((σ - σ') * t) := by gcongr
      _ ≤ Real.exp (σ * t) := by
          rw [one_mul]; apply Real.exp_le_exp.2; nlinarith
  have hA : C₀ * κ * Prelim.jap (t + v) ^ pW ≤ Cn * ahat κ σ t * Prelim.jap v ^ pW := by
    have hjv3 : 0 ≤ Prelim.jap v ^ pW := by positivity
    calc C₀ * κ * Prelim.jap (t + v) ^ pW
        ≤ C₀ * κ * ((2 : ℝ) ^ ((pW : ℝ) / 2) * Prelim.jap t ^ pW * Prelim.jap v ^ pW) := by
          gcongr
      _ = κ * Prelim.jap v ^ pW * ((2 : ℝ) ^ ((pW : ℝ) / 2) * C₀ * Prelim.jap t ^ pW) := by ring
      _ ≤ κ * Prelim.jap v ^ pW * Real.exp (σ * t) := by gcongr
      _ = 1 * ahat κ σ t * Prelim.jap v ^ pW := by unfold ahat; ring
      _ ≤ Cn * ahat κ σ t * Prelim.jap v ^ pW := by
          have := (ahat_pos hκ σ t).le
          gcongr
  rw [← ahat_add]
  linarith

/-- `|c(v)| ≤ 3κ` for `t₁ ≤ v ≤ ū` (`eq:A-t1` and (Coef), `05_single_ring.tex:953-956`). -/
theorem coef_after {χ : ℝ → ℝ} {c : RingConfig} {ubar C₀ κ σ' : ℝ}
    (hCoef : c.ActiveCoef χ ubar C₀ κ) (hσ : σ' < Eig.sigma χ c.G) (hσ'0 : 0 ≤ σ')
    (hC₀ : 1 ≤ C₀) (hκ : 0 < κ) {v : ℝ} (hv1 : tOne χ σ' C₀ c.G ≤ v) (hv2 : v ≤ ubar)
    (hv0 : 0 ≤ v) : ‖runCoef χ c.G (c.pert0 χ) c.h v‖ ≤ 3 * κ := by
  have h1 := hCoef v ⟨hv0, hv2⟩
  have h2 := small_after_t1 hσ hσ'0 hC₀ hv1
  calc _ ≤ κ * (2 + C₀ * Prelim.jap v ^ pW * Real.exp (-(Eig.sigma χ c.G * v))) := h1
    _ ≤ κ * (2 + 1) := by gcongr
    _ = 3 * κ := by ring

set_option maxHeartbeats 1000000 in
/-- **The case `u > t₁`** (`05_single_ring.tex:1022-1094`): restart at `t₁`, apply
`lem:window` with `κ₁ = â(t₁)`, and add the displacements. -/
theorem concl_window (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {s : ℕ} {σ' : ℝ} (hσ' : σ' ∈ Ioo (9 / 200 : ℝ) (Eig.sigb χ))
    {CL Cn δW κW CW C₀ κL C₄ C₂ C₃ : ℝ} (hCL : 0 ≤ CL) (hC₀ : 1 ≤ C₀) (hC₄ : 0 ≤ C₄)
    (hLay : LayerProp χ s σ' CL C₀ κL C₄) (hWin : WindowProp χ s σ' Cn δW κW CW)
    (hCW : 1 ≤ CW) (hκW1 : κW ≤ 1)
    (hCn : 6 * Eig.phiNormMax χ (Mact χ s - 2) + 2 * CL + 1 ≤ Cn) (hCn4 : 4 ≤ Cn)
    (hC₂ : 6 * Eig.phiNormMax χ (Mact χ s - 2) + 3 * (CW + 1) ≤ C₂)
    (hC₃ : C₃ = (1 + Eig.Cp) * C₂)
    {c : RingConfig} {ubar : ℝ} (hc : c.Hyp ubar) (hG : c.G ∈ Icc (0 : ℝ) Gbar)
    {κ ηb δ₀ : ℝ} (hκ : 0 < κ) (hηb : ηb ∈ Icc (0 : ℝ) etaMax) (hδ₀ : 0 < δ₀)
    (hδ₀W : δ₀ ≤ δW) (hδW1 : δW ≤ 1)
    (hInit : c.ActiveInit χ s C₀ κ) (hField : c.ActiveField χ s ubar C₀ κ ηb)
    (hCoef : c.ActiveCoef χ ubar C₀ κ)
    (hκL : κ ≤ κL) (hsm : C₄ * κ ≤ Real.sqrt κ / 2)
    (hsmφ : 2 * Eig.phiNormMax χ (Mact χ s - 2) * C₄ * κ ≤ Real.sqrt κ / 2)
    (hsqa : Real.sqrt κ ≤ a / 32) (hC₂δ : C₂ * δ₀ ≤ a / 32)
    (hκWκ : Real.exp (sigmaMax χ * tOneBar χ σ' C₀) * κ ≤ κW)
    (hvs : CW * (Real.exp (sigmaMax χ * tOneBar χ σ' C₀) * κ) * varsigma χ κ ^ NW χ s ≤
      Real.sqrt κ / 2)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) (min ubar (That (Eig.sigma χ c.G) δ₀ κ)))
    (hut : tOne χ σ' C₀ c.G < u) :
    c.ActiveConcl χ s σ' C₀ κ ηb δ₀ C₂ C₃ u := by
  obtain ⟨hσb, hσbσ, hσmax⟩ := sigma_facts χ hχ hN hG
  set σ := Eig.sigma χ c.G with hσ
  set t₁ := tOne χ σ' C₀ c.G with ht₁
  set Cφ := Eig.phiNormMax χ (Mact χ s - 2) with hCφ
  have hCφ0 : 0 ≤ Cφ := phiNormMax_nonneg χ hχ hN _
  have hσ'σ : σ' < σ := hσ'.2.trans_le hσbσ
  have hσ'0 : 0 < σ' := by linarith [hσ'.1]
  have hσ0 : 0 < σ := by linarith
  obtain ⟨ha0, ha1⟩ := a_facts hχ
  have hηb' : ηb ∈ Icc (0 : ℝ) 1 := hηb
  have hu0 := hu.1
  have huU : u ≤ ubar := hu.2.trans (min_le_left _ _)
  have huT : u ≤ That σ δ₀ κ := hu.2.trans (min_le_right _ _)
  obtain ⟨ht₁pos, -, -⟩ := tOneOf_spec hσ'σ hC₀
  have ht₁pos' : 0 < t₁ := ht₁pos
  have ht₁bar : t₁ ≤ tOneBar χ σ' C₀ := (active_tOne χ hχ hN hσ' hC₀ hG one_pos).1
  have ht₁U : t₁ < ubar := hut.trans_le huU
  have hupos : 0 < u := ht₁pos'.trans hut
  have hsq0 := Real.sqrt_nonneg κ
  have hκ1 : κ ≤ 1 := by
    have h1 : Real.sqrt κ ≤ 1 := by linarith
    calc κ = Real.sqrt κ * Real.sqrt κ := (Real.mul_self_sqrt hκ.le).symm
      _ ≤ 1 * 1 := mul_le_mul h1 h1 hsq0 zero_le_one
      _ = 1 := one_mul 1
  have hC4a : C₄ * κ ≤ a / 64 := by linarith
  have hC4k : C₄ * κ ≤ 1 := by linarith
  have hC₂0 : 0 ≤ C₂ := by linarith
  have hCWC₂ : CW ≤ C₂ := by linarith
  -- the layer at `t₁`
  obtain ⟨hmv1, hb1, hell1⟩ :=
    hLay c ubar κ ηb hc hG hκ hκL hηb hInit hField t₁ ⟨ht₁pos'.le, le_min ht₁U.le le_rfl⟩
  -- `κ₁ = â(t₁)`
  set κ₁ := ahat κ σ t₁ with hκ₁
  have hκ₁pos : 0 < κ₁ := ahat_pos hκ σ t₁
  have hκκ₁ : κ ≤ κ₁ := by
    rw [hκ₁, ahat]
    have : 1 ≤ Real.exp (σ * t₁) := Real.one_le_exp (by positivity)
    calc κ = κ * 1 := (mul_one κ).symm
      _ ≤ κ * Real.exp (σ * t₁) := mul_le_mul_of_nonneg_left this hκ.le
  have hC4k2 : C₄ * κ ^ 2 ≤ κ₁ := by
    calc C₄ * κ ^ 2 = (C₄ * κ) * κ := by ring
      _ ≤ 1 * κ := mul_le_mul_of_nonneg_right hC4k hκ.le
      _ = κ := one_mul κ
      _ ≤ κ₁ := hκκ₁
  have hσt : σ * t₁ ≤ sigmaMax χ * tOneBar χ σ' C₀ := by
    have hmax0 : 0 ≤ sigmaMax χ := by linarith
    calc σ * t₁ ≤ sigmaMax χ * t₁ := mul_le_mul_of_nonneg_right hσmax ht₁pos'.le
      _ ≤ sigmaMax χ * tOneBar χ σ' C₀ := mul_le_mul_of_nonneg_left ht₁bar hmax0
  have hκ₁le : κ₁ ≤ Real.exp (sigmaMax χ * tOneBar χ σ' C₀) * κ := by
    rw [hκ₁, ahat, mul_comm κ]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hσt) hκ.le
  have hκ₁W : κ₁ ≤ κW := hκ₁le.trans hκWκ
  -- the restart
  obtain ⟨c', hc', hG', hring', hh', hw', hpert', hflow'⟩ :=
    RingConfig.active_restart hc ht₁pos'.le ht₁U
  have hu'pos : 0 < u - t₁ := by linarith
  have hc'u : c'.Hyp (u - t₁) := hc'.mono hu'pos (by linarith)
  have hh'fun : c'.h = fun τ => c.h (t₁ + τ) := funext hh'
  have hpath : CkPathOn 0 annN' (Icc 0 ubar) c.h := (reduction_field hc).2 0
  set D := Eig.ellFn χ c.G (c.w χ t₁) -
    Complex.exp (Eig.lam χ c.G * t₁) * runCoef χ c.G (c.pert0 χ) c.h t₁ with hD
  have hDle : ‖D‖ ≤ C₄ * κ ^ 2 := by
    rw [hD, mul_comm (Complex.exp _)]; exact hell1
  have hshift : ∀ v : ℝ, 0 ≤ v → t₁ + v ≤ ubar →
      runCoef χ c'.G (c'.pert0 χ) c'.h v =
        Complex.exp (Eig.lam χ c.G * t₁) * runCoef χ c.G (c.pert0 χ) c.h (t₁ + v) + D := by
    intro v hv hvU
    rw [hG', hpert' χ, hh'fun]
    exact runCoef_shift χ hχ hN hG hpath ht₁pos'.le hv hvU (c.pert0 χ) (c.w χ t₁)
  have hc3 : ∀ v : ℝ, t₁ ≤ v → v ≤ ubar → ‖runCoef χ c.G (c.pert0 χ) c.h v‖ ≤ 3 * κ :=
    fun v hv1 hv2 => coef_after hCoef hσ'σ hσ'0.le hC₀ hκ hv1 hv2 (ht₁pos'.le.trans hv1)
  have hwt₁ : Lin.MemXFn (Mact χ s - 2) (c.w χ t₁) :=
    memXFn_w_of_moves χ hχ hc ht₁pos' ht₁U.le hInit.2 hmv1 (by linarith) _ t₁
      ⟨ht₁pos'.le, le_rfl⟩
  -- the hypotheses of `lem:window` for the restarted problem
  have hW1 : c'.G ∈ Icc (0 : ℝ) Gbar := by rw [hG']; exact hG
  have hW5 : u - t₁ ∈ Ioc (0 : ℝ) (That (Eig.sigma χ c'.G) δ₀ κ₁) := by
    rw [hG']
    refine ⟨hu'pos, ?_⟩
    rw [hκ₁, That_shift hσ0 hδ₀ hκ]
    linarith
  have hW7 : Sob.normH (Mact χ s - 2) (c'.pert0 χ) ≤ Cn * κ₁ := by
    rw [hpert' χ]
    have h1 := normH_le_modeFn χ hχ hN hG le_rfl hwt₁.1
      (runCoef χ c.G (c.pert0 χ) c.h t₁ * Complex.exp (Eig.lam χ c.G * t₁))
    have hX1 : ‖runCoef χ c.G (c.pert0 χ) c.h t₁ * Complex.exp (Eig.lam χ c.G * t₁)‖ ≤
        3 * κ₁ := by
      rw [norm_coef_exp]
      calc ‖runCoef χ c.G (c.pert0 χ) c.h t₁‖ * Real.exp (σ * t₁)
          ≤ (3 * κ) * Real.exp (σ * t₁) :=
            mul_le_mul_of_nonneg_right (hc3 t₁ le_rfl ht₁U.le) (Real.exp_pos _).le
        _ = 3 * κ₁ := by rw [hκ₁, ahat]; ring
    have hlay : C₀ * κ * Prelim.jap t₁ ^ pW * Real.exp (σ' * t₁) ≤ κ₁ := by
      exact rho_layer_t1 hσ'σ hC₀ hκ
    have hηâ : ηb * ahat κ σ t₁ ≤ κ₁ := by
      calc ηb * ahat κ σ t₁ ≤ 1 * κ₁ := mul_le_mul_of_nonneg_right hηb'.2 hκ₁pos.le
        _ = κ₁ := one_mul _
    have hCL1 : CL * (C₀ * κ * Prelim.jap t₁ ^ pW * Real.exp (σ' * t₁) + ηb * ahat κ σ t₁) ≤
        CL * (2 * κ₁) := mul_le_mul_of_nonneg_left (by linarith) hCL
    have hφ1 : 2 * Cφ * ‖runCoef χ c.G (c.pert0 χ) c.h t₁ * Complex.exp (Eig.lam χ c.G * t₁)‖ ≤
        2 * Cφ * (3 * κ₁) := mul_le_mul_of_nonneg_left hX1 (by positivity)
    have hCn1 : (6 * Cφ + 2 * CL + 1) * κ₁ ≤ Cn * κ₁ :=
      mul_le_mul_of_nonneg_right hCn hκ₁pos.le
    linarith
  have hW8 : tsupport c'.ring0 ⊆ Sect.closedAnnulus ((7 / 8 - 1 / 64) * a) (5 / 4 + a / 64) := by
    rw [hring']
    intro x hx
    obtain ⟨y, hy, -, hxy⟩ :=
      RingConfig.setting_movesRadially_tsupport hc hmv1 t₁ ⟨ht₁pos'.le, le_rfl⟩ x hx
    have hy' := hInit.2 hy
    rw [mem_annNm] at hy'
    rw [Sect.mem_closedAnnulus]
    have := abs_le.1 hxy
    constructor <;> linarith [this.1, this.2, hy'.1, hy'.2]
  have hW9 : ∀ v ∈ Icc (0 : ℝ) (u - t₁), normCk (Mact χ s) annN' (c'.h v) ≤
      Cn * κ₁ * Prelim.jap v ^ pW + ηb * ahat κ₁ (Eig.sigma χ c'.G) v := by
    intro v hv
    rw [hG', hh' v]
    have hb := field_bound hField (t₁ + v) ⟨by linarith [hv.1], by linarith [hv.2]⟩
    exact restart_field_bound hσ'σ hσ'0.le hC₀ hκ (by linarith) hb
  have hW10 : ∀ v ∈ Icc (0 : ℝ) (u - t₁), ‖runCoef χ c'.G (c'.pert0 χ) c'.h v‖ ≤ Cn * κ₁ := by
    intro v hv
    rw [hshift v hv.1 (by linarith [hv.2])]
    have h3 := hc3 (t₁ + v) (by linarith [hv.1]) (by linarith [hv.2])
    have hCn1 : 4 * κ₁ ≤ Cn * κ₁ := mul_le_mul_of_nonneg_right hCn4 hκ₁pos.le
    calc ‖Complex.exp (Eig.lam χ c.G * t₁) * runCoef χ c.G (c.pert0 χ) c.h (t₁ + v) + D‖
        ≤ ‖Complex.exp (Eig.lam χ c.G * t₁)‖ * ‖runCoef χ c.G (c.pert0 χ) c.h (t₁ + v)‖ +
            ‖D‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul]
      _ ≤ Real.exp (σ * t₁) * (3 * κ) + C₄ * κ ^ 2 := by
          rw [norm_exp_lam]
          gcongr
      _ ≤ 3 * κ₁ + κ₁ := by
          have e : Real.exp (σ * t₁) * (3 * κ) = 3 * κ₁ := by rw [hκ₁, ahat]; ring
          linarith
      _ ≤ Cn * κ₁ := by linarith
  obtain ⟨hWm, -, hWb⟩ := hWin c' (u - t₁) κ₁ δ₀ ηb hW1 ⟨hκ₁pos, hκ₁W⟩ ⟨hδ₀, hδ₀W⟩ hηb' hW5
    hc'u hW7 hW8 hW9 hW10 (u - t₁) ⟨hu'pos.le, le_rfl⟩
  rw [hshift (u - t₁) hu'pos.le (by linarith), hw' χ, hG'] at hWb
  have htu : t₁ + (u - t₁) = u := by ring
  rw [htu] at hWb
  -- identities
  have hâ : ahat κ₁ σ (u - t₁) = ahat κ σ u := by
    rw [hκ₁, ← ahat_add, htu]
  have hρ : rhoOne σ σ' (u - t₁) = rhoHatOf σ σ' C₀ u := by
    rw [rhoHatOf_of_le hut.le]; rfl
  have hXY : (Complex.exp (Eig.lam χ c.G * t₁) * runCoef χ c.G (c.pert0 χ) c.h u + D) *
        Complex.exp (Eig.lam χ c.G * ↑(u - t₁)) =
      runCoef χ c.G (c.pert0 χ) c.h u * Complex.exp (Eig.lam χ c.G * u) +
        D * Complex.exp (Eig.lam χ c.G * ↑(u - t₁)) := by
    have he : Complex.exp (Eig.lam χ c.G * t₁) * Complex.exp (Eig.lam χ c.G * ↑(u - t₁)) =
        Complex.exp (Eig.lam χ c.G * u) := by
      rw [← Complex.exp_add, ← mul_add]
      congr 2
      push_cast
      ring
    rw [add_mul, ← he]
    ring
  rw [hâ, hρ, hXY] at hWb
  -- the remaining small terms
  have hA0 : 0 ≤ ahat κ σ u := (ahat_pos hκ σ u).le
  have hR0 : 0 ≤ rhoHatOf σ σ' C₀ u := rhoHatOf_nonneg (by linarith) u
  obtain ⟨hvs0, hvsle⟩ := varsigma_le χ hσb hκ hκκ₁ (hκ₁W.trans hκW1)
  have hςb : CW * κ₁ * varsigma χ κ₁ ^ NW χ s ≤ Real.sqrt κ / 2 := by
    refine le_trans ?_ hvs
    have hp : varsigma χ κ₁ ^ NW χ s ≤ varsigma χ κ ^ NW χ s := pow_le_pow_left₀ hvs0 hvsle _
    have hp0 : 0 ≤ varsigma χ κ₁ ^ NW χ s := by positivity
    calc CW * κ₁ * varsigma χ κ₁ ^ NW χ s
        ≤ CW * (Real.exp (sigmaMax χ * tOneBar χ σ' C₀) * κ) * varsigma χ κ₁ ^ NW χ s := by
          gcongr
      _ ≤ CW * (Real.exp (sigmaMax χ * tOneBar χ σ' C₀) * κ) * varsigma χ κ ^ NW χ s := by
          have : 0 ≤ CW * (Real.exp (sigmaMax χ * tOneBar χ σ' C₀) * κ) := by positivity
          gcongr
  have hςb0 : 0 ≤ CW * κ₁ * varsigma χ κ₁ ^ NW χ s := by positivity
  have hY : ‖D * Complex.exp (Eig.lam χ c.G * ↑(u - t₁))‖ ≤ C₄ * κ * ahat κ σ u := by
    rw [norm_coef_exp]
    have he : Real.exp (σ * (u - t₁)) ≤ Real.exp (σ * u) := Real.exp_le_exp.2 (by
      rw [mul_sub]; linarith [mul_nonneg hσ0.le ht₁pos'.le])
    calc ‖D‖ * Real.exp (σ * (u - t₁)) ≤ C₄ * κ ^ 2 * Real.exp (σ * u) := by gcongr
      _ = C₄ * κ * ahat κ σ u := by unfold ahat; ring
  -- displacement and supports
  have hδsmall : C₂ * δ₀ + Real.sqrt κ ≤ a / 16 := by linarith
  have hmove0 := moves_compose hc ht₁pos'.le hring' hflow' hmv1 hWm (by positivity)
  have hmoveu : c.MovesRadially u (C₂ * δ₀ + Real.sqrt κ) := hmove0.mono (by
    have : CW * δ₀ ≤ C₂ * δ₀ := mul_le_mul_of_nonneg_right hCWC₂ hδ₀.le
    linarith)
  have hwu : Lin.MemXFn s (c.w χ u) :=
    memXFn_w_of_moves χ hχ hc hupos huU hInit.2 hmoveu hδsmall s u ⟨hu0, le_rfl⟩
  have hsM : s ≤ Mact χ s - 2 := by have := add_four_le_Mact χ s; omega
  apply concl_of_core χ hχ hN (by linarith : (0 : ℝ) ≤ C₀) hc hG hInit.2 hκ hκ1 hηb' hu0 le_rfl
    hupos huU (hmoveu.mono hδsmall) hmoveu hδsmall (by linarith : (0 : ℝ) ≤ CW + 1) hC₂ hC₃ ?_ ?_
    ((ahat_le_of_le_That hσ0 hδ₀ hκ huT).trans (hδ₀W.trans hδW1))
  · have h1 := normH_sub_modeFn_le χ hχ hN hG hsM hwu.1
      (runCoef χ c.G (c.pert0 χ) c.h u * Complex.exp (Eig.lam χ c.G * u))
      (D * Complex.exp (Eig.lam χ c.G * ↑(u - t₁)))
    have h2 : 2 * Cφ * ‖D * Complex.exp (Eig.lam χ c.G * ↑(u - t₁))‖ ≤
        ahat κ σ u * (Real.sqrt κ / 2) := by
      calc 2 * Cφ * ‖D * Complex.exp (Eig.lam χ c.G * ↑(u - t₁))‖
          ≤ 2 * Cφ * (C₄ * κ * ahat κ σ u) := mul_le_mul_of_nonneg_left hY (by positivity)
        _ = ahat κ σ u * (2 * Cφ * C₄ * κ) := by ring
        _ ≤ ahat κ σ u * (Real.sqrt κ / 2) := mul_le_mul_of_nonneg_left hsmφ hA0
    have h3 : CW * ahat κ σ u * (rhoHatOf σ σ' C₀ u + ahat κ σ u +
          κ₁ * varsigma χ κ₁ ^ NW χ s + ηb) ≤
        CW * ahat κ σ u * (rhoHatOf σ σ' C₀ u + ahat κ σ u + ηb) +
          ahat κ σ u * (Real.sqrt κ / 2) := by
      have : CW * ahat κ σ u * (κ₁ * varsigma χ κ₁ ^ NW χ s) ≤ ahat κ σ u * (Real.sqrt κ / 2) := by
        calc CW * ahat κ σ u * (κ₁ * varsigma χ κ₁ ^ NW χ s)
            = ahat κ σ u * (CW * κ₁ * varsigma χ κ₁ ^ NW χ s) := by ring
          _ ≤ ahat κ σ u * (Real.sqrt κ / 2) := mul_le_mul_of_nonneg_left hςb hA0
      calc CW * ahat κ σ u * (rhoHatOf σ σ' C₀ u + ahat κ σ u +
            κ₁ * varsigma χ κ₁ ^ NW χ s + ηb)
          = CW * ahat κ σ u * (rhoHatOf σ σ' C₀ u + ahat κ σ u + ηb) +
            CW * ahat κ σ u * (κ₁ * varsigma χ κ₁ ^ NW χ s) := by ring
        _ ≤ _ := by linarith [this]
    have h4 : CW * ahat κ σ u * (rhoHatOf σ σ' C₀ u + ahat κ σ u + ηb) +
          ahat κ σ u * Real.sqrt κ ≤
        (CW + 1) * ahat κ σ u *
          (rhoHatOf σ σ' C₀ u + ahat κ σ u + Real.sqrt κ + ηb) := by
      have := hηb'.1
      have e : 0 ≤ ahat κ σ u * (rhoHatOf σ σ' C₀ u + ahat κ σ u + ηb) := by positivity
      have e' : 0 ≤ CW * (ahat κ σ u * Real.sqrt κ) := by positivity
      have eq : (CW + 1) * ahat κ σ u *
          (rhoHatOf σ σ' C₀ u + ahat κ σ u + Real.sqrt κ + ηb) =
          CW * ahat κ σ u * (rhoHatOf σ σ' C₀ u + ahat κ σ u + ηb) +
            ahat κ σ u * Real.sqrt κ +
            (ahat κ σ u * (rhoHatOf σ σ' C₀ u + ahat κ σ u + ηb) +
              CW * (ahat κ σ u * Real.sqrt κ)) := by ring
      rw [eq]
      linarith
    linarith
  · rw [norm_coef_exp]
    have h3 := hc3 u hut.le huU
    have := Real.exp_pos (σ * u)
    calc ‖runCoef χ c.G (c.pert0 χ) c.h u‖ * Real.exp (σ * u) ≤ 3 * κ * Real.exp (σ * u) := by
          gcongr
      _ = 3 * ahat κ σ u := by unfold ahat; ring
      _ ≤ ahat κ σ u * (3 + rhoHatOf σ σ' C₀ u) := by
          rw [mul_add]; linarith [mul_nonneg hA0 hR0]

end NonUniqueEuler.OneRing.ActiveH
