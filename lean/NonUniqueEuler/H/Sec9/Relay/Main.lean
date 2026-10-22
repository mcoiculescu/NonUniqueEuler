import NonUniqueEuler.H.Sec9.Relay.Quiet
import NonUniqueEuler.H.Sec9.Relay.Active
import NonUniqueEuler.H.Sec9.Relay.Real

/-!
# Helpers for `prop:relay`: `maj^in_j(τ)` after the activation of ring `j+1`

Helper file of `P/Sec9/Relay.lean` (`09_relay.tex:500-590`). Everything here is proved.

`majIn_after_act`: if `τ^act = A_jt♯_{j+1} < τ ≤ t̄♯_j`, then `maj^in_j(τ)` is at most half the
right side of `eq:relay`. The Duhamel integral is split at `τ^act` and `b = min(τ, τ^sat)`:
* `I₁` (quiet phase of ring `j+1`): `e^{σ_j(τ-τ^act)}maj^in_j(τ^act)`, bounded by (o) at `τ^act`,
  `maj_{j+1}(t̄♯_{j+1}) ≤ K₁κ` ((H4)) and `eq:relay-id` (`phase1_exp`); `0` if `j+1 = n`;
* `I₂` (active phase): `active_pointwise`, `phase2_pt`, `phase2_int`;
* `I₃` (debris phase): `debris_pointwise`, length `≤ T_pin/μ ≤ T_pin`;
and the sum is `final_alg`.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

namespace RelayH

open RingData Datum

variable {S : Standing} {C₀ K₁ : ℝ} {j : ℕ} {τ : ℝ}

/-- `γ_jσ_{j+1} ≥ σ_j/μ` and `γ_jσ_{j+1} ≥ σ'` (`γ_j = max(σ_j, μσ')/(μσ_{j+1})`). -/
theorem gamma_bounds (h : S.RelayHyp C₀ K₁ j τ) (hS : S.Holds) :
    S.P.sigma j / S.P.μ ≤ S.gammaJ j * S.P.sigma (j + 1) ∧
      S.σ' ≤ S.gammaJ j * S.P.sigma (j + 1) := by
  have hμ : 0 < S.P.μ := by linarith [hS.one_lt_μ]
  have hσk := sigma_pos S hS (succ_mem h)
  have he : S.gammaJ j * S.P.sigma (j + 1) = max (S.P.sigma j) (S.P.μ * S.σ') / S.P.μ := by
    unfold Standing.gammaJ
    field_simp
  rw [he]
  refine ⟨div_le_div_of_nonneg_right (le_max_left _ _) hμ.le, ?_⟩
  rw [le_div_iff₀ hμ, mul_comm]
  exact le_max_right _ _

/-- **`maj^in_j(τ)` after the activation of ring `j+1`** (`09_relay.tex:500-590`). -/
theorem majIn_after_act (h : S.RelayHyp C₀ K₁ j τ) (hS : S.Holds) (hDet : S.Det)
    (hC₀ : 1 ≤ C₀) (hK₁ : 0 < K₁) (hact : S.P.A j * S.P.tsh (j + 1) < τ) :
    S.majIn j τ ≤ S.CM * S.P.eps j * Real.exp (S.P.xk j * S.P.Tpin) *
      (4 * S.C2 * S.P.δ₀ / (S.sigb * (S.P.μ - 1)) + CD S.P.Tpin + S.XiNext C₀ K₁ j) := by
  -- notation and signs
  have hA := hS.valid.A_pos j
  have hμ1 := hS.one_lt_μ
  have hμ : 0 < S.P.μ := by linarith
  have hσj := sigma_pos S hS (j_mem h)
  have hσk := sigma_pos S hS (succ_mem h)
  have hsb := sigb_pos S hS
  have hsbk := sigb_le_sigma S hS (succ_mem h)
  have hgap := gap h hS hDet
  obtain ⟨hγ1, hγ2⟩ := gamma_bounds h hS
  have hσ' : 0 ≤ S.σ' := by linarith [hS.σ'_gt]
  obtain ⟨hκ, hκδ⟩ := ksh_mem h
  have hδ := hS.δ₀_pos
  have hTp := hS.Tpin_pos
  have hTh := That_nonneg h hS
  have hC2 := one_le_C2 S
  have hCQ := CQ_nonneg S
  have hCM := CM_pos S
  have heps := hS.valid.eps_pos j
  have hCMe : 0 ≤ S.CM * S.P.eps j := mul_nonneg hCM.le heps.le
  have hCact : 0 ≤ S.Cact C₀ := le_trans (by linarith) (OneRing.le_Cact S.P.χ S.σ' C₀)
  set κ := S.P.ksh (j + 1) with hκdef
  set Th := S.P.That (j + 1) with hThdef
  set L := Real.log (S.P.δ₀ / κ) with hL
  set Y := (κ / S.P.δ₀) ^ (1 - S.gammaJ j) with hY
  set E := Real.exp (S.P.xk j * S.P.Tpin) with hE
  set τa := S.P.A j * S.P.tsh (j + 1) with hτa
  have hτa0 : 0 ≤ τa := mul_nonneg hA.le (tsh_succ_nonneg h hS)
  have hτs : S.P.A j * S.P.T (j + 1) = τa + Th / S.P.μ := tauSat_eq h hS
  have htash : S.P.tash j = S.P.A j * S.P.T (j + 1) + S.P.Tpin / S.P.μ := tash_eq h hS
  have hτle : τ ≤ τa + Th / S.P.μ + S.P.Tpin / S.P.μ := by
    have := h.τ_le; rw [htash, hτs] at this; exact this
  have hL0 : 0 ≤ L := Real.log_nonneg (by rw [le_div_iff₀ hκ, one_mul]; exact hκδ.le)
  have hσkTh : S.P.sigma (j + 1) * Th = L := by
    rw [hThdef, Approx.That, ← mul_assoc, mul_inv_cancel₀ hσk.ne', one_mul]
  have hκe : κ * Real.exp (S.P.sigma (j + 1) * Th) = S.P.δ₀ := by
    rw [hσkTh, hL, Real.exp_log (div_pos hδ hκ)]
    field_simp
  have hκγ : κ * Real.exp (S.gammaJ j * S.P.sigma (j + 1) * Th) = S.P.δ₀ * Y := by
    rw [mul_assoc, hσkTh, hL, hY]
    exact mul_exp_log_eq hκ hδ
  have hY0 : 0 ≤ Y := Real.rpow_nonneg (div_pos hκ hδ).le _
  have hEeq : E = Real.exp (S.P.sigma j / S.P.μ * S.P.Tpin) := rfl
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  -- the integrand
  set F : ℝ → ℝ := fun v => Real.exp (S.P.sigma j * (τ - v)) * S.etaIn j v with hF
  have hmaj : S.majIn j τ = ∫ v in (0 : ℝ)..τ, F v := rfl
  have hτ0 : 0 ≤ τ := h.τ_nonneg
  have hFint : IntervalIntegrable F volume 0 τ := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hτ0]
    exact ((by fun_prop : Continuous fun v : ℝ => Real.exp (S.P.sigma j * (τ - v))).continuousOn).mul
      (eta_cont_j h hS).1
  set b := min τ (S.P.A j * S.P.T (j + 1)) with hb
  have hτab : τa ≤ b := le_min hact.le (by rw [hτs]; have := div_nonneg hTh hμ.le; linarith)
  have hbτ : b ≤ τ := min_le_left _ _
  rw [hmaj, integral_split3 hτa0 hτab hbτ hFint]
  -- `I₁`
  have hI₁ : (∫ v in (0 : ℝ)..τa, F v) ≤
      S.CM * S.P.eps j * (2 * S.CQ / (S.sigb * (S.P.μ - 1)) + 1) * E * K₁ * (S.P.δ₀ * Y) := by
    have hshift : (∫ v in (0 : ℝ)..τa, F v) =
        Real.exp (S.P.sigma j * (τ - τa)) * S.majIn j τa :=
      integral_exp_shift (S.P.sigma j) τ τa (S.etaIn j)
    rw [hshift]
    have hRHS0 : 0 ≤ S.CM * S.P.eps j * (2 * S.CQ / (S.sigb * (S.P.μ - 1)) + 1) * E * K₁ *
        (S.P.δ₀ * Y) := by
      have : 0 ≤ 2 * S.CQ / (S.sigb * (S.P.μ - 1)) + 1 := by
        have : 0 < S.sigb * (S.P.μ - 1) := mul_pos hsb (by linarith)
        positivity
      positivity
    rcases lt_or_eq_of_le (Nat.succ_le_of_lt h.lt_n) with hjn | hjn
    · -- `j + 1 < n`: (o) at `τ^act` and (H4)
      have ho := quiet_o h hS hDet hjn (τ' := τa) ⟨hτa0, le_min hact.le le_rfl⟩
      have hμτa : S.P.μ * τa = S.P.tash (j + 1) := by
        rw [hτa, Approx.tash_def, A_succ S.P h.one_le]; ring
      have hK := (h.h4 (by rw [lt_div_iff₀ hA, mul_comm]; exact hact)).1
      rw [hμτa] at ho
      have hCr : 0 ≤ S.Crelay * S.P.eps j := by
        unfold Standing.Crelay
        have : 0 < S.sigb * (S.P.μ - 1) := mul_pos hsb (by linarith)
        positivity
      have h1 : S.majIn j τa ≤ S.Crelay * S.P.eps j * (K₁ * κ) :=
        ho.trans (mul_le_mul_of_nonneg_left hK hCr)
      have h2 := phase1_exp (Th := Th) (Tp := S.P.Tpin) hμ hσj.le hκ hTh hγ1 hκγ hτle
      have hCreq : S.Crelay * S.P.eps j =
          S.CM * S.P.eps j * (2 * S.CQ / (S.sigb * (S.P.μ - 1)) + 1) := by
        unfold Standing.Crelay; ring
      calc Real.exp (S.P.sigma j * (τ - τa)) * S.majIn j τa
          ≤ Real.exp (S.P.sigma j * (τ - τa)) * (S.Crelay * S.P.eps j * (K₁ * κ)) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = S.Crelay * S.P.eps j * K₁ * (κ * Real.exp (S.P.sigma j * (τ - τa))) := by ring
        _ ≤ S.Crelay * S.P.eps j * K₁ *
              (Real.exp (S.P.sigma j / S.P.μ * S.P.Tpin) * (S.P.δ₀ * Y)) :=
            mul_le_mul_of_nonneg_left h2 (mul_nonneg hCr hK₁.le)
        _ = _ := by rw [hCreq, ← hEeq]; ring
    · -- `j + 1 = n`: `τ^act = 0`
      have hjn' : j + 1 = S.P.n := hjn
      have h0 : τa = 0 := by rw [hτa, hjn', S.P.tsh_n, mul_zero]
      rw [h0, S.majIn_zero, mul_zero]
      exact hRHS0
  -- `I₂`
  set D := 2 * S.C2 * S.Cact C₀ + C₀ with hD
  have hI₂ : (∫ v in τa..b, F v) ≤ S.CM * S.P.eps j * E *
      (2 * S.C2 * S.P.δ₀ / (S.P.μ * S.P.sigma (j + 1) - S.P.sigma j) +
        D * S.P.δ₀ * Y * Prelim.jap Th ^ 3 * Th) := by
    have hc : 0 < S.P.μ * S.P.sigma (j + 1) - S.P.sigma j := by
      have : 0 < S.sigb * (S.P.μ - 1) := mul_pos hsb (by linarith)
      linarith
    have hK0 : 0 ≤ D * S.P.δ₀ * Y * Prelim.jap Th ^ 3 := by
      have : 0 ≤ D := by positivity
      have := pow_nonneg (Prelim.jap_nonneg Th) 3
      positivity
    have hint := phase2_int (F := F) (τa := τa) (b := b) (τs := τa + Th / S.P.μ)
      (c := S.P.μ * S.P.sigma (j + 1) - S.P.sigma j) (A₀ := S.CM * S.P.eps j * E)
      (B₀ := 2 * S.C2 * S.P.δ₀) (K := D * S.P.δ₀ * Y * Prelim.jap Th ^ 3) hτab
      (by rw [hb, ← hτs]; exact min_le_right _ _) hc (mul_nonneg hCMe hE0) (by positivity) hK0
      (fun v hv => by
        have hpt := active_pointwise h hS hC₀ hact hv
        have hv' : v ∈ Icc τa (τa + Th / S.P.μ) := ⟨hv.1, by rw [← hτs]; exact hv.2.trans (min_le_right _ _)⟩
        have := phase2_pt (σj := S.P.sigma j) (σk := S.P.sigma (j + 1)) (μ := S.P.μ)
          (σ' := S.σ') (κ := κ) (δ₀ := S.P.δ₀) (Th := Th) (γ := S.gammaJ j) (Y := Y)
          (Tp := S.P.Tpin) (τa := τa) (τ := τ) (v := v) (E := S.etaIn j v)
          (CMe := S.CM * S.P.eps j) (C2 := S.C2) (Cact := S.Cact C₀) (C0 := C₀)
          hμ hσj.le hκ hσ' hγ1 hγ2 hκe hκγ hv' hτle hCMe (by linarith) hCact (by linarith) hpt
        simp only [hF]
        rw [← hEeq] at this
        calc Real.exp (S.P.sigma j * (τ - v)) * S.etaIn j v ≤ _ := this
          _ = _ := by ring)
    refine hint.trans ?_
    have hlen : b - τa ≤ Th := by
      have : b - τa ≤ Th / S.P.μ := by
        have : b ≤ τa + Th / S.P.μ := by rw [hb, hτs]; exact min_le_right _ _
        linarith
      exact this.trans (div_le_self hTh hμ1.le)
    have := mul_le_mul_of_nonneg_left hlen hK0
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCMe hE0)
    linarith
  -- `I₃`
  have hI₃ : (∫ v in b..τ, F v) ≤ S.CM * S.P.eps j * E * CD S.P.Tpin := by
    have hCD0 : 0 ≤ CD S.P.Tpin := by
      unfold CD
      have := Cstar_nonneg
      positivity
    rcases le_or_gt τ (S.P.A j * S.P.T (j + 1)) with hτs' | hτs'
    · rw [hb, min_eq_left hτs', intervalIntegral.integral_same]
      exact mul_nonneg (mul_nonneg hCMe hE0) hCD0
    · rw [hb, min_eq_right hτs'.le]
      have hC0 : 0 ≤ S.CM * S.P.eps j * E * (2 + 2 * Cstar * S.P.Tpin) ^ 3 := by
        have := Cstar_nonneg
        positivity
      have hle := integral_le_mul_of_le hτs'.le hC0 fun v hv => by
        show Real.exp (S.P.sigma j * (τ - v)) * S.etaIn j v ≤ _
        have hd := debris_pointwise h hS hv
        have he : Real.exp (S.P.sigma j * (τ - v)) ≤ E := by
          rw [hEeq, Real.exp_le_exp]
          have : τ - v ≤ S.P.Tpin / S.P.μ := by
            have := h.τ_le; rw [htash] at this; linarith [hv.1]
          calc S.P.sigma j * (τ - v) ≤ S.P.sigma j * (S.P.Tpin / S.P.μ) :=
                mul_le_mul_of_nonneg_left this hσj.le
            _ = S.P.sigma j / S.P.μ * S.P.Tpin := by ring
        have hη0 := S.etaIn_nonneg j v
        have hb0 : 0 ≤ S.CM * S.P.eps j * (2 + 2 * Cstar * S.P.Tpin) ^ 3 := by
          have := Cstar_nonneg
          positivity
        calc Real.exp (S.P.sigma j * (τ - v)) * S.etaIn j v
            ≤ E * (S.CM * S.P.eps j * (2 + 2 * Cstar * S.P.Tpin) ^ 3) :=
              mul_le_mul he hd hη0 hE0
          _ = S.CM * S.P.eps j * E * (2 + 2 * Cstar * S.P.Tpin) ^ 3 := by ring
      refine hle.trans ?_
      have hlen : τ - S.P.A j * S.P.T (j + 1) ≤ S.P.Tpin := by
        have : τ - S.P.A j * S.P.T (j + 1) ≤ S.P.Tpin / S.P.μ := by
          have := h.τ_le; rw [htash] at this; linarith
        exact this.trans (div_le_self hTp.le hμ1.le)
      have := mul_le_mul_of_nonneg_right hlen hC0
      calc (τ - S.P.A j * S.P.T (j + 1)) * (S.CM * S.P.eps j * E * (2 + 2 * Cstar * S.P.Tpin) ^ 3)
          ≤ S.P.Tpin * (S.CM * S.P.eps j * E * (2 + 2 * Cstar * S.P.Tpin) ^ 3) := this
        _ = S.CM * S.P.eps j * E * CD S.P.Tpin := by unfold CD; ring
  -- the sum
  have hx : 0 < S.sigb * (S.P.μ - 1) := mul_pos hsb (by linarith)
  have hZ : 0 < S.sigb * min 1 S.sigb ^ 3 := mul_pos hsb (pow_pos (lt_min one_pos hsb) 3)
  have hThJ : Prelim.jap Th ^ 3 * Th ≤ Prelim.jap L ^ (3 + 1) / (S.sigb * min 1 S.sigb ^ 3) := by
    have := That_jap_le hL0 hsb hsbk
    rw [mul_comm]
    rw [hThdef, Approx.That]
    exact this
  have hJ4 : 1 ≤ Prelim.jap L ^ (3 + 1) := one_le_pow₀ (Prelim.one_le_jap L)
  have hfin := final_alg (I₁ := ∫ v in (0 : ℝ)..τa, F v) (I₂ := ∫ v in τa..b, F v)
    (I₃ := ∫ v in b..τ, F v) (CMe := S.CM * S.P.eps j) (E := E) (K₁ := K₁) (CQ := S.CQ)
    (C2 := S.C2) (D := D) (Z := S.sigb * min 1 S.sigb ^ 3) (x := S.sigb * (S.P.μ - 1))
    (c := S.P.μ * S.P.sigma (j + 1) - S.P.sigma j) (δ₀ := S.P.δ₀) (Y := Y)
    (J3 := Prelim.jap Th ^ 3) (J4 := Prelim.jap L ^ (3 + 1)) (Th := Th) (CDT := CD S.P.Tpin)
    hCMe hE0 hK₁ (by linarith) (by positivity) hZ hx hgap hδ hY0 hJ4 hThJ
    (by have := hI₁; linarith) hI₂ hI₃
  refine hfin.trans (le_of_eq ?_)
  unfold Standing.XiNext Standing.CXi
  rw [← hκdef, ← hL, ← hY]

end RelayH

end Relay

end NonUniqueEuler
