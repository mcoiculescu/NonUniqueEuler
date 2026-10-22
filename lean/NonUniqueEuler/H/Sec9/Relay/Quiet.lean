import NonUniqueEuler.H.Sec9.Relay.Setup
import NonUniqueEuler.I.Sec9.Detuning
import NonUniqueEuler.I.Sec9.TransferStep
import NonUniqueEuler.I.Sec5.Majorant

/-!
# Helpers for `prop:relay`: `maj_j ≤ 2maj^in_j` and item (o)

Helper file of `P/Sec9/Relay.lean` (`09_relay.tex:460-498`). Everything here is proved.

* `maj_le_two_of`, `maj_le_two_majIn`: `maj_j ≤ maj^in_j + θ_jτ'maj_j(τ') ≤ maj^in_j + maj_j/2`
  on `[0,τ]` ((H2), (M1));
* `quiet_bound`, `quiet_o`: `eq:relay-quiet` (item (o)) from `lem:transfer-step`(1) with
  `s' = s_h`, `thm:quiet`(c) for ring `j+1` ((H3)), (M1) for `maj_{j+1}` and `lem:detuning`
  (`μσ_{j+1} - σ_j ≥ σ_b(μ-1)/2`); the substitution `v' = μv` is
  `intervalIntegral.integral_comp_mul_left`.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

namespace RelayH

open RingData Datum

/-! ### Abstract forms -/

/-- **`maj ≤ 2 maj^in`** (`09_relay.tex:460-470`): if `η = η^in + η^out` with both parts
continuous and nonnegative on `[0,τ]`, `η^out ≤ θ maj` on `[0,τ]`, `θτ ≤ 1/2`, and (M1) holds at
`τ' ∈ [0,τ]`, then `maj(τ') ≤ 2 maj^in(τ')`. -/
theorem maj_le_two_of {σ θ τ τ' : ℝ} {ηi ηo : ℝ → ℝ} (hτ' : τ' ∈ Icc (0 : ℝ) τ)
    (hci : ContinuousOn ηi (Icc 0 τ)) (hco : ContinuousOn ηo (Icc 0 τ))
    (h0i : ∀ v, 0 ≤ ηi v) (h0o : ∀ v, 0 ≤ ηo v)
    (hM1 : ∀ v ∈ Icc (0 : ℝ) τ', Real.exp (σ * (τ' - v)) * OneRing.maj σ (fun v => ηi v + ηo v) v ≤
      OneRing.maj σ (fun v => ηi v + ηo v) τ')
    (hθ : ∀ v ∈ Icc (0 : ℝ) τ, ηo v ≤ θ * OneRing.maj σ (fun v => ηi v + ηo v) v)
    (hθτ : θ * τ ≤ 1 / 2) :
    OneRing.maj σ (fun v => ηi v + ηo v) τ' ≤ 2 * OneRing.maj σ ηi τ' := by
  set m := OneRing.maj σ (fun v => ηi v + ηo v) τ' with hm
  have hτ'0 : 0 ≤ τ' := hτ'.1
  have hsub : Icc (0 : ℝ) τ' ⊆ Icc 0 τ := Icc_subset_Icc le_rfl hτ'.2
  have hmaj0 : ∀ v ∈ Icc (0 : ℝ) τ, 0 ≤ OneRing.maj σ (fun v => ηi v + ηo v) v := fun v hv =>
    maj_nonneg_of hv.1 fun x _ => add_nonneg (h0i x) (h0o x)
  have hm0 : 0 ≤ m := hmaj0 τ' hτ'
  set θ' := max θ 0 with hθ'
  have hθ'0 : 0 ≤ θ' := le_max_right _ _
  have hθ'τ : θ' * τ' ≤ 1 / 2 := by
    rcases le_total θ 0 with hθ0 | hθ0
    · rw [hθ', max_eq_right hθ0, zero_mul]; norm_num
    · rw [hθ', max_eq_left hθ0]
      exact (mul_le_mul_of_nonneg_left hτ'.2 hθ0).trans hθτ
  -- integrability of the two parts
  have hexp : Continuous fun v : ℝ => Real.exp (σ * (τ' - v)) := by fun_prop
  have hii : IntervalIntegrable (fun v => Real.exp (σ * (τ' - v)) * ηi v) volume 0 τ' := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hτ'0]
    exact hexp.continuousOn.mul (hci.mono hsub)
  have hio : IntervalIntegrable (fun v => Real.exp (σ * (τ' - v)) * ηo v) volume 0 τ' := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hτ'0]
    exact hexp.continuousOn.mul (hco.mono hsub)
  have hsplit : m = OneRing.maj σ ηi τ' + ∫ v in (0 : ℝ)..τ', Real.exp (σ * (τ' - v)) * ηo v := by
    rw [hm, OneRing.maj, OneRing.maj, ← intervalIntegral.integral_add hii hio]
    refine intervalIntegral.integral_congr fun v _ => ?_
    ring
  -- the outer part
  have hout : (∫ v in (0 : ℝ)..τ', Real.exp (σ * (τ' - v)) * ηo v) ≤ (τ' - 0) * (θ' * m) := by
    refine integral_le_mul_of_le hτ'0 (mul_nonneg hθ'0 hm0) fun v hv => ?_
    have hE := Real.exp_pos (σ * (τ' - v))
    have hmv := hmaj0 v (hsub hv)
    have h1 : ηo v ≤ θ' * OneRing.maj σ (fun v => ηi v + ηo v) v :=
      (hθ v (hsub hv)).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hmv)
    calc Real.exp (σ * (τ' - v)) * ηo v
        ≤ Real.exp (σ * (τ' - v)) * (θ' * OneRing.maj σ (fun v => ηi v + ηo v) v) :=
          mul_le_mul_of_nonneg_left h1 hE.le
      _ = θ' * (Real.exp (σ * (τ' - v)) * OneRing.maj σ (fun v => ηi v + ηo v) v) := by ring
      _ ≤ θ' * m := mul_le_mul_of_nonneg_left (hM1 v hv) hθ'0
  rw [sub_zero] at hout
  have hhalf : τ' * (θ' * m) ≤ m / 2 := by
    have : τ' * (θ' * m) = (θ' * τ') * m := by ring
    rw [this]
    nlinarith
  linarith

/-- **`eq:relay-quiet`, abstract form** (`09_relay.tex:470-492`): if
`η^in_j(v) ≤ C(C_Q maj_{j+1}(μv) + η_{j+1}(μv))` on `[0,τ']`, (M1) holds for `maj_{j+1}` on
`[0,μτ']`, `η_{j+1}` is continuous and nonnegative, and `μσ_{j+1} - σ_j ≥ c₀ > 0`, then
`maj^in_j(τ') ≤ C(C_Q/c₀ + 1) maj_{j+1}(μτ')`. -/
theorem quiet_bound {σj σk μ CMe CQ c0 τ' : ℝ} {etaI etaN : ℝ → ℝ}
    (hμ : 1 ≤ μ) (hτ' : 0 ≤ τ') (hgap : c0 ≤ μ * σk - σj) (hc0 : 0 < c0)
    (hCMe : 0 ≤ CMe) (hCQ : 0 ≤ CQ)
    (hcont : ContinuousOn etaN (Icc 0 (μ * τ'))) (hN0 : ∀ x, 0 ≤ etaN x)
    (hM1 : ∀ v ∈ Icc (0 : ℝ) τ',
      Real.exp (σk * (μ * τ' - μ * v)) * OneRing.maj σk etaN (μ * v) ≤
        OneRing.maj σk etaN (μ * τ'))
    (hpt : ∀ v ∈ Icc (0 : ℝ) τ',
      etaI v ≤ CMe * (CQ * OneRing.maj σk etaN (μ * v) + etaN (μ * v))) :
    OneRing.maj σj etaI τ' ≤ CMe * (CQ / c0 + 1) * OneRing.maj σk etaN (μ * τ') := by
  have hμ0 : 0 < μ := by linarith
  set m := OneRing.maj σk etaN (μ * τ') with hm
  have hm0 : 0 ≤ m := maj_nonneg_of (mul_nonneg hμ0.le hτ') fun x _ => hN0 x
  set g₁ : ℝ → ℝ := fun v => CQ * m * Real.exp (-(c0 * (τ' - v))) with hg₁
  set g₂ : ℝ → ℝ := fun v => Real.exp (σk * (μ * τ' - μ * v)) * etaN (μ * v) with hg₂
  have hmaps : MapsTo (fun v : ℝ => μ * v) (Icc 0 τ') (Icc 0 (μ * τ')) := fun v hv =>
    ⟨mul_nonneg hμ0.le hv.1, mul_le_mul_of_nonneg_left hv.2 hμ0.le⟩
  have hg₁c : Continuous g₁ := by simp only [hg₁]; fun_prop
  have hg₂c : ContinuousOn g₂ (Icc 0 τ') := by
    simp only [hg₂]
    refine ((by fun_prop : Continuous fun v : ℝ => Real.exp (σk * (μ * τ' - μ * v))).continuousOn).mul ?_
    exact hcont.comp (continuous_const.mul continuous_id).continuousOn hmaps
  have hi₁ : IntervalIntegrable g₁ volume 0 τ' := hg₁c.intervalIntegrable _ _
  have hi₂ : IntervalIntegrable g₂ volume 0 τ' := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hτ']
    exact hg₂c
  have hg₁0 : ∀ v, 0 ≤ g₁ v := fun v => by
    simp only [hg₁]; have := Real.exp_pos (-(c0 * (τ' - v))); positivity
  have hg₂0 : ∀ v, 0 ≤ g₂ v := fun v => by
    simp only [hg₂]; exact mul_nonneg (Real.exp_pos _).le (hN0 _)
  -- pointwise bound
  have hpt' : ∀ v ∈ Icc (0 : ℝ) τ',
      Real.exp (σj * (τ' - v)) * etaI v ≤ CMe * (g₁ v + g₂ v) := by
    intro v hv
    have hE := Real.exp_pos (σj * (τ' - v))
    have hd : 0 ≤ τ' - v := by linarith [hv.2]
    have hmv : 0 ≤ OneRing.maj σk etaN (μ * v) :=
      maj_nonneg_of (mul_nonneg hμ0.le hv.1) fun x _ => hN0 x
    -- the majorant term
    have e1 : Real.exp (σj * (τ' - v)) * OneRing.maj σk etaN (μ * v) ≤
        Real.exp (-(c0 * (τ' - v))) * m := by
      have hsplit : Real.exp (σj * (τ' - v)) * OneRing.maj σk etaN (μ * v) =
          Real.exp (σj * (τ' - v) - σk * (μ * τ' - μ * v)) *
            (Real.exp (σk * (μ * τ' - μ * v)) * OneRing.maj σk etaN (μ * v)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      rw [hsplit]
      have hexp : Real.exp (σj * (τ' - v) - σk * (μ * τ' - μ * v)) ≤
          Real.exp (-(c0 * (τ' - v))) := by
        rw [Real.exp_le_exp]
        have : σj * (τ' - v) - σk * (μ * τ' - μ * v) = -((μ * σk - σj) * (τ' - v)) := by ring
        rw [this, neg_le_neg_iff]
        exact mul_le_mul_of_nonneg_right hgap hd
      calc Real.exp (σj * (τ' - v) - σk * (μ * τ' - μ * v)) *
            (Real.exp (σk * (μ * τ' - μ * v)) * OneRing.maj σk etaN (μ * v))
          ≤ Real.exp (σj * (τ' - v) - σk * (μ * τ' - μ * v)) * m :=
            mul_le_mul_of_nonneg_left (hM1 v hv) (Real.exp_pos _).le
        _ ≤ Real.exp (-(c0 * (τ' - v))) * m := mul_le_mul_of_nonneg_right hexp hm0
    -- the field term
    have e2 : Real.exp (σj * (τ' - v)) * etaN (μ * v) ≤ g₂ v := by
      simp only [hg₂]
      refine mul_le_mul_of_nonneg_right ?_ (hN0 _)
      rw [Real.exp_le_exp]
      have : σk * (μ * τ' - μ * v) = (μ * σk) * (τ' - v) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (by linarith) hd
    calc Real.exp (σj * (τ' - v)) * etaI v
        ≤ Real.exp (σj * (τ' - v)) * (CMe * (CQ * OneRing.maj σk etaN (μ * v) + etaN (μ * v))) :=
          mul_le_mul_of_nonneg_left (hpt v hv) hE.le
      _ = CMe * (CQ * (Real.exp (σj * (τ' - v)) * OneRing.maj σk etaN (μ * v)) +
            Real.exp (σj * (τ' - v)) * etaN (μ * v)) := by ring
      _ ≤ CMe * (CQ * (Real.exp (-(c0 * (τ' - v))) * m) + g₂ v) := by
          gcongr
      _ = CMe * (g₁ v + g₂ v) := by simp only [hg₁]; ring
  have hint : IntervalIntegrable (fun v => CMe * (g₁ v + g₂ v)) volume 0 τ' :=
    (hi₁.add hi₂).const_mul CMe
  have hint0 : 0 ≤ ∫ v in (0 : ℝ)..τ', CMe * (g₁ v + g₂ v) :=
    intervalIntegral.integral_nonneg hτ' fun v _ =>
      mul_nonneg hCMe (add_nonneg (hg₁0 v) (hg₂0 v))
  have hstep := integral_le_of_le hτ' hint hpt' hint0
  -- the integrals of `g₁`, `g₂`
  have hI₁ : (∫ v in (0 : ℝ)..τ', g₁ v) ≤ CQ * m / c0 := by
    simp only [hg₁]
    rw [intervalIntegral.integral_const_mul]
    have := integral_exp_neg_le hc0 hτ' (le_refl τ')
    calc CQ * m * ∫ v in (0 : ℝ)..τ', Real.exp (-(c0 * (τ' - v)))
        ≤ CQ * m * (1 / c0) := mul_le_mul_of_nonneg_left this (mul_nonneg hCQ hm0)
      _ = CQ * m / c0 := by ring
  have hI₂ : (∫ v in (0 : ℝ)..τ', g₂ v) ≤ m := by
    have hsub := intervalIntegral.integral_comp_mul_left
      (fun x => Real.exp (σk * (μ * τ' - x)) * etaN x) (a := 0) (b := τ') hμ0.ne'
    have hg₂eq : (∫ v in (0 : ℝ)..τ', g₂ v) = μ⁻¹ * m := by
      simp only [hg₂]
      rw [hsub, mul_zero, smul_eq_mul, hm, OneRing.maj]
    rw [hg₂eq]
    have : μ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hμ
    nlinarith
  have hcalc : (∫ v in (0 : ℝ)..τ', CMe * (g₁ v + g₂ v)) ≤ CMe * (CQ * m / c0 + m) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hi₁ hi₂]
    exact mul_le_mul_of_nonneg_left (add_le_add hI₁ hI₂) hCMe
  have hfin : CMe * (CQ * m / c0 + m) = CMe * (CQ / c0 + 1) * m := by ring
  calc OneRing.maj σj etaI τ' = ∫ v in (0 : ℝ)..τ', Real.exp (σj * (τ' - v)) * etaI v := rfl
    _ ≤ _ := hstep
    _ ≤ CMe * (CQ * m / c0 + m) := hcalc
    _ = CMe * (CQ / c0 + 1) * m := hfin

/-! ### The standing data -/

variable {S : Standing} {C₀ K₁ : ℝ} {j : ℕ} {τ : ℝ}

/-- `μσ_{j+1} - σ_j ≥ σ_b(μ-1)/2` (`lem:detuning`). -/
theorem gap (h : S.RelayHyp C₀ K₁ j τ) (hS : S.Holds) (hDet : S.Det) :
    S.sigb * (S.P.μ - 1) / 2 ≤ S.P.μ * S.P.sigma (j + 1) - S.P.sigma j := by
  have hd := ((detuning S hS hDet).2.2 (j + 1) (succ_mem h)).2.2.2.2.2 j (j_mem h)
  linarith [hd.1, hd.2.1, hd.2.2.1]

/-- (M1) for `maj_k` on `[0,T]` when `η_k` is continuous there. -/
theorem maj_M1 (hS : S.Holds) {k : ℕ} (hk : k ∈ Finset.Icc 1 S.P.n) {T : ℝ}
    (hc : ContinuousOn (S.eta k) (Icc 0 T)) {τ₁ τ₂ : ℝ} (h0 : 0 ≤ τ₁) (h12 : τ₁ ≤ τ₂)
    (h2 : τ₂ ≤ T) :
    Real.exp (S.P.sigma k * (τ₂ - τ₁)) * S.maj k τ₁ ≤ S.maj k τ₂ :=
  ((OneRing.majorant_of_pos (sigma_pos S hS hk) (hc.integrableOn_Icc)
    fun t _ => S.eta_nonneg k t).1 τ₁ τ₂ h0 h12 h2).1

/-- **`maj_j ≤ 2maj^in_j` on `[0,τ]`** (`09_relay.tex:460-470`). -/
theorem maj_le_two_majIn (h : S.RelayHyp C₀ K₁ j τ) (hS : S.Holds) {τ' : ℝ}
    (hτ' : τ' ∈ Icc (0 : ℝ) τ) : S.maj j τ' ≤ 2 * S.majIn j τ' := by
  obtain ⟨hci, hco, hc⟩ := eta_cont_j h hS
  exact maj_le_two_of (ηi := S.etaIn j) (ηo := S.etaOut j) hτ' hci hco
    (fun v => S.etaIn_nonneg j v) (fun v => S.etaOut_nonneg j v)
    (fun v hv => maj_M1 hS (j_mem h) hc hv.1 hv.2 hτ'.2) h.h2.1 h.h2.2

/-- The pointwise bound of the quiet phase (`09_relay.tex:478-480`):
`η^in_j(v) ≤ C_Mε_j(C_Q maj_{j+1}(μv) + η_{j+1}(μv))` for `v ∈ [0, min(τ, τ^act)]`. -/
theorem quiet_pointwise (h : S.RelayHyp C₀ K₁ j τ) (hS : S.Holds) (hjn : j + 1 < S.P.n)
    {v : ℝ} (hv : v ∈ Icc (0 : ℝ) (min τ (S.P.A j * S.P.tsh (j + 1)))) :
    S.etaIn j v ≤ S.CM * S.P.eps j *
      (S.CQ * S.maj (j + 1) (S.P.μ * v) + S.eta (j + 1) (S.P.μ * v)) := by
  have hA := hS.valid.A_pos j
  have hμ0 : 0 < S.P.μ := by linarith [hS.one_lt_μ]
  set t := v / S.P.A j with ht
  have ht0 : 0 ≤ t := div_nonneg hv.1 hA.le
  have htτ : t ≤ τ / S.P.A j := div_le_div_of_nonneg_right (hv.2.trans (min_le_left _ _)) hA.le
  have hts : t ≤ S.P.tsh (j + 1) := by
    rw [ht, div_le_iff₀ hA, mul_comm]
    exact hv.2.trans (min_le_right _ _)
  have htT : t ≤ S.P.T (j + 1) := by
    rw [T_succ h]
    have := div_nonneg (That_nonneg h hS) (hS.valid.A_pos (j + 1)).le
    linarith
  have htI : t ∈ Icc (0 : ℝ) (τ / S.P.A j) := ⟨ht0, htτ⟩
  have hts1 := (transfer_step_one S hS h.one_le h.lt_n ht0 (pertDefined_succ h htI htT)
    (hDefined_j h hS htI) (hDefined_succ_quiet h htI hts) S.sh).2
  have hAt : S.P.A j * t = v := mul_div_A hS j v
  have hA't : S.P.A (j + 1) * t = S.P.μ * v := by
    rw [ht, A_succ S.P h.one_le]
    field_simp
  rw [hAt, hA't] at hts1
  -- `thm:quiet`(c) for ring `j+1` ((H3))
  have hq := (h.h3 hjn).bound (S.P.μ * v) ⟨mul_nonneg hμ0.le hv.1, by
    rw [← hA't]
    exact mul_le_mul_of_nonneg_left (le_min htτ hts) (hS.valid.A_pos (j + 1)).le⟩
  have hdiv : S.P.μ * v / S.P.A (j + 1) = t := by
    rw [← hA't, mul_div_cancel_left₀ _ (hS.valid.A_pos (j + 1)).ne']
  rw [hdiv] at hq
  have hCMe : 0 ≤ S.CM * S.P.eps j := mul_nonneg (CM_pos S).le (hS.valid.eps_pos j).le
  have hle : S.etaIn (j + 1) (S.P.μ * v) ≤ S.eta (j + 1) (S.P.μ * v) := by
    rw [S.eta_eq_add]
    linarith [S.etaOut_nonneg (j + 1) (S.P.μ * v)]
  calc S.etaIn j v
      ≤ S.CM * S.P.eps j * (Sob.normH S.sh (S.P.w (j + 1) t) + S.etaIn (j + 1) (S.P.μ * v)) :=
        hts1
    _ ≤ S.CM * S.P.eps j * (S.CQ * S.maj (j + 1) (S.P.μ * v) + S.eta (j + 1) (S.P.μ * v)) :=
        mul_le_mul_of_nonneg_left (add_le_add hq hle) hCMe

/-- **Item (o) of `prop:relay`** (`eq:relay-quiet`, `09_relay.tex:488-492`). -/
theorem quiet_o (h : S.RelayHyp C₀ K₁ j τ) (hS : S.Holds) (hDet : S.Det) (hjn : j + 1 < S.P.n)
    {τ' : ℝ} (hτ' : τ' ∈ Icc (0 : ℝ) (min τ (S.P.A j * S.P.tsh (j + 1)))) :
    S.majIn j τ' ≤ S.Crelay * S.P.eps j * S.maj (j + 1) (S.P.μ * τ') := by
  have hμ := hS.one_lt_μ
  have hμ0 : 0 < S.P.μ := by linarith
  have hsb := sigb_pos S hS
  have hc0 : 0 < S.sigb * (S.P.μ - 1) / 2 := by
    have : 0 < S.sigb * (S.P.μ - 1) := mul_pos hsb (by linarith)
    linarith
  have hcont := eta_cont_succ h hS hτ'
  have hCMe : 0 ≤ S.CM * S.P.eps j := mul_nonneg (CM_pos S).le (hS.valid.eps_pos j).le
  have hb := quiet_bound (σj := S.P.sigma j) (σk := S.P.sigma (j + 1)) (μ := S.P.μ)
    (CMe := S.CM * S.P.eps j) (CQ := S.CQ) (c0 := S.sigb * (S.P.μ - 1) / 2) (τ' := τ')
    (etaI := S.etaIn j) (etaN := S.eta (j + 1)) hμ.le hτ'.1 (gap h hS hDet) hc0 hCMe
    (CQ_nonneg S) hcont (fun x => S.eta_nonneg (j + 1) x)
    (fun v hv => by
      have := maj_M1 hS (succ_mem h) hcont (mul_nonneg hμ0.le hv.1)
        (mul_le_mul_of_nonneg_left hv.2 hμ0.le) le_rfl
      exact this)
    (fun v hv => quiet_pointwise h hS hjn
      ⟨hv.1, hv.2.trans (hτ'.2)⟩)
  have heq : S.CM * S.P.eps j * (S.CQ / (S.sigb * (S.P.μ - 1) / 2) + 1) =
      S.Crelay * S.P.eps j := by
    unfold Standing.Crelay
    have : S.sigb * (S.P.μ - 1) ≠ 0 := (mul_pos hsb (by linarith)).ne'
    field_simp
  rw [← heq]
  exact hb

end RelayH

end Relay

end NonUniqueEuler
