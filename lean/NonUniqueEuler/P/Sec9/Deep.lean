import NonUniqueEuler.Defs.Sec9.All
import NonUniqueEuler.I.Sec7.Confine
import NonUniqueEuler.I.Sec9.Detuning
import NonUniqueEuler.I.Sec9.Standing
import NonUniqueEuler.I.Sec6.Clock
import NonUniqueEuler.I.Sec6.FieldContinuity
import NonUniqueEuler.I.Sec4.Uniform
import NonUniqueEuler.H.Sec9.Deep.Real
import NonUniqueEuler.H.Sec9.Deep.Split

/-!
# Proof: `lem:deep` (the moment of the deeper rings during the active phase of ring `k+1`)

Proof of `I/Sec9/Deep.lean` (`09_relay.tex:1103-1132`, proof `:1134-1177`). Helpers:
`H/Sec9/Deep/Split.lean` (the splitting `q_{k+1} = q^ring + q^deep` and the kick time of ring `k+1`),
`H/Sec9/Deep/Real.lean` (the elementary integral and exponent identities of part (3)).

* `deep_clock`: the clock facts at level `k+1` (`A_{k+1} > 0`, `T_{k+1} = t♯_{k+1} + T̂_{k+1}/A_{k+1}`,
  `t♯_{k+1} ≥ 0`, `T̂_{k+1} ≥ 0`, `σ_{k+1} > 0`, `κ♯_{k+1} ∈ (0, δ₀)`);
* `deep_phase`: `t ∈ Ph_{k+1} ⟺ τ_K ∈ [-T_g, 0]`;
* `deep_one`, `deep_two`, `deep_integrable`, `deep_three_first`, `deep_three_second`: the parts.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

open RingData Datum

namespace DeepAux

/-- The clock facts at level `k+1` used throughout the proof. -/
theorem deep_clock (S : Standing) (hS : S.Holds) {k : ℕ} (hk : 1 ≤ k) (hkn : k < S.P.n)
    (hc : S.P.ClockUpTo (k + 1)) :
    0 < S.P.A (k + 1) ∧
      S.P.T (k + 1) = S.P.tsh (k + 1) + S.P.That (k + 1) / S.P.A (k + 1) ∧
      0 ≤ S.P.tsh (k + 1) ∧ 0 < S.P.sigma (k + 1) ∧
      S.P.ksh (k + 1) ∈ Ioo (0 : ℝ) S.P.δ₀ ∧ 0 ≤ S.P.That (k + 1) := by
  have hP : S.P.Valid := hS.valid
  obtain ⟨hsigb, -, hG, hlev⟩ := standing_levels S hS
  have hA1 : 0 < S.P.A (k + 1) := hP.A_pos _
  have hT1 : S.P.T (k + 1) = S.P.tsh (k + 1) + S.P.That (k + 1) / S.P.A (k + 1) :=
    S.P.T_of_ne (by omega)
  have hco := Approx.clock_order S.P hP hS.hN hG (by omega : 1 ≤ k + 1) hc
  have htsh0 : 0 ≤ S.P.tsh (k + 1) := hco.2.2.2 (k + 1) (Finset.mem_Icc.2 ⟨le_rfl, hkn⟩)
  have hσ1 : 0 < S.P.sigma (k + 1) :=
    lt_of_lt_of_le hsigb (hlev (k + 1) (Finset.mem_Icc.2 ⟨by omega, hkn⟩)).2.2
  have hκ : S.P.ksh (k + 1) ∈ Ioo (0 : ℝ) S.P.δ₀ := hc.ksh_mem le_rfl hkn
  have hThat : 0 ≤ S.P.That (k + 1) := by
    unfold Approx.That
    refine mul_nonneg (inv_nonneg.2 hσ1.le) (Real.log_nonneg ?_)
    rw [le_div_iff₀ hκ.1, one_mul]
    exact hκ.2.le
  exact ⟨hA1, hT1, htsh0, hσ1, hκ, hThat⟩

/-- The kick time of `t = T_{k+1} + τ_K/A_{k+1}` is `τ_K`. -/
theorem kickTime_of_kick (S : Standing) (hS : S.Holds) (k : ℕ) (τK : ℝ) :
    S.P.kickTime k (S.P.T (k + 1) + τK / S.P.A (k + 1)) = τK := by
  have hA1 : S.P.A (k + 1) ≠ 0 := (hS.valid.A_pos _).ne'
  simp only [Approx.kickTime]
  field_simp
  ring

/-- `t ∈ Ph_{k+1}` iff `τ_K = A_{k+1}(t - T_{k+1}) ∈ [-T_g, 0]` (`09_relay.tex:1135-1137`). -/
theorem deep_phase (S : Standing) (hS : S.Holds) {k : ℕ} (hk : 1 ≤ k) (hkn : k < S.P.n)
    (hc : S.P.ClockUpTo (k + 1)) (t : ℝ) :
    t ∈ S.P.Phase (k + 1) ↔ S.P.kickTime k t ∈ Icc (-S.P.That (k + 1)) 0 := by
  obtain ⟨hA1, hT1, -, -, -, -⟩ := deep_clock S hS hk hkn hc
  have hkey : S.P.A (k + 1) * (t - S.P.T (k + 1)) =
      S.P.A (k + 1) * (t - S.P.tsh (k + 1)) - S.P.That (k + 1) := by
    rw [hT1]
    field_simp
    ring
  simp only [Approx.Phase, Approx.kickTime, mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, mul_nonpos_of_nonneg_of_nonpos hA1.le (by linarith)⟩
    have := mul_nonneg hA1.le (sub_nonneg.2 h1)
    linarith
  · rintro ⟨h1, h2⟩
    constructor
    · by_contra hne
      rw [not_le] at hne
      have := mul_neg_of_pos_of_neg hA1 (sub_neg.2 hne)
      linarith
    · by_contra hne
      rw [not_le] at hne
      have := mul_pos hA1 (sub_pos.2 hne)
      linarith

/-- For `τ_K ∈ [-T_g, 0]`, the time `t = T_{k+1} + τ_K/A_{k+1}` lies in `Ph_{k+1}` and `t ≥ 0`. -/
theorem kick_mem_phase (S : Standing) (hS : S.Holds) {k : ℕ} (hk : 1 ≤ k) (hkn : k < S.P.n)
    (hc : S.P.ClockUpTo (k + 1)) {τK : ℝ} (hτ : τK ∈ Icc (-S.P.That (k + 1)) 0) :
    S.P.T (k + 1) + τK / S.P.A (k + 1) ∈ S.P.Phase (k + 1) ∧
      0 ≤ S.P.T (k + 1) + τK / S.P.A (k + 1) := by
  obtain ⟨-, -, htsh0, -, -, -⟩ := deep_clock S hS hk hkn hc
  have hmem : S.P.T (k + 1) + τK / S.P.A (k + 1) ∈ S.P.Phase (k + 1) := by
    rw [deep_phase S hS hk hkn hc, kickTime_of_kick S hS]
    exact hτ
  exact ⟨hmem, le_trans htsh0 hmem.1⟩

/-- **Part (1)** (`09_relay.tex:1135-1150`). -/
theorem deep_one (S : Standing) (hS : S.Holds) {k : ℕ} (hk : 1 ≤ k) (hkn : k < S.P.n)
    (hc : S.P.ClockUpTo (k + 1)) :
    (∀ t : ℝ, t ∈ S.P.Phase (k + 1) ↔ S.P.kickTime k t ∈ Icc (-S.P.That (k + 1)) 0) ∧
      (∀ τK ∈ Icc (-S.P.That (k + 1)) 0, S.P.qKick k τK = S.P.qRing k τK + S.P.qDeep k τK) ∧
      (k + 1 = S.P.n → ∀ τK : ℝ, S.P.qDeep k τK = 0) := by
  refine ⟨deep_phase S hS hk hkn hc, fun τK hτ => ?_, fun h τK => S.P.qDeep_of_succ_eq_n h τK⟩
  have ht0 := (kick_mem_phase S hS hk hkn hc hτ).2
  rw [qKick_split S.P hS.valid hS.hN hk hkn ht0]
  congr 1
  rcases Nat.lt_or_ge (k + 1) S.P.n with hlt | hge
  · exact deepTerm_eq S.P hS.valid hk hlt τK
  · exact deepTerm_eq_of_succ_eq_n S.P (by omega) τK

/-- `q^deep(τ_K) = μ s_{k+1}^5 q_{k+2}(t)` with `t = T_{k+1} + τ_K/A_{k+1}` (`k + 1 < n`). -/
theorem qDeep_eq_q (S : Standing) (hS : S.Holds) {k : ℕ} (hk : 1 ≤ k) (hkn1 : k + 1 < S.P.n)
    (τK : ℝ) :
    S.P.qDeep k τK = ((S.P.μ * S.P.s (k + 1) ^ (3 + 2) : ℝ) : ℂ) *
      S.P.q (k + 1 + 1) (S.P.T (k + 1) + τK / S.P.A (k + 1)) := by
  simp only [Approx.qDeep, Approx.qKick]
  rw [kick_time_succ S.P hS.valid hk hkn1 τK]

/-- **Part (2)** (`09_relay.tex:1152-1157`). -/
theorem deep_two (S : Standing) (hS : S.Holds) {k : ℕ} (hk : 1 ≤ k) (hkn : k < S.P.n)
    (hc : S.P.ClockUpTo (k + 1)) (hkn1 : k + 1 < S.P.n)
    (hconf : S.P.ConfineHyp (k + 1) (S.P.T (k + 1))) :
    ∀ τK ∈ Icc (-S.P.That (k + 1)) 0, ‖S.P.qDeep k τK‖ ≤
      S.P.μ * S.P.s (k + 1) ^ (3 + 2) * Rings.Cmom *
        (1 + S.P.Tpin + S.P.μ * (τK + S.P.That (k + 1))) ^ 3 := by
  intro τK hτ
  have hP : S.P.Valid := hS.valid
  obtain ⟨-, -, hG, -⟩ := standing_levels S hS
  have hcc := Rings.confine S.P hP hS.hN hG hconf
  have htime := kick_time_succ S.P hP hk hkn1 τK
  obtain ⟨hmem, -⟩ := kick_mem_phase S hS hk hkn hc hτ
  -- `t ≥ t♯_{k+1} = T_{k+2} + T_pin/A_{k+2} ≥ T_{k+2}`
  have htsh : S.P.tsh (k + 1) = S.P.T (k + 1 + 1) + S.P.Tpin / S.P.A (k + 1 + 1) :=
    S.P.tsh_eq_T_add hkn1
  have hpin : 0 ≤ S.P.Tpin / S.P.A (k + 1 + 1) := div_nonneg hS.Tpin_pos.le (hP.A_pos _).le
  have hW : S.P.T (k + 1) + τK / S.P.A (k + 1) ∈ Icc (S.P.T (k + 1 + 1)) (S.P.T (k + 1)) :=
    ⟨by linarith [hmem.1], hmem.2⟩
  have hq := (hcc _ hW).q_le
  have hkt : S.P.kickTime (k + 1) (S.P.T (k + 1) + τK / S.P.A (k + 1)) =
      S.P.Tpin + S.P.μ * (τK + S.P.That (k + 1)) := by
    have hA2 : S.P.A (k + 1 + 1) ≠ 0 := (hP.A_pos _).ne'
    rw [← htime]
    simp only [Approx.kickTime]
    field_simp
    ring
  rw [hkt] at hq
  have hc0 : 0 ≤ S.P.μ * S.P.s (k + 1) ^ (3 + 2) :=
    mul_nonneg (by linarith [hS.one_lt_μ]) (pow_nonneg (hP.s_pos _).le _)
  rw [qDeep_eq_q S hS hk hkn1, norm_mul, Complex.norm_of_nonneg hc0]
  calc S.P.μ * S.P.s (k + 1) ^ (3 + 2) *
        ‖S.P.q (k + 1 + 1) (S.P.T (k + 1) + τK / S.P.A (k + 1))‖
      ≤ S.P.μ * S.P.s (k + 1) ^ (3 + 2) *
          (Rings.Cmom * (1 + (S.P.Tpin + S.P.μ * (τK + S.P.That (k + 1)))) ^ 3) :=
        mul_le_mul_of_nonneg_left hq hc0
    _ = S.P.μ * S.P.s (k + 1) ^ (3 + 2) * Rings.Cmom *
          (1 + S.P.Tpin + S.P.μ * (τK + S.P.That (k + 1))) ^ 3 := by ring

/-- **Integrability in part (3)**: `τ_K ↦ e^{-xτ_K}|q^deep(τ_K)|` is continuous on `[-T_g, 0]`
(`q_{k+2}` is continuous on `[0, ∞)`, `q_continuous`), hence interval integrable. -/
theorem deep_integrable (S : Standing) (hS : S.Holds) {k : ℕ} (hk : 1 ≤ k) (hkn : k < S.P.n)
    (hc : S.P.ClockUpTo (k + 1)) (hkn1 : k + 1 < S.P.n) :
    IntervalIntegrable (fun τK => Real.exp (-(S.P.xk k * τK)) * ‖S.P.qDeep k τK‖) volume
      (-S.P.That (k + 1)) 0 := by
  have hP : S.P.Valid := hS.valid
  obtain ⟨-, -, -, -, -, hThat⟩ := deep_clock S hS hk hkn hc
  have hqc := Approx.q_continuous S.P hP hS.hN (k := k + 1) (by omega) hkn1
  have hφc : Continuous fun τK : ℝ => S.P.T (k + 1) + τK / S.P.A (k + 1) := by fun_prop
  have hmaps : MapsTo (fun τK : ℝ => S.P.T (k + 1) + τK / S.P.A (k + 1))
      (Icc (-S.P.That (k + 1)) 0) (Ici 0) := fun τK hτ =>
    (kick_mem_phase S hS hk hkn hc hτ).2
  have hcont : ContinuousOn (fun τK => S.P.qDeep k τK) (Icc (-S.P.That (k + 1)) 0) := by
    have h := continuousOn_const (c := ((S.P.μ * S.P.s (k + 1) ^ (3 + 2) : ℝ) : ℂ))
      (s := Icc (-S.P.That (k + 1)) 0) |>.mul (hqc.comp hφc.continuousOn hmaps)
    exact h.congr fun τK _ => qDeep_eq_q S hS hk hkn1 τK
  refine ContinuousOn.intervalIntegrable_of_Icc (by linarith) ?_
  exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).continuousOn).mul
    hcont.norm

/-- **The elementary estimate of part (3)** (`09_relay.tex:1159-1172`), with abstract data: if
`0 ≤ f(τ) ≤ μ s₅ C_m (1 + T_pin + μ(τ + T_g))³` on `[-T_g, 0]`, `T_g = σ₁⁻¹L`, `σ₁ ≥ 15σ/16`,
`x ≥ σ/4`, `L ≥ 1`, `μ ≤ 2` and `K_lo s₅ ≤ κ`, then
`∫_{-T_g}^0 e^{-xτ}f ≤ (4μC_m(1 + T_pin + 32/(15σ))³/(σK_lo)) κ e^{xT_g} L³`. -/
theorem deep_integral_real {f : ℝ → ℝ} {x Tg L σ σ₁ μ Tpin Cm s5 κ Klo : ℝ}
    (hf : IntervalIntegrable (fun τ => Real.exp (-(x * τ)) * f τ) volume (-Tg) 0)
    (hbound : ∀ τ ∈ Icc (-Tg) 0, f τ ≤ μ * s5 * Cm * (1 + Tpin + μ * (τ + Tg)) ^ 3)
    (hσ : 0 < σ) (hx : σ / 4 ≤ x) (hσ1 : 15 / 16 * σ ≤ σ₁) (hTg : Tg = σ₁⁻¹ * L) (hL : 1 ≤ L)
    (hμ0 : 0 < μ) (hμ2 : μ ≤ 2) (hTpin : 0 ≤ Tpin) (hCm : 0 < Cm) (hs5 : 0 ≤ s5)
    (hKlo : 0 < Klo) (hKs : Klo * s5 ≤ κ) :
    ∫ τ in (-Tg)..0, Real.exp (-(x * τ)) * f τ ≤
      4 * μ * Cm * (1 + Tpin + 32 / (15 * σ)) ^ 3 / (σ * Klo) * (κ * Real.exp (x * Tg)) *
        L ^ 3 := by
  have hxpos : 0 < x := by linarith
  have hσ1pos : 0 < σ₁ := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hTg0 : 0 ≤ Tg := by
    rw [hTg]
    exact mul_nonneg (inv_nonneg.2 hσ1pos.le) hL0
  -- `T_g ≤ 16L/(15σ)`
  have hTgle : Tg ≤ 16 / (15 * σ) * L := by
    rw [hTg]
    refine mul_le_mul_of_nonneg_right ?_ hL0
    calc σ₁⁻¹ ≤ (15 / 16 * σ)⁻¹ := inv_anti₀ (by positivity) hσ1
      _ = 16 / (15 * σ) := by field_simp
  have hc32 : 0 < 32 / (15 * σ) := div_pos (by norm_num) (by positivity)
  have hB : 0 < 1 + Tpin + 32 / (15 * σ) := by linarith
  have hκ0 : 0 ≤ κ := le_trans (mul_nonneg hKlo.le hs5) hKs
  have hc0 : 0 ≤ μ * s5 * Cm := mul_nonneg (mul_nonneg hμ0.le hs5) hCm.le
  -- the pointwise bound `1 + T_pin + μ(τ + T_g) ≤ (1 + T_pin + 32/(15σ)) L`
  have hpt : ∀ τ ∈ Icc (-Tg) 0, Real.exp (-(x * τ)) * f τ ≤
      Real.exp (-(x * τ)) * (μ * s5 * Cm * ((1 + Tpin + 32 / (15 * σ)) * L) ^ 3) := by
    intro τ hτ
    refine mul_le_mul_of_nonneg_left ((hbound τ hτ).trans ?_) (Real.exp_pos _).le
    refine mul_le_mul_of_nonneg_left ?_ hc0
    have hτ0 : 0 ≤ τ + Tg := by linarith [hτ.1]
    have h1 : μ * (τ + Tg) ≤ 2 * (τ + Tg) := mul_le_mul_of_nonneg_right hμ2 hτ0
    have h2 : 1 + Tpin ≤ (1 + Tpin) * L := le_mul_of_one_le_right (by linarith) hL
    have h3 : 2 * Tg ≤ 32 / (15 * σ) * L := by
      have : 2 * (16 / (15 * σ) * L) = 32 / (15 * σ) * L := by ring
      linarith
    have hBL : (1 + Tpin + 32 / (15 * σ)) * L = (1 + Tpin) * L + 32 / (15 * σ) * L := by ring
    refine pow_le_pow_left₀ (by nlinarith [mul_nonneg hμ0.le hτ0]) ?_ 3
    rw [hBL]
    linarith [hτ.2]
  have hgI : IntervalIntegrable
      (fun τ => Real.exp (-(x * τ)) * (μ * s5 * Cm * ((1 + Tpin + 32 / (15 * σ)) * L) ^ 3))
      volume (-Tg) 0 :=
    (by fun_prop : Continuous fun τ : ℝ =>
      Real.exp (-(x * τ)) * (μ * s5 * Cm * ((1 + Tpin + 32 / (15 * σ)) * L) ^ 3)).intervalIntegrable
      _ _
  have hI1 := intervalIntegral.integral_mono_on (by linarith) hf hgI hpt
  rw [intervalIntegral.integral_mul_const] at hI1
  have hI3 := integral_exp_neg_mul_le hxpos Tg
  have hK0 : 0 ≤ μ * s5 * Cm * ((1 + Tpin + 32 / (15 * σ)) * L) ^ 3 :=
    mul_nonneg hc0 (pow_nonneg (mul_nonneg hB.le hL0) 3)
  have hfrac : s5 / x ≤ 4 * κ / (σ * Klo) := by
    rw [div_le_div_iff₀ hxpos (mul_pos hσ hKlo)]
    calc s5 * (σ * Klo) = σ * (Klo * s5) := by ring
      _ ≤ σ * κ := mul_le_mul_of_nonneg_left hKs hσ.le
      _ ≤ (4 * x) * κ := mul_le_mul_of_nonneg_right (by linarith) hκ0
      _ = 4 * κ * x := by ring
  have hpos : 0 ≤ Real.exp (x * Tg) * μ * Cm * (1 + Tpin + 32 / (15 * σ)) ^ 3 * L ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le hμ0.le) hCm.le)
      (pow_pos hB 3).le) (pow_nonneg hL0 3)
  calc ∫ τ in (-Tg)..0, Real.exp (-(x * τ)) * f τ
      ≤ (∫ τ in (-Tg)..0, Real.exp (-(x * τ))) *
          (μ * s5 * Cm * ((1 + Tpin + 32 / (15 * σ)) * L) ^ 3) := hI1
    _ ≤ Real.exp (x * Tg) / x * (μ * s5 * Cm * ((1 + Tpin + 32 / (15 * σ)) * L) ^ 3) :=
        mul_le_mul_of_nonneg_right hI3 hK0
    _ = Real.exp (x * Tg) * μ * Cm * (1 + Tpin + 32 / (15 * σ)) ^ 3 * L ^ 3 * (s5 / x) := by
        ring
    _ ≤ Real.exp (x * Tg) * μ * Cm * (1 + Tpin + 32 / (15 * σ)) ^ 3 * L ^ 3 *
          (4 * κ / (σ * Klo)) := mul_le_mul_of_nonneg_left hfrac hpos
    _ = 4 * μ * Cm * (1 + Tpin + 32 / (15 * σ)) ^ 3 / (σ * Klo) * (κ * Real.exp (x * Tg)) *
          L ^ 3 := by ring

/-- `K_lo > 0` (`c_N > 0` by `lem:uniform`, `|z| ≥ Re z = σ > 0`, `μ > 1`, `δ₀ > 0`). -/
theorem Klo_pos (S : Standing) (hS : S.Holds) : 0 < S.Klo := by
  obtain ⟨hsigb, hsigb_le, -, -⟩ := standing_levels S hS
  have hσ : 0 < S.sigma0 := lt_of_lt_of_le hsigb hsigb_le
  obtain ⟨-, -, -, -, -, -, hcN, -⟩ := Eig.uniform_constants S.P.χ hS.admissible hS.hN
  have hre : S.z.re = S.sigma0 := rfl
  have hz : 0 < ‖S.z‖ := lt_of_lt_of_le (hre ▸ hσ) (Complex.re_le_norm S.z)
  have hμ1 : 0 < S.P.μ - 1 := by linarith [hS.one_lt_μ]
  rw [Standing.Klo_def]
  exact div_pos (mul_pos hcN hS.δ₀_pos) (mul_pos (mul_pos (by norm_num) hz) hμ1)

/-- **Part (3), first inequality** (`09_relay.tex:1159-1172`). -/
theorem deep_three_first (S : Standing) (hS : S.Holds) (hDet : S.Det) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k < S.P.n) (hc : S.P.ClockUpTo (k + 1)) (hkn1 : k + 1 < S.P.n)
    (hconf : S.P.ConfineHyp (k + 1) (S.P.T (k + 1)))
    (hKlo : S.Klo * S.P.s (k + 1) ^ (3 + 2) ≤ S.P.ksh (k + 1))
    (hkC : S.kickIneqC (S.P.ksh (k + 1))) :
    ∫ τK in (-S.P.That (k + 1))..0, Real.exp (-(S.P.xk k * τK)) * ‖S.P.qDeep k τK‖ ≤
      S.Cdeep * S.P.δ₀ * (S.P.ksh (k + 1) / S.P.δ₀) ^ (1 - S.P.xk k / S.P.sigma (k + 1)) *
        Real.log (S.P.δ₀ / S.P.ksh (k + 1)) ^ 3 := by
  have hP : S.P.Valid := hS.valid
  obtain ⟨-, -, -, hσ1, hκ, -⟩ := deep_clock S hS hk hkn hc
  obtain ⟨hsigb, hsigb_le, -, -⟩ := standing_levels S hS
  have hσ : 0 < S.sigma0 := lt_of_lt_of_le hsigb hsigb_le
  obtain ⟨-, -, hdet⟩ := detuning S hS hDet
  obtain ⟨-, -, -, hxk, -, -⟩ := hdet k (Finset.mem_Icc.2 ⟨hk, hkn.le⟩)
  obtain ⟨-, hσ1lo, -, -, -, -⟩ := hdet (k + 1) (Finset.mem_Icc.2 ⟨by omega, hkn⟩)
  have hL : 1 ≤ Real.log (S.P.δ₀ / S.P.ksh (k + 1)) :=
    one_le_log_of_le_rpow hκ.1 hS.one_lt_μ hkC
  have hTg : S.P.That (k + 1) =
      (S.P.sigma (k + 1))⁻¹ * Real.log (S.P.δ₀ / S.P.ksh (k + 1)) := rfl
  have hmain := deep_integral_real (f := fun τK => ‖S.P.qDeep k τK‖)
    (deep_integrable S hS hk hkn hc hkn1) (deep_two S hS hk hkn hc hkn1 hconf) hσ hxk hσ1lo hTg
    hL (by linarith [hS.one_lt_μ]) (le_trans hS.μ_le (by norm_num)) hS.Tpin_pos.le
    Rings.Cmom_pos (pow_nonneg (hP.s_pos _).le _) (Klo_pos S hS) hKlo
  refine hmain.trans (le_of_eq ?_)
  rw [hTg, kappa_mul_exp_eq _ hκ.1 hS.δ₀_pos hσ1.ne', Standing.Cdeep_def]
  ring

/-- **Part (3), second inequality** (`09_relay.tex:1173-1177`): `1 - x/σ_{k+1} ≥ ϑ_μ` and
`κ < δ₀`. -/
theorem deep_three_second (S : Standing) (hS : S.Holds) (hDet : S.Det) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k < S.P.n) (hc : S.P.ClockUpTo (k + 1)) :
    S.Cdeep * S.P.δ₀ * (S.P.ksh (k + 1) / S.P.δ₀) ^ (1 - S.P.xk k / S.P.sigma (k + 1)) *
          Real.log (S.P.δ₀ / S.P.ksh (k + 1)) ^ 3 ≤
        S.Cdeep * S.P.δ₀ * (S.P.ksh (k + 1) / S.P.δ₀) ^ S.varthetaMu *
          Real.log (S.P.δ₀ / S.P.ksh (k + 1)) ^ 3 := by
  obtain ⟨-, -, -, hσ1, hκ, -⟩ := deep_clock S hS hk hkn hc
  obtain ⟨hsigb, hsigb_le, -, -⟩ := standing_levels S hS
  have hσ : 0 < S.sigma0 := lt_of_lt_of_le hsigb hsigb_le
  obtain ⟨hemu, -, hdet⟩ := detuning S hS hDet
  have hkI : k ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.2 ⟨hk, hkn.le⟩
  obtain ⟨habs, -, -, -, -, hl⟩ := hdet (k + 1) (Finset.mem_Icc.2 ⟨by omega, hkn⟩)
  obtain ⟨hg1, hg2, -, -⟩ := hl k hkI
  have hμ1 : 1 < S.P.μ := hS.one_lt_μ
  have hμ0 : 0 < S.P.μ := by linarith
  have hμle : S.P.μ ≤ 17 / 16 := hS.μ_le
  -- `σ_{k+1} ≤ (17/16)σ`
  have hσ1hi : S.P.sigma (k + 1) ≤ 17 / 16 * S.sigma0 := by
    have h1 := (abs_le.1 habs).2
    have h2 : S.emu * S.sigma0 ≤ 1 / 136 * S.sigma0 := mul_le_mul_of_nonneg_right hemu hσ.le
    linarith
  -- `(μ-1)/3 · μσ_{k+1} ≤ (3/4)σ(μ-1)` (uses `μ ≤ 36/17`)
  have hD : (S.P.μ - 1) / 3 * (S.P.μ * S.P.sigma (k + 1)) ≤ 3 / 4 * S.sigma0 * (S.P.μ - 1) := by
    have h1 : S.P.μ * S.P.sigma (k + 1) ≤ 17 / 16 * (17 / 16 * S.sigma0) :=
      mul_le_mul hμle hσ1hi hσ1.le (by norm_num)
    have h2 := mul_le_mul_of_nonneg_left h1 (by linarith : 0 ≤ (S.P.μ - 1) / 3)
    have h3 : 0 ≤ (S.P.μ - 1) * S.sigma0 := mul_nonneg (by linarith) hσ.le
    nlinarith
  -- `1 - x/σ_{k+1} ≥ ϑ_μ`
  have hϑ : S.varthetaMu ≤ 1 - S.P.xk k / S.P.sigma (k + 1) := by
    have h : S.P.xk k / S.P.sigma (k + 1) ≤ 1 - (S.P.μ - 1) / 3 := by
      show S.P.sigma k / S.P.μ / S.P.sigma (k + 1) ≤ _
      rw [div_div, div_le_iff₀ (mul_pos hμ0 hσ1)]
      nlinarith
    rw [Standing.varthetaMu]
    linarith
  have hq0 : 0 < S.P.ksh (k + 1) / S.P.δ₀ := div_pos hκ.1 hS.δ₀_pos
  have hq1 : S.P.ksh (k + 1) / S.P.δ₀ ≤ 1 := (div_le_one hS.δ₀_pos).2 hκ.2.le
  have hrp := Real.rpow_le_rpow_of_exponent_ge hq0 hq1 hϑ
  have hL0 : 0 ≤ Real.log (S.P.δ₀ / S.P.ksh (k + 1)) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hκ.1, one_mul]
    exact hκ.2.le
  have hc32 : 0 < 32 / (15 * S.sigma0) := div_pos (by norm_num) (by positivity)
  have hB : 0 < 1 + S.P.Tpin + 32 / (15 * S.sigma0) := by linarith [hS.Tpin_pos]
  have hCd : 0 ≤ S.Cdeep := by
    rw [Standing.Cdeep_def]
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hμ0.le)
      Rings.Cmom_pos.le) (pow_pos hB 3).le) (mul_nonneg hσ.le (Klo_pos S hS).le)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hrp (mul_nonneg hCd hS.δ₀_pos.le)) (pow_nonneg hL0 3)

end DeepAux

/-- **`lem:deep`** (`09_relay.tex:1103-1132`). Assume (SA), (Det), `1 ≤ k < n` and the clock
defined up to level `k+1`; `T_g = T̂_{k+1}`, `κ = κ♯_{k+1}`, `x = x_k`.
(1) `t ∈ Ph_{k+1}` iff the kick time `τ_K` of ring `k` lies in `[-T_g, 0]`; there
`q_{k+1} = q^ring + q^deep`; and `q^deep ≡ 0` if `k+1 = n`.
(2) If `k+1 < n` and `prop:confine` applies at level `k+1` with `t₁ = T_{k+1}`:
`|q^deep(τ_K)| ≤ μs_{k+1}⁵C_mom(1 + T_pin + μ(τ_K+T_g))³` on `[-T_g, 0]`.
(3) If moreover `K_lo s_{k+1}⁵ ≤ κ ≤ δ₀4^{-μ/(μ-1)}`: `e^{-xτ_K}|q^deep|` is integrable on
`[-T_g, 0]` and its integral is `≤ C_deep δ₀(κ/δ₀)^{1-x/σ_{k+1}}L³ ≤ C_deep δ₀(κ/δ₀)^{ϑ_μ}L³`,
`L = log(δ₀/κ)`. -/
theorem deep (S : Standing) (hS : S.Holds) (hDet : S.Det) {k : ℕ} (hk : 1 ≤ k) (hkn : k < S.P.n)
    (hc : S.P.ClockUpTo (k + 1)) :
    ((∀ t : ℝ, t ∈ S.P.Phase (k + 1) ↔ S.P.kickTime k t ∈ Icc (-S.P.That (k + 1)) 0) ∧
      (∀ τK ∈ Icc (-S.P.That (k + 1)) 0, S.P.qKick k τK = S.P.qRing k τK + S.P.qDeep k τK) ∧
      (k + 1 = S.P.n → ∀ τK : ℝ, S.P.qDeep k τK = 0)) ∧
    (k + 1 < S.P.n → S.P.ConfineHyp (k + 1) (S.P.T (k + 1)) →
      (∀ τK ∈ Icc (-S.P.That (k + 1)) 0, ‖S.P.qDeep k τK‖ ≤
        S.P.μ * S.P.s (k + 1) ^ (3 + 2) * Rings.Cmom *
          (1 + S.P.Tpin + S.P.μ * (τK + S.P.That (k + 1))) ^ 3) ∧
      (S.Klo * S.P.s (k + 1) ^ (3 + 2) ≤ S.P.ksh (k + 1) → S.kickIneqC (S.P.ksh (k + 1)) →
        IntervalIntegrable (fun τK => Real.exp (-(S.P.xk k * τK)) * ‖S.P.qDeep k τK‖) volume
            (-S.P.That (k + 1)) 0 ∧
        ∫ τK in (-S.P.That (k + 1))..0, Real.exp (-(S.P.xk k * τK)) * ‖S.P.qDeep k τK‖ ≤
            S.Cdeep * S.P.δ₀ * (S.P.ksh (k + 1) / S.P.δ₀) ^ (1 - S.P.xk k / S.P.sigma (k + 1)) *
              Real.log (S.P.δ₀ / S.P.ksh (k + 1)) ^ 3 ∧
        S.Cdeep * S.P.δ₀ * (S.P.ksh (k + 1) / S.P.δ₀) ^ (1 - S.P.xk k / S.P.sigma (k + 1)) *
              Real.log (S.P.δ₀ / S.P.ksh (k + 1)) ^ 3 ≤
            S.Cdeep * S.P.δ₀ * (S.P.ksh (k + 1) / S.P.δ₀) ^ S.varthetaMu *
              Real.log (S.P.δ₀ / S.P.ksh (k + 1)) ^ 3)) :=
  ⟨DeepAux.deep_one S hS hk hkn hc, fun hkn1 hconf =>
    ⟨DeepAux.deep_two S hS hk hkn hc hkn1 hconf, fun hKlo hkC =>
      ⟨DeepAux.deep_integrable S hS hk hkn hc hkn1,
        DeepAux.deep_three_first S hS hDet hk hkn hc hkn1 hconf hKlo hkC,
        DeepAux.deep_three_second S hS hDet hk hkn hc⟩⟩⟩

end Relay

end NonUniqueEuler
