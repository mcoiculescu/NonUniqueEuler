import NonUniqueEuler.H.Sec9.KickTrue.Q1
import NonUniqueEuler.H.Sec9.KickTrue.Pre

/-!
# Helpers for `P/Sec9/KickTrue`: the hypotheses of `prop:kick`

Helper file of `P/Sec9/KickTrue.lean` (`lem:kicktrue`, `09_relay.tex:1233-1397`). For
`1 ≤ k < n` under `S.KickTrueHyp C₀ K₁ k`, with `err = errE(· + T_g) + |q^deep|`, `Q_pre = |q_{k+1}|`:
* `qs_facts`: `|q_s| ∈ [15/16, 17/16]·2π|pout_*(G_{k+1})|δ₀`, `q_s ≠ 0`, `|q_s| ≥ (15/16)c_outδ₀`
  (`lem:drift`, `lem:uniform`; `09_relay.tex:1262-1273`);
* `budget_le`: `𝖡 = (15/16)c_outδ₀/(20|z|(μ-1)) ≤ |q_s|/(20|z|(μ-1))`;
* `Cdeep_nonneg`: `C_deep ≥ 0`;
* `budget_real` (generic): the six terms of `Err_g` and the deep term add up to at most `𝖡`, by
  (a), (d), (f) (`09_relay.tex:1369-1372`);
* `errG_le_sum`: `Err_g ≤` the six terms of `errE_integral_le` plus `1_{k+1<n}C_deepδ₀(κ/δ₀)^{ϑ_μ}L³`;
* `errG_le`: `Err_g ≤ 𝖡` on `[-T_g, 0]` ((Kick3), `09_relay.tex:1309-1372`);
* `kickHyp_of`: for every `T'_g ∈ [17T_g/24, T_g]` with `τ₀ < -T'_g` and (Kick4) for `T'_g`, the
  hypotheses `Kick.KickHyp` of `prop:kick` hold with `(Q̄, p) = (C_mom, 3)` and `T'_g`.
Everything here is proved.
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler

namespace Relay

namespace KickTrueAux

open RingData Datum

variable (S : Standing)

/-- **The amplitude `q_s`** (`09_relay.tex:1262-1273`). -/
theorem qs_facts (hS : S.Holds) (hDet : S.Det) {C₀ K₁ : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hkn : k < S.P.n) (hc : S.P.ClockUpTo (k + 1)) (h : S.KickTrueHyp C₀ K₁ k) :
    ‖S.P.kickQs k‖ ∈ Icc (15 / 16 * (2 * Real.pi * ‖Eig.pout S.P.χ (S.P.G (k + 1))‖ * S.P.δ₀))
      (17 / 16 * (2 * Real.pi * ‖Eig.pout S.P.χ (S.P.G (k + 1))‖ * S.P.δ₀)) ∧
      S.P.kickQs k ≠ 0 ∧ 15 / 16 * Eig.cout S.P.χ * S.P.δ₀ ≤ ‖S.P.kickQs k‖ := by
  obtain ⟨hTg0⟩ := And.intro (kappa_facts S hS hDet hk hkn hc h.ineqC).2.2.2.2.2 trivial
  obtain ⟨-, hG1, -, -, -⟩ := level_facts S hS hDet hk hkn
  obtain ⟨hcout, hcle, -, -, -, -⟩ := uniform_facts S hS hG1
  obtain ⟨η, hη, hdh, hsmall⟩ := h.drift
  have hd := ((drift S hS hDet (k := k + 1) (by omega) hkn hc ⟨hTg0.le, le_rfl⟩ hη.1 hdh).2
    h.rT_le hsmall).2.2 rfl
  have hnorm : ‖S.P.kickQs k‖ = 2 * Real.pi * ‖Eig.pout S.P.χ (S.P.G (k + 1))‖ *
      (‖S.P.runCoefK (k + 1) (S.P.That (k + 1))‖ *
        Real.exp (S.P.sigma (k + 1) * S.P.That (k + 1))) := by
    have h1 : S.P.kickQs k = 2 * Real.pi * Eig.pout S.P.χ (S.P.G (k + 1)) *
        (S.P.runCoefK (k + 1) (S.P.That (k + 1)) *
          Complex.exp (S.P.lam (k + 1) * (S.P.That (k + 1) : ℂ))) := by
      simp only [Approx.kickQs]; ring
    rw [h1, norm_two_pi_mul]
    have hre : (S.P.lam (k + 1)).re = S.P.sigma (k + 1) := rfl
    rw [hre]
    ring
  have hP0 : 0 ≤ 2 * Real.pi * ‖Eig.pout S.P.χ (S.P.G (k + 1))‖ := by positivity
  have hrange : ‖S.P.kickQs k‖ ∈
      Icc (15 / 16 * (2 * Real.pi * ‖Eig.pout S.P.χ (S.P.G (k + 1))‖ * S.P.δ₀))
        (17 / 16 * (2 * Real.pi * ‖Eig.pout S.P.χ (S.P.G (k + 1))‖ * S.P.δ₀)) := by
    rw [hnorm]
    constructor
    · have := mul_le_mul_of_nonneg_left hd.1 hP0
      linarith
    · have := mul_le_mul_of_nonneg_left hd.2 hP0
      linarith
  have hδ := hS.δ₀_pos
  have hge : 15 / 16 * Eig.cout S.P.χ * S.P.δ₀ ≤ ‖S.P.kickQs k‖ := by
    have := mul_le_mul_of_nonneg_right hcle hδ.le
    nlinarith [hrange.1]
  refine ⟨hrange, ?_, hge⟩
  intro h0
  rw [h0, norm_zero] at hge
  have : 0 < 15 / 16 * Eig.cout S.P.χ * S.P.δ₀ := by positivity
  linarith

/-- `𝖡 = (15/16)c_outδ₀/(20|z|(μ-1)) ≤ |q_s|/(20|z|(μ-1))` (`09_relay.tex:1270-1272`). -/
theorem budget_le (hS : S.Holds) (hDet : S.Det) {C₀ K₁ : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hkn : k < S.P.n) (hc : S.P.ClockUpTo (k + 1)) (h : S.KickTrueHyp C₀ K₁ k) :
    15 / 16 * Eig.cout S.P.χ * S.P.δ₀ / (20 * ‖S.z‖ * (S.P.μ - 1)) ≤
      ‖S.P.kickQs k‖ / (20 * ‖S.z‖ * (S.P.μ - 1)) := by
  obtain ⟨-, -, hge⟩ := qs_facts S hS hDet hk hkn hc h
  obtain ⟨-, -, -, -, hz⟩ := sigma_facts S hS
  have hμ := hS.one_lt_μ
  exact div_le_div_of_nonneg_right hge (by
    have : 0 < S.P.μ - 1 := by linarith
    positivity)

/-- `C_deep ≥ 0`. -/
theorem Cdeep_nonneg (hS : S.Holds) : 0 ≤ S.Cdeep := by
  obtain ⟨-, -, hσ, -, hz⟩ := sigma_facts S hS
  have hμ := hS.one_lt_μ
  have hcN : 0 < Eig.cN S.P.χ := by
    obtain ⟨-, -, -, -, -, -, hcN, -⟩ := Eig.uniform_constants S.P.χ hS.admissible hS.hN
    exact hcN
  have hKlo : 0 < S.Klo := by
    show 0 < Eig.cN S.P.χ * S.P.δ₀ / (22 * ‖S.z‖ * (S.P.μ - 1))
    exact div_pos (mul_pos hcN hS.δ₀_pos) (mul_pos (mul_pos (by norm_num) hz) (by linarith))
  rw [Standing.Cdeep_def]
  have hT := hS.Tpin_pos
  apply div_nonneg _ (mul_pos hσ hKlo).le
  have : 0 ≤ (1 + S.P.Tpin + 32 / (15 * S.sigma0)) ^ 3 := by positivity
  have := Rings.Cmom_pos
  have : 0 ≤ S.P.μ := by linarith
  positivity

/-- **The budget of (Kick3)** (`09_relay.tex:1369-1372`), generic: the six terms of `Err_g` and the
deep term `D` add up to at most `𝖡 = (15/16)c_outδ₀/(20|z|(μ-1))`, by (a), (d) and (f). -/
theorem budget_real {δ₀ c Z μ C₃ sk σ Ctr ρg L Cdeep Cid rt Ipv ρv ι Cod ηb D : ℝ}
    (hδ : 0 < δ₀) (hc : 0 ≤ c) (hZ : 0 < Z) (hμ : 1 < μ) (hμ2 : μ ≤ 2) (hσ : 0 < σ) (hL : 1 ≤ L)
    (hι1 : ι ≤ 1) (hX : 0 ≤ Cid * rt * Ipv * ρv) (hD : D ≤ Cdeep * δ₀ * ρv * L ^ 3)
    (hA : 16 / 15 * (2 * Real.pi * C₃ * δ₀ ^ 2 / σ) ≤ 1 / 4 * (15 / 16) * (c * δ₀ / (20 * Z)))
    (hDd : 2 * Real.pi * C₃ * sk * μ / (3 / 4 * σ * (μ - 1)) + Ctr * ρg * L ^ (3 + 1) +
        (Cdeep + Cid * rt * Ipv) * ρv * L ^ 3 ≤ 1 / 2 * (15 / 16) * (c / (20 * Z * (μ - 1))))
    (hF : Cod * ηb * δ₀ * (μ ^ 2 / (σ ^ 2 * (μ - 1) ^ 2)) +
        2 * Real.pi * C₃ * ηb * (4 * μ * δ₀ / (3 * σ * (μ - 1))) ≤
      1 / 4 * (15 / 16) * (c * δ₀ / (20 * Z * (μ - 1)))) :
    Ctr * δ₀ * ρg * L ^ (3 + 1) + 16 / 15 * (2 * Real.pi * C₃ * δ₀ ^ 2 / σ) +
        2 * Real.pi * C₃ * sk * (4 * μ * δ₀ / (3 * σ * (μ - 1))) +
        2 * Real.pi * C₃ * ηb * (4 * μ * δ₀ / (3 * σ * (μ - 1))) +
        ι * Cid * rt * Ipv * (δ₀ * ρv) + Cod * ηb * δ₀ * (μ ^ 2 / (σ ^ 2 * (μ - 1) ^ 2)) + D ≤
      15 / 16 * c * δ₀ / (20 * Z * (μ - 1)) := by
  have hm1 : 0 < μ - 1 := by linarith
  set B := 15 / 16 * c * δ₀ / (20 * Z * (μ - 1)) with hB
  -- (a)
  have hT2 : 16 / 15 * (2 * Real.pi * C₃ * δ₀ ^ 2 / σ) ≤ 1 / 4 * B := by
    refine hA.trans ?_
    have h1 : c * δ₀ / (20 * Z) ≤ c * δ₀ / (20 * Z * (μ - 1)) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      have : 20 * Z * (μ - 1) ≤ 20 * Z * 1 :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    have := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 1 / 4 * (15 / 16))
    have e : 1 / 4 * (15 / 16) * (c * δ₀ / (20 * Z * (μ - 1))) = 1 / 4 * B := by
      rw [hB]; ring
    linarith
  -- (d)
  have hT3 : 2 * Real.pi * C₃ * sk * (4 * μ * δ₀ / (3 * σ * (μ - 1))) =
      δ₀ * (2 * Real.pi * C₃ * sk * μ / (3 / 4 * σ * (μ - 1))) := by
    field_simp
  have hT1 : Ctr * δ₀ * ρg * L ^ (3 + 1) = δ₀ * (Ctr * ρg * L ^ (3 + 1)) := by ring
  have hT5 : ι * Cid * rt * Ipv * (δ₀ * ρv) + D ≤ δ₀ * ((Cdeep + Cid * rt * Ipv) * ρv * L ^ 3) := by
    have hX' : 0 ≤ δ₀ * (Cid * rt * Ipv * ρv) := mul_nonneg hδ.le hX
    have hL3 : 1 ≤ L ^ 3 := one_le_pow₀ hL
    have h1 : ι * (δ₀ * (Cid * rt * Ipv * ρv)) ≤ δ₀ * (Cid * rt * Ipv * ρv) :=
      mul_le_of_le_one_left hX' hι1
    have h2 : δ₀ * (Cid * rt * Ipv * ρv) ≤ δ₀ * (Cid * rt * Ipv * ρv) * L ^ 3 :=
      le_mul_of_one_le_right hX' hL3
    have e1 : ι * Cid * rt * Ipv * (δ₀ * ρv) = ι * (δ₀ * (Cid * rt * Ipv * ρv)) := by ring
    have e2 : δ₀ * ((Cdeep + Cid * rt * Ipv) * ρv * L ^ 3) =
        Cdeep * δ₀ * ρv * L ^ 3 + δ₀ * (Cid * rt * Ipv * ρv) * L ^ 3 := by ring
    rw [e1, e2]
    linarith
  have hDsum : δ₀ * (2 * Real.pi * C₃ * sk * μ / (3 / 4 * σ * (μ - 1))) +
      δ₀ * (Ctr * ρg * L ^ (3 + 1)) + δ₀ * ((Cdeep + Cid * rt * Ipv) * ρv * L ^ 3) ≤
      1 / 2 * B := by
    have := mul_le_mul_of_nonneg_left hDd hδ.le
    have e : δ₀ * (1 / 2 * (15 / 16) * (c / (20 * Z * (μ - 1)))) = 1 / 2 * B := by
      rw [hB]; ring
    have e' : δ₀ * (2 * Real.pi * C₃ * sk * μ / (3 / 4 * σ * (μ - 1)) + Ctr * ρg * L ^ (3 + 1) +
        (Cdeep + Cid * rt * Ipv) * ρv * L ^ 3) =
        δ₀ * (2 * Real.pi * C₃ * sk * μ / (3 / 4 * σ * (μ - 1))) +
          δ₀ * (Ctr * ρg * L ^ (3 + 1)) + δ₀ * ((Cdeep + Cid * rt * Ipv) * ρv * L ^ 3) := by ring
    linarith
  -- (f)
  have hT6 : Cod * ηb * δ₀ * (μ ^ 2 / (σ ^ 2 * (μ - 1) ^ 2)) +
      2 * Real.pi * C₃ * ηb * (4 * μ * δ₀ / (3 * σ * (μ - 1))) ≤ 1 / 4 * B := by
    refine hF.trans (le_of_eq ?_)
    rw [hB]; ring
  linarith

/-- **`Err_g` as the sum of the six terms and the deep term** (`09_relay.tex:1309-1372`). -/
theorem errG_le_sum (hS : S.Holds) (hDet : S.Det) {C₀ K₁ : ℝ} (hC₀ : 1 ≤ C₀) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k < S.P.n) (hc : S.P.ClockUpTo (k + 1)) (h : S.KickTrueHyp C₀ K₁ k) :
    Kick.errG (S.P.xk k) (S.P.That (k + 1))
        (fun τ => kickErrE S C₀ K₁ k (τ + S.P.That (k + 1)) + ‖S.P.qDeep k τ‖) ≤
      S.Ctr C₀ * S.P.δ₀ * (S.P.ksh (k + 1) / S.P.δ₀) ^ S.gammaMu *
          Real.log (S.P.δ₀ / S.P.ksh (k + 1)) ^ (3 + 1) +
        16 / 15 * (2 * Real.pi * S.C3 * S.P.δ₀ ^ 2 / S.sigma0) +
        2 * Real.pi * S.C3 * Real.sqrt (S.P.ksh (k + 1)) *
          (4 * S.P.μ * S.P.δ₀ / (3 * S.sigma0 * (S.P.μ - 1))) +
        2 * Real.pi * S.C3 * S.etab C₀ K₁ * (4 * S.P.μ * S.P.δ₀ / (3 * S.sigma0 * (S.P.μ - 1))) +
        (if k + 1 < S.P.n then (1 : ℝ) else 0) * S.Cid * S.rT S.P.Tpin * Ip 3 (S.sigma0 / 8) *
          (S.P.δ₀ * (S.P.ksh (k + 1) / S.P.δ₀) ^ S.varthetaMu) +
        S.Cod * S.etab C₀ K₁ * S.P.δ₀ * (S.P.μ ^ 2 / (S.sigma0 ^ 2 * (S.P.μ - 1) ^ 2)) +
        (if k + 1 < S.P.n then
          S.Cdeep * S.P.δ₀ * (S.P.ksh (k + 1) / S.P.δ₀) ^ S.varthetaMu *
            Real.log (S.P.δ₀ / S.P.ksh (k + 1)) ^ 3 else 0) := by
  obtain ⟨hκ, hκδ, -, hL, hTg, -⟩ := kappa_facts S hS hDet hk hkn hc h.ineqC
  obtain ⟨hσp, -, -, hlow, hup, hvt, -, -, -⟩ := rew_facts S hS hDet hk hkn
  obtain ⟨-, -, hσ, -, -⟩ := sigma_facts S hS
  obtain ⟨-, hG1, -, -, -⟩ := level_facts S hS hDet hk hkn
  obtain ⟨-, -, -, hP, hCls, -⟩ := uniform_facts S hS hG1
  obtain ⟨hdi, -, hdb⟩ := deep_facts S hS hDet hk hkn hc h
  obtain ⟨η, hη, -, -⟩ := h.drift
  have hηb : 0 ≤ S.etab C₀ K₁ := hη.1.trans hη.2
  have hC₃ : 0 ≤ S.C3 := (C3_pos S.P.χ S.s S.σ').le
  have hCact : 0 ≤ S.Cact C₀ := le_trans (by linarith) (OneRing.le_Cact S.P.χ S.σ' C₀)
  have hσ' : 0 ≤ S.σ' := by linarith [hS.σ'_gt]
  have hι : 0 ≤ (if k + 1 < S.P.n then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have hγx : S.gammaMu ≤ 1 - S.P.xk k / S.P.sigma (k + 1) :=
    S.gammaMu_le_varthetaMu.trans hvt
  have hγσ' : S.gammaMu ≤ 1 - 16 * S.σ' / (15 * S.sigma0) := S.gammaMu_le_cgamma
  have hE := errE_integral_le (x := S.P.xk k) (σ' := S.σ') (C₃ := S.C3) (Cact := S.Cact C₀)
    (P := S.poutMax) (Cls := Eig.Cls S.P.χ) (ηb := S.etab C₀ K₁) (Tpin := S.P.Tpin)
    (ι := if k + 1 < S.P.n then 1 else 0) (γ := S.gammaMu) (ϑ := S.varthetaMu)
    hκ hκδ hσ hσp hσ' hS.one_lt_μ hS.μ_le hlow hup hC₃ hCact hP hι hCls hηb hS.Tpin_pos.le
    hTg hL hγx hγσ' hvt
  rw [kickErrE_def, errG_split (continuous_errE _ _ _ _ _ _ _ _ _ _ _ _ _) hdi]
  exact add_le_add hE hdb

/-- **(Kick3) on `[-T_g, 0]`** (`09_relay.tex:1309-1372`): `Err_g ≤ 𝖡`. -/
theorem errG_le (hS : S.Holds) (hDet : S.Det) {C₀ K₁ : ℝ} (hC₀ : 1 ≤ C₀) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k < S.P.n) (hc : S.P.ClockUpTo (k + 1)) (h : S.KickTrueHyp C₀ K₁ k) :
    Kick.errG (S.P.xk k) (S.P.That (k + 1))
        (fun τ => kickErrE S C₀ K₁ k (τ + S.P.That (k + 1)) + ‖S.P.qDeep k τ‖) ≤
      15 / 16 * Eig.cout S.P.χ * S.P.δ₀ / (20 * ‖S.z‖ * (S.P.μ - 1)) := by
  obtain ⟨hκ, hκδ, -, hL, -, -⟩ := kappa_facts S hS hDet hk hkn hc h.ineqC
  obtain ⟨-, -, hσ, -, hz⟩ := sigma_facts S hS
  obtain ⟨-, hG1, -, -, -⟩ := level_facts S hS hDet hk hkn
  obtain ⟨hcout, -, -, hP, -, -⟩ := uniform_facts S hS hG1
  have hδ := hS.δ₀_pos
  have hι1 : (if k + 1 < S.P.n then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  have hCid : 0 ≤ S.Cid := by
    show 0 ≤ 4 * Real.pi * (17 / 16) ^ 3 * S.poutMax
    positivity
  have hrt : 0 ≤ S.rT S.P.Tpin :=
    mul_nonneg (pow_nonneg (by linarith [hS.Tpin_pos]) 3) (Real.exp_pos _).le
  have hIpv : 0 ≤ Ip 3 (S.sigma0 / 8) := (Ip_pos 3 (by positivity)).le
  have hρv : 0 ≤ (S.P.ksh (k + 1) / S.P.δ₀) ^ S.varthetaMu :=
    Real.rpow_nonneg (div_nonneg hκ.le hδ.le) _
  have hX : 0 ≤ S.Cid * S.rT S.P.Tpin * Ip 3 (S.sigma0 / 8) *
      (S.P.ksh (k + 1) / S.P.δ₀) ^ S.varthetaMu :=
    mul_nonneg (mul_nonneg (mul_nonneg hCid hrt) hIpv) hρv
  have hCdeep := Cdeep_nonneg S hS
  have hD : (if k + 1 < S.P.n then
        S.Cdeep * S.P.δ₀ * (S.P.ksh (k + 1) / S.P.δ₀) ^ S.varthetaMu *
          Real.log (S.P.δ₀ / S.P.ksh (k + 1)) ^ 3 else 0) ≤
      S.Cdeep * S.P.δ₀ * (S.P.ksh (k + 1) / S.P.δ₀) ^ S.varthetaMu *
        Real.log (S.P.δ₀ / S.P.ksh (k + 1)) ^ 3 := by
    split_ifs
    · exact le_rfl
    · have : 0 ≤ Real.log (S.P.δ₀ / S.P.ksh (k + 1)) ^ 3 := pow_nonneg (by linarith) 3
      positivity
  exact (errG_le_sum S hS hDet hC₀ hk hkn hc h).trans
    (budget_real hδ hcout.le hz hS.one_lt_μ (by linarith [hS.μ_le]) hσ hL hι1 hX hD h.ineqA
      h.ineqD h.ineqF)

/-- **The hypotheses of `prop:kick`** (`09_relay.tex:1233-1397`): for `T'_g ∈ [17T_g/24, T_g]` with
`τ₀ < -T'_g` and (Kick4) for `T'_g`, `Kick.KickHyp` holds with `(Q̄, p) = (C_mom, 3)`,
`err = errE(· + T_g) + |q^deep|` and `Q_pre = |q_{k+1}|`. -/
theorem kickHyp_of (hS : S.Holds) (hDet : S.Det) {C₀ K₁ : ℝ} (hC₀ : 1 ≤ C₀) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k < S.P.n) (hc : S.P.ClockUpTo (k + 1)) (h : S.KickTrueHyp C₀ K₁ k)
    (hset : Kick.IsSetting (S.P.zeta0 k) (S.P.betaK k) (S.P.tau0 k) (S.P.Tpin : EReal)
      (S.P.qKick k))
    {Tg' : ℝ} (h1 : 17 / 24 * S.P.That (k + 1) ≤ Tg') (h2 : Tg' ≤ S.P.That (k + 1))
    (hτ₀ : S.P.tau0 k < -Tg')
    (hpre : Kick.errPre (S.P.xk k) (S.P.tau0 k) Tg' (fun τ => ‖S.P.qKick k τ‖) ≤
      ‖S.P.kickQs k‖ / (20 * ‖S.z‖ * (S.P.μ - 1))) :
    Kick.KickHyp S.P.χ S.P.μ (S.P.G k) (S.P.G (k + 1)) (S.P.betaK k) (S.P.tau0 k)
      (S.P.Tpin : EReal) (S.P.qKick k) Tg' Rings.Cmom 3 (S.P.kickQs k)
      (fun τ => kickErrE S C₀ K₁ k (τ + S.P.That (k + 1)) + ‖S.P.qDeep k τ‖)
      (fun τ => ‖S.P.qKick k τ‖) := by
  obtain ⟨hTg0⟩ := And.intro (kappa_facts S hS hDet hk hkn hc h.ineqC).2.2.2.2.2 trivial
  obtain ⟨hGk, hG1, hdk, hdk1, -⟩ := level_facts S hS hDet hk hkn
  obtain ⟨-, -, hσ, -, hz⟩ := sigma_facts S hS
  obtain ⟨-, -, hcP, hP, hCls, -⟩ := uniform_facts S hS hG1
  obtain ⟨-, hne, hge⟩ := qs_facts S hS hDet hk hkn hc h
  obtain ⟨-, hdInt, -⟩ := deep_facts S hS hDet hk hkn hc h
  obtain ⟨hdi, -, -⟩ := deep_facts S hS hDet hk hkn hc h
  obtain ⟨η, hη, -, -⟩ := h.drift
  have hηb : 0 ≤ S.etab C₀ K₁ := hη.1.trans hη.2
  have hC₃ : 0 ≤ S.C3 := (C3_pos S.P.χ S.s S.σ').le
  have hCact : 0 ≤ S.Cact C₀ := le_trans (by linarith) (OneRing.le_Cact S.P.χ S.σ' C₀)
  have hι : 0 ≤ (if k + 1 < S.P.n then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have hμ0 : 0 ≤ S.P.μ := by linarith [hS.one_lt_μ]
  have hTpin := hS.Tpin_pos
  have hxre : (Eig.lam S.P.χ (S.P.G k) / (S.P.μ : ℂ)).re = S.P.xk k := by
    rw [Complex.div_ofReal_re]; rfl
  have hcont : ContinuousOn (S.P.qKick k) (Icc (S.P.tau0 k) S.P.Tpin) := by
    have := hset.continuousOn
    rwa [Kick.interval_coe] at this
  have hTg'0 : 0 < Tg' := by nlinarith
  set Tg := S.P.That (k + 1) with hTgdef
  have hsub : Icc (-Tg') 0 ⊆ Icc (-Tg) 0 := Icc_subset_Icc (by linarith) le_rfl
  have hEc : Continuous (fun τ => kickErrE S C₀ K₁ k (τ + Tg)) :=
    (continuous_errE _ _ _ _ _ _ _ _ _ _ _ _ _).comp (continuous_add_const _)
  have herr0 : ∀ τ ∈ Icc (-Tg) 0, 0 ≤ kickErrE S C₀ K₁ k (τ + Tg) + ‖S.P.qDeep k τ‖ := by
    intro τ hτ
    have hu : τ + Tg ∈ Icc (0 : ℝ) Tg := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have := errE_nonneg (σ' := S.σ') (σp := S.P.sigma (k + 1)) (σ := S.sigma0) hC₃ hCact
      (le_of_lt (kappa_facts S hS hDet hk hkn hc h.ineqC).1) hηb hP hι hCls hTpin.le hμ0 hu
    rw [kickErrE_def]
    exact add_nonneg this (norm_nonneg _)
  refine
    { setting := hset
      one_lt_μ := hS.one_lt_μ
      μ_le_two := by linarith [hS.μ_le]
      G_mem := hGk
      G'_mem := hG1
      detuned := hdk
      detuned' := hdk1
      Tg_pos := hTg'0
      τ₀_lt := hτ₀
      τ₁_pos := EReal.coe_pos.2 hTpin
      Qbar_pos := Rings.Cmom_pos
      q1 := ?_
      q2 := ?_
      q3 := ?_
      kick1 := ?_
      kick2 := kick2_of_ge S hS hDet hk hkn hc h.ineqC h1
      kick3 := ?_
      kick4 := by rw [hxre]; exact hpre }
  · -- (Q1)
    refine ⟨hne, ?_, fun τ hτ => herr0 τ (hsub hτ), fun τ hτ => ?_⟩
    · exact (hEc.integrableOn_Icc).add (hdInt.mono_set hsub)
    · exact q1_bound S hS hDet hC₀ hk hkn hc h (hsub hτ)
  · -- (Q2)
    have hsub2 : Icc (S.P.tau0 k) (-Tg') ⊆ Icc (S.P.tau0 k) S.P.Tpin :=
      Icc_subset_Icc le_rfl (by linarith)
    exact ⟨((hcont.mono hsub2).norm).integrableOn_Icc, fun τ _ => norm_nonneg _,
      fun τ _ => le_rfl⟩
  · -- (Q3)
    intro τ hτ hτ0
    rw [Kick.interval_coe] at hτ
    exact h.pin τ ⟨hτ0, hτ.2⟩
  · -- (Kick1)
    refine h.ineqB.trans (div_le_div_of_nonneg_right hge ?_)
    exact mul_nonneg (mul_nonneg (by positivity) Rings.Cmom_pos.le) (Ip_pos 3 (by positivity)).le
  · -- (Kick3)
    rw [hxre]
    refine le_trans ?_ ((errG_le S hS hDet hC₀ hk hkn hc h).trans (budget_le S hS hDet hk hkn hc h))
    unfold Kick.errG
    have hfi : IntervalIntegrable (fun τ => Real.exp (-(S.P.xk k * τ)) *
        (kickErrE S C₀ K₁ k (τ + Tg) + ‖S.P.qDeep k τ‖)) volume (-Tg) 0 := by
      have he : IntervalIntegrable (fun τ => Real.exp (-(S.P.xk k * τ)) *
          kickErrE S C₀ K₁ k (τ + Tg)) volume (-Tg) 0 :=
        (by fun_prop : Continuous fun τ : ℝ => Real.exp (-(S.P.xk k * τ))).mul hEc
          |>.intervalIntegrable _ _
      have := he.add hdi
      refine this.congr ?_
      intro τ _
      simp only
      ring
    refine intervalIntegral.integral_mono_interval (by linarith) (by linarith) le_rfl ?_ hfi
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun τ hτ => ?_
    exact mul_nonneg (Real.exp_pos _).le (herr0 τ ⟨hτ.1.le, hτ.2⟩)

end KickTrueAux

end Relay

end NonUniqueEuler
