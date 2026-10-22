import NonUniqueEuler.I.Sec9.Deep
import NonUniqueEuler.I.Sec9.Drift
import NonUniqueEuler.I.Sec5.ActiveT1
import NonUniqueEuler.H.Sec9.KickTrue.Setup
import NonUniqueEuler.H.Sec9.KickTrue.ErrG
import NonUniqueEuler.H.Sec9.KickTrue.RingMoment

/-!
# Helpers for `P/Sec9/KickTrue`: hypothesis (Q1) of `prop:kick`

Helper file of `P/Sec9/KickTrue.lean` (`lem:kicktrue`, step (Q1), `09_relay.tex:1288-1308`).
For `1 ≤ k < n`, `κ = κ♯_{k+1}`, `T_g = T̂_{k+1}`, `η_b = S.etab C₀ K₁`, `ι = 1_{k+1<n}`:
* `kickErrE S C₀ K₁ k`: the continuous part `errE` of `err` with the constants of the lemma;
* `kickQs_mul_exp`: `q_s e^{z'τ} = 2π pout_*(G_{k+1}) c_{k+1}(T_g) e^{z'(τ + T_g)}`;
* `q1_bound`: `|q_{k+1}(τ) - q_s e^{z'τ}| ≤ errE(τ + T_g) + |q^deep(τ)|` on `[-T_g, 0]`
  (`lem:deep`(1), `qRing_eq`, `cor:active-moment`, `thm:active` "Moreover", `eq:drift-interval`);
* `deep_facts`: integrability of `|q^deep|` and of `e^{-xτ}|q^deep|` on `[-T_g, 0]`, and
  `∫ e^{-xτ}|q^deep| ≤ 1_{k+1<n} C_deep δ₀(κ/δ₀)^{ϑ_μ}L³` (`lem:deep`(1),(3)).
Everything here is proved.
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler

namespace Relay

namespace KickTrueAux

open RingData Datum

variable (S : Standing)

/-- The continuous part of `err` for `lem:kicktrue` at level `k` (`09_relay.tex:1304-1308`), in active
time `u` of ring `k+1`. -/
def kickErrE (C₀ K₁ : ℝ) (k : ℕ) : ℝ → ℝ :=
  errE S.C3 (S.Cact C₀) (S.P.ksh (k + 1)) S.σ' (S.P.sigma (k + 1)) (S.etab C₀ K₁) S.poutMax
    (if k + 1 < S.P.n then 1 else 0) S.P.Tpin S.P.μ S.sigma0 (Eig.Cls S.P.χ) (S.P.That (k + 1))

theorem kickErrE_def (C₀ K₁ : ℝ) (k : ℕ) : kickErrE S C₀ K₁ k =
    errE S.C3 (S.Cact C₀) (S.P.ksh (k + 1)) S.σ' (S.P.sigma (k + 1)) (S.etab C₀ K₁) S.poutMax
      (if k + 1 < S.P.n then 1 else 0) S.P.Tpin S.P.μ S.sigma0 (Eig.Cls S.P.χ)
      (S.P.That (k + 1)) := rfl

/-- `q_s e^{z'τ} = 2π pout_*(G_{k+1}) (c_{k+1}(T_g) e^{z'(τ + T_g)})` (`09_relay.tex:1297`). -/
theorem kickQs_mul_exp (k : ℕ) (τ : ℝ) :
    S.P.kickQs k * Complex.exp (Eig.lam S.P.χ (S.P.G (k + 1)) * τ) =
      2 * Real.pi * Eig.pout S.P.χ (S.P.G (k + 1)) *
        (S.P.runCoefK (k + 1) (S.P.That (k + 1)) *
          Complex.exp (S.P.lam (k + 1) * ((τ + S.P.That (k + 1) : ℝ) : ℂ))) := by
  simp only [Approx.kickQs, Approx.lam]
  have : Complex.exp (Eig.lam S.P.χ (S.P.G (k + 1)) * ((τ + S.P.That (k + 1) : ℝ) : ℂ)) =
      Complex.exp (Eig.lam S.P.χ (S.P.G (k + 1)) * (S.P.That (k + 1) : ℂ)) *
        Complex.exp (Eig.lam S.P.χ (S.P.G (k + 1)) * (τ : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [this]
  ring

/-- `‖2π a b e^{z u}‖ = 2π‖a‖‖b‖e^{Re z u}` for real `u`. -/
theorem norm_two_pi_mul (a b z : ℂ) (u : ℝ) :
    ‖2 * Real.pi * a * (b * Complex.exp (z * u))‖ =
      2 * Real.pi * ‖a‖ * ‖b‖ * Real.exp (z.re * u) := by
  rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_exp, Complex.re_mul_ofReal,
    Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  norm_num
  ring

/-- **(Q1) of `prop:kick`** (`09_relay.tex:1288-1308`): for `τ ∈ [-T_g, 0]`,
`|q_{k+1}(τ) - q_s e^{z'τ}| ≤ errE(τ + T_g) + |q^deep(τ)|`. -/
theorem q1_bound (hS : S.Holds) (hDet : S.Det) {C₀ K₁ : ℝ} (hC₀ : 1 ≤ C₀) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k < S.P.n) (hc : S.P.ClockUpTo (k + 1)) (h : S.KickTrueHyp C₀ K₁ k) {τ : ℝ}
    (hτ : τ ∈ Icc (-S.P.That (k + 1)) 0) :
    ‖S.P.qKick k τ - S.P.kickQs k * Complex.exp (Eig.lam S.P.χ (S.P.G (k + 1)) * τ)‖ ≤
      kickErrE S C₀ K₁ k (τ + S.P.That (k + 1)) + ‖S.P.qDeep k τ‖ := by
  obtain ⟨hκ, hκδ, -, -, -, hTg0⟩ := kappa_facts S hS hDet hk hkn hc h.ineqC
  obtain ⟨hT, -, -, -, -⟩ := clock_facts S hS hk hkn hc
  obtain ⟨-, hG1, -, -, -⟩ := level_facts S hS hDet hk hkn
  obtain ⟨-, -, hpmax, -, hCls, -⟩ := uniform_facts S hS hG1
  have hA := hS.valid.A_pos (k + 1)
  have hμ0 : 0 ≤ S.P.μ := by linarith [hS.one_lt_μ]
  set Tg := S.P.That (k + 1) with hTgdef
  set κ := S.P.ksh (k + 1) with hκdef
  set u := τ + Tg with hudef
  have hu : u ∈ Icc (0 : ℝ) Tg := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  -- the drift with `η_b`
  obtain ⟨η, hη, hdh, -⟩ := h.drift
  have hηb : 0 ≤ S.etab C₀ K₁ := hη.1.trans hη.2
  have hdh' := hdh.mono le_rfl hη.2 hA.le hμ0
  have hdrift := (drift S hS hDet (k := k + 1) (by omega) hkn hc ⟨hTg0.le, le_rfl⟩ hηb hdh').1
    u hu Tg ⟨hu.2, le_rfl⟩
  -- the split `q = q^ring + q^deep` and `q^ring = 2π pout_3[w_{k+1}]`
  have hdeep := (deep S hS hDet hk hkn hc).1.2.1 τ hτ
  have hring := qRing_eq S.P hS.valid k τ
  have htime : S.P.T (k + 1) + τ / S.P.A (k + 1) = S.P.tsh (k + 1) + u / S.P.A (k + 1) := by
    rw [hT, hudef]; field_simp; ring
  rw [htime] at hring
  -- the moment bound of `cor:active-moment` at `u`, and `â ρ̂ ≤ C(C₀)κ⟨u⟩³e^{σ'u}`
  have hmom := (h.active u hu).moment
  have htone := (OneRing.active_tOne S.P.χ hS.admissible hS.hN ⟨hS.σ'_gt, hS.σ'_lt_sigb⟩ hC₀ hG1
    hκ).2 u hu.1
  have hC₃ : 0 ≤ S.C3 := (C3_pos S.P.χ S.s S.σ').le
  -- the algebraic decomposition
  set R := 2 * Real.pi * BS.pout 3 (S.P.w (k + 1) (S.P.tsh (k + 1) + u / S.P.A (k + 1))) with hR
  set X := 2 * Real.pi * Eig.pout S.P.χ (S.P.G (k + 1)) *
    (S.P.runCoefK (k + 1) u * Complex.exp (S.P.lam (k + 1) * (u : ℂ))) with hX
  have hqs := kickQs_mul_exp S k τ
  have hsplit : S.P.qKick k τ - S.P.kickQs k * Complex.exp (Eig.lam S.P.χ (S.P.G (k + 1)) * τ) =
      (R - X) + 2 * Real.pi * Eig.pout S.P.χ (S.P.G (k + 1)) *
        ((S.P.runCoefK (k + 1) u - S.P.runCoefK (k + 1) Tg) *
          Complex.exp (S.P.lam (k + 1) * (u : ℂ))) + S.P.qDeep k τ := by
    rw [hdeep, hring, hqs, hX]
    ring
  rw [hsplit]
  have hnX := norm_two_pi_mul (Eig.pout S.P.χ (S.P.G (k + 1)))
    (S.P.runCoefK (k + 1) u - S.P.runCoefK (k + 1) Tg) (S.P.lam (k + 1)) u
  have hre : (S.P.lam (k + 1)).re = S.P.sigma (k + 1) := rfl
  rw [hre] at hnX
  -- bound the drift term
  have hdiff : ‖S.P.runCoefK (k + 1) u - S.P.runCoefK (k + 1) Tg‖ ≤
      (if k + 1 < S.P.n then 1 else 0) * (2 * ((1 + (S.P.Tpin + S.P.μ * u)) ^ 3 *
        Real.exp (-(S.sigma0 * (S.P.Tpin + S.P.μ * u) / 4))) * κ) +
        Eig.Cls S.P.χ * S.etab C₀ K₁ * (Tg - u) * κ := by
    rw [norm_sub_rev]
    refine hdrift.trans (le_of_eq ?_)
    split_ifs <;> simp [Standing.rT_def, hκdef]
  have hpos_e : 0 ≤ Real.exp (S.P.sigma (k + 1) * u) := (Real.exp_pos _).le
  have hD : 2 * Real.pi * ‖Eig.pout S.P.χ (S.P.G (k + 1))‖ *
        ‖S.P.runCoefK (k + 1) u - S.P.runCoefK (k + 1) Tg‖ * Real.exp (S.P.sigma (k + 1) * u) ≤
      2 * Real.pi * S.poutMax * ((if k + 1 < S.P.n then 1 else 0) *
        (2 * ((1 + (S.P.Tpin + S.P.μ * u)) ^ 3 *
          Real.exp (-(S.sigma0 * (S.P.Tpin + S.P.μ * u) / 4))) * κ)) *
          Real.exp (S.P.sigma (k + 1) * u) +
        2 * Real.pi * S.poutMax * (Eig.Cls S.P.χ * S.etab C₀ K₁ * (Tg - u) * κ) *
          Real.exp (S.P.sigma (k + 1) * u) := by
    have h2pi : 0 ≤ 2 * Real.pi := by positivity
    have hn0 := norm_nonneg (S.P.runCoefK (k + 1) u - S.P.runCoefK (k + 1) Tg)
    have hstep : 2 * Real.pi * ‖Eig.pout S.P.χ (S.P.G (k + 1))‖ *
          ‖S.P.runCoefK (k + 1) u - S.P.runCoefK (k + 1) Tg‖ ≤
        2 * Real.pi * S.poutMax * ((if k + 1 < S.P.n then 1 else 0) *
          (2 * ((1 + (S.P.Tpin + S.P.μ * u)) ^ 3 *
            Real.exp (-(S.sigma0 * (S.P.Tpin + S.P.μ * u) / 4))) * κ) +
          Eig.Cls S.P.χ * S.etab C₀ K₁ * (Tg - u) * κ) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hpmax h2pi) hdiff hn0
      exact mul_nonneg h2pi ((norm_nonneg _).trans hpmax)
    have := mul_le_mul_of_nonneg_right hstep hpos_e
    linarith
  -- bound the moment bracket
  have hM : ‖R - X‖ ≤ 2 * Real.pi * S.C3 * (S.Cact C₀ * κ * Prelim.jap u ^ 3 *
        Real.exp (S.σ' * u)) +
      2 * Real.pi * S.C3 * (κ * Real.exp (S.P.sigma (k + 1) * u)) ^ 2 +
      2 * Real.pi * S.C3 * (κ * Real.exp (S.P.sigma (k + 1) * u) * Real.sqrt κ) +
      2 * Real.pi * S.C3 * (κ * Real.exp (S.P.sigma (k + 1) * u) * S.etab C₀ K₁) := by
    refine hmom.trans ?_
    have hah : S.ahatK (k + 1) u = κ * Real.exp (S.P.sigma (k + 1) * u) := rfl
    have hrho : S.ahatK (k + 1) u * S.rhoHatK C₀ (k + 1) u ≤
        S.Cact C₀ * κ * Prelim.jap u ^ 3 * Real.exp (S.σ' * u) := htone
    have h2 : 0 ≤ 2 * Real.pi * S.C3 := by positivity
    have := mul_le_mul_of_nonneg_left hrho h2
    rw [hah] at this ⊢
    nlinarith
  -- assemble
  calc ‖(R - X) + 2 * Real.pi * Eig.pout S.P.χ (S.P.G (k + 1)) *
          ((S.P.runCoefK (k + 1) u - S.P.runCoefK (k + 1) Tg) *
            Complex.exp (S.P.lam (k + 1) * (u : ℂ))) + S.P.qDeep k τ‖
      ≤ ‖R - X‖ + ‖2 * Real.pi * Eig.pout S.P.χ (S.P.G (k + 1)) *
          ((S.P.runCoefK (k + 1) u - S.P.runCoefK (k + 1) Tg) *
            Complex.exp (S.P.lam (k + 1) * (u : ℂ)))‖ + ‖S.P.qDeep k τ‖ := norm_add₃_le
    _ ≤ kickErrE S C₀ K₁ k u + ‖S.P.qDeep k τ‖ := by
      rw [hnX, kickErrE_def]
      unfold errE
      linarith [hM, hD]

/-- **The deep term** (`lem:deep`(1),(3), `09_relay.tex:1369-1372`): `|q^deep|` and `e^{-xτ}|q^deep|`
are integrable on `[-T_g, 0]`, and `∫_{-T_g}^0 e^{-xτ}|q^deep| ≤ 1_{k+1<n} C_deep δ₀(κ/δ₀)^{ϑ_μ}L³`. -/
theorem deep_facts (hS : S.Holds) (hDet : S.Det) {C₀ K₁ : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hkn : k < S.P.n) (hc : S.P.ClockUpTo (k + 1)) (h : S.KickTrueHyp C₀ K₁ k) :
    IntervalIntegrable (fun τ => Real.exp (-(S.P.xk k * τ)) * ‖S.P.qDeep k τ‖) volume
        (-S.P.That (k + 1)) 0 ∧
      IntegrableOn (fun τ => ‖S.P.qDeep k τ‖) (Icc (-S.P.That (k + 1)) 0) ∧
      ∫ τ in (-S.P.That (k + 1))..0, Real.exp (-(S.P.xk k * τ)) * ‖S.P.qDeep k τ‖ ≤
        (if k + 1 < S.P.n then
          S.Cdeep * S.P.δ₀ * (S.P.ksh (k + 1) / S.P.δ₀) ^ S.varthetaMu *
            Real.log (S.P.δ₀ / S.P.ksh (k + 1)) ^ 3 else 0) := by
  have hTg0 := (kappa_facts S hS hDet hk hkn hc h.ineqC).2.2.2.2.2
  have hD := deep S hS hDet hk hkn hc
  have hle : -S.P.That (k + 1) ≤ 0 := by linarith
  have hw : IntervalIntegrable (fun τ => Real.exp (-(S.P.xk k * τ)) * ‖S.P.qDeep k τ‖) volume
        (-S.P.That (k + 1)) 0 ∧
      ∫ τ in (-S.P.That (k + 1))..0, Real.exp (-(S.P.xk k * τ)) * ‖S.P.qDeep k τ‖ ≤
        (if k + 1 < S.P.n then
          S.Cdeep * S.P.δ₀ * (S.P.ksh (k + 1) / S.P.δ₀) ^ S.varthetaMu *
            Real.log (S.P.δ₀ / S.P.ksh (k + 1)) ^ 3 else 0) := by
    by_cases hlt : k + 1 < S.P.n
    · obtain ⟨-, -, hconf, hlo⟩ := h.deeper hlt
      obtain ⟨hi, hb, hb'⟩ := (hD.2 hlt hconf).2 hlo h.ineqC
      simp only [hlt, ↓reduceIte]
      exact ⟨hi, hb.trans hb'⟩
    · have heq : k + 1 = S.P.n := by omega
      have h0 : (fun τ => Real.exp (-(S.P.xk k * τ)) * ‖S.P.qDeep k τ‖) = fun _ => 0 := by
        funext τ
        rw [Approx.qDeep_of_succ_eq_n S.P heq τ, norm_zero, mul_zero]
      rw [h0]
      simp only [hlt, ↓reduceIte]
      simp
  refine ⟨hw.1, ?_, hw.2⟩
  have hm : IntervalIntegrable (fun τ => Real.exp (-(S.P.xk k * τ)) * ‖S.P.qDeep k τ‖ *
      Real.exp (S.P.xk k * τ)) volume (-S.P.That (k + 1)) 0 :=
    hw.1.mul_continuousOn (by fun_prop)
  have hfun : (fun τ => Real.exp (-(S.P.xk k * τ)) * ‖S.P.qDeep k τ‖ *
      Real.exp (S.P.xk k * τ)) = fun τ => ‖S.P.qDeep k τ‖ := by
    funext τ
    rw [mul_comm, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  rw [hfun] at hm
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hle).1 hm

end KickTrueAux

end Relay

end NonUniqueEuler
