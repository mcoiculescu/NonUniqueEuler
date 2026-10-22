import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import NonUniqueEuler.Defs.Sec2.Conventions
import NonUniqueEuler.I.Infra.Ip.Ip

/-!
# Helpers for `P/Sec9/KickTrue`: elementary real estimates

Helper file of `P/Sec9/KickTrue.lean` (`lem:kicktrue`, `09_relay.tex:1233-1397`). Pure real
analysis, no project objects except `Prelim.jap` and `Ip`:
* `kappa_mul_exp_eq`, `kappa_mul_exp_le`, `kappa_mul_exp_self`: `κe^{yT_g} = δ₀(κ/δ₀)^{1-y/σ₊}` for
  `T_g = σ₊⁻¹log(δ₀/κ)` (`09_relay.tex:1258-1259`), and the consequences;
* `one_lt_log_four`, `one_le_log_of_le_rpow`: (c) gives `L ≥ 1` (`09_relay.tex:1257`);
* `integral_exp_mul_eq`, `integral_weight_exp_le`, `integral_v_exp_le`: the three elementary
  integrals;
* `errT1_le` … `errT6_le`: the six error terms of `Err_g` (`09_relay.tex:1316-1372`), in active time
  `u ∈ [0, T_g]` with the weight `e^{x(T_g-u)}`.
The first four lemmas are copies of `Relay.DeepAux` (`H/Sec9/Deep/Real.lean`, proved there).
Everything here is proved.
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler

namespace Relay

namespace KickTrueAux

/-- `κ e^{x T_g} = δ₀ (κ/δ₀)^{1 - x/σ₁}` for `T_g = σ₁⁻¹ log(δ₀/κ)` (`09_relay.tex:1258-1259`). -/
theorem kappa_mul_exp_eq {κ δ₀ σ₁ : ℝ} (x : ℝ) (hκ : 0 < κ) (hδ : 0 < δ₀) (hσ : σ₁ ≠ 0) :
    κ * Real.exp (x * (σ₁⁻¹ * Real.log (δ₀ / κ))) = δ₀ * (κ / δ₀) ^ (1 - x / σ₁) := by
  have hq : 0 < κ / δ₀ := div_pos hκ hδ
  rw [Real.rpow_def_of_pos hq]
  have hlog : Real.log (κ / δ₀) = -Real.log (δ₀ / κ) := by
    rw [← Real.log_inv, inv_div]
  rw [hlog]
  have hsplit : -Real.log (δ₀ / κ) * (1 - x / σ₁) =
      -Real.log (δ₀ / κ) + x * (σ₁⁻¹ * Real.log (δ₀ / κ)) := by
    field_simp
    ring
  rw [hsplit, Real.exp_add, Real.exp_neg, Real.exp_log (div_pos hδ hκ), inv_div]
  field_simp

/-- `κ e^{y T_g} ≤ δ₀ (κ/δ₀)^g` whenever `g ≤ 1 - y/σ₁` and `0 < κ < δ₀`. -/
theorem kappa_mul_exp_le {κ δ₀ σ₁ g : ℝ} (y : ℝ) (hκ : 0 < κ) (hκδ : κ < δ₀) (hσ : σ₁ ≠ 0)
    (hg : g ≤ 1 - y / σ₁) :
    κ * Real.exp (y * (σ₁⁻¹ * Real.log (δ₀ / κ))) ≤ δ₀ * (κ / δ₀) ^ g := by
  have hδ : 0 < δ₀ := hκ.trans hκδ
  rw [kappa_mul_exp_eq y hκ hδ hσ]
  apply mul_le_mul_of_nonneg_left _ hδ.le
  exact Real.rpow_le_rpow_of_exponent_ge (div_pos hκ hδ) ((div_le_one hδ).2 hκδ.le) hg

/-- `κ e^{σ₁ T_g} = δ₀`. -/
theorem kappa_mul_exp_self {κ δ₀ σ₁ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ₀) (hσ : σ₁ ≠ 0) :
    κ * Real.exp (σ₁ * (σ₁⁻¹ * Real.log (δ₀ / κ))) = δ₀ := by
  rw [← mul_assoc, mul_inv_cancel₀ hσ, one_mul, Real.exp_log (div_pos hδ hκ)]
  field_simp

/-- `1 < log 4`. -/
theorem one_lt_log_four : 1 < Real.log 4 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

/-- `κ ≤ δ₀ 4^{-μ/(μ-1)}` with `κ > 0`, `μ > 1` gives `log(δ₀/κ) ≥ (μ/(μ-1)) log 4`
(`09_relay.tex:1257`). -/
theorem log_ge_of_le_rpow {κ δ₀ μ : ℝ} (hκ : 0 < κ)
    (h : κ ≤ δ₀ * (4 : ℝ) ^ (-(μ / (μ - 1)))) : μ / (μ - 1) * Real.log 4 ≤ Real.log (δ₀ / κ) := by
  set p : ℝ := μ / (μ - 1) with hp
  have h4p : 0 < (4 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) p
  have h4np : (4 : ℝ) ^ (-p) = ((4 : ℝ) ^ p)⁻¹ := Real.rpow_neg (by norm_num) p
  have hle : (4 : ℝ) ^ p ≤ δ₀ / κ := by
    rw [le_div_iff₀ hκ]
    rw [h4np] at h
    have := mul_le_mul_of_nonneg_left h h4p.le
    calc (4 : ℝ) ^ p * κ ≤ (4 : ℝ) ^ p * (δ₀ * ((4 : ℝ) ^ p)⁻¹) := this
      _ = δ₀ := by field_simp
  rw [← Real.log_rpow (by norm_num)]
  exact Real.log_le_log h4p hle

/-- `κ ≤ δ₀ 4^{-μ/(μ-1)}` with `κ > 0`, `μ > 1` gives `log(δ₀/κ) ≥ 1` (`09_relay.tex:1257`). -/
theorem one_le_log_of_le_rpow {κ δ₀ μ : ℝ} (hκ : 0 < κ) (hμ : 1 < μ)
    (h : κ ≤ δ₀ * (4 : ℝ) ^ (-(μ / (μ - 1)))) : 1 ≤ Real.log (δ₀ / κ) := by
  have hlog := log_ge_of_le_rpow hκ h
  have hp1 : 1 ≤ μ / (μ - 1) := by
    rw [one_le_div (by linarith)]
    linarith
  have hl4 := one_lt_log_four
  nlinarith

/-! ### Elementary integrals -/

/-- `∫₀ᵀ e^{au} du = (e^{aT} - 1)/a` for `a ≠ 0`. -/
theorem integral_exp_mul_eq (a T : ℝ) (ha : a ≠ 0) :
    ∫ u in (0 : ℝ)..T, Real.exp (a * u) = (Real.exp (a * T) - 1) / a := by
  have hderiv : ∀ u ∈ uIcc (0 : ℝ) T,
      HasDerivAt (fun u : ℝ => Real.exp (a * u) / a) (Real.exp (a * u)) u := by
    intro u _
    have h : HasDerivAt (fun u : ℝ => Real.exp (a * u) / a) (Real.exp (a * u) * (a * 1) / a) u :=
      (((hasDerivAt_id u).const_mul a).exp).div_const a
    refine h.congr_deriv ?_
    field_simp
  have hint : IntervalIntegrable (fun u : ℝ => Real.exp (a * u)) volume 0 T :=
    (by fun_prop : Continuous fun u : ℝ => Real.exp (a * u)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [mul_zero, Real.exp_zero]
  ring

/-- `∫₀ᵀ e^{x(T-u)} e^{bu} du ≤ e^{bT}/(b-x)` for `x < b`, `T ≥ 0`. -/
theorem integral_weight_exp_le {x b T : ℝ} (hxb : x < b) :
    ∫ u in (0 : ℝ)..T, Real.exp (x * (T - u)) * Real.exp (b * u) ≤
      Real.exp (b * T) / (b - x) := by
  have hab : 0 < b - x := sub_pos.2 hxb
  have heq : (fun u : ℝ => Real.exp (x * (T - u)) * Real.exp (b * u)) =
      fun u => Real.exp (x * T) * Real.exp ((b - x) * u) := by
    funext u
    rw [← Real.exp_add, ← Real.exp_add]
    ring_nf
  rw [heq, intervalIntegral.integral_const_mul, integral_exp_mul_eq _ _ hab.ne']
  have h1 : Real.exp (b * T) = Real.exp (x * T) * Real.exp ((b - x) * T) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : (Real.exp ((b - x) * T) - 1) / (b - x) ≤ Real.exp ((b - x) * T) / (b - x) :=
    div_le_div_of_nonneg_right (by linarith) hab.le
  calc Real.exp (x * T) * ((Real.exp ((b - x) * T) - 1) / (b - x))
      ≤ Real.exp (x * T) * (Real.exp ((b - x) * T) / (b - x)) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = Real.exp (b * T) / (b - x) := by rw [h1]; ring

/-- `∫₀ᵀ v e^{-av} dv ≤ 1/a²` for `a > 0`, `T ≥ 0`. -/
theorem integral_v_exp_le {a T : ℝ} (ha : 0 < a) (hT : 0 ≤ T) :
    ∫ v in (0 : ℝ)..T, v * Real.exp (-(a * v)) ≤ 1 / a ^ 2 := by
  have hderiv : ∀ v ∈ uIcc (0 : ℝ) T,
      HasDerivAt (fun v : ℝ => -(v / a + 1 / a ^ 2) * Real.exp (-(a * v)))
        (v * Real.exp (-(a * v))) v := by
    intro v _
    have h1 : HasDerivAt (fun v : ℝ => -(v / a + 1 / a ^ 2)) (-(1 / a)) v :=
      (((hasDerivAt_id v).div_const a).add_const (1 / a ^ 2)).neg
    have h2 : HasDerivAt (fun v : ℝ => Real.exp (-(a * v))) (Real.exp (-(a * v)) * (-(a * 1))) v :=
      (((hasDerivAt_id v).const_mul a).neg).exp
    refine (h1.mul h2).congr_deriv ?_
    field_simp
    ring
  have hint : IntervalIntegrable (fun v : ℝ => v * Real.exp (-(a * v))) volume 0 T :=
    (by fun_prop : Continuous fun v : ℝ => v * Real.exp (-(a * v))).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have h0 : 0 ≤ (T / a + 1 / a ^ 2) * Real.exp (-(a * T)) := by positivity
  simp only [zero_div, zero_add, mul_zero, neg_zero, Real.exp_zero, mul_one]
  linarith

/-- `⟨t⟩ ≤ 1 + t` for `t ≥ 0`. -/
theorem jap_le_one_add {t : ℝ} (ht : 0 ≤ t) : Prelim.jap t ≤ 1 + t := by
  rw [Prelim.jap, Real.sqrt_le_left (by linarith)]
  nlinarith

/-- `⟨u⟩ ≤ ⟨t⟩` for `0 ≤ u ≤ t`. -/
theorem jap_mono {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) : Prelim.jap u ≤ Prelim.jap t := by
  rw [Prelim.jap, Prelim.jap]
  exact Real.sqrt_le_sqrt (by nlinarith)

theorem continuous_jap : Continuous Prelim.jap := by
  unfold Prelim.jap
  fun_prop

/-- `1/R ≤ 4μ/(3σ(μ-1))` for `R ≥ (3/4)σ(μ-1)/μ` (`eq:Rew`). -/
theorem inv_le_of_rew {σ μ R : ℝ} (hσ : 0 < σ) (hμ : 1 < μ) (hR : 3 / 4 * σ * ((μ - 1) / μ) ≤ R) :
    1 / R ≤ 4 * μ / (3 * σ * (μ - 1)) := by
  have hμ0 : 0 < μ := by linarith
  have hpos : 0 < 3 / 4 * σ * ((μ - 1) / μ) := by
    have : 0 < μ - 1 := by linarith
    positivity
  calc 1 / R ≤ 1 / (3 / 4 * σ * ((μ - 1) / μ)) := one_div_le_one_div_of_le hpos hR
    _ = 4 * μ / (3 * σ * (μ - 1)) := by
      have : μ - 1 ≠ 0 := by linarith
      field_simp

/-! ### The six terms of `Err_g` (`09_relay.tex:1316-1372`), in active time with weight
`e^{x(T_g - u)}` -/

/-- A generic exponential term: `∫₀^{T} e^{x(T-u)} K e^{bu} du ≤ K e^{bT}/(b-x)`. -/
theorem errT_exp_le {x b T K : ℝ} (hxb : x < b) (hK : 0 ≤ K) :
    ∫ u in (0 : ℝ)..T, Real.exp (x * (T - u)) * (K * Real.exp (b * u)) ≤
      K * Real.exp (b * T) / (b - x) := by
  have heq : (fun u : ℝ => Real.exp (x * (T - u)) * (K * Real.exp (b * u))) =
      fun u => K * (Real.exp (x * (T - u)) * Real.exp (b * u)) := by
    funext u; ring
  rw [heq, intervalIntegral.integral_const_mul, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (integral_weight_exp_le hxb) hK

/-- **The transient term** (`09_relay.tex:1334-1343`):
`∫₀^{T_g} e^{x(T_g-u)} 2πC₃ C(C₀)κ⟨u⟩³e^{σ'u} du ≤ C_tr δ₀(κ/δ₀)^γ L⁴`. -/
theorem errT1_le {x σp σ σ' κ δ₀ C₃ Cact Ctr Tg γ : ℝ} (hκ : 0 < κ) (hκδ : κ < δ₀)
    (hσ : 0 < σ) (hσp : 15 / 16 * σ ≤ σp) (hσ' : 0 ≤ σ') (hC₃ : 0 ≤ C₃)
    (hCact : 0 ≤ Cact) (hTg : Tg = σp⁻¹ * Real.log (δ₀ / κ)) (hL : 1 ≤ Real.log (δ₀ / κ))
    (hγx : γ ≤ 1 - x / σp) (hγσ' : γ ≤ 1 - 16 * σ' / (15 * σ))
    (hCtr : Ctr = 32 * Real.pi * C₃ / (15 * σ) * (1 + 16 / (15 * σ)) ^ 3 * Cact) :
    ∫ u in (0 : ℝ)..Tg, Real.exp (x * (Tg - u)) *
        (2 * Real.pi * C₃ * (Cact * κ * Prelim.jap u ^ 3 * Real.exp (σ' * u))) ≤
      Ctr * δ₀ * (κ / δ₀) ^ γ * Real.log (δ₀ / κ) ^ (3 + 1) := by
  set L := Real.log (δ₀ / κ) with hLdef
  have hσp0 : 0 < σp := lt_of_lt_of_le (by positivity) hσp
  have hTg0 : 0 ≤ Tg := by rw [hTg]; exact mul_nonneg (inv_nonneg.2 hσp0.le) (by linarith)
  set m := max x σ' with hm
  -- pointwise bound by a constant
  have hpt : ∀ u ∈ Icc (0 : ℝ) Tg, Real.exp (x * (Tg - u)) *
      (2 * Real.pi * C₃ * (Cact * κ * Prelim.jap u ^ 3 * Real.exp (σ' * u))) ≤
      2 * Real.pi * C₃ * Cact * Prelim.jap Tg ^ 3 * (κ * Real.exp (m * Tg)) := by
    intro u hu
    have hexp : Real.exp (x * (Tg - u)) * Real.exp (σ' * u) ≤ Real.exp (m * Tg) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have h1 : x * (Tg - u) ≤ m * (Tg - u) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith [hu.2])
      have h2 : σ' * u ≤ m * u := mul_le_mul_of_nonneg_right (le_max_right _ _) hu.1
      nlinarith
    have hjap : Prelim.jap u ^ 3 ≤ Prelim.jap Tg ^ 3 :=
      pow_le_pow_left₀ (Prelim.jap_nonneg u) (jap_mono hu.1 hu.2) 3
    have hA : 0 ≤ 2 * Real.pi * C₃ * Cact * κ := by positivity
    calc Real.exp (x * (Tg - u)) *
          (2 * Real.pi * C₃ * (Cact * κ * Prelim.jap u ^ 3 * Real.exp (σ' * u)))
        = (2 * Real.pi * C₃ * Cact * κ) * Prelim.jap u ^ 3 *
            (Real.exp (x * (Tg - u)) * Real.exp (σ' * u)) := by ring
      _ ≤ (2 * Real.pi * C₃ * Cact * κ) * Prelim.jap Tg ^ 3 * Real.exp (m * Tg) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hjap hA) hexp (by positivity)
        exact mul_nonneg hA (pow_nonneg (Prelim.jap_nonneg _) 3)
      _ = 2 * Real.pi * C₃ * Cact * Prelim.jap Tg ^ 3 * (κ * Real.exp (m * Tg)) := by ring
  have hint1 : IntervalIntegrable (fun u => Real.exp (x * (Tg - u)) *
      (2 * Real.pi * C₃ * (Cact * κ * Prelim.jap u ^ 3 * Real.exp (σ' * u)))) volume 0 Tg := by
    have : Continuous (fun u => Real.exp (x * (Tg - u)) *
        (2 * Real.pi * C₃ * (Cact * κ * Prelim.jap u ^ 3 * Real.exp (σ' * u)))) := by
      have := continuous_jap
      fun_prop
    exact this.intervalIntegrable _ _
  have hle1 := intervalIntegral.integral_mono_on hTg0 hint1 intervalIntegrable_const hpt
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hle1
  refine hle1.trans ?_
  -- the constant
  have hkm : κ * Real.exp (m * Tg) ≤ δ₀ * (κ / δ₀) ^ γ := by
    rw [hTg]
    apply kappa_mul_exp_le m hκ hκδ hσp0.ne'
    rcases le_total x σ' with h | h
    · rw [hm, max_eq_right h]
      refine hγσ'.trans ?_
      have : σ' / σp ≤ 16 * σ' / (15 * σ) := by
        rw [show 16 * σ' / (15 * σ) = σ' / (15 / 16 * σ) by field_simp]
        exact div_le_div_of_nonneg_left hσ' (by positivity) hσp
      linarith
    · rw [hm, max_eq_left h]; exact hγx
  have hTgle : Tg ≤ 16 / (15 * σ) * L := by
    rw [hTg]
    have : σp⁻¹ ≤ 16 / (15 * σ) := by
      rw [show 16 / (15 * σ) = (15 / 16 * σ)⁻¹ by field_simp]
      exact inv_anti₀ (by positivity) hσp
    exact mul_le_mul_of_nonneg_right this (by linarith)
  have hjapT : Prelim.jap Tg ≤ (1 + 16 / (15 * σ)) * L := by
    refine (jap_le_one_add hTg0).trans ?_
    have : 0 ≤ 16 / (15 * σ) := by positivity
    nlinarith
  have hjap3 : Prelim.jap Tg ^ 3 ≤ ((1 + 16 / (15 * σ)) * L) ^ 3 :=
    pow_le_pow_left₀ (Prelim.jap_nonneg _) hjapT 3
  have hB : 0 ≤ 2 * Real.pi * C₃ * Cact := by positivity
  have hδ0 : 0 < δ₀ := hκ.trans hκδ
  have hkm0 : 0 ≤ κ * Real.exp (m * Tg) := by positivity
  calc Tg * (2 * Real.pi * C₃ * Cact * Prelim.jap Tg ^ 3 * (κ * Real.exp (m * Tg)))
      = Tg * (2 * Real.pi * C₃ * Cact) * Prelim.jap Tg ^ 3 * (κ * Real.exp (m * Tg)) := by ring
    _ ≤ (16 / (15 * σ) * L) * (2 * Real.pi * C₃ * Cact) * ((1 + 16 / (15 * σ)) * L) ^ 3 *
          (δ₀ * (κ / δ₀) ^ γ) := by
      apply mul_le_mul _ hkm hkm0 (by positivity)
      apply mul_le_mul (mul_le_mul_of_nonneg_right hTgle hB) hjap3
        (pow_nonneg (Prelim.jap_nonneg _) 3)
      exact mul_nonneg (mul_nonneg (by positivity) (by linarith)) hB
    _ = Ctr * δ₀ * (κ / δ₀) ^ γ * L ^ (3 + 1) := by
      rw [hCtr]; ring

/-- **The `â²`-term** (`09_relay.tex:1318-1324`):
`∫₀^{T_g} e^{x(T_g-u)} 2πC₃(κe^{σ₊u})² du ≤ (16/15)(2πC₃δ₀²/σ)`. -/
theorem errT2_le {x σp σ κ δ₀ C₃ Tg : ℝ} (hκ : 0 < κ) (hδ : 0 < δ₀) (hσ : 0 < σ)
    (hσp : 15 / 16 * σ ≤ σp) (hx : x < σp) (hC₃ : 0 ≤ C₃)
    (hTg : Tg = σp⁻¹ * Real.log (δ₀ / κ)) :
    ∫ u in (0 : ℝ)..Tg, Real.exp (x * (Tg - u)) * (2 * Real.pi * C₃ * (κ * Real.exp (σp * u)) ^ 2) ≤
      16 / 15 * (2 * Real.pi * C₃ * δ₀ ^ 2 / σ) := by
  have hσp0 : 0 < σp := lt_of_lt_of_le (by positivity) hσp
  have heq : (fun u : ℝ => Real.exp (x * (Tg - u)) * (2 * Real.pi * C₃ * (κ * Real.exp (σp * u)) ^ 2))
      = fun u => Real.exp (x * (Tg - u)) * ((2 * Real.pi * C₃ * κ ^ 2) * Real.exp ((2 * σp) * u)) := by
    funext u
    rw [mul_pow, ← Real.exp_nat_mul]
    push_cast
    ring_nf
  rw [heq]
  refine (errT_exp_le (by linarith) (by positivity)).trans ?_
  have hk : κ * Real.exp (σp * Tg) = δ₀ := by rw [hTg]; exact kappa_mul_exp_self hκ hδ hσp0.ne'
  have hk2 : κ ^ 2 * Real.exp (2 * σp * Tg) = δ₀ ^ 2 := by
    rw [← hk, mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
  have hden : 15 / 16 * σ ≤ 2 * σp - x := by linarith
  calc 2 * Real.pi * C₃ * κ ^ 2 * Real.exp (2 * σp * Tg) / (2 * σp - x)
      = 2 * Real.pi * C₃ * δ₀ ^ 2 / (2 * σp - x) := by rw [← hk2]; ring
    _ ≤ 2 * Real.pi * C₃ * δ₀ ^ 2 / (15 / 16 * σ) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = 16 / 15 * (2 * Real.pi * C₃ * δ₀ ^ 2 / σ) := by field_simp

/-- **The `κ^{1/2}`- and `η_b`-terms** (`09_relay.tex:1325-1330`): for `c ≥ 0`,
`∫₀^{T_g} e^{x(T_g-u)} 2πC₃(κe^{σ₊u} c) du ≤ 2πC₃ c (4μδ₀/(3σ(μ-1)))`. -/
theorem errT34_le {x σp σ κ δ₀ μ C₃ c Tg : ℝ} (hκ : 0 < κ) (hδ : 0 < δ₀) (hσ : 0 < σ)
    (hσp0 : 0 < σp) (hμ : 1 < μ) (hrew : 3 / 4 * σ * ((μ - 1) / μ) ≤ σp - x) (hC₃ : 0 ≤ C₃)
    (hc : 0 ≤ c) (hTg : Tg = σp⁻¹ * Real.log (δ₀ / κ)) :
    ∫ u in (0 : ℝ)..Tg, Real.exp (x * (Tg - u)) * (2 * Real.pi * C₃ * (κ * Real.exp (σp * u) * c)) ≤
      2 * Real.pi * C₃ * c * (4 * μ * δ₀ / (3 * σ * (μ - 1))) := by
  have hR : 0 < σp - x := lt_of_lt_of_le (by
    have : 0 < μ - 1 := by linarith
    have : 0 < μ := by linarith
    positivity) hrew
  have heq : (fun u : ℝ => Real.exp (x * (Tg - u)) * (2 * Real.pi * C₃ * (κ * Real.exp (σp * u) * c)))
      = fun u => Real.exp (x * (Tg - u)) * ((2 * Real.pi * C₃ * c * κ) * Real.exp (σp * u)) := by
    funext u; ring
  rw [heq]
  refine (errT_exp_le (by linarith) (by positivity)).trans ?_
  have hk : κ * Real.exp (σp * Tg) = δ₀ := by rw [hTg]; exact kappa_mul_exp_self hκ hδ hσp0.ne'
  have hinv := inv_le_of_rew hσ hμ hrew
  have hA : 0 ≤ 2 * Real.pi * C₃ * c * δ₀ := by positivity
  calc 2 * Real.pi * C₃ * c * κ * Real.exp (σp * Tg) / (σp - x)
      = (2 * Real.pi * C₃ * c * δ₀) * (1 / (σp - x)) := by rw [← hk]; ring
    _ ≤ (2 * Real.pi * C₃ * c * δ₀) * (4 * μ / (3 * σ * (μ - 1))) :=
      mul_le_mul_of_nonneg_left hinv hA
    _ = 2 * Real.pi * C₃ * c * (4 * μ * δ₀ / (3 * σ * (μ - 1))) := by ring

/-- **The inner drift term** (`09_relay.tex:1347-1359`), with `r_T(T) = (1+T)³e^{-σT/4}` and a
weight `ι ≥ 0` (`ι = 1_{k+1<n}`):
`∫₀^{T_g} e^{x(T_g-u)} 2πP(ι·2r_T(T_pin+μu)κ)e^{σ₊u} du ≤ ι C_id r_T(T_pin) I_3(σ/8) δ₀(κ/δ₀)^ϑ`,
`C_id = 4π(17/16)³P`. -/
theorem errT5_le {x σp σ κ δ₀ μ P ι Tpin Tg ϑ : ℝ} (hκ : 0 < κ) (hκδ : κ < δ₀) (hσ : 0 < σ)
    (hσp0 : 0 < σp) (hμ : 1 ≤ μ) (hμ' : μ ≤ 17 / 16) (hrew : σp - x ≤ σ / 8) (hP : 0 ≤ P)
    (hι : 0 ≤ ι) (hTpin : 0 ≤ Tpin) (hTg : Tg = σp⁻¹ * Real.log (δ₀ / κ)) (hTg0 : 0 ≤ Tg)
    (hϑ : ϑ ≤ 1 - x / σp) :
    ∫ u in (0 : ℝ)..Tg, Real.exp (x * (Tg - u)) *
        (2 * Real.pi * P * (ι * (2 * ((1 + (Tpin + μ * u)) ^ 3 *
          Real.exp (-(σ * (Tpin + μ * u) / 4))) * κ)) * Real.exp (σp * u)) ≤
      ι * (4 * Real.pi * (17 / 16) ^ 3 * P) * ((1 + Tpin) ^ 3 * Real.exp (-(σ * Tpin / 4))) *
        Ip 3 (σ / 8) * (δ₀ * (κ / δ₀) ^ ϑ) := by
  set K := 2 * Real.pi * P * ι * 2 * κ * Real.exp (x * Tg) *
    ((1 + Tpin) ^ 3 * Real.exp (-(σ * Tpin / 4))) * μ ^ 3 with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hpt : ∀ u ∈ Icc (0 : ℝ) Tg, Real.exp (x * (Tg - u)) *
        (2 * Real.pi * P * (ι * (2 * ((1 + (Tpin + μ * u)) ^ 3 *
          Real.exp (-(σ * (Tpin + μ * u) / 4))) * κ)) * Real.exp (σp * u)) ≤
      K * ((1 + u) ^ 3 * Real.exp (-(σ / 8) * u)) := by
    intro u hu
    have hu0 := hu.1
    have hpoly : (1 + (Tpin + μ * u)) ^ 3 ≤ (1 + Tpin) ^ 3 * μ ^ 3 * (1 + u) ^ 3 := by
      have h1 : 1 + (Tpin + μ * u) ≤ (1 + Tpin) * (μ * (1 + u)) := by
        nlinarith [mul_nonneg (sub_nonneg.2 hμ) hTpin, mul_nonneg (sub_nonneg.2 hμ) hu0,
          mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ μ) hTpin) hu0]
      calc (1 + (Tpin + μ * u)) ^ 3 ≤ ((1 + Tpin) * (μ * (1 + u))) ^ 3 :=
            pow_le_pow_left₀ (by positivity) h1 3
        _ = (1 + Tpin) ^ 3 * μ ^ 3 * (1 + u) ^ 3 := by ring
    have hexp : Real.exp (x * (Tg - u)) * Real.exp (-(σ * (Tpin + μ * u) / 4)) *
        Real.exp (σp * u) ≤
        Real.exp (x * Tg) * Real.exp (-(σ * Tpin / 4)) * Real.exp (-(σ / 8) * u) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.2
      have h1 : σ * u ≤ σ * (μ * u) :=
        mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg (sub_nonneg.2 hμ) hu0]) hσ.le
      have h2 : (σp - x) * u ≤ σ / 8 * u := mul_le_mul_of_nonneg_right hrew hu0
      linarith
    have hA : 0 ≤ 2 * Real.pi * P * ι * 2 * κ := by positivity
    calc Real.exp (x * (Tg - u)) *
          (2 * Real.pi * P * (ι * (2 * ((1 + (Tpin + μ * u)) ^ 3 *
            Real.exp (-(σ * (Tpin + μ * u) / 4))) * κ)) * Real.exp (σp * u))
        = (2 * Real.pi * P * ι * 2 * κ) * (1 + (Tpin + μ * u)) ^ 3 *
            (Real.exp (x * (Tg - u)) * Real.exp (-(σ * (Tpin + μ * u) / 4)) *
              Real.exp (σp * u)) := by ring
      _ ≤ (2 * Real.pi * P * ι * 2 * κ) * ((1 + Tpin) ^ 3 * μ ^ 3 * (1 + u) ^ 3) *
            (Real.exp (x * Tg) * Real.exp (-(σ * Tpin / 4)) * Real.exp (-(σ / 8) * u)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hpoly hA) hexp (by positivity)
        positivity
      _ = K * ((1 + u) ^ 3 * Real.exp (-(σ / 8) * u)) := by rw [hK]; ring
  have hcont : Continuous (fun u : ℝ => Real.exp (x * (Tg - u)) *
        (2 * Real.pi * P * (ι * (2 * ((1 + (Tpin + μ * u)) ^ 3 *
          Real.exp (-(σ * (Tpin + μ * u) / 4))) * κ)) * Real.exp (σp * u))) := by fun_prop
  have hcont2 : Continuous (fun u : ℝ => K * ((1 + u) ^ 3 * Real.exp (-(σ / 8) * u))) := by
    fun_prop
  refine (intervalIntegral.integral_mono_on hTg0 (hcont.intervalIntegrable _ _)
    (hcont2.intervalIntegrable _ _) hpt).trans ?_
  rw [intervalIntegral.integral_const_mul]
  have hIp := intervalIntegral_le_Ip 3 (by positivity : 0 < σ / 8) hTg0
  have hkx : κ * Real.exp (x * Tg) ≤ δ₀ * (κ / δ₀) ^ ϑ := by
    rw [hTg]; exact kappa_mul_exp_le x hκ hκδ hσp0.ne' hϑ
  have hμ3 : μ ^ 3 ≤ (17 / 16) ^ 3 := pow_le_pow_left₀ (by linarith) hμ' 3
  have hI0 : 0 ≤ Ip 3 (σ / 8) := (Ip_pos 3 (by positivity)).le
  have hr0 : 0 ≤ (1 + Tpin) ^ 3 * Real.exp (-(σ * Tpin / 4)) := by positivity
  calc K * ∫ u in (0 : ℝ)..Tg, (1 + u) ^ 3 * Real.exp (-(σ / 8) * u)
      ≤ K * Ip 3 (σ / 8) := mul_le_mul_of_nonneg_left hIp hK0
    _ = (4 * Real.pi * P * ι * ((1 + Tpin) ^ 3 * Real.exp (-(σ * Tpin / 4))) * Ip 3 (σ / 8)) *
          μ ^ 3 * (κ * Real.exp (x * Tg)) := by rw [hK]; ring
    _ ≤ (4 * Real.pi * P * ι * ((1 + Tpin) ^ 3 * Real.exp (-(σ * Tpin / 4))) * Ip 3 (σ / 8)) *
          (17 / 16) ^ 3 * (δ₀ * (κ / δ₀) ^ ϑ) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hμ3 (by positivity)) hkx (by positivity)
      positivity
    _ = ι * (4 * Real.pi * (17 / 16) ^ 3 * P) * ((1 + Tpin) ^ 3 * Real.exp (-(σ * Tpin / 4))) *
          Ip 3 (σ / 8) * (δ₀ * (κ / δ₀) ^ ϑ) := by ring

/-- **The outer drift term** (`09_relay.tex:1360-1368`):
`∫₀^{T_g} e^{x(T_g-u)} 2πP(C_ls η_b (T_g-u) κ)e^{σ₊u} du ≤ C_od η_b δ₀ μ²/(σ²(μ-1)²)`,
`C_od = (32π/9) C_ls P`. -/
theorem errT6_le {x σp σ κ δ₀ μ P Cls ηb Tg : ℝ} (hκ : 0 < κ) (hδ : 0 < δ₀) (hσ : 0 < σ)
    (hσp0 : 0 < σp) (hμ : 1 < μ) (hrew : 3 / 4 * σ * ((μ - 1) / μ) ≤ σp - x) (hP : 0 ≤ P)
    (hCls : 0 ≤ Cls) (hηb : 0 ≤ ηb) (hTg : Tg = σp⁻¹ * Real.log (δ₀ / κ)) (hTg0 : 0 ≤ Tg) :
    ∫ u in (0 : ℝ)..Tg, Real.exp (x * (Tg - u)) *
        (2 * Real.pi * P * (Cls * ηb * (Tg - u) * κ) * Real.exp (σp * u)) ≤
      32 * Real.pi / 9 * Cls * P * ηb * δ₀ * (μ ^ 2 / (σ ^ 2 * (μ - 1) ^ 2)) := by
  have hμ0 : 0 < μ := by linarith
  have hμ1 : 0 < μ - 1 := by linarith
  have hR : 0 < σp - x := lt_of_lt_of_le (by positivity) hrew
  set a := σp - x with ha
  have hk : κ * Real.exp (σp * Tg) = δ₀ := by rw [hTg]; exact kappa_mul_exp_self hκ hδ hσp0.ne'
  have heq : (fun u : ℝ => Real.exp (x * (Tg - u)) *
        (2 * Real.pi * P * (Cls * ηb * (Tg - u) * κ) * Real.exp (σp * u))) =
      fun u => (2 * Real.pi * P * Cls * ηb * (κ * Real.exp (σp * Tg))) *
        ((fun v : ℝ => v * Real.exp (-(a * v))) (Tg - u)) := by
    funext u
    simp only
    have : Real.exp (x * (Tg - u)) * Real.exp (σp * u) =
        Real.exp (σp * Tg) * Real.exp (-(a * (Tg - u))) := by
      rw [← Real.exp_add, ← Real.exp_add, ha]; ring_nf
    calc Real.exp (x * (Tg - u)) * (2 * Real.pi * P * (Cls * ηb * (Tg - u) * κ) * Real.exp (σp * u))
        = (2 * Real.pi * P * Cls * ηb * κ * (Tg - u)) *
            (Real.exp (x * (Tg - u)) * Real.exp (σp * u)) := by ring
      _ = _ := by rw [this]; ring
  rw [heq, intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_left
    (fun v : ℝ => v * Real.exp (-(a * v))) Tg, sub_self, sub_zero, hk]
  have hv := integral_v_exp_le hR hTg0
  have hinv := inv_le_of_rew hσ hμ hrew
  have hinv2 : 1 / a ^ 2 ≤ (4 * μ / (3 * σ * (μ - 1))) ^ 2 := by
    rw [one_div, ← inv_pow, ← one_div]
    exact pow_le_pow_left₀ (by positivity) hinv 2
  calc 2 * Real.pi * P * Cls * ηb * δ₀ * ∫ v in (0 : ℝ)..Tg, v * Real.exp (-(a * v))
      ≤ 2 * Real.pi * P * Cls * ηb * δ₀ * (1 / a ^ 2) :=
        mul_le_mul_of_nonneg_left hv (by positivity)
    _ ≤ 2 * Real.pi * P * Cls * ηb * δ₀ * (4 * μ / (3 * σ * (μ - 1))) ^ 2 :=
        mul_le_mul_of_nonneg_left hinv2 (by positivity)
    _ = 32 * Real.pi / 9 * Cls * P * ηb * δ₀ * (μ ^ 2 / (σ ^ 2 * (μ - 1) ^ 2)) := by
      field_simp
      ring

end KickTrueAux

end Relay

end NonUniqueEuler
