import NonUniqueEuler.Defs.Sec8.Kick
import NonUniqueEuler.H.Sec9.KickTrue.Real

/-!
# Helpers for `P/Sec9/KickTrue`: the error function `err` and the bound on `Err_g`

Helper file of `P/Sec9/KickTrue.lean` (`lem:kicktrue`, steps (Q1) and (Kick3),
`09_relay.tex:1288-1372`). Pure real analysis.

* `errE C₃ Cact κ σ' σ₊ η_b P ι T_pin μ σ C_ls T_g u`: the continuous part of the function `err` of the
  proof, in active time `u = τ + T_g` (`09_relay.tex:1304-1308`), with the transient term
  `2πC₃â(u)ρ̂(u)` replaced by its bound `2πC₃C(C₀)κ⟨u⟩³e^{σ'u}` (`thm:active`, "Moreover"); the full
  `err` is `errE(τ + T_g) + |q^deep(τ)|`;
* `continuous_errE`, `errE_nonneg`;
* `errE_integral_le`: `∫₀^{T_g} e^{x(T_g-u)} errE(u) du` is at most the sum of the six bounds of
  `errT1_le` … `errT6_le` (`09_relay.tex:1316-1368`);
* `errG_split`: `Err_g = ∫₀^{T_g} e^{x(T_g-u)} errE(u) du + ∫_{-T_g}^0 e^{-xτ} g(τ) dτ` for
  `err = errE(· + T_g) + g` (the substitution `u = τ + T_g`, `09_relay.tex:1311-1312`).
Everything here is proved.
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler

namespace Relay

namespace KickTrueAux

/-- **The continuous part of `err`** (`09_relay.tex:1304-1308`), in active time `u`: the `ρ̂`-term
(bounded by `C(C₀)κ⟨u⟩³e^{σ'u}`), the `â²`-, `κ^{1/2}`- and `η_b`-terms of `cor:active-moment`, and
the inner (`ι = 1_{k+1<n}`) and outer drift terms. -/
def errE (C₃ Cact κ σ' σp ηb P ι Tpin μ σ Cls Tg : ℝ) (u : ℝ) : ℝ :=
  2 * Real.pi * C₃ * (Cact * κ * Prelim.jap u ^ 3 * Real.exp (σ' * u)) +
    2 * Real.pi * C₃ * (κ * Real.exp (σp * u)) ^ 2 +
    2 * Real.pi * C₃ * (κ * Real.exp (σp * u) * Real.sqrt κ) +
    2 * Real.pi * C₃ * (κ * Real.exp (σp * u) * ηb) +
    2 * Real.pi * P * (ι * (2 * ((1 + (Tpin + μ * u)) ^ 3 *
      Real.exp (-(σ * (Tpin + μ * u) / 4))) * κ)) * Real.exp (σp * u) +
    2 * Real.pi * P * (Cls * ηb * (Tg - u) * κ) * Real.exp (σp * u)

theorem continuous_errE (C₃ Cact κ σ' σp ηb P ι Tpin μ σ Cls Tg : ℝ) :
    Continuous (errE C₃ Cact κ σ' σp ηb P ι Tpin μ σ Cls Tg) := by
  have := continuous_jap
  unfold errE
  fun_prop

theorem errE_nonneg {C₃ Cact κ σ' σp ηb P ι Tpin μ σ Cls Tg u : ℝ} (hC₃ : 0 ≤ C₃)
    (hCact : 0 ≤ Cact) (hκ : 0 ≤ κ) (hηb : 0 ≤ ηb) (hP : 0 ≤ P) (hι : 0 ≤ ι) (hCls : 0 ≤ Cls)
    (hTpin : 0 ≤ Tpin) (hμ : 0 ≤ μ) (hu : u ∈ Icc (0 : ℝ) Tg) :
    0 ≤ errE C₃ Cact κ σ' σp ηb P ι Tpin μ σ Cls Tg u := by
  have h1 : 0 ≤ 1 + (Tpin + μ * u) := by nlinarith [hu.1]
  have h2 : 0 ≤ Tg - u := by linarith [hu.2]
  have hj := Prelim.jap_nonneg u
  unfold errE
  have : 0 ≤ (1 + (Tpin + μ * u)) ^ 3 := pow_nonneg h1 3
  positivity

/-- **The six terms of `Err_g`** (`09_relay.tex:1316-1368`): the weighted integral of `errE` over
`[0, T_g]` is at most the sum of the bounds of `errT1_le` … `errT6_le`. -/
theorem errE_integral_le {x σp σ σ' κ δ₀ μ C₃ Cact P ι Cls ηb Tpin Tg γ ϑ : ℝ}
    (hκ : 0 < κ) (hκδ : κ < δ₀) (hσ : 0 < σ) (hσp : 15 / 16 * σ ≤ σp) (hσ' : 0 ≤ σ')
    (hμ : 1 < μ) (hμ' : μ ≤ 17 / 16) (hlow : 3 / 4 * σ * ((μ - 1) / μ) ≤ σp - x)
    (hup : σp - x ≤ σ / 8) (hC₃ : 0 ≤ C₃) (hCact : 0 ≤ Cact) (hP : 0 ≤ P) (hι : 0 ≤ ι)
    (hCls : 0 ≤ Cls) (hηb : 0 ≤ ηb) (hTpin : 0 ≤ Tpin)
    (hTg : Tg = σp⁻¹ * Real.log (δ₀ / κ)) (hL : 1 ≤ Real.log (δ₀ / κ))
    (hγx : γ ≤ 1 - x / σp) (hγσ' : γ ≤ 1 - 16 * σ' / (15 * σ)) (hϑ : ϑ ≤ 1 - x / σp) :
    ∫ u in (0 : ℝ)..Tg, Real.exp (x * (Tg - u)) *
        errE C₃ Cact κ σ' σp ηb P ι Tpin μ σ Cls Tg u ≤
      32 * Real.pi * C₃ / (15 * σ) * (1 + 16 / (15 * σ)) ^ 3 * Cact * δ₀ * (κ / δ₀) ^ γ *
          Real.log (δ₀ / κ) ^ (3 + 1) +
        16 / 15 * (2 * Real.pi * C₃ * δ₀ ^ 2 / σ) +
        2 * Real.pi * C₃ * Real.sqrt κ * (4 * μ * δ₀ / (3 * σ * (μ - 1))) +
        2 * Real.pi * C₃ * ηb * (4 * μ * δ₀ / (3 * σ * (μ - 1))) +
        ι * (4 * Real.pi * (17 / 16) ^ 3 * P) * ((1 + Tpin) ^ 3 * Real.exp (-(σ * Tpin / 4))) *
          Ip 3 (σ / 8) * (δ₀ * (κ / δ₀) ^ ϑ) +
        32 * Real.pi / 9 * Cls * P * ηb * δ₀ * (μ ^ 2 / (σ ^ 2 * (μ - 1) ^ 2)) := by
  have hδ : 0 < δ₀ := hκ.trans hκδ
  have hσp0 : 0 < σp := lt_of_lt_of_le (by positivity) hσp
  have hR : 0 < σp - x := lt_of_lt_of_le (by
    have : 0 < μ - 1 := by linarith
    have : 0 < μ := by linarith
    positivity) hlow
  have hx : x < σp := by linarith
  have hTg0 : 0 ≤ Tg := by rw [hTg]; exact mul_nonneg (inv_nonneg.2 hσp0.le) (by linarith)
  have hj := continuous_jap
  -- the six integrands
  set f1 : ℝ → ℝ := fun u => Real.exp (x * (Tg - u)) *
    (2 * Real.pi * C₃ * (Cact * κ * Prelim.jap u ^ 3 * Real.exp (σ' * u))) with hf1
  set f2 : ℝ → ℝ := fun u => Real.exp (x * (Tg - u)) *
    (2 * Real.pi * C₃ * (κ * Real.exp (σp * u)) ^ 2) with hf2
  set f3 : ℝ → ℝ := fun u => Real.exp (x * (Tg - u)) *
    (2 * Real.pi * C₃ * (κ * Real.exp (σp * u) * Real.sqrt κ)) with hf3
  set f4 : ℝ → ℝ := fun u => Real.exp (x * (Tg - u)) *
    (2 * Real.pi * C₃ * (κ * Real.exp (σp * u) * ηb)) with hf4
  set f5 : ℝ → ℝ := fun u => Real.exp (x * (Tg - u)) *
    (2 * Real.pi * P * (ι * (2 * ((1 + (Tpin + μ * u)) ^ 3 *
      Real.exp (-(σ * (Tpin + μ * u) / 4))) * κ)) * Real.exp (σp * u)) with hf5
  set f6 : ℝ → ℝ := fun u => Real.exp (x * (Tg - u)) *
    (2 * Real.pi * P * (Cls * ηb * (Tg - u) * κ) * Real.exp (σp * u)) with hf6
  have hsum : (fun u => Real.exp (x * (Tg - u)) * errE C₃ Cact κ σ' σp ηb P ι Tpin μ σ Cls Tg u) =
      fun u => f1 u + f2 u + f3 u + f4 u + f5 u + f6 u := by
    funext u
    simp only [hf1, hf2, hf3, hf4, hf5, hf6, errE]
    ring
  have i1 : IntervalIntegrable f1 volume 0 Tg := by
    apply Continuous.intervalIntegrable; rw [hf1]; fun_prop
  have i2 : IntervalIntegrable f2 volume 0 Tg := by
    apply Continuous.intervalIntegrable; rw [hf2]; fun_prop
  have i3 : IntervalIntegrable f3 volume 0 Tg := by
    apply Continuous.intervalIntegrable; rw [hf3]; fun_prop
  have i4 : IntervalIntegrable f4 volume 0 Tg := by
    apply Continuous.intervalIntegrable; rw [hf4]; fun_prop
  have i5 : IntervalIntegrable f5 volume 0 Tg := by
    apply Continuous.intervalIntegrable; rw [hf5]; fun_prop
  have i6 : IntervalIntegrable f6 volume 0 Tg := by
    apply Continuous.intervalIntegrable; rw [hf6]; fun_prop
  rw [hsum, intervalIntegral.integral_add (((i1.add i2).add i3).add i4 |>.add i5) i6,
    intervalIntegral.integral_add (((i1.add i2).add i3).add i4) i5,
    intervalIntegral.integral_add ((i1.add i2).add i3) i4,
    intervalIntegral.integral_add (i1.add i2) i3, intervalIntegral.integral_add i1 i2]
  have b1 := errT1_le (x := x) (σ' := σ') hκ hκδ hσ hσp hσ' hC₃ hCact hTg hL hγx hγσ' rfl
  have b2 := errT2_le (x := x) hκ hδ hσ hσp hx hC₃ hTg
  have b3 := errT34_le hκ hδ hσ hσp0 hμ hlow hC₃ (Real.sqrt_nonneg κ) hTg
  have b4 := errT34_le hκ hδ hσ hσp0 hμ hlow hC₃ hηb hTg
  have b5 := errT5_le hκ hκδ hσ hσp0 hμ.le hμ' hup hP hι hTpin hTg hTg0 hϑ
  have b6 := errT6_le hκ hδ hσ hσp0 hμ hlow hP hCls hηb hTg hTg0
  simp only [hf1, hf2, hf3, hf4, hf5, hf6]
  linarith [b1, b2, b3, b4, b5, b6]

/-- **The substitution `u = τ + T_g`** (`09_relay.tex:1311-1312`): for `err = errE(· + T_g) + g`,
`Err_g = ∫₀^{T_g} e^{x(T_g-u)} errE(u) du + ∫_{-T_g}^0 e^{-xτ} g(τ) dτ`. -/
theorem errG_split {x Tg : ℝ} {E g : ℝ → ℝ} (hE : Continuous E)
    (hg : IntervalIntegrable (fun τ => Real.exp (-(x * τ)) * g τ) volume (-Tg) 0) :
    Kick.errG x Tg (fun τ => E (τ + Tg) + g τ) =
      (∫ u in (0 : ℝ)..Tg, Real.exp (x * (Tg - u)) * E u) +
        ∫ τ in (-Tg)..0, Real.exp (-(x * τ)) * g τ := by
  unfold Kick.errG
  have hE' : IntervalIntegrable (fun τ => Real.exp (-(x * τ)) * E (τ + Tg)) volume (-Tg) 0 := by
    apply Continuous.intervalIntegrable
    have : Continuous fun τ : ℝ => E (τ + Tg) := hE.comp (by fun_prop)
    fun_prop
  simp_rw [mul_add]
  rw [intervalIntegral.integral_add hE' hg]
  congr 1
  have hfun : (fun τ => Real.exp (-(x * τ)) * E (τ + Tg)) =
      fun τ => (fun u => Real.exp (x * (Tg - u)) * E u) (τ + Tg) := by
    funext τ
    simp only
    congr 2
    ring
  rw [hfun, intervalIntegral.integral_comp_add_right (fun u => Real.exp (x * (Tg - u)) * E u) Tg]
  simp

end KickTrueAux

end Relay

end NonUniqueEuler
