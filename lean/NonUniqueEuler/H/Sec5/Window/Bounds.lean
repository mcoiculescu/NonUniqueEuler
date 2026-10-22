import NonUniqueEuler.H.Sec5.Window.Real

/-!
# Helpers for `lem:window`: the real-number estimates

Helper file of `P/Sec5/Window.lean`. Fully proved.
Notation: `â(τ) = ahat κ σ τ = κe^{στ}`, `𝔟 = â + C♮κ⟨τ⟩^{p+2}`, `V = ς(κ₁)`, `N = N_G`.
* `v_integral_le`: `eq:W-v` and `eq:W-theta` (`05_single_ring.tex:807-829`):
  `∫₀^τ e^{Λ(τ-τ')} C_app â 𝔟^N ≤ C_v(â(τ)^{N+1} + κ²V^{(p+2)N})`, with
  `C_v = C_app 2^N C♮^N/σ_b`. Deviation: instead of `κ₁e^{Λu} ≤ κ₁^{1-Λ/σ}δ₀^{Λ/σ}` (real powers)
  we use `e^{Λτ} ≤ e^{(N-1)στ}` (from `Λ ≤ (N-1)σ_b`), so that
  `κ^{N+1}e^{Λτ} ≤ κ²â(τ)^{N-1} ≤ κ²`; same bound.
* `collect_mode`, `collect_w`: the collection step (`05_single_ring.tex:830-845`).
* `disp_integral_le`: the displacement integral (`05_single_ring.tex:846-855`).
-/

noncomputable section

open MeasureTheory Set Real

namespace NonUniqueEuler

namespace OneRing

namespace WindowH

theorem add_pow_le_two_pow {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (N : ℕ) :
    (x + y) ^ N ≤ 2 ^ N * (x ^ N + y ^ N) := by
  have h1 := add_pow_le hx hy N
  have h2 : (2 : ℝ) ^ (N - 1) ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) (Nat.sub_le N 1)
  have h3 : 0 ≤ x ^ N + y ^ N := by positivity
  nlinarith

theorem continuous_ahat (κ σ : ℝ) : Continuous (fun τ => ahat κ σ τ) := by
  unfold ahat
  fun_prop

theorem continuous_jap : Continuous Prelim.jap := by
  unfold Prelim.jap
  fun_prop

theorem ahat_nonneg {κ : ℝ} (hκ : 0 ≤ κ) (σ τ : ℝ) : 0 ≤ ahat κ σ τ := by
  unfold ahat
  positivity

theorem exp_pow_eq (σ τ : ℝ) (n : ℕ) :
    Real.exp (σ * τ) ^ n = Real.exp ((n : ℝ) * σ * τ) := by
  rw [← Real.exp_nat_mul]
  ring_nf

/-- **`eq:W-v` with `eq:W-theta`** (`05_single_ring.tex:807-829`). -/
theorem v_integral_le {σ σb Λ κ δ₀ Cn Capp V τ : ℝ} {N : ℕ}
    (hσb : 0 < σb) (hσ : σb ≤ σ) (hΛσ : 2 * σ ≤ Λ) (hNG : Λ / σb + 1 ≤ N) (hκ : 0 < κ)
    (hδ1 : δ₀ ≤ 1) (hCn : 1 ≤ Cn) (hCapp : 0 ≤ Capp) (hτ : 0 ≤ τ) (hexp : ahat κ σ τ ≤ δ₀)
    (hV : ∀ τ' ∈ Icc (0 : ℝ) τ, Prelim.jap τ' ≤ V) :
    ∫ τ' in (0 : ℝ)..τ, Real.exp (Λ * (τ - τ')) *
        (Capp * ahat κ σ τ' * (ahat κ σ τ' + Cn * κ * Prelim.jap τ' ^ (pW + 2)) ^ N) ≤
      Capp * 2 ^ N * Cn ^ N / σb * (ahat κ σ τ ^ (N + 1) + κ ^ 2 * V ^ ((pW + 2) * N)) := by
  have hσ0 : 0 < σ := hσb.trans_le hσ
  have hΛ0 : 0 ≤ Λ := by linarith
  have hV1 : 1 ≤ V := (Prelim.one_le_jap 0).trans (hV 0 ⟨le_rfl, hτ⟩)
  have hV0 : 0 ≤ V := by linarith
  -- `N ≥ 1` and the inequalities of `eq:W-exp`
  have hNσb : Λ + σb ≤ N * σb := by
    have := mul_le_mul_of_nonneg_right hNG hσb.le
    rwa [add_mul, div_mul_cancel₀ _ hσb.ne', one_mul] at this
  have hN1 : (1 : ℝ) ≤ N := by
    have : 0 ≤ Λ / σb := div_nonneg hΛ0 hσb.le
    linarith
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := Nat.exists_eq_add_of_le' (by exact_mod_cast hN1)
  push_cast at hNσb hN1 ⊢
  have hM0 : (0 : ℝ) ≤ M := by linarith
  have hB1 : 2 * σb ≤ ((M : ℝ) + 2) * σ - Λ := by
    have : ((M : ℝ) + 1 + 1) * σb ≤ ((M : ℝ) + 1 + 1) * σ :=
      mul_le_mul_of_nonneg_left hσ (by linarith)
    nlinarith
  have hB2 : σb ≤ Λ - σ := by linarith
  have hB3 : Λ ≤ (M : ℝ) * σ := by
    have : (M : ℝ) * σb ≤ M * σ := mul_le_mul_of_nonneg_left hσ hM0
    nlinarith
  set β := Cn * κ * V ^ (pW + 2) with hβ
  have hβ0 : 0 ≤ β := by positivity
  -- the two exponential integrands
  set F₁ : ℝ → ℝ := fun x => Real.exp (Λ * (τ - x)) *
    Real.exp (((M : ℝ) + 2) * σ * x) with hF₁
  set F₂ : ℝ → ℝ := fun x => Real.exp (Λ * (τ - x)) * Real.exp (σ * x) with hF₂
  have hF₁c : Continuous F₁ := by rw [hF₁]; fun_prop
  have hF₂c : Continuous F₂ := by rw [hF₂]; fun_prop
  set g : ℝ → ℝ := fun x => Capp * 2 ^ (M + 1) * (κ ^ (M + 1 + 1) * F₁ x + β ^ (M + 1) * κ * F₂ x)
    with hg
  have hgc : Continuous g := by rw [hg]; fun_prop
  have hfc : Continuous fun τ' : ℝ => Real.exp (Λ * (τ - τ')) *
      (Capp * ahat κ σ τ' * (ahat κ σ τ' + Cn * κ * Prelim.jap τ' ^ (pW + 2)) ^ (M + 1)) := by
    have := continuous_ahat κ σ
    have := continuous_jap
    fun_prop
  have hpt : ∀ x ∈ Icc (0 : ℝ) τ, Real.exp (Λ * (τ - x)) *
      (Capp * ahat κ σ x * (ahat κ σ x + Cn * κ * Prelim.jap x ^ (pW + 2)) ^ (M + 1)) ≤ g x := by
    intro x hx
    have ha0 := ahat_nonneg hκ.le σ x
    have hj0 := Prelim.jap_nonneg x
    have hb : ahat κ σ x + Cn * κ * Prelim.jap x ^ (pW + 2) ≤ ahat κ σ x + β := by
      have : Prelim.jap x ^ (pW + 2) ≤ V ^ (pW + 2) := pow_le_pow_left₀ hj0 (hV x hx) _
      have : Cn * κ * Prelim.jap x ^ (pW + 2) ≤ Cn * κ * V ^ (pW + 2) :=
        mul_le_mul_of_nonneg_left this (by positivity)
      linarith
    have hb0 : 0 ≤ ahat κ σ x + Cn * κ * Prelim.jap x ^ (pW + 2) := by positivity
    have hbN : (ahat κ σ x + Cn * κ * Prelim.jap x ^ (pW + 2)) ^ (M + 1) ≤
        2 ^ (M + 1) * (ahat κ σ x ^ (M + 1) + β ^ (M + 1)) :=
      (pow_le_pow_left₀ hb0 hb _).trans (add_pow_le_two_pow ha0 hβ0 _)
    have he0 := (Real.exp_pos (Λ * (τ - x))).le
    calc Real.exp (Λ * (τ - x)) *
          (Capp * ahat κ σ x * (ahat κ σ x + Cn * κ * Prelim.jap x ^ (pW + 2)) ^ (M + 1))
        ≤ Real.exp (Λ * (τ - x)) *
          (Capp * ahat κ σ x * (2 ^ (M + 1) * (ahat κ σ x ^ (M + 1) + β ^ (M + 1)))) := by
          gcongr
      _ = g x := by
          rw [hg, hF₁, hF₂]
          simp only [ahat]
          have h2 := exp_pow_eq σ x (M + 2)
          push_cast at h2
          rw [← h2]
          ring
  -- integrate
  have hmono := intervalIntegral.integral_mono_on hτ (hfc.intervalIntegrable (μ := volume) 0 τ)
    (hgc.intervalIntegrable (μ := volume) 0 τ) hpt
  refine hmono.trans ?_
  have hI : ∫ x in (0 : ℝ)..τ, g x = Capp * 2 ^ (M + 1) *
      (κ ^ (M + 1 + 1) * ∫ x in (0 : ℝ)..τ, F₁ x) +
      Capp * 2 ^ (M + 1) * (β ^ (M + 1) * κ * ∫ x in (0 : ℝ)..τ, F₂ x) := by
    rw [hg]
    simp only [mul_add]
    rw [intervalIntegral.integral_add ((by fun_prop : Continuous fun x =>
        Capp * 2 ^ (M + 1) * (κ ^ (M + 1 + 1) * F₁ x)).intervalIntegrable 0 τ)
      ((by fun_prop : Continuous fun x =>
        Capp * 2 ^ (M + 1) * (β ^ (M + 1) * κ * F₂ x)).intervalIntegrable 0 τ)]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [hI]
  have hI1 : ∫ x in (0 : ℝ)..τ, F₁ x ≤
      Real.exp (((M : ℝ) + 2) * σ * τ) / (2 * σb) := by
    have hlt : Λ < ((M : ℝ) + 2) * σ := by linarith
    have h1 := integral_exp_le_of_lt (τ := τ) hlt
    rw [hF₁]
    have e : ∀ x : ℝ, ((M : ℝ) + 2) * σ * x = (((M : ℝ) + 2) * σ) * x := fun x => rfl
    refine h1.trans ?_
    apply div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity)
    linarith
  have hI2 : ∫ x in (0 : ℝ)..τ, F₂ x ≤ Real.exp (Λ * τ) / σb := by
    have hlt : σ < Λ := by linarith
    have h1 := integral_exp_le_of_gt (τ := τ) hlt
    rw [hF₂]
    refine h1.trans ?_
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le hσb hB2
  -- the first term: `κ^{N+1} e^{(N+1)στ} = â(τ)^{N+1}`
  have hT1 : κ ^ (M + 1 + 1) * ∫ x in (0 : ℝ)..τ, F₁ x ≤
      Cn ^ (M + 1) / σb * ahat κ σ τ ^ (M + 1 + 1) := by
    have hA : κ ^ (M + 1 + 1) * Real.exp (((M : ℝ) + 2) * σ * τ) =
        ahat κ σ τ ^ (M + 1 + 1) := by
      simp only [ahat]
      have h2 := exp_pow_eq σ τ (M + 2)
      push_cast at h2
      rw [mul_pow, ← h2]
    have hCnN : 1 ≤ Cn ^ (M + 1) := one_le_pow₀ hCn
    have h1 : κ ^ (M + 1 + 1) * ∫ x in (0 : ℝ)..τ, F₁ x ≤
        κ ^ (M + 1 + 1) * (Real.exp (((M : ℝ) + 2) * σ * τ) / (2 * σb)) :=
      mul_le_mul_of_nonneg_left hI1 (by positivity)
    refine h1.trans ?_
    rw [← mul_div_assoc, hA]
    have ha0 : 0 ≤ ahat κ σ τ ^ (M + 1 + 1) := pow_nonneg (ahat_nonneg hκ.le σ τ) _
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hσb]
    have h2 : ahat κ σ τ ^ (M + 1 + 1) * 1 ≤ ahat κ σ τ ^ (M + 1 + 1) * Cn ^ (M + 1) :=
      mul_le_mul_of_nonneg_left hCnN ha0
    have h3 : 0 ≤ ahat κ σ τ ^ (M + 1 + 1) * Cn ^ (M + 1) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h2 hσb.le, mul_nonneg h3 hσb.le]
  -- the second term: `β^N κ e^{Λτ} ≤ C♮^N κ² V^{(p+2)N}`
  have hT2 : β ^ (M + 1) * κ * ∫ x in (0 : ℝ)..τ, F₂ x ≤
      Cn ^ (M + 1) / σb * (κ ^ 2 * V ^ ((pW + 2) * (M + 1))) := by
    have h1 : β ^ (M + 1) * κ * ∫ x in (0 : ℝ)..τ, F₂ x ≤
        β ^ (M + 1) * κ * (Real.exp (Λ * τ) / σb) :=
      mul_le_mul_of_nonneg_left hI2 (by positivity)
    refine h1.trans ?_
    have hexpΛ : Real.exp (Λ * τ) ≤ Real.exp (σ * τ) ^ M := by
      rw [exp_pow_eq]
      apply Real.exp_le_exp.2
      nlinarith
    have haM : (κ * Real.exp (σ * τ)) ^ M ≤ 1 := by
      have : κ * Real.exp (σ * τ) ≤ 1 := (show ahat κ σ τ ≤ 1 from hexp.trans hδ1)
      exact pow_le_one₀ (by positivity) this
    have hkey : κ ^ (M + 1) * κ * Real.exp (Λ * τ) ≤ κ ^ 2 := by
      calc κ ^ (M + 1) * κ * Real.exp (Λ * τ) ≤ κ ^ (M + 1) * κ * Real.exp (σ * τ) ^ M :=
            mul_le_mul_of_nonneg_left hexpΛ (by positivity)
        _ = κ ^ 2 * (κ * Real.exp (σ * τ)) ^ M := by ring
        _ ≤ κ ^ 2 * 1 := mul_le_mul_of_nonneg_left haM (by positivity)
        _ = κ ^ 2 := mul_one _
    have hβN : β ^ (M + 1) = Cn ^ (M + 1) * κ ^ (M + 1) * V ^ ((pW + 2) * (M + 1)) := by
      rw [hβ, mul_pow, mul_pow, ← pow_mul]
    rw [hβN]
    have hCV : 0 ≤ Cn ^ (M + 1) * V ^ ((pW + 2) * (M + 1)) := by positivity
    calc Cn ^ (M + 1) * κ ^ (M + 1) * V ^ ((pW + 2) * (M + 1)) * κ * (Real.exp (Λ * τ) / σb)
        = Cn ^ (M + 1) * V ^ ((pW + 2) * (M + 1)) * (κ ^ (M + 1) * κ * Real.exp (Λ * τ)) /
          σb := by ring
      _ ≤ Cn ^ (M + 1) * V ^ ((pW + 2) * (M + 1)) * κ ^ 2 / σb := by
          gcongr
      _ = Cn ^ (M + 1) / σb * (κ ^ 2 * V ^ ((pW + 2) * (M + 1))) := by ring
  have hC0 : 0 ≤ Capp * 2 ^ (M + 1) := by positivity
  calc Capp * 2 ^ (M + 1) * (κ ^ (M + 1 + 1) * ∫ x in (0 : ℝ)..τ, F₁ x) +
        Capp * 2 ^ (M + 1) * (β ^ (M + 1) * κ * ∫ x in (0 : ℝ)..τ, F₂ x)
      ≤ Capp * 2 ^ (M + 1) * (Cn ^ (M + 1) / σb * ahat κ σ τ ^ (M + 1 + 1)) +
        Capp * 2 ^ (M + 1) * (Cn ^ (M + 1) / σb * (κ ^ 2 * V ^ ((pW + 2) * (M + 1)))) :=
        add_le_add (mul_le_mul_of_nonneg_left hT1 hC0) (mul_le_mul_of_nonneg_left hT2 hC0)
    _ = Capp * 2 ^ (M + 1) * Cn ^ (M + 1) / σb *
        (ahat κ σ τ ^ (M + 1 + 1) + κ ^ 2 * V ^ ((pW + 2) * (M + 1))) := by ring

/-- **Collection of the bound on `w - 2Re(ce^{λu}φ_*)`** (`05_single_ring.tex:830-841`). -/
theorem collect_mode {Capp Cv CW Cn A κ V ρ ηb J E : ℝ} {N NW : ℕ}
    (hCapp : 0 ≤ Capp) (hCv : 0 ≤ Cv) (hCW : Cv + Capp + Capp * Cn ≤ CW) (hCn : 1 ≤ Cn)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hκA : κ ≤ A) (hκ0 : 0 < κ) (hV1 : 1 ≤ V) (hρ : 0 ≤ ρ)
    (hηb : 0 ≤ ηb) (hJ0 : 0 ≤ J) (hJ : J ≤ V) (hN : 1 ≤ N) (hNW1 : pW + 2 ≤ NW)
    (hNW2 : (pW + 2) * N ≤ NW)
    (hE : E ≤ Cv * (A ^ (N + 1) + κ ^ 2 * V ^ ((pW + 2) * N)) +
      Capp * A * (ρ + ηb + (A + Cn * κ * J ^ (pW + 2)))) :
    E ≤ CW * A * (ρ + A + κ * V ^ NW + ηb) := by
  set X := κ * V ^ NW with hX
  have hX0 : 0 ≤ X := by positivity
  have h1 : A ^ (N + 1) ≤ A * A := by
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := Nat.exists_eq_add_of_le' hN
    calc A ^ (M + 1 + 1) = A ^ M * (A * A) := by ring
      _ ≤ 1 * (A * A) := mul_le_mul_of_nonneg_right (pow_le_one₀ hA0 hA1) (by positivity)
      _ = A * A := one_mul _
  have hVmono : ∀ {m n : ℕ}, m ≤ n → V ^ m ≤ V ^ n := fun h => pow_le_pow_right₀ hV1 h
  have h2 : κ ^ 2 * V ^ ((pW + 2) * N) ≤ A * X := by
    rw [hX, sq]
    have : V ^ ((pW + 2) * N) ≤ V ^ NW := hVmono hNW2
    have hV0 : 0 ≤ V ^ ((pW + 2) * N) := by positivity
    calc κ * κ * V ^ ((pW + 2) * N) ≤ A * κ * V ^ NW := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hκA hκ0.le) this hV0 (by positivity)
      _ = A * (κ * V ^ NW) := by ring
  have h3 : Cn * κ * J ^ (pW + 2) ≤ Cn * X := by
    rw [hX]
    have : J ^ (pW + 2) ≤ V ^ NW := (pow_le_pow_left₀ hJ0 hJ _).trans (hVmono hNW1)
    have := mul_le_mul_of_nonneg_left this (mul_nonneg (by linarith : (0 : ℝ) ≤ Cn) hκ0.le)
    linarith
  have hE' : E ≤ Cv * (A * A + A * X) + Capp * A * (ρ + ηb + (A + Cn * X)) := by
    have hCA : 0 ≤ Capp * A := mul_nonneg hCapp hA0
    have e1 : Cv * (A ^ (N + 1) + κ ^ 2 * V ^ ((pW + 2) * N)) ≤ Cv * (A * A + A * X) :=
      mul_le_mul_of_nonneg_left (add_le_add h1 h2) hCv
    have e2 : Capp * A * (ρ + ηb + (A + Cn * κ * J ^ (pW + 2))) ≤
        Capp * A * (ρ + ηb + (A + Cn * X)) :=
      mul_le_mul_of_nonneg_left (by linarith) hCA
    linarith
  have hS : 0 ≤ ρ + A + X + ηb := by positivity
  have hCn0 : 0 ≤ Cn := by linarith
  nlinarith [mul_nonneg (sub_nonneg.2 hCW) (mul_nonneg hA0 hS), mul_nonneg hCv (mul_nonneg hA0 hρ),
    mul_nonneg hCv (mul_nonneg hA0 hηb), mul_nonneg hCapp (mul_nonneg hA0 hX0),
    mul_nonneg (mul_nonneg hCapp hCn0) (mul_nonneg hA0 hρ),
    mul_nonneg (mul_nonneg hCapp hCn0) (mul_nonneg hA0 hA0),
    mul_nonneg (mul_nonneg hCapp hCn0) (mul_nonneg hA0 hηb)]

/-- The bound `‖w‖_{H^s} ≤ (C_v + C_app)â + C_v κ²V^{(p+2)N}` and its consequence
`≤ C_Wδ₀ + C_Wκ V^{N_W}` (`05_single_ring.tex:842-845`). -/
theorem collect_w {Capp Cv CW A κ V δ₀ E : ℝ} {N NW : ℕ}
    (hCapp : 0 ≤ Capp) (hCv : 0 ≤ Cv) (hCW : Cv + Capp ≤ CW) (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (hAδ : A ≤ δ₀) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hV1 : 1 ≤ V) (hNW2 : (pW + 2) * N ≤ NW)
    (hE : E ≤ Cv * (A ^ (N + 1) + κ ^ 2 * V ^ ((pW + 2) * N)) + Capp * A) :
    E ≤ (Cv + Capp) * A + Cv * κ ^ 2 * V ^ ((pW + 2) * N) ∧
      (Cv + Capp) * A + Cv * κ ^ 2 * V ^ ((pW + 2) * N) ≤ CW * δ₀ + CW * κ * V ^ NW := by
  have h1 : A ^ (N + 1) ≤ A := pow_le_of_le_one hA0 hA1 (Nat.succ_ne_zero N)
  refine ⟨by nlinarith, ?_⟩
  have hδ0 : 0 ≤ δ₀ := hA0.trans hAδ
  have h2 : κ ^ 2 * V ^ ((pW + 2) * N) ≤ κ * V ^ NW := by
    have : V ^ ((pW + 2) * N) ≤ V ^ NW := pow_le_pow_right₀ hV1 hNW2
    have hk : κ ^ 2 ≤ κ := by nlinarith
    exact mul_le_mul hk this (by positivity) hκ0.le
  have h3 : (Cv + Capp) * A ≤ CW * δ₀ :=
    mul_le_mul hCW hAδ hA0 (by linarith)
  have h4 : Cv * κ ^ 2 * V ^ ((pW + 2) * N) ≤ CW * κ * V ^ NW := by
    have := mul_le_mul_of_nonneg_left h2 hCv
    have h5 : Cv * (κ * V ^ NW) ≤ CW * (κ * V ^ NW) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith
  linarith

/-- **The displacement integral** (`05_single_ring.tex:846-855`). -/
theorem disp_integral_le {σ σb κ δ₀ Cn Capp Cv CW CB V τ : ℝ} {N NW : ℕ}
    (hσb : 0 < σb) (hσ : σb ≤ σ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hτV : τ ≤ V)
    (hV1 : 1 ≤ V) (hexp : ahat κ σ τ ≤ δ₀) (hCn : 0 ≤ Cn) (hCapp : 0 ≤ Capp) (hCv : 0 ≤ Cv)
    (hCB : 0 ≤ CB) (hCW1 : Cn + CB * Cv ≤ CW) (hCW2 : (1 + CB * (Cv + Capp)) / σb ≤ CW)
    (hNW1 : pW + 1 ≤ NW) (hNW2 : (pW + 2) * N + 1 ≤ NW) :
    ∫ τ' in (0 : ℝ)..τ, ((Cn * κ * V ^ pW + ahat κ σ τ') +
        CB * ((Cv + Capp) * ahat κ σ τ' + Cv * κ ^ 2 * V ^ ((pW + 2) * N))) ≤
      CW * δ₀ + CW * κ * V ^ NW := by
  have hσ0 : 0 < σ := hσb.trans_le hσ
  set K₀ := Cn * κ * V ^ pW + CB * (Cv * κ ^ 2 * V ^ ((pW + 2) * N)) with hK₀
  set K₁ := 1 + CB * (Cv + Capp) with hK₁
  have hfun : (fun τ' => (Cn * κ * V ^ pW + ahat κ σ τ') +
      CB * ((Cv + Capp) * ahat κ σ τ' + Cv * κ ^ 2 * V ^ ((pW + 2) * N))) =
      fun τ' => K₀ + K₁ * κ * Real.exp (σ * τ') := by
    funext τ'
    simp only [hK₀, hK₁, ahat]
    ring
  rw [hfun, intervalIntegral.integral_add intervalIntegrable_const
    ((by fun_prop : Continuous fun τ' => K₁ * κ * Real.exp (σ * τ')).intervalIntegrable 0 τ),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    integral_exp_mul σ τ hσ0.ne']
  simp only [sub_zero, smul_eq_mul]
  have hδ : κ * Real.exp (σ * τ) ≤ δ₀ := hexp
  have hK₁0 : 0 ≤ K₁ := by rw [hK₁]; positivity
  -- the exponential part
  have hE : K₁ * κ * ((Real.exp (σ * τ) - 1) / σ) ≤ CW * δ₀ := by
    have h1 : K₁ * κ * ((Real.exp (σ * τ) - 1) / σ) ≤ K₁ * (κ * Real.exp (σ * τ)) / σ := by
      have e1 : K₁ * κ * ((Real.exp (σ * τ) - 1) / σ) = (K₁ * κ * (Real.exp (σ * τ) - 1)) / σ := by
        ring
      have e2 : K₁ * (κ * Real.exp (σ * τ)) / σ = (K₁ * κ * Real.exp (σ * τ)) / σ := by ring
      rw [e1, e2]
      apply div_le_div_of_nonneg_right _ hσ0.le
      have := mul_nonneg hK₁0 hκ0.le
      nlinarith
    have hδ0 : 0 ≤ δ₀ := le_trans (by positivity) hδ
    have h2 : K₁ * (κ * Real.exp (σ * τ)) / σ ≤ K₁ * δ₀ / σb := by
      apply div_le_div₀ (mul_nonneg hK₁0 hδ0) (mul_le_mul_of_nonneg_left hδ hK₁0) hσb hσ
    have h3 : K₁ * δ₀ / σb = K₁ / σb * δ₀ := by ring
    have h4 : K₁ / σb * δ₀ ≤ CW * δ₀ := mul_le_mul_of_nonneg_right hCW2 hδ0
    linarith
  -- the constant part
  have hC : τ * K₀ ≤ CW * κ * V ^ NW := by
    have hVm : ∀ {m n : ℕ}, m ≤ n → V ^ m ≤ V ^ n := fun h => pow_le_pow_right₀ hV1 h
    have hV0 : 0 ≤ V := by linarith
    have a1 : τ * (Cn * κ * V ^ pW) ≤ Cn * κ * V ^ NW := by
      calc τ * (Cn * κ * V ^ pW) ≤ V * (Cn * κ * V ^ pW) :=
            mul_le_mul_of_nonneg_right hτV (by positivity)
        _ = Cn * κ * V ^ (pW + 1) := by ring
        _ ≤ Cn * κ * V ^ NW := mul_le_mul_of_nonneg_left (hVm hNW1) (by positivity)
    have a2 : τ * (CB * (Cv * κ ^ 2 * V ^ ((pW + 2) * N))) ≤ CB * Cv * κ * V ^ NW := by
      have hk : κ ^ 2 ≤ κ := by nlinarith
      calc τ * (CB * (Cv * κ ^ 2 * V ^ ((pW + 2) * N)))
          ≤ V * (CB * (Cv * κ * V ^ ((pW + 2) * N))) := by
            apply mul_le_mul hτV _ (by positivity) hV0
            gcongr
        _ = CB * Cv * κ * V ^ ((pW + 2) * N + 1) := by ring
        _ ≤ CB * Cv * κ * V ^ NW := mul_le_mul_of_nonneg_left (hVm hNW2) (by positivity)
    have a3 : Cn * κ * V ^ NW + CB * Cv * κ * V ^ NW ≤ CW * κ * V ^ NW := by
      have : (Cn + CB * Cv) * (κ * V ^ NW) ≤ CW * (κ * V ^ NW) :=
        mul_le_mul_of_nonneg_right hCW1 (by positivity)
      nlinarith
    rw [hK₀, mul_add]
    linarith
  linarith

end WindowH

end OneRing

end NonUniqueEuler
