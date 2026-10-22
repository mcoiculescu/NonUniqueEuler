import NonUniqueEuler.Defs.Sec5.All
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Helpers for `lem:window`: elementary real analysis

Helper file of `P/Sec5/Window.lean`. Everything here is
elementary and fully proved:
* exponential integrals `∫₀^τ e^{A(τ-τ')} e^{Bτ'} dτ'` (`integral_exp_mul_exp`, and the two bounds
  `integral_exp_le_of_lt`, `integral_exp_le_of_gt`), used for `eq:W-v` and the displacement
  (`05_single_ring.tex:807-823`, `:846-855`);
* the Japanese bracket and `ς`: `⟨u⟩ ≤ 1 + u`, `ς ≥ 1`, and the window bookkeeping of
  `05_single_ring.tex:737-741` (`u ≤ T̂₁ ⟹ 1 + u ≤ ς(κ₁)`, `â₁(u) ≤ δ₀`, `κ₁ ≤ â₁(u)`);
* the existence of `κ_W` (`05_single_ring.tex:731-733`: `x ς(x)^N → 0` as `x → 0⁺`), in the
  explicit form `x ς(x)^N ≤ K^N √x`.
-/

noncomputable section

open MeasureTheory Set Real

namespace NonUniqueEuler

namespace OneRing

namespace WindowH

/-! ### Exponential integrals -/

theorem integral_exp_mul (d τ : ℝ) (hd : d ≠ 0) :
    ∫ x in (0 : ℝ)..τ, Real.exp (d * x) = (Real.exp (d * τ) - 1) / d := by
  have hder : ∀ x ∈ uIcc (0 : ℝ) τ,
      HasDerivAt (fun x => Real.exp (d * x) / d) (Real.exp (d * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun x => d * x) d x := by
      simpa using (hasDerivAt_id x).const_mul d
    have h2 := h1.exp.div_const d
    rwa [mul_div_cancel_right₀ _ hd] at h2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)]
  simp only [mul_zero, Real.exp_zero]
  ring

/-- `∫₀^τ e^{A(τ-τ')} e^{Bτ'} dτ' = e^{Aτ}(e^{(B-A)τ} - 1)/(B-A)` for `A ≠ B`. -/
theorem integral_exp_mul_exp (A B τ : ℝ) (hAB : A ≠ B) :
    ∫ x in (0 : ℝ)..τ, Real.exp (A * (τ - x)) * Real.exp (B * x) =
      Real.exp (A * τ) * ((Real.exp ((B - A) * τ) - 1) / (B - A)) := by
  have hfun : (fun x => Real.exp (A * (τ - x)) * Real.exp (B * x)) =
      fun x => Real.exp (A * τ) * Real.exp ((B - A) * x) := by
    funext x
    rw [← Real.exp_add, ← Real.exp_add]
    ring_nf
  rw [hfun, intervalIntegral.integral_const_mul,
    integral_exp_mul (B - A) τ (sub_ne_zero.2 (Ne.symm hAB))]

/-- `∫₀^τ e^{A(τ-τ')} e^{Bτ'} dτ' ≤ e^{Bτ}/(B-A)` for `A < B`. -/
theorem integral_exp_le_of_lt {A B τ : ℝ} (hAB : A < B) :
    ∫ x in (0 : ℝ)..τ, Real.exp (A * (τ - x)) * Real.exp (B * x) ≤
      Real.exp (B * τ) / (B - A) := by
  rw [integral_exp_mul_exp A B τ hAB.ne]
  have hBA : 0 < B - A := sub_pos.2 hAB
  have he : Real.exp (A * τ) * Real.exp ((B - A) * τ) = Real.exp (B * τ) := by
    rw [← Real.exp_add]; ring_nf
  rw [mul_div_assoc', div_le_div_iff_of_pos_right hBA, mul_sub, he, mul_one]
  linarith [Real.exp_pos (A * τ)]

/-- `∫₀^τ e^{A(τ-τ')} e^{Bτ'} dτ' ≤ e^{Aτ}/(A-B)` for `B < A`. -/
theorem integral_exp_le_of_gt {A B τ : ℝ} (hBA : B < A) :
    ∫ x in (0 : ℝ)..τ, Real.exp (A * (τ - x)) * Real.exp (B * x) ≤
      Real.exp (A * τ) / (A - B) := by
  rw [integral_exp_mul_exp A B τ hBA.ne']
  have hAB : 0 < A - B := sub_pos.2 hBA
  have h1 : (Real.exp ((B - A) * τ) - 1) / (B - A) = (1 - Real.exp ((B - A) * τ)) / (A - B) := by
    rw [← neg_sub A B, div_neg, ← neg_div, neg_sub]
  rw [h1, mul_div_assoc', div_le_div_iff_of_pos_right hAB]
  have := Real.exp_pos ((B - A) * τ)
  have he := Real.exp_pos (A * τ)
  nlinarith

/-- The integrand of the exponential integrals is continuous. -/
theorem continuous_exp_mul_exp (A B τ : ℝ) :
    Continuous fun x : ℝ => Real.exp (A * (τ - x)) * Real.exp (B * x) := by
  fun_prop

/-! ### The Japanese bracket and `ς` -/

theorem jap_le_one_add {u : ℝ} (hu : 0 ≤ u) : Prelim.jap u ≤ 1 + u := by
  unfold Prelim.jap
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith

theorem one_le_varsigma {χ : ℝ → ℝ} (hσb : 0 < Eig.sigb χ) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    1 ≤ varsigma χ x := by
  unfold varsigma
  have : 0 ≤ Real.log (1 / x) := Real.log_nonneg (by rw [le_div_iff₀ hx0]; linarith)
  have := mul_nonneg (inv_nonneg.2 hσb.le) this
  linarith

/-- The window bookkeeping (`05_single_ring.tex:737-741`): for `σ ≥ σ_b > 0`,
`0 < κ₁`, `δ₀ ≤ 1` and `0 ≤ u ≤ T̂₁ = σ⁻¹ log(δ₀/κ₁)`: `κ₁ ≤ δ₀`, `1 + u ≤ ς(κ₁)`,
`κ₁ ≤ â₁(u) ≤ δ₀`. -/
theorem window_bookkeeping {χ : ℝ → ℝ} {σ κ₁ δ₀ u : ℝ} (hσb : 0 < Eig.sigb χ)
    (hσ : Eig.sigb χ ≤ σ) (hκ : 0 < κ₁) (hδ0 : 0 < δ₀) (hδ : δ₀ ≤ 1) (hu0 : 0 ≤ u)
    (huT : u ≤ That σ δ₀ κ₁)
    (hT : 0 < That σ δ₀ κ₁) :
    κ₁ ≤ δ₀ ∧ κ₁ ≤ 1 ∧ 1 + u ≤ varsigma χ κ₁ ∧ κ₁ ≤ ahat κ₁ σ u ∧ ahat κ₁ σ u ≤ δ₀ := by
  have hσ0 : 0 < σ := hσb.trans_le hσ
  unfold That at hT huT
  have hlog : 0 < Real.log (δ₀ / κ₁) := by
    by_contra hneg
    push Not at hneg
    have : σ⁻¹ * Real.log (δ₀ / κ₁) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 hσ0.le) hneg
    linarith
  have hδκ : κ₁ < δ₀ := by
    have h1 : 1 < δ₀ / κ₁ := (Real.log_pos_iff (div_pos hδ0 hκ).le).1 hlog
    rwa [lt_div_iff₀ hκ, one_mul] at h1
  have hκ1 : κ₁ ≤ 1 := hδκ.le.trans hδ
  refine ⟨hδκ.le, hκ1, ?_, ?_, ?_⟩
  · -- `u ≤ σ⁻¹ log(δ₀/κ₁) ≤ σ_b⁻¹ log(1/κ₁)`
    unfold varsigma
    have h1 : Real.log (δ₀ / κ₁) ≤ Real.log (1 / κ₁) :=
      Real.log_le_log (div_pos hδ0 hκ) (div_le_div_of_nonneg_right hδ hκ.le)
    have h2 : σ⁻¹ ≤ (Eig.sigb χ)⁻¹ := inv_anti₀ hσb hσ
    have h3 : σ⁻¹ * Real.log (δ₀ / κ₁) ≤ (Eig.sigb χ)⁻¹ * Real.log (1 / κ₁) :=
      mul_le_mul h2 h1 hlog.le (inv_nonneg.2 hσb.le)
    linarith
  · unfold ahat
    have : 1 ≤ Real.exp (σ * u) := Real.one_le_exp (mul_nonneg hσ0.le hu0)
    nlinarith
  · unfold ahat
    have h1 : σ * u ≤ Real.log (δ₀ / κ₁) := by
      have := mul_le_mul_of_nonneg_left huT hσ0.le
      rwa [← mul_assoc, mul_inv_cancel₀ hσ0.ne', one_mul] at this
    have h2 : Real.exp (σ * u) ≤ δ₀ / κ₁ := by
      calc Real.exp (σ * u) ≤ Real.exp (Real.log (δ₀ / κ₁)) := Real.exp_le_exp.2 h1
        _ = δ₀ / κ₁ := Real.exp_log (div_pos hδ0 hκ)
    calc κ₁ * Real.exp (σ * u) ≤ κ₁ * (δ₀ / κ₁) := mul_le_mul_of_nonneg_left h2 hκ.le
      _ = δ₀ := by field_simp

/-! ### The choice of `κ_W` -/

/-- `ς(x)^N ≤ K^N e^{log(1/x)/2}` for `x ∈ (0,1]`, `K = max 1 ((2N+2)/σ_b)`. -/
theorem varsigma_pow_le {χ : ℝ → ℝ} (hσb : 0 < Eig.sigb χ) (N : ℕ) {x : ℝ} (hx0 : 0 < x)
    (hx1 : x ≤ 1) :
    varsigma χ x ^ N ≤ max 1 ((2 * N + 2) / Eig.sigb χ) ^ N *
      Real.exp (Real.log (1 / x) / 2) := by
  set y := Real.log (1 / x) with hy
  have hy0 : 0 ≤ y := Real.log_nonneg (by rw [le_div_iff₀ hx0]; linarith)
  set m : ℝ := 2 * N + 2 with hm
  have hm0 : 0 < m := by positivity
  set K := max 1 (m / Eig.sigb χ) with hK
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK2 : m / Eig.sigb χ ≤ K := le_max_right _ _
  -- `ς(x) ≤ K (1 + y/m) ≤ K e^{y/m}`
  have h1 : varsigma χ x ≤ K * Real.exp (y / m) := by
    unfold varsigma
    rw [← hy]
    have hA : 1 + (Eig.sigb χ)⁻¹ * y ≤ K * (1 + y / m) := by
      have e1 : (Eig.sigb χ)⁻¹ * y = (m / Eig.sigb χ) * (y / m) := by
        field_simp
      rw [e1, mul_add, mul_one]
      have : (m / Eig.sigb χ) * (y / m) ≤ K * (y / m) :=
        mul_le_mul_of_nonneg_right hK2 (div_nonneg hy0 hm0.le)
      linarith
    have hB : 1 + y / m ≤ Real.exp (y / m) := by
      have := Real.add_one_le_exp (y / m)
      linarith
    calc 1 + (Eig.sigb χ)⁻¹ * y ≤ K * (1 + y / m) := hA
      _ ≤ K * Real.exp (y / m) := mul_le_mul_of_nonneg_left hB (by linarith)
  have hς0 : 0 ≤ varsigma χ x := by
    have := one_le_varsigma hσb hx0 hx1
    linarith
  calc varsigma χ x ^ N ≤ (K * Real.exp (y / m)) ^ N := pow_le_pow_left₀ hς0 h1 N
    _ = K ^ N * Real.exp (N * (y / m)) := by rw [mul_pow, ← Real.exp_nat_mul]
    _ ≤ K ^ N * Real.exp (y / 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp.2
        rw [mul_div_assoc']
        rw [div_le_div_iff₀ hm0 (by norm_num : (0 : ℝ) < 2)]
        have : (N : ℝ) * 2 ≤ m := by rw [hm]; linarith
        nlinarith

/-- `x e^{log(1/x)/2} = e^{log x / 2}` for `x > 0`. -/
theorem mul_exp_log_inv_half {x : ℝ} (hx0 : 0 < x) :
    x * Real.exp (Real.log (1 / x) / 2) = Real.exp (Real.log x / 2) := by
  have : x * Real.exp (Real.log (1 / x) / 2) =
      Real.exp (Real.log x) * Real.exp (Real.log (1 / x) / 2) := by rw [Real.exp_log hx0]
  rw [this, ← Real.exp_add, one_div, Real.log_inv]
  ring_nf

/-- **Existence of `κ_W`** (`05_single_ring.tex:731-733`): for `C > 0`, `ε > 0` and `N`, there is
`κ ∈ (0,1]` with `C x ς(x)^N ≤ ε` for every `x ∈ (0,κ]`. -/
theorem exists_kappa {χ : ℝ → ℝ} (hσb : 0 < Eig.sigb χ) (N : ℕ) {C ε : ℝ} (hC : 0 < C)
    (hε : 0 < ε) :
    ∃ κ : ℝ, κ ∈ Ioc (0 : ℝ) 1 ∧ ∀ x ∈ Ioc (0 : ℝ) κ, C * x * varsigma χ x ^ N ≤ ε := by
  set K := max 1 ((2 * N + 2) / Eig.sigb χ) with hK
  have hK0 : 0 < K := lt_of_lt_of_le one_pos (le_max_left _ _)
  set z := ε / (C * K ^ N) with hz
  have hz0 : 0 < z := div_pos hε (mul_pos hC (pow_pos hK0 N))
  refine ⟨min 1 (z ^ 2), ⟨lt_min one_pos (pow_pos hz0 2), min_le_left _ _⟩, ?_⟩
  intro x hx
  have hx0 : 0 < x := hx.1
  have hx1 : x ≤ 1 := hx.2.trans (min_le_left _ _)
  have hxz : x ≤ z ^ 2 := hx.2.trans (min_le_right _ _)
  have h1 := varsigma_pow_le hσb N hx0 hx1
  rw [← hK] at h1
  have h2 : Real.exp (Real.log x / 2) ≤ z := by
    have : Real.log x ≤ Real.log (z ^ 2) := Real.log_le_log hx0 hxz
    rw [Real.log_pow] at this
    calc Real.exp (Real.log x / 2) ≤ Real.exp (Real.log z) := by
          apply Real.exp_le_exp.2; push_cast at this; linarith
      _ = z := Real.exp_log hz0
  calc C * x * varsigma χ x ^ N
      ≤ C * x * (K ^ N * Real.exp (Real.log (1 / x) / 2)) :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg hC.le hx0.le)
    _ = C * K ^ N * (x * Real.exp (Real.log (1 / x) / 2)) := by ring
    _ = C * K ^ N * Real.exp (Real.log x / 2) := by rw [mul_exp_log_inv_half hx0]
    _ ≤ C * K ^ N * z := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = ε := by rw [hz]; field_simp

end WindowH

end OneRing

end NonUniqueEuler
