import NonUniqueEuler.Defs.Sec5.All
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Helpers for `window_approx`: scalar estimates

Helper of `P/Sec5/Window/Approx.lean` (`05_single_ring.tex:766-786`, the integrals in the proof
of `eq:W-hier`). Namespace `NonUniqueEuler.OneRing.WAppH`. Only real analysis.

With `â₁(v) = κe^{σv}` (`ahat κ σ v`), `ε ≥ 0` and `𝔟(v) = â₁(v) + ε⟨v⟩^{p+2}`:

* `jap_mono`, `le_jap`, `continuous_jap`, `ahat_mono`, `ahat_shift` (`e^{σ(u-v)}â₁(v) = â₁(u)`);
* `integral_ahat_le`: `∫₀ᵘ â₁ ≤ â₁(u)/σ`; `integral_jap_pow_le`: `∫₀ᵘ ⟨v⟩^p ≤ ⟨u⟩^{p+1}`;
* `hier_integral_le`: `∫₀ᵘ (â₁ + ε⟨v⟩^p) 𝔟^n ≤ (σ⁻¹ + 1) 𝔟(u)^{n+1}` — a simplification of the
  binomial computation of the manuscript (`:766-786`): `𝔟` is nondecreasing, so
  `𝔟(v)^n ≤ 𝔟(u)^n`, and `∫₀ᵘ â₁ ≤ â₁(u)/σ ≤ 𝔟(u)/σ`, `∫₀ᵘ ε⟨v⟩^p ≤ ε⟨u⟩^{p+2} ≤ 𝔟(u)`;
* `duhamel_hier_le`: the resulting bound of the Duhamel integral of
  `K â₁(â₁ + ε⟨v⟩^p)𝔟^n` with growth `Ce^{σ(u-v)}`, and `duhamel_hier_integrable`.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace NonUniqueEuler.OneRing.WAppH

open Prelim

theorem continuous_jap : Continuous jap := by
  unfold jap
  fun_prop

theorem jap_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) : jap u ≤ jap v := by
  unfold jap
  apply Real.sqrt_le_sqrt
  nlinarith

theorem le_jap (u : ℝ) : u ≤ jap u := (le_abs_self u).trans (abs_le_jap u)

theorem jap_pow_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (p : ℕ) : jap u ^ p ≤ jap v ^ p :=
  pow_le_pow_left₀ (jap_nonneg u) (jap_mono hu huv) p

theorem jap_pow_le_pow {u : ℝ} {p q : ℕ} (hpq : p ≤ q) : jap u ^ p ≤ jap u ^ q :=
  pow_le_pow_right₀ (one_le_jap u) hpq

theorem ahat_nonneg {κ σ : ℝ} (hκ : 0 ≤ κ) (u : ℝ) : 0 ≤ ahat κ σ u :=
  mul_nonneg hκ (Real.exp_pos _).le

theorem ahat_mono {κ σ u v : ℝ} (hκ : 0 ≤ κ) (hσ : 0 ≤ σ) (huv : u ≤ v) :
    ahat κ σ u ≤ ahat κ σ v := by
  unfold ahat
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left huv hσ)) hκ

theorem ahat_shift (κ σ u v : ℝ) : Real.exp (σ * (u - v)) * ahat κ σ v = ahat κ σ u := by
  unfold ahat
  rw [mul_left_comm, ← Real.exp_add]
  ring_nf

theorem continuous_ahat (κ σ : ℝ) : Continuous (ahat κ σ) := by
  unfold ahat
  fun_prop

/-- `∫₀ᵘ â₁ ≤ â₁(u)/σ`. -/
theorem integral_ahat_le {κ σ u : ℝ} (hκ : 0 ≤ κ) (hσ : 0 < σ) :
    ∫ v in (0 : ℝ)..u, ahat κ σ v ≤ ahat κ σ u / σ := by
  have hd : ∀ x ∈ uIcc (0 : ℝ) u,
      HasDerivAt (fun v => κ / σ * Real.exp (σ * v)) (ahat κ σ x) x := by
    intro x _
    have h1 := ((hasDerivAt_id x).const_mul σ).exp.const_mul (κ / σ)
    have hσ0 : σ ≠ 0 := hσ.ne'
    refine h1.congr_deriv ?_
    unfold ahat
    simp only [id]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuous_ahat κ σ).intervalIntegrable _ _)]
  have h0 : 0 ≤ κ / σ * Real.exp (σ * 0) := by positivity
  have he : κ / σ * Real.exp (σ * u) = ahat κ σ u / σ := by
    unfold ahat; ring
  linarith

/-- `∫₀ᵘ ⟨v⟩^p ≤ ⟨u⟩^{p+1}` for `u ≥ 0`. -/
theorem integral_jap_pow_le {u : ℝ} (hu : 0 ≤ u) (p : ℕ) :
    ∫ v in (0 : ℝ)..u, jap v ^ p ≤ jap u ^ (p + 1) := by
  have hint : IntervalIntegrable (fun v => jap v ^ p) volume 0 u :=
    (continuous_jap.pow p).intervalIntegrable _ _
  have h1 : ∫ v in (0 : ℝ)..u, jap v ^ p ≤ ∫ v in (0 : ℝ)..u, jap u ^ p :=
    intervalIntegral.integral_mono_on hu hint intervalIntegrable_const
      fun v hv => jap_pow_mono hv.1 hv.2 p
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h1
  calc _ ≤ u * jap u ^ p := h1
    _ ≤ jap u * jap u ^ p := mul_le_mul_of_nonneg_right (le_jap u) (pow_nonneg (jap_nonneg u) p)
    _ = jap u ^ (p + 1) := by ring

/-- `𝔟(v) = â₁(v) + ε⟨v⟩^q`. -/
def bW (κ σ ε : ℝ) (q : ℕ) (v : ℝ) : ℝ := ahat κ σ v + ε * jap v ^ q

theorem bW_nonneg {κ σ ε : ℝ} (hκ : 0 ≤ κ) (hε : 0 ≤ ε) (q : ℕ) (v : ℝ) : 0 ≤ bW κ σ ε q v :=
  add_nonneg (ahat_nonneg hκ v) (mul_nonneg hε (pow_nonneg (jap_nonneg v) q))

theorem bW_mono {κ σ ε u v : ℝ} (hκ : 0 ≤ κ) (hσ : 0 ≤ σ) (hε : 0 ≤ ε) (q : ℕ) (hu : 0 ≤ u)
    (huv : u ≤ v) : bW κ σ ε q u ≤ bW κ σ ε q v :=
  add_le_add (ahat_mono hκ hσ huv) (mul_le_mul_of_nonneg_left (jap_pow_mono hu huv q) hε)

theorem continuous_bW (κ σ ε : ℝ) (q : ℕ) : Continuous (bW κ σ ε q) := by
  unfold bW
  exact (continuous_ahat κ σ).add (continuous_const.mul (continuous_jap.pow q))

theorem ahat_le_bW {κ σ ε : ℝ} (hε : 0 ≤ ε) (q : ℕ) (v : ℝ) : ahat κ σ v ≤ bW κ σ ε q v :=
  le_add_of_nonneg_right (mul_nonneg hε (pow_nonneg (jap_nonneg v) q))

/-- `â₁(v) + ε⟨v⟩^p ≤ 𝔟(v)`. -/
theorem field_le_bW {κ σ ε : ℝ} (hε : 0 ≤ ε) (p : ℕ) (v : ℝ) :
    ahat κ σ v + ε * jap v ^ p ≤ bW κ σ ε (p + 2) v :=
  add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (jap_pow_le_pow (u := v) (p := p) (q := p + 2) (by omega)) hε)

/-- **The integral of the hierarchy** (`05_single_ring.tex:766-786`, simplified):
`∫₀ᵘ (â₁ + ε⟨v⟩^p) 𝔟^n ≤ (σ⁻¹ + 1) 𝔟(u)^{n+1}`. -/
theorem hier_integral_le {κ σ ε u : ℝ} (p n : ℕ) (hκ : 0 ≤ κ) (hσ : 0 < σ) (hε : 0 ≤ ε)
    (hu : 0 ≤ u) :
    ∫ v in (0 : ℝ)..u, (ahat κ σ v + ε * jap v ^ p) * bW κ σ ε (p + 2) v ^ n ≤
      (σ⁻¹ + 1) * bW κ σ ε (p + 2) u ^ (n + 1) := by
  set B := bW κ σ ε (p + 2) with hB
  have hf : Continuous fun v => ahat κ σ v + ε * jap v ^ p :=
    (continuous_ahat κ σ).add (continuous_const.mul (continuous_jap.pow p))
  have hint1 : IntervalIntegrable (fun v => (ahat κ σ v + ε * jap v ^ p) * B v ^ n) volume 0 u :=
    (hf.mul ((continuous_bW κ σ ε (p + 2)).pow n)).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun v => (ahat κ σ v + ε * jap v ^ p) * B u ^ n) volume 0 u :=
    (hf.mul continuous_const).intervalIntegrable _ _
  have h1 : ∫ v in (0 : ℝ)..u, (ahat κ σ v + ε * jap v ^ p) * B v ^ n ≤
      ∫ v in (0 : ℝ)..u, (ahat κ σ v + ε * jap v ^ p) * B u ^ n := by
    refine intervalIntegral.integral_mono_on hu hint1 hint2 fun v hv => ?_
    refine mul_le_mul_of_nonneg_left ?_
      (add_nonneg (ahat_nonneg hκ v) (mul_nonneg hε (pow_nonneg (jap_nonneg v) p)))
    exact pow_le_pow_left₀ (bW_nonneg hκ hε _ v) (bW_mono hκ hσ.le hε _ hv.1 hv.2) n
  have hia : IntervalIntegrable (ahat κ σ) volume 0 u := (continuous_ahat κ σ).intervalIntegrable _ _
  have hij : IntervalIntegrable (fun v => ε * jap v ^ p) volume 0 u :=
    (continuous_const.mul (continuous_jap.pow p)).intervalIntegrable _ _
  have h2 : ∫ v in (0 : ℝ)..u, (ahat κ σ v + ε * jap v ^ p) * B u ^ n =
      ((∫ v in (0 : ℝ)..u, ahat κ σ v) + ε * ∫ v in (0 : ℝ)..u, jap v ^ p) * B u ^ n := by
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_add hia hij,
      intervalIntegral.integral_const_mul]
  have h3 : (∫ v in (0 : ℝ)..u, ahat κ σ v) + ε * ∫ v in (0 : ℝ)..u, jap v ^ p ≤
      (σ⁻¹ + 1) * B u := by
    have ha := integral_ahat_le (u := u) hκ hσ
    have hj := integral_jap_pow_le hu p
    have hj' : ε * ∫ v in (0 : ℝ)..u, jap v ^ p ≤ ε * jap u ^ (p + 2) := by
      refine mul_le_mul_of_nonneg_left (hj.trans (jap_pow_le_pow (p := p + 1) (q := p + 2)
        (by omega))) hε
    have hab : ahat κ σ u ≤ B u := ahat_le_bW hε _ u
    have hBnn : 0 ≤ B u := bW_nonneg hκ hε _ u
    have hσi : 0 < σ⁻¹ := inv_pos.2 hσ
    have hdiv : ahat κ σ u / σ = σ⁻¹ * ahat κ σ u := by rw [div_eq_inv_mul]
    have hjB : ε * jap u ^ (p + 2) ≤ B u := le_add_of_nonneg_left (ahat_nonneg hκ u)
    nlinarith
  have hBn : 0 ≤ B u ^ n := pow_nonneg (bW_nonneg hκ hε _ u) n
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ (σ⁻¹ + 1) * B u * B u ^ n := mul_le_mul_of_nonneg_right h3 hBn
    _ = (σ⁻¹ + 1) * B u ^ (n + 1) := by ring

/-- The integrand of the Duhamel bound of the hierarchy is integrable. -/
theorem duhamel_hier_integrable (C K κ σ ε u : ℝ) (p n : ℕ) :
    IntervalIntegrable (fun v => C * Real.exp (σ * (u - v)) *
      (K * ahat κ σ v * (ahat κ σ v + ε * jap v ^ p) * bW κ σ ε (p + 2) v ^ n)) volume 0 u := by
  refine Continuous.intervalIntegrable ?_ _ _
  have hf : Continuous fun v => ahat κ σ v + ε * jap v ^ p :=
    (continuous_ahat κ σ).add (continuous_const.mul (continuous_jap.pow p))
  exact (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
    (continuous_const.sub continuous_id)))).mul
    (((continuous_const.mul (continuous_ahat κ σ)).mul hf).mul
      ((continuous_bW κ σ ε (p + 2)).pow n))

/-- **The Duhamel bound of the hierarchy**: with growth `Ce^{σ(u-v)}` and forcing bound
`K â₁(â₁ + ε⟨v⟩^p)𝔟^n`, the integral is at most `CK(σ⁻¹+1) â₁(u)𝔟(u)^{n+1}`. -/
theorem duhamel_hier_le {C K κ σ ε u : ℝ} (p n : ℕ) (hC : 0 ≤ C) (hK : 0 ≤ K) (hκ : 0 ≤ κ)
    (hσ : 0 < σ) (hε : 0 ≤ ε) (hu : 0 ≤ u) :
    ∫ v in (0 : ℝ)..u, C * Real.exp (σ * (u - v)) *
        (K * ahat κ σ v * (ahat κ σ v + ε * jap v ^ p) * bW κ σ ε (p + 2) v ^ n) ≤
      C * K * (σ⁻¹ + 1) * ahat κ σ u * bW κ σ ε (p + 2) u ^ (n + 1) := by
  have heq : (fun v => C * Real.exp (σ * (u - v)) *
        (K * ahat κ σ v * (ahat κ σ v + ε * jap v ^ p) * bW κ σ ε (p + 2) v ^ n)) =
      fun v => (C * K * ahat κ σ u) *
        ((ahat κ σ v + ε * jap v ^ p) * bW κ σ ε (p + 2) v ^ n) := by
    funext v
    rw [← ahat_shift κ σ u v]
    ring
  rw [heq, intervalIntegral.integral_const_mul]
  have h := hier_integral_le p n hκ hσ hε hu (κ := κ) (σ := σ)
  have hc : 0 ≤ C * K * ahat κ σ u := mul_nonneg (mul_nonneg hC hK) (ahat_nonneg hκ u)
  calc _ ≤ (C * K * ahat κ σ u) * ((σ⁻¹ + 1) * bW κ σ ε (p + 2) u ^ (n + 1)) :=
        mul_le_mul_of_nonneg_left h hc
    _ = _ := by ring

/-- `ρ̄ = sup_{u ≥ 0} ⟨u⟩^p e^{-δu} < ∞` for `δ > 0` (`eq:W-const`): an explicit bound
`⟨u⟩^p e^{-δu} ≤ p! e^δ / δ^p`. -/
theorem jap_pow_mul_exp_le {δ : ℝ} (hδ : 0 < δ) (p : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    jap u ^ p * Real.exp (-(δ * u)) ≤ p.factorial * Real.exp δ / δ ^ p := by
  have hj : jap u ≤ 1 + u := by
    unfold jap
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hx : 0 ≤ δ * (1 + u) := by positivity
  have hexp := Real.pow_div_factorial_le_exp (δ * (1 + u)) hx p
  have hfac : (0 : ℝ) < p.factorial := by exact_mod_cast p.factorial_pos
  have h1 : (δ * (1 + u)) ^ p ≤ p.factorial * Real.exp (δ * (1 + u)) := by
    rw [div_le_iff₀ hfac] at hexp
    linarith
  have hδp : 0 < δ ^ p := pow_pos hδ p
  have h2 : jap u ^ p ≤ (1 + u) ^ p := pow_le_pow_left₀ (jap_nonneg u) hj p
  have h3 : (1 + u) ^ p ≤ p.factorial * Real.exp (δ * (1 + u)) / δ ^ p := by
    rw [le_div_iff₀ hδp, ← mul_pow, mul_comm (1 + u) δ]
    exact h1
  have he : Real.exp (δ * (1 + u)) * Real.exp (-(δ * u)) = Real.exp δ := by
    rw [← Real.exp_add]; ring_nf
  have hpos : 0 < Real.exp (-(δ * u)) := Real.exp_pos _
  calc jap u ^ p * Real.exp (-(δ * u)) ≤
        (p.factorial * Real.exp (δ * (1 + u)) / δ ^ p) * Real.exp (-(δ * u)) :=
        mul_le_mul_of_nonneg_right (h2.trans h3) hpos.le
    _ = p.factorial * (Real.exp (δ * (1 + u)) * Real.exp (-(δ * u))) / δ ^ p := by ring
    _ = p.factorial * Real.exp δ / δ ^ p := by rw [he]

end NonUniqueEuler.OneRing.WAppH
