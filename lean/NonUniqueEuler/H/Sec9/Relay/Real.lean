import NonUniqueEuler.H.Sec9.Relay.Basic

/-!
# Helpers for `prop:relay`: the real inequalities of the active phase and the final sum

Helper file of `P/Sec9/Relay.lean` (`09_relay.tex:500-593`). Everything here is proved and
independent of the standing data. Notation: `σ_j`, `σ_k = σ_{j+1}`, `κ = κ♯_{j+1}`,
`T̂ = T̂_{j+1}`, `τ^act = τ_a`, `τ^sat = τ_a + T̂/μ`, `t̄♯_j = τ^sat + T_pin/μ`,
`Y = (κ/δ₀)^{1-γ_j}`, `u = μ(v - τ_a)`.

* `phase2_pt` (`09_relay.tex:527-562`): for `v ∈ [τ^act, τ^sat]`, a bound
  `η ≤ C(2C₂κe^{σ_ku} + 2C₂C(C₀)κ⟨u⟩^me^{σ'u} + C₀κ⟨u⟩^m)` gives
  `e^{σ_j(τ-v)}η ≤ Ce^{x_jT_pin}[2C₂δ₀e^{-(μσ_k-σ_j)(τ^sat-v)} + (2C₂C(C₀)+C₀)δ₀Y⟨T̂⟩^m]`
  (`eq:relay-id`, `κe^{σ_kT̂} = δ₀`, `(σ_j/μ)(T̂-u) + σ'u ≤ γ_jσ_kT̂`);
* `phase2_int`: the integral of that bound over `[τ^act, b]`;
* `phase1_exp`: `κe^{σ_j(τ-τ^act)} ≤ e^{x_jT_pin}δ₀Y` (`09_relay.tex:507-515`);
* `final_alg`: the sum of the three parts and `C'_Ξ ≤ C_Ξ(1 + 1/(σ_b(μ-1)))`
  (`09_relay.tex:575-590`).
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler

namespace Relay

namespace RelayH

/-- **The active phase of ring `j+1`, pointwise** (`09_relay.tex:527-562`). -/
theorem phase2_pt {σj σk μ σ' κ δ₀ Th γ Y Tp τa τ v E CMe C2 Cact C0 : ℝ}
    (hμ : 0 < μ) (hσj : 0 ≤ σj) (hκ : 0 < κ) (hσ' : 0 ≤ σ')
    (hγ1 : σj / μ ≤ γ * σk) (hγ2 : σ' ≤ γ * σk)
    (hκe : κ * Real.exp (σk * Th) = δ₀) (hκγ : κ * Real.exp (γ * σk * Th) = δ₀ * Y)
    (hv : v ∈ Icc τa (τa + Th / μ)) (hτ : τ ≤ τa + Th / μ + Tp / μ)
    (hCMe : 0 ≤ CMe) (hC2 : 0 ≤ C2) (hCact : 0 ≤ Cact) (hC0 : 0 ≤ C0)
    (hE : E ≤ CMe * (2 * C2 * (κ * Real.exp (σk * (μ * (v - τa)))) +
      2 * C2 * (Cact * κ * Prelim.jap (μ * (v - τa)) ^ 3 * Real.exp (σ' * (μ * (v - τa)))) +
      C0 * κ * Prelim.jap (μ * (v - τa)) ^ 3)) :
    Real.exp (σj * (τ - v)) * E ≤
      CMe * Real.exp (σj / μ * Tp) *
        (2 * C2 * δ₀ * Real.exp (-((μ * σk - σj) * (τa + Th / μ - v))) +
          (2 * C2 * Cact + C0) * δ₀ * Y * Prelim.jap Th ^ 3) := by
  set u := μ * (v - τa) with hu
  have hu0 : 0 ≤ u := mul_nonneg hμ.le (by linarith [hv.1])
  have huTh : u ≤ Th := by
    have h1 : v - τa ≤ Th / μ := by linarith [hv.2]
    have := mul_le_mul_of_nonneg_left h1 hμ.le
    rwa [mul_div_cancel₀ _ hμ.ne'] at this
  have hγk : 0 ≤ γ * σk := hσ'.trans hγ2
  have hJ3 : Prelim.jap u ^ 3 ≤ Prelim.jap Th ^ 3 :=
    pow_le_pow_left₀ (Prelim.jap_nonneg _) (jap_le_jap hu0 huTh) 3
  have hJu : 0 ≤ Prelim.jap u ^ 3 := pow_nonneg (Prelim.jap_nonneg _) 3
  set e := Real.exp (σj / μ * (Th - u)) with he
  have he0 : 0 < e := Real.exp_pos _
  -- the time weight
  have hvτ : τa + Th / μ + Tp / μ - v = (Th - u) / μ + Tp / μ := by
    rw [hu]; field_simp; ring
  have hexp1 : Real.exp (σj * (τ - v)) ≤ Real.exp (σj / μ * Tp) * e := by
    rw [he, ← Real.exp_add, Real.exp_le_exp]
    have h1 : σj * (τ - v) ≤ σj * (τa + Th / μ + Tp / μ - v) :=
      mul_le_mul_of_nonneg_left (by linarith) hσj
    rw [hvτ] at h1
    have h2 : σj * ((Th - u) / μ + Tp / μ) = σj / μ * Tp + σj / μ * (Th - u) := by
      field_simp; ring
    linarith
  -- the three terms
  have t1 : e * (κ * Real.exp (σk * u)) =
      δ₀ * Real.exp (-((μ * σk - σj) * (τa + Th / μ - v))) := by
    have hid : τa + Th / μ - v = (Th - u) / μ := by rw [hu]; field_simp; ring
    rw [← hκe, hid, he]
    have : σj / μ * (Th - u) + σk * u = σk * Th + -((μ * σk - σj) * ((Th - u) / μ)) := by
      field_simp; ring
    calc Real.exp (σj / μ * (Th - u)) * (κ * Real.exp (σk * u))
        = κ * Real.exp (σj / μ * (Th - u) + σk * u) := by rw [Real.exp_add]; ring
      _ = κ * Real.exp (σk * Th + -((μ * σk - σj) * ((Th - u) / μ))) := by rw [this]
      _ = κ * Real.exp (σk * Th) * Real.exp (-((μ * σk - σj) * ((Th - u) / μ))) := by
          rw [Real.exp_add]; ring
  have hexpγ : σj / μ * (Th - u) ≤ γ * σk * Th - γ * σk * u :=
    by nlinarith [mul_le_mul_of_nonneg_right hγ1 (by linarith : (0 : ℝ) ≤ Th - u)]
  have t2 : e * Real.exp (σ' * u) * κ ≤ δ₀ * Y := by
    rw [← hκγ, he, ← Real.exp_add, mul_comm]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hκ.le
    nlinarith [mul_le_mul_of_nonneg_right hγ2 hu0]
  have t3 : e * κ ≤ δ₀ * Y := by
    rw [← hκγ, he, mul_comm]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hκ.le
    nlinarith [mul_nonneg hγk hu0]
  -- the bracket
  set B := 2 * C2 * (κ * Real.exp (σk * u)) +
      2 * C2 * (Cact * κ * Prelim.jap u ^ 3 * Real.exp (σ' * u)) + C0 * κ * Prelim.jap u ^ 3
    with hB
  have hB0 : 0 ≤ B := by
    have := Real.exp_pos (σk * u)
    have := Real.exp_pos (σ' * u)
    positivity
  have heB : e * B ≤ 2 * C2 * δ₀ * Real.exp (-((μ * σk - σj) * (τa + Th / μ - v))) +
      (2 * C2 * Cact + C0) * δ₀ * Y * Prelim.jap Th ^ 3 := by
    have hδY : 0 ≤ δ₀ * Y := (mul_nonneg he0.le hκ.le).trans t3
    have eq1 : e * B = 2 * C2 * (e * (κ * Real.exp (σk * u))) +
        2 * C2 * Cact * Prelim.jap u ^ 3 * (e * Real.exp (σ' * u) * κ) +
        C0 * Prelim.jap u ^ 3 * (e * κ) := by rw [hB]; ring
    rw [eq1, t1]
    have h2C : 0 ≤ 2 * C2 * Cact * Prelim.jap u ^ 3 := by positivity
    have h0C : 0 ≤ C0 * Prelim.jap u ^ 3 := by positivity
    have s2 := mul_le_mul_of_nonneg_left t2 h2C
    have s3 := mul_le_mul_of_nonneg_left t3 h0C
    have s4 : (2 * C2 * Cact + C0) * δ₀ * Y * Prelim.jap u ^ 3 ≤
        (2 * C2 * Cact + C0) * δ₀ * Y * Prelim.jap Th ^ 3 := by
      have : 0 ≤ (2 * C2 * Cact + C0) * δ₀ * Y := by
        have : 0 ≤ 2 * C2 * Cact + C0 := by positivity
        rw [mul_assoc]; exact mul_nonneg this hδY
      exact mul_le_mul_of_nonneg_left hJ3 this
    nlinarith
  calc Real.exp (σj * (τ - v)) * E
      ≤ Real.exp (σj * (τ - v)) * (CMe * B) :=
        mul_le_mul_of_nonneg_left hE (Real.exp_pos _).le
    _ ≤ Real.exp (σj / μ * Tp) * e * (CMe * B) :=
        mul_le_mul_of_nonneg_right hexp1 (mul_nonneg hCMe hB0)
    _ = CMe * Real.exp (σj / μ * Tp) * (e * B) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left heB (mul_nonneg hCMe (Real.exp_pos _).le)

/-- **The active phase of ring `j+1`, integrated** (`09_relay.tex:537-562`). -/
theorem phase2_int {F : ℝ → ℝ} {τa b τs c A₀ B₀ K : ℝ} (hab : τa ≤ b) (hbs : b ≤ τs)
    (hc : 0 < c) (hA₀ : 0 ≤ A₀) (hB₀ : 0 ≤ B₀) (hK : 0 ≤ K)
    (hpt : ∀ v ∈ Icc τa b, F v ≤ A₀ * (B₀ * Real.exp (-(c * (τs - v))) + K)) :
    (∫ v in τa..b, F v) ≤ A₀ * (B₀ / c + K * (b - τa)) := by
  set g : ℝ → ℝ := fun v => A₀ * (B₀ * Real.exp (-(c * (τs - v))) + K) with hg
  have hgc : Continuous g := by simp only [hg]; fun_prop
  have hg0 : 0 ≤ ∫ v in τa..b, g v :=
    intervalIntegral.integral_nonneg hab fun v _ => by
      simp only [hg]; have := Real.exp_pos (-(c * (τs - v))); positivity
  refine (integral_le_of_le hab (hgc.intervalIntegrable _ _) hpt hg0).trans ?_
  have hi1 : IntervalIntegrable (fun v => B₀ * Real.exp (-(c * (τs - v)))) volume τa b :=
    (by fun_prop : Continuous fun v => B₀ * Real.exp (-(c * (τs - v)))).intervalIntegrable _ _
  have hcalc : (∫ v in τa..b, g v) =
      A₀ * (B₀ * (∫ v in τa..b, Real.exp (-(c * (τs - v)))) + (b - τa) * K) := by
    simp only [hg]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hi1 intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
  rw [hcalc]
  have hI := integral_exp_neg_le hc hab hbs
  have : B₀ * (∫ v in τa..b, Real.exp (-(c * (τs - v)))) ≤ B₀ / c := by
    calc B₀ * (∫ v in τa..b, Real.exp (-(c * (τs - v)))) ≤ B₀ * (1 / c) :=
          mul_le_mul_of_nonneg_left hI hB₀
      _ = B₀ / c := by ring
  have h2 : (b - τa) * K = K * (b - τa) := mul_comm _ _
  rw [h2]
  exact mul_le_mul_of_nonneg_left (by linarith) hA₀

/-- **The weight of the quiet phase at `τ`** (`09_relay.tex:507-515`, `eq:relay-id`):
`κ e^{σ_j(τ-τ^act)} ≤ e^{x_jT_pin} δ₀Y` for `τ ≤ τ^act + T̂/μ + T_pin/μ`. -/
theorem phase1_exp {σj σk μ κ δ₀ Th γ Y Tp τa τ : ℝ} (hμ : 0 < μ) (hσj : 0 ≤ σj)
    (hκ : 0 < κ) (hTh : 0 ≤ Th) (hγ1 : σj / μ ≤ γ * σk)
    (hκγ : κ * Real.exp (γ * σk * Th) = δ₀ * Y) (hτ : τ ≤ τa + Th / μ + Tp / μ) :
    κ * Real.exp (σj * (τ - τa)) ≤ Real.exp (σj / μ * Tp) * (δ₀ * Y) := by
  rw [← hκγ]
  have h1 : σj * (τ - τa) ≤ σj / μ * Tp + γ * σk * Th := by
    have : σj * (τ - τa) ≤ σj * (Th / μ + Tp / μ) :=
      mul_le_mul_of_nonneg_left (by linarith) hσj
    have h2 : σj * (Th / μ + Tp / μ) = σj / μ * Tp + σj / μ * Th := by field_simp; ring
    have h3 : σj / μ * Th ≤ γ * σk * Th := mul_le_mul_of_nonneg_right hγ1 hTh
    linarith
  calc κ * Real.exp (σj * (τ - τa)) ≤ κ * Real.exp (σj / μ * Tp + γ * σk * Th) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h1) hκ.le
    _ = Real.exp (σj / μ * Tp) * (κ * Real.exp (γ * σk * Th)) := by rw [Real.exp_add]; ring

/-- **The sum of the three parts** (`09_relay.tex:575-590`): with `x = σ_b(μ-1)`,
`c ≥ x/2`, `T̂⟨T̂⟩^m ≤ ⟨L⟩^{m+1}/Z`, the parts `I₁ ≤ C(2C_Q/x + 1)EK₁δ₀Y`,
`I₂ ≤ CE(2C₂δ₀/c + Dδ₀Y⟨T̂⟩^mT̂)`, `I₃ ≤ CE·C_D` sum to at most
`CE[4C₂δ₀/x + C_D + (max(1,2C_Q)K₁ + D/Z)(1 + 1/x)δ₀Y⟨L⟩^{m+1}]`. -/
theorem final_alg {I₁ I₂ I₃ CMe E K₁ CQ C2 D Z x c δ₀ Y J3 J4 Th CDT : ℝ}
    (hCMe : 0 ≤ CMe) (hE : 0 ≤ E) (hK₁ : 0 < K₁) (hC2 : 0 ≤ C2) (hD : 0 ≤ D)
    (hZ : 0 < Z) (hx : 0 < x) (hc : x / 2 ≤ c) (hδ : 0 < δ₀) (hY : 0 ≤ Y) (hJ4 : 1 ≤ J4)
    (hThJ : J3 * Th ≤ J4 / Z)
    (h1 : I₁ ≤ CMe * (2 * CQ / x + 1) * E * K₁ * (δ₀ * Y))
    (h2 : I₂ ≤ CMe * E * (2 * C2 * δ₀ / c + D * δ₀ * Y * J3 * Th))
    (h3 : I₃ ≤ CMe * E * CDT) :
    I₁ + I₂ + I₃ ≤ CMe * E * (4 * C2 * δ₀ / x + CDT +
      (max 1 (2 * CQ) * K₁ + D / Z) * (1 + 1 / x) * δ₀ * Y * J4) := by
  have hc0 : 0 < c := lt_of_lt_of_le (by linarith) hc
  have hCE : 0 ≤ CMe * E := mul_nonneg hCMe hE
  have hδY : 0 ≤ δ₀ * Y := mul_nonneg hδ.le hY
  -- `2C₂δ₀/c ≤ 4C₂δ₀/x`
  have hA : 2 * C2 * δ₀ / c ≤ 4 * C2 * δ₀ / x := by
    rw [div_le_div_iff₀ hc0 hx]
    have : 0 ≤ C2 * δ₀ := mul_nonneg hC2 hδ.le
    nlinarith
  -- `K₁(2C_Q/x + 1) ≤ max(1,2C_Q)K₁(1 + 1/x)⟨L⟩^{m+1}`
  have hM1 : 1 ≤ max 1 (2 * CQ) := le_max_left _ _
  have hM2 : 2 * CQ ≤ max 1 (2 * CQ) := le_max_right _ _
  have hix : 0 < 1 / x := by positivity
  have hB : K₁ * (2 * CQ / x + 1) ≤ max 1 (2 * CQ) * K₁ * (1 + 1 / x) * J4 := by
    have e1 : 2 * CQ / x = 2 * CQ * (1 / x) := by ring
    have s1 : 2 * CQ * (1 / x) + 1 ≤ max 1 (2 * CQ) * (1 + 1 / x) := by
      nlinarith [mul_le_mul_of_nonneg_right hM2 hix.le]
    have s2 : max 1 (2 * CQ) * K₁ * (1 + 1 / x) ≤ max 1 (2 * CQ) * K₁ * (1 + 1 / x) * J4 := by
      have : 0 ≤ max 1 (2 * CQ) * K₁ * (1 + 1 / x) := by positivity
      nlinarith
    rw [e1]
    nlinarith
  -- `D⟨T̂⟩^mT̂ ≤ (D/Z)(1 + 1/x)⟨L⟩^{m+1}`
  have hC : D * J3 * Th ≤ D / Z * (1 + 1 / x) * J4 := by
    have s1 : D * (J3 * Th) ≤ D * (J4 / Z) := mul_le_mul_of_nonneg_left hThJ hD
    have s2 : D * (J4 / Z) = D / Z * J4 := by ring
    have s3 : D / Z * J4 ≤ D / Z * (1 + 1 / x) * J4 := by
      have : 0 ≤ D / Z * J4 := by positivity
      nlinarith
    nlinarith
  have hsum : (2 * CQ / x + 1) * K₁ * (δ₀ * Y) + (2 * C2 * δ₀ / c + D * δ₀ * Y * J3 * Th) +
      CDT ≤ 4 * C2 * δ₀ / x + CDT +
        (max 1 (2 * CQ) * K₁ + D / Z) * (1 + 1 / x) * δ₀ * Y * J4 := by
    have e1 : (2 * CQ / x + 1) * K₁ * (δ₀ * Y) = K₁ * (2 * CQ / x + 1) * (δ₀ * Y) := by ring
    have e2 : D * δ₀ * Y * J3 * Th = D * J3 * Th * (δ₀ * Y) := by ring
    have e3 : (max 1 (2 * CQ) * K₁ + D / Z) * (1 + 1 / x) * δ₀ * Y * J4 =
        max 1 (2 * CQ) * K₁ * (1 + 1 / x) * J4 * (δ₀ * Y) +
          D / Z * (1 + 1 / x) * J4 * (δ₀ * Y) := by ring
    rw [e1, e2, e3]
    have := mul_le_mul_of_nonneg_right hB hδY
    have := mul_le_mul_of_nonneg_right hC hδY
    linarith
  calc I₁ + I₂ + I₃ ≤ CMe * (2 * CQ / x + 1) * E * K₁ * (δ₀ * Y) +
        CMe * E * (2 * C2 * δ₀ / c + D * δ₀ * Y * J3 * Th) + CMe * E * CDT := by linarith
    _ = CMe * E * ((2 * CQ / x + 1) * K₁ * (δ₀ * Y) + (2 * C2 * δ₀ / c + D * δ₀ * Y * J3 * Th) +
        CDT) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum hCE

end RelayH

end Relay

end NonUniqueEuler
