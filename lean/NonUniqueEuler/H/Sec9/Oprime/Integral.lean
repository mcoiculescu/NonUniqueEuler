import NonUniqueEuler.Defs.Sec9.All
import NonUniqueEuler.I.Infra.Ip.Ip
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Helpers for `lem:Oprime`: the Duhamel integrals

Helper file of `P/Sec9/Oprime.lean` (`09_relay.tex:681-725`). Everything here is proved.

* `integral_le_of_le`: comparison of interval integrals when only the larger integrand is known
  to be integrable (the smaller integral is then either bounded or the junk value `0`);
* `maj_le_split`: `maj(τ') ≤ e^{σ(τ'-τ_a)} maj(τ_a) + ∫₀^{τ'-τ_a} e^{σ(τ'-τ_a-x)} η(τ_a+x) dx`
  (`09_relay.tex:682-686`; an equality when the integrand is integrable, and `maj(τ') = 0`
  otherwise);
* `jap_mul_pow_le`: `⟨μx⟩^m ≤ μ^m(1+x)^m ≤ 2(1+x)^m` (`09_relay.tex:707-708`);
* `tail_bound`: the three integrals of the second term (`09_relay.tex:703-725`):
  `∫₀^L e^{σ_j(L-x)}[αe^{μσ_kx} + β(1+x)^3e^{μσ'x} + γ(1+x)^3] dx
   ≤ e^{μσ_kL}[α/(μσ_k - σ_j) + βI_3(X) + γI_3(X)]` when `X ≤ σ_j`, `X ≤ σ_j - μσ'`.
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler

namespace Relay

namespace OprimeH

/-- Comparison of interval integrals with only the larger integrand integrable. -/
theorem integral_le_of_le {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b) (hfg : ∀ x ∈ Icc a b, f x ≤ g x)
    (hg0 : 0 ≤ ∫ x in a..b, g x) : (∫ x in a..b, f x) ≤ ∫ x in a..b, g x := by
  by_cases hf : IntervalIntegrable f volume a b
  · exact intervalIntegral.integral_mono_on hab hf hg hfg
  · rw [intervalIntegral.integral_undef hf]
    exact hg0

/-- **Splitting the Duhamel majorant at `τ_a`** (`09_relay.tex:682-686`). -/
theorem maj_le_split {σ : ℝ} {η : ℝ → ℝ} {τa τ' : ℝ} (h0 : 0 ≤ τa) (hτ : τa ≤ τ')
    (hη : ∀ v ∈ Icc (0 : ℝ) τ', 0 ≤ η v) :
    OneRing.maj σ η τ' ≤ Real.exp (σ * (τ' - τa)) * OneRing.maj σ η τa +
      ∫ x in (0 : ℝ)..(τ' - τa), Real.exp (σ * ((τ' - τa) - x)) * η (τa + x) := by
  set F : ℝ → ℝ := fun v => Real.exp (σ * (τ' - v)) * η v with hF
  have hmaj : OneRing.maj σ η τ' = ∫ v in (0 : ℝ)..τ', F v := rfl
  have hmajA : 0 ≤ OneRing.maj σ η τa := by
    unfold OneRing.maj
    exact intervalIntegral.integral_nonneg h0 fun v hv =>
      mul_nonneg (Real.exp_pos _).le (hη v ⟨hv.1, hv.2.trans hτ⟩)
  have htail0 : 0 ≤ ∫ x in (0 : ℝ)..(τ' - τa), Real.exp (σ * ((τ' - τa) - x)) * η (τa + x) :=
    intervalIntegral.integral_nonneg (by linarith) fun x hx =>
      mul_nonneg (Real.exp_pos _).le (hη _ ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  by_cases hint : IntervalIntegrable F volume 0 τ'
  · have h1 : IntervalIntegrable F volume 0 τa :=
      hint.mono_set (by
        rw [uIcc_of_le h0, uIcc_of_le (h0.trans hτ)]
        exact Icc_subset_Icc le_rfl hτ)
    have h2 : IntervalIntegrable F volume τa τ' :=
      hint.mono_set (by
        rw [uIcc_of_le hτ, uIcc_of_le (h0.trans hτ)]
        exact Icc_subset_Icc h0 le_rfl)
    rw [hmaj, ← intervalIntegral.integral_add_adjacent_intervals h1 h2]
    have hfirst : (∫ v in (0 : ℝ)..τa, F v) =
        Real.exp (σ * (τ' - τa)) * OneRing.maj σ η τa := by
      unfold OneRing.maj
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun v _ => ?_
      simp only [hF]
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    have hsecond : (∫ v in τa..τ', F v) =
        ∫ x in (0 : ℝ)..(τ' - τa), Real.exp (σ * ((τ' - τa) - x)) * η (τa + x) := by
      have := intervalIntegral.integral_comp_add_right F τa (a := 0) (b := τ' - τa)
      rw [zero_add, sub_add_cancel] at this
      rw [← this]
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [hF]
      congr 2
      · ring
      · ring
    rw [hfirst, hsecond]
  · rw [hmaj, intervalIntegral.integral_undef hint]
    have := Real.exp_pos (σ * (τ' - τa))
    positivity

/-- `⟨μx⟩ ≤ μ(1+x)` for `μ ≥ 1`, `x ≥ 0`. -/
theorem jap_mul_le {μ x : ℝ} (hμ : 1 ≤ μ) (hx : 0 ≤ x) : Prelim.jap (μ * x) ≤ μ * (1 + x) := by
  unfold Prelim.jap
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg hx (by linarith : (0 : ℝ) ≤ μ)) (by linarith : (0 : ℝ) ≤ μ)]

/-- `⟨μx⟩^3 ≤ 2(1+x)^3` for `1 ≤ μ`, `μ^3 ≤ 2`, `x ≥ 0` (`09_relay.tex:707-708`). -/
theorem jap_mul_pow_le {μ x : ℝ} (hμ : 1 ≤ μ) (hμ3 : μ ^ 3 ≤ 2) (hx : 0 ≤ x) :
    Prelim.jap (μ * x) ^ 3 ≤ 2 * (1 + x) ^ 3 := by
  have h0 : 0 ≤ Prelim.jap (μ * x) := Real.sqrt_nonneg _
  calc Prelim.jap (μ * x) ^ 3 ≤ (μ * (1 + x)) ^ 3 := pow_le_pow_left₀ h0 (jap_mul_le hμ hx) 3
    _ = μ ^ 3 * (1 + x) ^ 3 := by ring
    _ ≤ 2 * (1 + x) ^ 3 := by
        have : 0 ≤ (1 + x) ^ 3 := by positivity
        nlinarith

/-- `∫₀^L e^{gx} dx ≤ e^{gL}/g` for `g > 0`. -/
theorem integral_exp_mul_le {g L : ℝ} (hg : 0 < g) :
    (∫ x in (0 : ℝ)..L, Real.exp (g * x)) ≤ Real.exp (g * L) / g := by
  have h := intervalIntegral.integral_comp_mul_left (fun x => Real.exp x) (a := 0) (b := L)
    hg.ne'
  rw [h, integral_exp, mul_zero, Real.exp_zero, smul_eq_mul]
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hg.le)

/-- **The three integrals of the second term** (`09_relay.tex:703-725`). -/
theorem tail_bound {σj σk μ σ' X L α β γ : ℝ} (hL : 0 ≤ L) (hX : 0 < X)
    (hg : 0 < μ * σk - σj) (hXj : X ≤ σj) (hXj' : X ≤ σj - μ * σ')
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) {F : ℝ → ℝ}
    (hF : ∀ x ∈ Icc (0 : ℝ) L, F x ≤ α * Real.exp (μ * σk * x) +
      β * ((1 + x) ^ 3 * Real.exp (μ * σ' * x)) + γ * (1 + x) ^ 3) :
    (∫ x in (0 : ℝ)..L, Real.exp (σj * (L - x)) * F x) ≤
      Real.exp (μ * σk * L) * (α / (μ * σk - σj) + β * Ip 3 X + γ * Ip 3 X) := by
  set g := μ * σk - σj with hgdef
  set G : ℝ → ℝ := fun x => α * Real.exp (σj * L) * Real.exp (g * x) +
    (β + γ) * Real.exp (μ * σk * L) * ((1 + x) ^ 3 * Real.exp (-X * x)) with hG
  have hGc : Continuous G := by
    simp only [hG]
    fun_prop
  have hGint : IntervalIntegrable G volume 0 L := hGc.intervalIntegrable _ _
  have hG0 : ∀ x ∈ Icc (0 : ℝ) L, 0 ≤ G x := by
    intro x hx
    have : 0 ≤ 1 + x := by linarith [hx.1]
    simp only [hG]
    positivity
  have hpt : ∀ x ∈ Icc (0 : ℝ) L, Real.exp (σj * (L - x)) * F x ≤ G x := by
    intro x hx
    have hx0 : 0 ≤ x := hx.1
    have h1x : 0 ≤ (1 + x) ^ 3 := by positivity
    have hE := Real.exp_pos (σj * (L - x))
    have hmono : σj * L ≤ μ * σk * L := mul_le_mul_of_nonneg_right (by linarith) hL
    -- the three exponential identities / bounds
    have e1 : Real.exp (σj * (L - x)) * Real.exp (μ * σk * x) =
        Real.exp (σj * L) * Real.exp (g * x) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      simp only [hgdef]
      ring
    have e2 : Real.exp (σj * (L - x)) * Real.exp (μ * σ' * x) ≤
        Real.exp (μ * σk * L) * Real.exp (-X * x) := by
      rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
      nlinarith
    have e3 : Real.exp (σj * (L - x)) ≤ Real.exp (μ * σk * L) * Real.exp (-X * x) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      nlinarith
    calc Real.exp (σj * (L - x)) * F x
        ≤ Real.exp (σj * (L - x)) * (α * Real.exp (μ * σk * x) +
            β * ((1 + x) ^ 3 * Real.exp (μ * σ' * x)) + γ * (1 + x) ^ 3) :=
          mul_le_mul_of_nonneg_left (hF x hx) hE.le
      _ = α * (Real.exp (σj * (L - x)) * Real.exp (μ * σk * x)) +
            β * (1 + x) ^ 3 * (Real.exp (σj * (L - x)) * Real.exp (μ * σ' * x)) +
            γ * (1 + x) ^ 3 * Real.exp (σj * (L - x)) := by ring
      _ ≤ α * (Real.exp (σj * L) * Real.exp (g * x)) +
            β * (1 + x) ^ 3 * (Real.exp (μ * σk * L) * Real.exp (-X * x)) +
            γ * (1 + x) ^ 3 * (Real.exp (μ * σk * L) * Real.exp (-X * x)) := by
          rw [e1]
          have hb : 0 ≤ β * (1 + x) ^ 3 := mul_nonneg hβ h1x
          have hc : 0 ≤ γ * (1 + x) ^ 3 := mul_nonneg hγ h1x
          gcongr
      _ = G x := by simp only [hG]; ring
  have hstep := integral_le_of_le hL hGint hpt (intervalIntegral.integral_nonneg hL hG0)
  refine hstep.trans ?_
  -- compute the integral of `G`
  have hc1 : IntervalIntegrable (fun x : ℝ => α * Real.exp (σj * L) * Real.exp (g * x))
      volume 0 L := (by fun_prop : Continuous fun x : ℝ =>
        α * Real.exp (σj * L) * Real.exp (g * x)).intervalIntegrable _ _
  have hc2 : IntervalIntegrable (fun x : ℝ =>
      (β + γ) * Real.exp (μ * σk * L) * ((1 + x) ^ 3 * Real.exp (-X * x))) volume 0 L :=
    (by fun_prop : Continuous fun x : ℝ =>
      (β + γ) * Real.exp (μ * σk * L) * ((1 + x) ^ 3 * Real.exp (-X * x))).intervalIntegrable _ _
  have hsplit : (∫ x in (0 : ℝ)..L, G x) =
      α * Real.exp (σj * L) * (∫ x in (0 : ℝ)..L, Real.exp (g * x)) +
        (β + γ) * Real.exp (μ * σk * L) *
          ∫ x in (0 : ℝ)..L, (1 + x) ^ 3 * Real.exp (-X * x) := by
    simp only [hG]
    rw [intervalIntegral.integral_add hc1 hc2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  rw [hsplit]
  have hI1 := integral_exp_mul_le (L := L) hg
  have hI2 := intervalIntegral_le_Ip 3 hX hL
  have hA : 0 ≤ α * Real.exp (σj * L) := mul_nonneg hα (Real.exp_pos _).le
  have hB : 0 ≤ (β + γ) * Real.exp (μ * σk * L) := mul_nonneg (by linarith) (Real.exp_pos _).le
  have hexp : Real.exp (σj * L) * Real.exp (g * L) = Real.exp (μ * σk * L) := by
    rw [← Real.exp_add]
    congr 1
    simp only [hgdef]
    ring
  calc α * Real.exp (σj * L) * (∫ x in (0 : ℝ)..L, Real.exp (g * x)) +
        (β + γ) * Real.exp (μ * σk * L) * ∫ x in (0 : ℝ)..L, (1 + x) ^ 3 * Real.exp (-X * x)
      ≤ α * Real.exp (σj * L) * (Real.exp (g * L) / g) +
          (β + γ) * Real.exp (μ * σk * L) * Ip 3 X := by
        gcongr
    _ = Real.exp (μ * σk * L) * (α / g + β * Ip 3 X + γ * Ip 3 X) := by
        rw [← hexp]
        field_simp
        ring
