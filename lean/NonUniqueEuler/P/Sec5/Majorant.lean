import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Sec4.PropSU
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Proof: `def:majorant` and `lem:majorant` (the Duhamel majorant)

Proof of `I/Sec5/Majorant.lean` (`lem:majorant`, `05_single_ring.tex:390-398`, proof `:399-406`).

The proof factors the kernel: `maj(t) = e^{σt} F(t)` with `F(t) = ∫₀ᵗ e^{-στ}η(τ) dτ`
(`maj_eq_exp_mul`). `F` is nonnegative and nondecreasing on `[0,T]` (the integrand
`e^{-στ}η(τ)` is integrable and nonnegative there). Then
* (M1) `e^{σ(t-τ)} maj(τ) = e^{σt} F(τ) ≤ e^{σt} F(t) = maj(t)`;
* (M2) `∫_τ^t η ≤ ∫₀ᵗ η ≤ ∫₀ᵗ e^{σ(t-v)}η(v) dv = maj(t)` (`η ≥ 0`, `e^{σ(t-v)} ≥ 1`);
* (M3) `maj(v) ≤ e^{σv} F(t)` on `[0,t]`, so `∫₀ᵗ maj ≤ F(t)(e^{σt}-1)/σ ≤ maj(t)/σ` (if `maj` is
  not interval integrable the integral is `0 ≤ maj(t)/σ`);
* monotonicity from (M1), `e^{σ(t-τ)} ≥ 1` and `maj(τ) ≥ 0`.

This is the manuscript's argument, with (M3) obtained from the factorization instead of
integrating (M1) in `τ` (the same bound).
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace OneRing

open RingData

/-- The kernel factorization `maj(t) = e^{σt} ∫₀ᵗ e^{-στ}η(τ) dτ`. -/
theorem maj_eq_exp_mul (σ : ℝ) (η : ℝ → ℝ) (t : ℝ) :
    maj σ η t = Real.exp (σ * t) * ∫ τ in (0 : ℝ)..t, Real.exp (-(σ * τ)) * η τ := by
  rw [maj, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun τ _ => ?_
  rw [← mul_assoc, ← Real.exp_add, show σ * t + -(σ * τ) = σ * (t - τ) by ring]

/-- `∫₀^t e^{σv} dv = σ⁻¹ (e^{σt} - 1)` for `σ ≠ 0`. -/
theorem integral_exp_mul_self {σ : ℝ} (hσ : σ ≠ 0) (t : ℝ) :
    (∫ v in (0 : ℝ)..t, Real.exp (σ * v)) = σ⁻¹ * (Real.exp (σ * t) - 1) := by
  rw [intervalIntegral.integral_comp_mul_left (fun v => Real.exp v) hσ, integral_exp]
  simp

/-- **`lem:majorant` for a general rate `σ > 0`** (`05_single_ring.tex:390-398`): if `η` is
integrable and nonnegative on `[0,T]`, then for `0 ≤ τ ≤ t ≤ T`:
(M1) `e^{σ(t-τ)} maj(τ) ≤ maj(t)`; (M2) `∫_τ^t η ≤ maj(t)`; (M3) `∫₀ᵗ maj ≤ maj(t)/σ`;
and `maj` is nondecreasing on `[0,T]`. -/
theorem majorant_of_pos {σ T : ℝ} (hσ : 0 < σ) {η : ℝ → ℝ} (hη : IntegrableOn η (Icc 0 T))
    (hη0 : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ η t) :
    (∀ τ t : ℝ, 0 ≤ τ → τ ≤ t → t ≤ T →
      Real.exp (σ * (t - τ)) * maj σ η τ ≤ maj σ η t ∧
        (∫ v in τ..t, η v) ≤ maj σ η t ∧
        (∫ v in (0 : ℝ)..t, maj σ η v) ≤ maj σ η t / σ) ∧
      MonotoneOn (maj σ η) (Icc 0 T) := by
  -- the factorized integrand `g(τ) = e^{-στ} η(τ)` and its primitive `F`
  set g : ℝ → ℝ := fun τ => Real.exp (-(σ * τ)) * η τ with hg_def
  set F : ℝ → ℝ := fun t => ∫ τ in (0 : ℝ)..t, g τ with hF_def
  have hmaj : ∀ t, maj σ η t = Real.exp (σ * t) * F t := fun t => maj_eq_exp_mul σ η t
  have hgT : IntegrableOn g (Icc 0 T) :=
    hη.continuousOn_mul (by fun_prop) isCompact_Icc
  have hg0 : ∀ v ∈ Icc (0 : ℝ) T, 0 ≤ g v := fun v hv =>
    mul_nonneg (Real.exp_pos _).le (hη0 v hv)
  -- interval integrability on subintervals of `[0,T]`
  have hsub : ∀ a b : ℝ, 0 ≤ a → a ≤ T → 0 ≤ b → b ≤ T → uIcc a b ⊆ Icc 0 T :=
    fun a b ha haT hb hbT => uIcc_subset_Icc ⟨ha, haT⟩ ⟨hb, hbT⟩
  have hgi : ∀ a b : ℝ, 0 ≤ a → a ≤ T → 0 ≤ b → b ≤ T → IntervalIntegrable g volume a b :=
    fun a b ha haT hb hbT => (hgT.mono_set (hsub a b ha haT hb hbT)).intervalIntegrable
  have hηi : ∀ a b : ℝ, 0 ≤ a → a ≤ T → 0 ≤ b → b ≤ T → IntervalIntegrable η volume a b :=
    fun a b ha haT hb hbT => (hη.mono_set (hsub a b ha haT hb hbT)).intervalIntegrable
  -- `F` is nonnegative and nondecreasing on `[0,T]`
  have hF0 : ∀ t, 0 ≤ t → t ≤ T → 0 ≤ F t := fun t ht0 htT =>
    intervalIntegral.integral_nonneg ht0 fun u hu => hg0 u ⟨hu.1, hu.2.trans htT⟩
  have hFmono : ∀ τ t, 0 ≤ τ → τ ≤ t → t ≤ T → F τ ≤ F t := by
    intro τ t hτ hτt htT
    refine intervalIntegral.integral_mono_interval le_rfl hτ hτt ?_
      (hgi 0 t le_rfl (hτ.trans (hτt.trans htT)) (hτ.trans hτt) htT)
    exact ae_restrict_of_forall_mem measurableSet_Ioc fun v hv =>
      hg0 v ⟨hv.1.le, hv.2.trans htT⟩
  have hmaj0 : ∀ t, 0 ≤ t → t ≤ T → 0 ≤ maj σ η t := fun t ht0 htT => by
    rw [hmaj]; exact mul_nonneg (Real.exp_pos _).le (hF0 t ht0 htT)
  -- (M1)
  have hM1 : ∀ τ t, 0 ≤ τ → τ ≤ t → t ≤ T →
      Real.exp (σ * (t - τ)) * maj σ η τ ≤ maj σ η t := by
    intro τ t hτ hτt htT
    rw [hmaj, hmaj, ← mul_assoc, ← Real.exp_add, show σ * (t - τ) + σ * τ = σ * t by ring]
    exact mul_le_mul_of_nonneg_left (hFmono τ t hτ hτt htT) (Real.exp_pos _).le
  refine ⟨fun τ t hτ hτt htT => ⟨hM1 τ t hτ hτt htT, ?_, ?_⟩, ?_⟩
  · -- (M2)
    have ht0 : 0 ≤ t := hτ.trans hτt
    have hTnn : 0 ≤ T := ht0.trans htT
    have h1 : (∫ v in τ..t, η v) ≤ ∫ v in (0 : ℝ)..t, η v := by
      refine intervalIntegral.integral_mono_interval hτ hτt le_rfl ?_
        (hηi 0 t le_rfl hTnn ht0 htT)
      exact ae_restrict_of_forall_mem measurableSet_Ioc fun v hv =>
        hη0 v ⟨hv.1.le, hv.2.trans htT⟩
    have hki : IntervalIntegrable (fun v => Real.exp (σ * (t - v)) * η v) volume 0 t := by
      have : IntegrableOn (fun v => Real.exp (σ * (t - v)) * η v) (uIcc 0 t) :=
        (hη.mono_set (hsub 0 t le_rfl hTnn ht0 htT)).continuousOn_mul (by fun_prop)
          isCompact_uIcc
      exact this.intervalIntegrable
    have h2 : (∫ v in (0 : ℝ)..t, η v) ≤ maj σ η t := by
      refine intervalIntegral.integral_mono_on ht0 (hηi 0 t le_rfl hTnn ht0 htT) hki ?_
      intro v hv
      exact le_mul_of_one_le_left (hη0 v ⟨hv.1, hv.2.trans htT⟩)
        (Real.one_le_exp (mul_nonneg hσ.le (sub_nonneg.2 hv.2)))
    exact h1.trans h2
  · -- (M3)
    have ht0 : 0 ≤ t := hτ.trans hτt
    by_cases hint : IntervalIntegrable (maj σ η) volume 0 t
    · have hbd : ∀ v ∈ Icc (0 : ℝ) t, maj σ η v ≤ Real.exp (σ * v) * F t := by
        intro v hv
        rw [hmaj]
        exact mul_le_mul_of_nonneg_left (hFmono v t hv.1 hv.2 htT) (Real.exp_pos _).le
      have hci : IntervalIntegrable (fun v => Real.exp (σ * v) * F t) volume 0 t :=
        (Continuous.intervalIntegrable (by fun_prop) _ _)
      calc (∫ v in (0 : ℝ)..t, maj σ η v)
          ≤ ∫ v in (0 : ℝ)..t, Real.exp (σ * v) * F t :=
            intervalIntegral.integral_mono_on ht0 hint hci hbd
        _ = σ⁻¹ * (Real.exp (σ * t) - 1) * F t := by
            rw [intervalIntegral.integral_mul_const, integral_exp_mul_self hσ.ne']
        _ ≤ σ⁻¹ * Real.exp (σ * t) * F t := by
            refine mul_le_mul_of_nonneg_right ?_ (hF0 t ht0 htT)
            exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 hσ.le)
        _ = maj σ η t / σ := by rw [hmaj]; ring
    · rw [intervalIntegral.integral_undef hint]
      exact div_nonneg (hmaj0 t ht0 htT) hσ.le
  · -- monotonicity
    intro a ha b hb hab
    calc maj σ η a ≤ Real.exp (σ * (b - a)) * maj σ η a :=
          le_mul_of_one_le_left (hmaj0 a ha.1 ha.2)
            (Real.one_le_exp (mul_nonneg hσ.le (sub_nonneg.2 hab)))
      _ ≤ maj σ η b := hM1 a b ha.1 hab hb.2

/-- **`lem:majorant`** (`05_single_ring.tex:390-398`). Let `G ∈ [0,G₁]` and let `η` be
integrable and nonnegative on `[0,T]`, with Duhamel majorant `maj = maj (σ(G)) η`
(`def:majorant`). Then for `0 ≤ τ ≤ t ≤ T`: (M1) `e^{σ(G)(t-τ)} maj(τ) ≤ maj(t)`;
(M2) `∫_τ^t η ≤ maj(t)`; (M3) `∫₀ᵗ maj ≤ maj(t)/σ(G)`; in particular `maj` is nondecreasing. -/
theorem majorant (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {G T : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) {η : ℝ → ℝ} (hη : IntegrableOn η (Icc 0 T))
    (hη0 : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ η t) :
    (∀ τ t : ℝ, 0 ≤ τ → τ ≤ t → t ≤ T →
      Real.exp (Eig.sigma χ G * (t - τ)) * maj (Eig.sigma χ G) η τ ≤ maj (Eig.sigma χ G) η t ∧
        (∫ v in τ..t, η v) ≤ maj (Eig.sigma χ G) η t ∧
        (∫ v in (0 : ℝ)..t, maj (Eig.sigma χ G) η v) ≤ maj (Eig.sigma χ G) η t / Eig.sigma χ G) ∧
      MonotoneOn (maj (Eig.sigma χ G) η) (Icc 0 T) := by
  have hσ : 0 < Eig.sigma χ G := by
    have h := (Eig.lam_SU χ hχ hN hG 0).1
    unfold Eig.sigma
    linarith
  exact majorant_of_pos hσ hη hη0

end OneRing

end NonUniqueEuler
