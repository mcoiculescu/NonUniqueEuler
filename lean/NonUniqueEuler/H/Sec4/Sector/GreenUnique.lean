import NonUniqueEuler.Defs.Sec4.Extra1Sector
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Topology.Algebra.Order.Field

/-!
# Helper for `lem:sector`(1): uniqueness for the radial Poisson equation

Helper file of `P/Sec4/Sector.lean` (fully proved). Manuscript `04_ring.tex:236-239`.

If `ψ₁, ψ₂` solve `ψ'' + ψ'/r - ℓ²ψ/r² = g` on `(0, ∞)` (`IsRadialPoissonSol`, `ℓ ≠ 0`) and
`φ = ψ₁ - ψ₂` is `O(rⁿ)` at `0` and `O(r⁻ⁿ)` at `∞` (`n = |ℓ|`), then `φ = 0` on `(0, ∞)`.
The manuscript says "`ψ₁ - ψ₂ = Arⁿ + Br⁻ⁿ`, and the conditions force `A = B = 0`". Here the
general solution is obtained from the two first integrals of the homogeneous equation:
`(rφ' + nφ)/rⁿ` and `(rφ' - nφ)rⁿ` have zero derivative.
-/

noncomputable section

open MeasureTheory Set Filter Topology Asymptotics

namespace NonUniqueEuler.SectorH

open SectorSetting

/-- The difference of two solutions solves the homogeneous equation. -/
theorem homogeneous_of_sub {ℓ : ℤ} {g ψ₁ ψ₂ ψ₁' ψ₂' : ℝ → ℂ}
    (hg : ∀ a' b' : ℝ, 0 < a' → 0 < b' → IntervalIntegrable g volume a' b')
    (hd₁ : ∀ r : ℝ, 0 < r → HasDerivAt ψ₁ (ψ₁' r) r) (hc₁ : ContinuousOn ψ₁' (Ioi 0))
    (hi₁ : ∀ a b : ℝ, 0 < a → 0 < b →
      ψ₁' b - ψ₁' a = ∫ r in a..b, (g r - ψ₁' r / (r : ℂ) + (ℓ : ℂ) ^ 2 * ψ₁ r / (r : ℂ) ^ 2))
    (hd₂ : ∀ r : ℝ, 0 < r → HasDerivAt ψ₂ (ψ₂' r) r) (hc₂ : ContinuousOn ψ₂' (Ioi 0))
    (hi₂ : ∀ a b : ℝ, 0 < a → 0 < b →
      ψ₂' b - ψ₂' a = ∫ r in a..b, (g r - ψ₂' r / (r : ℂ) + (ℓ : ℂ) ^ 2 * ψ₂ r / (r : ℂ) ^ 2))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (ψ₁' b - ψ₂' b) - (ψ₁' a - ψ₂' a) =
      ∫ r in a..b, (-((ψ₁' r - ψ₂' r) / (r : ℂ)) +
        (ℓ : ℂ) ^ 2 * (ψ₁ r - ψ₂ r) / (r : ℂ) ^ 2) := by
  have hsub : uIcc a b ⊆ Ioi 0 := fun r hr => lt_of_lt_of_le (lt_min ha hb) hr.1
  have hr0 : ∀ r ∈ uIcc a b, (r : ℂ) ≠ 0 := fun r hr => by exact_mod_cast ne_of_gt (hsub hr)
  have hcont : ∀ {ψ ψ' : ℝ → ℂ}, (∀ r : ℝ, 0 < r → HasDerivAt ψ (ψ' r) r) →
      ContinuousOn ψ' (Ioi 0) → IntervalIntegrable (fun r : ℝ => g r - ψ' r / (r : ℂ) +
        (ℓ : ℂ) ^ 2 * ψ r / (r : ℂ) ^ 2) volume a b := by
    intro ψ ψ' hd hc
    have hψ : ContinuousOn ψ (uIcc a b) := fun r hr =>
      (hd r (hsub hr)).continuousAt.continuousWithinAt
    have h2 : ContinuousOn (fun r : ℝ => -(ψ' r / (r : ℂ)) + (ℓ : ℂ) ^ 2 * ψ r / (r : ℂ) ^ 2)
        (uIcc a b) :=
      ((hc.mono hsub).div Complex.continuous_ofReal.continuousOn hr0).neg.add
        ((continuousOn_const.mul hψ).div (Complex.continuous_ofReal.continuousOn.pow 2)
          fun r hr => pow_ne_zero 2 (hr0 r hr))
    exact ((hg a b ha hb).add h2.intervalIntegrable).congr fun r _ => by ring
  rw [show (ψ₁' b - ψ₂' b) - (ψ₁' a - ψ₂' a) = (ψ₁' b - ψ₁' a) - (ψ₂' b - ψ₂' a) by ring,
    hi₁ a b ha hb, hi₂ a b ha hb, ← intervalIntegral.integral_sub (hcont hd₁ hc₁)
      (hcont hd₂ hc₂)]
  congr 1
  funext r
  ring

/-- Uniqueness of the solution of the radial Poisson equation with the growth conditions
(`lem:sector`(1), `04_ring.tex:236-239`). -/
theorem eqOn_of_isRadialPoissonSol {ℓ : ℤ} (hℓ : ℓ ≠ 0) {g ψ₁ ψ₂ : ℝ → ℂ}
    (hg : ∀ a' b' : ℝ, 0 < a' → 0 < b' → IntervalIntegrable g volume a' b')
    (h₁ : IsRadialPoissonSol ℓ g ψ₁) (h₂ : IsRadialPoissonSol ℓ g ψ₂)
    (h0 : (fun r => ψ₁ r - ψ₂ r) =O[𝓝[>] 0] fun r : ℝ => r ^ ℓ.natAbs)
    (hinf : (fun r => ψ₁ r - ψ₂ r) =O[atTop] fun r : ℝ => r ^ (-(ℓ.natAbs : ℤ))) :
    EqOn ψ₁ ψ₂ (Ioi 0) := by
  obtain ⟨ψ₁', hd₁, hc₁, hi₁⟩ := h₁
  obtain ⟨ψ₂', hd₂, hc₂, hi₂⟩ := h₂
  obtain ⟨m, hm⟩ : ∃ m, ℓ.natAbs = m + 1 :=
    ⟨ℓ.natAbs - 1, by have := Int.natAbs_ne_zero.2 hℓ; omega⟩
  rw [hm] at h0 hinf
  set n := m + 1 with hn
  set N : ℂ := (n : ℂ) with hN
  have hn1 : 1 ≤ n := by omega
  have hN0 : N ≠ 0 := by rw [hN]; exact_mod_cast (show n ≠ 0 by omega)
  have hℓsq : (ℓ : ℂ) ^ 2 = N ^ 2 := by
    have h2 := congrArg (fun z : ℤ => (z : ℂ)) (Int.natAbs_sq ℓ)
    simp only [Int.cast_pow, Int.cast_natCast, hm] at h2
    rw [hN]
    exact h2.symm
  set φ : ℝ → ℂ := fun r => ψ₁ r - ψ₂ r with hφ
  set φ' : ℝ → ℂ := fun r => ψ₁' r - ψ₂' r with hφ'
  set hh : ℝ → ℂ := fun r => -(φ' r / (r : ℂ)) + N ^ 2 * φ r / (r : ℂ) ^ 2 with hhh
  have hφd : ∀ r : ℝ, 0 < r → HasDerivAt φ (φ' r) r := fun r hr => (hd₁ r hr).sub (hd₂ r hr)
  have hφc : ContinuousOn φ' (Ioi 0) := hc₁.sub hc₂
  have hφi : ∀ a b : ℝ, 0 < a → 0 < b → φ' b - φ' a = ∫ r in a..b, hh r := by
    intro a b ha hb
    have := homogeneous_of_sub hg hd₁ hc₁ hi₁ hd₂ hc₂ hi₂ ha hb
    simp only [hφ', hhh, hφ, ← hℓsq]
    exact this
  have hhc : ContinuousOn hh (Ioi 0) := by
    have hφcont : ContinuousOn φ (Ioi 0) := fun r hr =>
      (hφd r hr).continuousAt.continuousWithinAt
    have hr0 : ∀ r ∈ Ioi (0 : ℝ), (r : ℂ) ≠ 0 := fun r hr => by exact_mod_cast ne_of_gt hr
    exact (hφc.div Complex.continuous_ofReal.continuousOn hr0).neg.add
      ((continuousOn_const.mul hφcont).div (Complex.continuous_ofReal.continuousOn.pow 2)
        fun r hr => pow_ne_zero 2 (hr0 r hr))
  -- `φ'` is differentiable with derivative `hh`
  have hφ'd : ∀ r : ℝ, 0 < r → HasDerivAt φ' (hh r) r := by
    intro r hr
    have hF : HasDerivAt (fun s => φ' r + ∫ u in r..s, hh u) (hh r) r :=
      (intervalIntegral.integral_hasDerivAt_right IntervalIntegrable.refl
        (hhc.stronglyMeasurableAtFilter isOpen_Ioi r hr)
        (hhc.continuousAt (Ioi_mem_nhds hr))).const_add _
    refine hF.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hr] with s hs
    rw [← hφi r s hr hs]
    ring
  have hid : ∀ r : ℝ, HasDerivAt (fun r : ℝ => (r : ℂ)) 1 r := fun r =>
    (hasDerivAt_id r).ofReal_comp
  -- first integral `(rφ' + nφ)/rⁿ`
  have hu : ∃ A : ℂ, ∀ r ∈ Ioi (0 : ℝ),
      ((r : ℂ) * φ' r + N * φ r) / (r : ℂ) ^ n = A := by
    have hder : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt
        (fun r : ℝ => ((r : ℂ) * φ' r + N * φ r) / (r : ℂ) ^ n) 0 r := by
      intro r hr
      have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (show (0 : ℝ) < r from hr)
      have h1 := (((hid r).mul (hφ'd r hr)).add ((hφd r hr).const_mul N)).div
        ((hid r).pow n) (pow_ne_zero n hr0)
      refine h1.congr_deriv ?_
      simp only [hhh, hN, hn, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
        Nat.add_sub_cancel]
      field_simp
      push_cast
      ring
    obtain ⟨A, hA⟩ := isOpen_Ioi.exists_is_const_of_deriv_eq_zero isPreconnected_Ioi
      (fun r hr => (hder r hr).differentiableAt.differentiableWithinAt)
      (fun r hr => (hder r hr).deriv)
    exact ⟨A, hA⟩
  -- second integral `(rφ' - nφ)rⁿ`
  have hv : ∃ B : ℂ, ∀ r ∈ Ioi (0 : ℝ),
      ((r : ℂ) * φ' r - N * φ r) * (r : ℂ) ^ n = B := by
    have hder : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt
        (fun r : ℝ => ((r : ℂ) * φ' r - N * φ r) * (r : ℂ) ^ n) 0 r := by
      intro r hr
      have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (show (0 : ℝ) < r from hr)
      have h1 := (((hid r).mul (hφ'd r hr)).sub ((hφd r hr).const_mul N)).mul ((hid r).pow n)
      refine h1.congr_deriv ?_
      simp only [hhh, hN, hn, Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
        Nat.add_sub_cancel]
      field_simp
      push_cast
      ring
    obtain ⟨B, hB⟩ := isOpen_Ioi.exists_is_const_of_deriv_eq_zero isPreconnected_Ioi
      (fun r hr => (hder r hr).differentiableAt.differentiableWithinAt)
      (fun r hr => (hder r hr).deriv)
    exact ⟨B, hB⟩
  obtain ⟨A, hA⟩ := hu
  obtain ⟨B, hB⟩ := hv
  -- `2Nφ rⁿ = A r^{2n} - B`
  have hrel : ∀ r : ℝ, 0 < r → A * (r : ℂ) ^ (2 * n) - 2 * N * (φ r * (r : ℂ) ^ n) = B := by
    intro r hr
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr
    have e1 := hA r hr
    have e2 := hB r hr
    rw [div_eq_iff (pow_ne_zero n hr0)] at e1
    rw [two_mul, pow_add]
    linear_combination (-(r : ℂ) ^ n) * e1 + e2
  -- `B = 0`, from the behaviour at `0`
  have hB0 : B = 0 := by
    have ht1 : Tendsto (fun r : ℝ => φ r * (r : ℂ) ^ n) (𝓝[>] 0) (𝓝 0) := by
      have hO : (fun r : ℝ => φ r * (r : ℂ) ^ n) =O[𝓝[>] 0]
          fun r : ℝ => r ^ n * r ^ n := h0.mul (isBigO_of_le _ fun r => by
            rw [norm_pow, norm_pow, Complex.norm_real])
      refine hO.trans_tendsto ?_
      have : Tendsto (fun r : ℝ => r ^ n * r ^ n) (𝓝 0) (𝓝 (0 ^ n * 0 ^ n)) :=
        ((continuous_pow n).mul (continuous_pow n)).tendsto 0
      rw [zero_pow (by omega), zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    have ht2 : Tendsto (fun r : ℝ => A * (r : ℂ) ^ (2 * n)) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun r : ℝ => A * (r : ℂ) ^ (2 * n)) (𝓝 0) (𝓝 (A * ((0 : ℝ) : ℂ) ^ (2 * n))) :=
        ((continuous_const.mul (Complex.continuous_ofReal.pow _))).tendsto 0
      rw [Complex.ofReal_zero, zero_pow (by omega), mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have ht := ht2.sub (ht1.const_mul (2 * N))
    rw [mul_zero, sub_zero] at ht
    have hev : (fun r : ℝ => A * (r : ℂ) ^ (2 * n) - 2 * N * (φ r * (r : ℂ) ^ n)) =ᶠ[𝓝[>] 0]
        fun _ => B := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact hrel r hr
    exact tendsto_nhds_unique (tendsto_const_nhds.congr' hev.symm) ht
  -- `A = 0`, from the behaviour at `∞`
  have hA0 : A = 0 := by
    have ht : Tendsto (fun r : ℝ => φ r * ((r : ℂ) ^ n)⁻¹) atTop (𝓝 0) := by
      have hO : (fun r : ℝ => φ r * ((r : ℂ) ^ n)⁻¹) =O[atTop]
          fun r : ℝ => r ^ (-(n : ℤ)) * r ^ (-(n : ℤ)) := hinf.mul (isBigO_of_le _ fun r => by
            rw [norm_inv, norm_pow, Complex.norm_real, zpow_neg, zpow_natCast, norm_inv, norm_pow])
      refine hO.trans_tendsto ?_
      have : Tendsto (fun r : ℝ => r ^ (-(2 * n : ℤ))) atTop (𝓝 0) :=
        tendsto_zpow_atTop_zero (by omega)
      refine this.congr' ?_
      filter_upwards [Ioi_mem_atTop 0] with r hr
      rw [← zpow_add₀ (ne_of_gt hr)]
      ring_nf
    have hev : (fun r : ℝ => φ r * ((r : ℂ) ^ n)⁻¹) =ᶠ[atTop] fun _ => A / (2 * N) := by
      filter_upwards [Ioi_mem_atTop 0] with r hr
      have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr
      have e := hrel r hr
      rw [hB0, sub_eq_zero, two_mul, pow_add] at e
      have e' : A * (r : ℂ) ^ n = 2 * N * φ r := by
        refine mul_right_cancel₀ (pow_ne_zero n hr0) ?_
        linear_combination e
      field_simp
      linear_combination (-1 : ℂ) * e'
    have := tendsto_nhds_unique (tendsto_const_nhds.congr' hev.symm) ht
    rw [div_eq_zero_iff] at this
    rcases this with h | h
    · exact h
    · exact absurd h (mul_ne_zero two_ne_zero hN0)
  intro r hr
  have e := hrel r hr
  rw [hA0, hB0, zero_mul, zero_sub, neg_eq_zero] at e
  have hr0 : (r : ℂ) ^ n ≠ 0 := pow_ne_zero n (by exact_mod_cast ne_of_gt (show (0 : ℝ) < r from hr))
  have : φ r = 0 := by
    rcases mul_eq_zero.1 e with h | h
    · exact absurd h (mul_ne_zero two_ne_zero hN0)
    · rcases mul_eq_zero.1 h with h' | h'
      · exact h'
      · exact absurd h' hr0
  exact sub_eq_zero.1 this

end NonUniqueEuler.SectorH
