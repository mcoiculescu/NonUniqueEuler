import NonUniqueEuler.Defs.Sec4.Setting
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Helper for `lem:adjoint`: the Green operator `𝒢_ℓ` (symmetry, values off the support)

Helper of `P/Sec4/Adjoint.lean`.
* `integral_green_mul_symm`: the kernel of `𝒢_ℓ` is real and symmetric for `ρ dρ`, so
  `∫ (𝒢_ℓ g) h r dr = ∫ g (𝒢_ℓ h) ρ dρ` (Fubini; `04_ring.tex:605-606`);
* `green_eq_exterior`, `green_eq_interior`: for `h` vanishing off `[a,b]`,
  `𝒢_ℓ h(r) = -(2ℓ)⁻¹ r^{-ℓ} ∫ρ^{ℓ+1}h` for `r ≥ b` and `-(2ℓ)⁻¹ r^ℓ ∫ρ^{1-ℓ}h` for `r ≤ a`
  (`04_ring.tex:621-624`).
-/

noncomputable section

open MeasureTheory Set Filter

namespace NonUniqueEuler.AdjointAux

open SectorSetting

/-- Symmetry of the Green kernel (Fubini): `∫ (𝒢_ℓ g) h r dr = ∫ g (𝒢_ℓ h) ρ dρ`. -/
theorem integral_green_mul_symm (ℓ : ℤ) {g h : ℝ → ℂ}
    (hg : IntegrableOn (fun ρ => g ρ * (ρ : ℂ)) (Ioi 0))
    (hh : IntegrableOn (fun r => h r * (r : ℂ)) (Ioi 0)) :
    ∫ r in Ioi (0 : ℝ), green ℓ g r * h r * (r : ℂ) =
      ∫ ρ in Ioi (0 : ℝ), g ρ * green ℓ h ρ * (ρ : ℂ) := by
  set μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμ
  let K : ℝ → ℝ → ℂ := fun r ρ => (((min r ρ / max r ρ) ^ ℓ.natAbs : ℝ) : ℂ)
  let c : ℂ := (((2 * |(ℓ : ℝ)|)⁻¹ : ℝ) : ℂ)
  let F : ℝ → ℝ → ℂ := fun r ρ => K r ρ * ((h r * r) * (g ρ * ρ))
  have hKs : ∀ r ρ, K ρ r = K r ρ := fun r ρ => by simp only [K, min_comm, max_comm]
  have hKm : Measurable (Function.uncurry K) := by
    apply Complex.measurable_ofReal.comp
    exact ((measurable_fst.min measurable_snd).div (measurable_fst.max measurable_snd)).pow_const _
  have hKb : ∀ᵐ p ∂(μ.prod μ), ‖Function.uncurry K p‖ ≤ 1 := by
    rw [hμ, Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
    obtain ⟨h1, h2⟩ := hp
    simp only [mem_Ioi] at h1 h2
    simp only [Function.uncurry, K, Complex.norm_real, Real.norm_eq_abs]
    have hmax : 0 < max p.1 p.2 := lt_max_of_lt_left h1
    have hmin : 0 < min p.1 p.2 := lt_min h1 h2
    rw [abs_of_nonneg (by positivity)]
    apply pow_le_one₀ (by positivity)
    rw [div_le_one hmax]
    exact min_le_max
  have hint : Integrable (Function.uncurry F) (μ.prod μ) := by
    have hP := hh.mul_prod hg
    exact hP.bdd_mul hKm.aestronglyMeasurable hKb
  have hL : ∀ r, green ℓ g r * h r * (r : ℂ) = -c * ∫ ρ in Ioi 0, F r ρ := by
    intro r
    have : ∫ ρ in Ioi 0, F r ρ = (∫ ρ in Ioi (0 : ℝ), K r ρ * g ρ * (ρ : ℂ)) * (h r * r) := by
      rw [← integral_mul_const]
      congr 1
      funext ρ
      simp only [F]
      ring
    rw [this, green]
    ring
  have hR : ∀ ρ, g ρ * green ℓ h ρ * (ρ : ℂ) = -c * ∫ r in Ioi 0, F r ρ := by
    intro ρ
    have : ∫ r in Ioi 0, F r ρ = (∫ r in Ioi (0 : ℝ), K ρ r * h r * (r : ℂ)) * (g ρ * ρ) := by
      rw [← integral_mul_const]
      congr 1
      funext r
      simp only [F, hKs r ρ]
      ring
    rw [this, green]
    ring
  simp_rw [hL, hR]
  rw [integral_const_mul, integral_const_mul, integral_integral_swap hint]

/-- `𝒢_ℓ h(r) = -(2ℓ)⁻¹ r^{-ℓ} ∫_0^∞ ρ^{ℓ+1} h(ρ) dρ` for `r ≥ b` when `h` vanishes off `[a,b]`. -/
theorem green_eq_exterior (ℓ : ℕ) {h : ℝ → ℂ} {a b : ℝ}
    (hh : ∀ ρ : ℝ, 0 < ρ → ρ ∉ Icc a b → h ρ = 0) {r : ℝ} (hr0 : 0 < r) (hr : b ≤ r) :
    green ℓ h r = -((2 * (ℓ : ℂ))⁻¹) * (r : ℂ) ^ (-(ℓ : ℤ)) *
      ∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ (ℓ + 1) * h ρ := by
  have hpt : ∀ ρ ∈ Ioi (0 : ℝ), (((min r ρ / max r ρ) ^ (ℓ : ℤ).natAbs : ℝ) : ℂ) * h ρ * (ρ : ℂ) =
      (r : ℂ) ^ (-(ℓ : ℤ)) * ((ρ : ℂ) ^ (ℓ + 1) * h ρ) := by
    intro ρ hρ
    rw [Int.natAbs_natCast]
    rcases le_or_gt ρ r with hρr | hρr
    · rw [min_eq_right hρr, max_eq_left hρr, zpow_neg, zpow_natCast]
      have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
      push_cast
      rw [div_pow, pow_succ]
      field_simp
    · have : h ρ = 0 := hh ρ hρ fun hm => absurd (hm.2.trans hr) (not_le.2 hρr)
      rw [this]
      ring
  rw [green, setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  have habs : |((ℓ : ℤ) : ℝ)| = (ℓ : ℝ) := by
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg ℓ)]
  rw [habs]
  push_cast
  ring

/-- `𝒢_ℓ h(r) = -(2ℓ)⁻¹ r^ℓ ∫_0^∞ ρ^{1-ℓ} h(ρ) dρ` for `0 < r ≤ a` when `h` vanishes off
`[a,b]`. -/
theorem green_eq_interior (ℓ : ℕ) {h : ℝ → ℂ} {a b : ℝ}
    (hh : ∀ ρ : ℝ, 0 < ρ → ρ ∉ Icc a b → h ρ = 0) {r : ℝ} (hr0 : 0 < r) (hr : r ≤ a) :
    green ℓ h r = -((2 * (ℓ : ℂ))⁻¹) * (r : ℂ) ^ ℓ *
      ∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ ((1 : ℤ) - ℓ) * h ρ := by
  have hpt : ∀ ρ ∈ Ioi (0 : ℝ), (((min r ρ / max r ρ) ^ (ℓ : ℤ).natAbs : ℝ) : ℂ) * h ρ * (ρ : ℂ) =
      (r : ℂ) ^ ℓ * ((ρ : ℂ) ^ ((1 : ℤ) - ℓ) * h ρ) := by
    intro ρ hρ
    rw [Int.natAbs_natCast]
    have hρ0 : (ρ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hρ)
    rcases le_or_gt r ρ with hρr | hρr
    · rw [min_eq_left hρr, max_eq_right hρr, zpow_sub₀ hρ0, zpow_one, zpow_natCast]
      push_cast
      rw [div_pow]
      field_simp
    · have : h ρ = 0 := hh ρ hρ fun hm => absurd (hr.trans hm.1) (not_le.2 hρr)
      rw [this]
      ring
  rw [green, setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  have habs : |((ℓ : ℤ) : ℝ)| = (ℓ : ℝ) := by
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg ℓ)]
  rw [habs]
  push_cast
  ring

end NonUniqueEuler.AdjointAux
