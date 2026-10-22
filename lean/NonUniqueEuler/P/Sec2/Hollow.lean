import NonUniqueEuler.Defs.Sec2.BiotSavart
import NonUniqueEuler.Defs.Infra.Polar
import NonUniqueEuler.I.Infra.Multipole.Laurent
import NonUniqueEuler.I.Infra.Multipole.Moments
import NonUniqueEuler.I.Infra.Multipole.CauchySmooth
import NonUniqueEuler.I.Infra.Polar.AngularAverage
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Proof of `lem:hollow`, the velocity inside a hollow region

Proof of the interface `NonUniqueEuler/I/Sec2/Hollow.lean` (`02_prelim.tex:408-444`).

Structure (following the manuscript proof, `02_prelim.tex:420-444`).
* `integrable_biotSavart_of_hollow`: for `|x| < R`, `ν = 0` a.e. on `ball x (R - |x|)`, so the
  Biot–Savart integral converges absolutely (`Multipole.integrable_biotSavart_of_vanishing`).
* `velocity_angAvg_eq_zero_of_hollow`: the interior expansion of the Cauchy transform of `ν̄`
  (`Multipole.hasSum_cauchyTransform_interior`) has vanishing coefficients
  (`Multipole.moment_angAvg_eq_zero`), so `u₁ - iu₂ = (2πi)⁻¹ C[ν̄] = 0`.
* `norm_velocity_le_of_hollow`: one deviation in the bookkeeping. Instead of writing
  `c_l(ν) = c_l(ν - ν̄)` for the moments of `ν`, we use `K ∗ ν = K ∗ (ν - ν̄)` on `B_R` (from
  `K ∗ ν̄ = 0`) and run the expansion for `h = ν - ν̄` directly; `h` is again real, integrable,
  `m₀`-fold symmetric (`ν̄` is radial) and vanishes a.e. on `B_R`. The generic estimate is
  `norm_velocity_le_aux`: only the coefficients `c_{m₀(j+1)}(h)` survive
  (`Multipole.moment_eq_zero_of_isMFoldSymmetric`), `|c_l(h)| ≤ ‖h‖₁ R^{-l}`
  (`Multipole.norm_moment_neg_le`), and the surviving series is the geometric series
  `‖h‖₁ |x|^{m₀-1} R^{-m₀} Σ_j q^j`, `q = (|x|/R)^{m₀} ≤ 1/4`, so `(1 - q)⁻¹ ≤ 4/3`. Finally
  `‖ν - ν̄‖₁ ≤ ‖ν‖₁ + ‖ν̄‖₁ ≤ 2‖ν‖₁` (`Polar.eLpNorm_angAvg_le`).
-/

noncomputable section

open MeasureTheory Set Metric ComplexConjugate
open scoped ENNReal

namespace NonUniqueEuler.BS

/-! ### Helpers -/

namespace HollowAux

/-- If `g = 0` a.e. on `B_R`, then `g = 0` a.e. on `ball x (R - |x|)`. -/
theorem ae_ball_sub_of_hollow {R : ℝ} {g : ℂ → ℝ} (hsupp : ∀ᵐ y, ‖y‖ < R → g y = 0) (x : ℂ) :
    ∀ᵐ y, y ∈ ball x (R - ‖x‖) → g y = 0 := by
  filter_upwards [hsupp] with y hy hyb
  apply hy
  rw [mem_ball, dist_eq_norm] at hyb
  have := norm_sub_norm_le y x
  linarith

/-- If `g = 0` a.e. on `B_R`, then `ḡ = 0` a.e. on `B_R`. -/
theorem ae_angAvg_eq_zero_of_hollow {R : ℝ} {g : ℂ → ℝ} (hsupp : ∀ᵐ y, ‖y‖ < R → g y = 0) :
    ∀ᵐ y, ‖y‖ < R → Polar.angAvg g y = 0 :=
  Polar.ae_angAvg_eq_zero_of_ae (A := Iio R) measurableSet_Iio hsupp

/-- `|K ∗ g(x)| = (2π)⁻¹ |C[g](x)|` for real `g` (the complex form of the Biot–Savart law). -/
theorem norm_velocity_eq_cauchyTransform (g : ℂ → ℝ) (x : ℂ) :
    ‖velocity g x‖ =
      (2 * Real.pi)⁻¹ * ‖Multipole.cauchyTransform (fun w => (g w : ℂ)) x‖ := by
  rw [Multipole.velocity_eq_conj_cauchyTransform, Complex.norm_conj, norm_mul, norm_inv]
  congr 2
  simp [abs_of_pos Real.pi_pos]

/-- Only the indices `l = m₀ j + (m₀ - 1)` (i.e. `m₀ ∣ l + 1`) are hit. -/
theorem mem_range_of_dvd_succ {m₀ l : ℕ} (hm : 0 < m₀) (hdvd : (m₀ : ℤ) ∣ -((l : ℤ) + 1)) :
    l ∈ Set.range (fun j : ℕ => m₀ * j + (m₀ - 1)) := by
  have h1 : (m₀ : ℤ) ∣ ((l + 1 : ℕ) : ℤ) := by
    have := hdvd.neg_right
    simpa using this
  obtain ⟨k, hk⟩ := Int.natCast_dvd_natCast.mp h1
  rcases k with _ | k
  · simp at hk
  · refine ⟨k, ?_⟩
    rw [Nat.mul_succ] at hk
    show m₀ * k + (m₀ - 1) = l
    omega

/-- The power identity `R^{-(φ(j)+1)} |x|^{φ(j)} = |x|^{m₀-1} R^{-m₀} ((|x|/R)^{m₀})^j` for
`φ(j) = m₀ j + (m₀ - 1)`. -/
theorem pow_identity_hollow {m₀ : ℕ} (hm₀ : 1 ≤ m₀) {R : ℝ} (hR : 0 < R) (t : ℝ) (j : ℕ) :
    (R ^ (m₀ * j + (m₀ - 1) + 1))⁻¹ * t ^ (m₀ * j + (m₀ - 1)) =
      t ^ (m₀ - 1) * (R ^ m₀)⁻¹ * ((t / R) ^ m₀) ^ j := by
  have e1 : m₀ * j + (m₀ - 1) + 1 = m₀ + m₀ * j := by omega
  rw [e1, ← pow_mul, div_pow, pow_add R, pow_add t]
  have hR' : R ≠ 0 := hR.ne'
  field_simp

/-- The generic estimate behind `lem:hollow`: for real, integrable, `m₀`-fold symmetric `g`
vanishing a.e. on `B_R` and `|x| ≤ R/2`, `|K ∗ g(x)| ≤ (2/(3π)) ‖g‖₁ |x|^{m₀-1} R^{-m₀}`. -/
theorem norm_velocity_le_aux {m₀ : ℕ} (hm₀ : 2 ≤ m₀) {R : ℝ} (hR : 0 < R)
    {g : ℂ → ℝ} (hg : Integrable g) (hsym : IsMFoldSymmetric m₀ g)
    (hsupp : ∀ᵐ y, ‖y‖ < R → g y = 0) {x : ℂ} (hx : ‖x‖ ≤ R / 2) :
    ‖velocity g x‖ ≤
      2 / (3 * Real.pi) * (eLpNorm g 1 volume).toReal * ‖x‖ ^ (m₀ - 1) * (R ^ m₀)⁻¹ := by
  set G : ℂ → ℂ := fun w => (g w : ℂ) with hG
  have hGi : Integrable G := hg.ofReal
  have hGs : ∀ᵐ w, ‖w‖ < R → G w = 0 := by
    filter_upwards [hsupp] with w hw h
    simp [hG, hw h]
  have hxR : ‖x‖ < R := by linarith [norm_nonneg x]
  have hs := Multipole.hasSum_cauchyTransform_interior hGi hGs hxR
  set φ : ℕ → ℕ := fun j => m₀ * j + (m₀ - 1) with hφ
  have hφinj : Function.Injective φ := by
    intro a b hab
    simp only [hφ] at hab
    have : m₀ * a = m₀ * b := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  have hoff : ∀ l, l ∉ Set.range φ →
      -(Multipole.moment G (-((l : ℤ) + 1)) * x ^ l) = 0 := by
    intro l hl
    rw [Multipole.moment_eq_zero_of_isMFoldSymmetric (by omega) hsym, zero_mul, neg_zero]
    exact fun hdvd => hl (mem_range_of_dvd_succ (by omega) hdvd)
  have hs' := (hφinj.hasSum_iff hoff).mpr hs
  set D : ℝ := ∫ w, ‖G w‖ with hD
  set A : ℝ := ‖x‖ ^ (m₀ - 1) * (R ^ m₀)⁻¹ with hA
  set q : ℝ := (‖x‖ / R) ^ m₀ with hq
  have hq0 : 0 ≤ q := by positivity
  have hq4 : q ≤ 1 / 4 := by
    have h1 : ‖x‖ / R ≤ 1 / 2 := by
      rw [div_le_iff₀ hR]
      linarith
    calc q ≤ (1 / 2 : ℝ) ^ m₀ := pow_le_pow_left₀ (by positivity) h1 m₀
      _ ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hm₀
      _ = 1 / 4 := by norm_num
  have hgeom : HasSum (fun j : ℕ => D * A * q ^ j) (D * A * (1 - q)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0 (by linarith)).mul_left (D * A)
  have hbd : ∀ j, ‖((fun l : ℕ => -(Multipole.moment G (-((l : ℤ) + 1)) * x ^ l)) ∘ φ) j‖ ≤
      D * A * q ^ j := by
    intro j
    simp only [Function.comp, norm_neg, norm_mul, norm_pow]
    have hm := Multipole.norm_moment_neg_le hGi hR hGs (φ j + 1)
    have e : (-((φ j : ℤ) + 1)) = -(((φ j + 1 : ℕ) : ℤ)) := by push_cast; ring
    rw [e]
    calc ‖Multipole.moment G (-(((φ j + 1 : ℕ) : ℤ)))‖ * ‖x‖ ^ φ j
        ≤ D * (R ^ (φ j + 1))⁻¹ * ‖x‖ ^ φ j :=
          mul_le_mul_of_nonneg_right hm (by positivity)
      _ = D * ((R ^ (φ j + 1))⁻¹ * ‖x‖ ^ φ j) := by ring
      _ = D * A * q ^ j := by
          rw [hφ, pow_identity_hollow (by omega) hR]
          ring
  have hC : ‖Multipole.cauchyTransform G x‖ ≤ D * A * (1 - q)⁻¹ :=
    hs'.norm_le_of_bounded hgeom hbd
  have hinv : (1 - q)⁻¹ ≤ 4 / 3 := by
    have : (3 / 4 : ℝ) ≤ 1 - q := by linarith
    calc (1 - q)⁻¹ ≤ (3 / 4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) this
      _ = 4 / 3 := by norm_num
  have hDn : D = (eLpNorm g 1 volume).toReal := by
    rw [toReal_eLpNorm hg.aestronglyMeasurable,
      lpNorm_one_eq_integral_norm hg.aestronglyMeasurable, hD]
    simp [hG, Complex.norm_real]
  have hD0 : 0 ≤ D := integral_nonneg fun _ => norm_nonneg _
  have hA0 : 0 ≤ A := by positivity
  rw [norm_velocity_eq_cauchyTransform, ← hG, ← hDn]
  have hpi : 0 < Real.pi := Real.pi_pos
  calc (2 * Real.pi)⁻¹ * ‖Multipole.cauchyTransform G x‖
      ≤ (2 * Real.pi)⁻¹ * (D * A * (1 - q)⁻¹) :=
        mul_le_mul_of_nonneg_left hC (by positivity)
    _ ≤ (2 * Real.pi)⁻¹ * (D * A * (4 / 3)) := by gcongr
    _ = 2 / (3 * Real.pi) * D * ‖x‖ ^ (m₀ - 1) * (R ^ m₀)⁻¹ := by
        rw [hA]
        field_simp
        ring

end HollowAux

open HollowAux

/-! ### The interface statements -/

set_option linter.unusedVariables false in
/-- `lem:hollow`, first step of the proof: for `|x| < R` the integral defining `K ∗ ν(x)`
converges absolutely (`ν ∈ L¹` vanishing a.e. on `B_R`). -/
theorem integrable_biotSavart_of_hollow {m₀ : ℕ} (hm₀ : 2 ≤ m₀) {R : ℝ} (hR : 0 < R)
    {ν : ℂ → ℝ} (hν1 : MemLp ν 1 volume) (hνinf : MemLp ν ⊤ volume)
    (hsym : IsMFoldSymmetric m₀ ν) (hsupp : ∀ᵐ y, ‖y‖ < R → ν y = 0) :
    ∀ x ∈ ball (0 : ℂ) R, Integrable (fun y => biotSavartKernel (x - y) * (ν y : ℂ)) volume := by
  intro x hx
  rw [mem_ball_zero_iff] at hx
  exact Multipole.integrable_biotSavart_of_vanishing (memLp_one_iff_integrable.mp hν1)
    (sub_pos.mpr hx) (ae_ball_sub_of_hollow hsupp x)

set_option linter.unusedVariables false in
/-- `lem:hollow`: `K ∗ ν̄ = 0` on `B_R`. -/
theorem velocity_angAvg_eq_zero_of_hollow {m₀ : ℕ} (hm₀ : 2 ≤ m₀) {R : ℝ} (hR : 0 < R)
    {ν : ℂ → ℝ} (hν1 : MemLp ν 1 volume) (hνinf : MemLp ν ⊤ volume)
    (hsym : IsMFoldSymmetric m₀ ν) (hsupp : ∀ᵐ y, ‖y‖ < R → ν y = 0) :
    ∀ x ∈ ball (0 : ℂ) R, velocity (Polar.angAvg ν) x = 0 := by
  intro x hx
  rw [mem_ball_zero_iff] at hx
  have hint : Integrable (fun w => ((Polar.angAvg ν w : ℝ) : ℂ)) :=
    (Polar.integrable_angAvg (memLp_one_iff_integrable.mp hν1)).ofReal
  have hsupp' : ∀ᵐ w, ‖w‖ < R → ((Polar.angAvg ν w : ℝ) : ℂ) = 0 := by
    filter_upwards [ae_angAvg_eq_zero_of_hollow hsupp] with w hw h
    rw [hw h, Complex.ofReal_zero]
  have hs := Multipole.hasSum_cauchyTransform_interior hint hsupp' hx
  have h0 : Multipole.cauchyTransform (fun w => ((Polar.angAvg ν w : ℝ) : ℂ)) x = 0 := by
    refine hs.unique ?_
    convert hasSum_zero with l
    rw [Multipole.moment_angAvg_eq_zero ν (by omega), zero_mul, neg_zero]
  rw [Multipole.velocity_eq_conj_cauchyTransform, h0, mul_zero, map_zero]

/-- `lem:hollow`: for `|x| ≤ R/2`,
`|K ∗ ν(x)| ≤ (2/(3π)) ‖ν - ν̄‖₁ |x|^{m₀-1} R^{-m₀} ≤ (4/(3π)) ‖ν‖₁ |x|^{m₀-1} R^{-m₀}`. -/
theorem norm_velocity_le_of_hollow {m₀ : ℕ} (hm₀ : 2 ≤ m₀) {R : ℝ} (hR : 0 < R)
    {ν : ℂ → ℝ} (hν1 : MemLp ν 1 volume) (hνinf : MemLp ν ⊤ volume)
    (hsym : IsMFoldSymmetric m₀ ν) (hsupp : ∀ᵐ y, ‖y‖ < R → ν y = 0) {x : ℂ}
    (hx : ‖x‖ ≤ R / 2) :
    ‖velocity ν x‖ ≤
        2 / (3 * Real.pi) * (eLpNorm (ν - Polar.angAvg ν) 1 volume).toReal * ‖x‖ ^ (m₀ - 1) *
          (R ^ m₀)⁻¹ ∧
      2 / (3 * Real.pi) * (eLpNorm (ν - Polar.angAvg ν) 1 volume).toReal * ‖x‖ ^ (m₀ - 1) *
          (R ^ m₀)⁻¹ ≤
        4 / (3 * Real.pi) * (eLpNorm ν 1 volume).toReal * ‖x‖ ^ (m₀ - 1) * (R ^ m₀)⁻¹ := by
  have hν : Integrable ν := memLp_one_iff_integrable.mp hν1
  have hν' : Integrable (Polar.angAvg ν) := Polar.integrable_angAvg hν
  have hxR : x ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff]
    linarith [norm_nonneg x]
  -- `K ∗ ν = K ∗ (ν - ν̄)` at `x`, since `K ∗ ν̄ = 0` there.
  have hvel : velocity ν x = velocity (ν - Polar.angAvg ν) x := by
    have h1 := integrable_biotSavart_of_hollow hm₀ hR hν1 hνinf hsym hsupp x hxR
    have h2 : Integrable
        (fun y => biotSavartKernel (x - y) * ((Polar.angAvg ν y : ℝ) : ℂ)) :=
      Multipole.integrable_biotSavart_of_vanishing hν'
        (sub_pos.mpr (mem_ball_zero_iff.mp hxR))
        (ae_ball_sub_of_hollow (ae_angAvg_eq_zero_of_hollow hsupp) x)
    have h0 := velocity_angAvg_eq_zero_of_hollow hm₀ hR hν1 hνinf hsym hsupp x hxR
    have : velocity (ν - Polar.angAvg ν) x = velocity ν x - velocity (Polar.angAvg ν) x := by
      rw [velocity, velocity, velocity, ← integral_sub h1 h2]
      congr 1
      funext y
      simp only [Pi.sub_apply, Complex.ofReal_sub]
      ring
    rw [this, h0, sub_zero]
  -- `ν - ν̄` is again real, integrable, `m₀`-fold symmetric and hollow.
  have hhi : Integrable (ν - Polar.angAvg ν) := hν.sub hν'
  have hhs : ∀ᵐ y, ‖y‖ < R → (ν - Polar.angAvg ν) y = 0 := by
    filter_upwards [hsupp, ae_angAvg_eq_zero_of_hollow hsupp] with y h1 h2 hy
    simp [h1 hy, h2 hy]
  have hhsym : IsMFoldSymmetric m₀ (ν - Polar.angAvg ν) := by
    unfold IsMFoldSymmetric
    filter_upwards [hsym] with y hy
    simp [hy]
  refine ⟨?_, ?_⟩
  · rw [hvel]
    exact norm_velocity_le_aux hm₀ hR hhi hhsym hhs hx
  · have hfin : eLpNorm ν 1 volume ≠ ⊤ := hν1.eLpNorm_ne_top
    have hle : eLpNorm (ν - Polar.angAvg ν) 1 volume ≤ 2 * eLpNorm ν 1 volume := by
      calc eLpNorm (ν - Polar.angAvg ν) 1 volume
          ≤ eLpNorm ν 1 volume + eLpNorm (Polar.angAvg ν) 1 volume :=
            eLpNorm_sub_le hν.aestronglyMeasurable hν'.aestronglyMeasurable le_rfl
        _ ≤ eLpNorm ν 1 volume + eLpNorm ν 1 volume := by
            gcongr
            exact Polar.eLpNorm_angAvg_le hν.aestronglyMeasurable le_rfl
        _ = 2 * eLpNorm ν 1 volume := (two_mul _).symm
    have hle' : (eLpNorm (ν - Polar.angAvg ν) 1 volume).toReal ≤
        2 * (eLpNorm ν 1 volume).toReal := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hfin) hle
      simpa [ENNReal.toReal_mul] using this
    have hpi : 0 < Real.pi := Real.pi_pos
    calc 2 / (3 * Real.pi) * (eLpNorm (ν - Polar.angAvg ν) 1 volume).toReal *
          ‖x‖ ^ (m₀ - 1) * (R ^ m₀)⁻¹
        ≤ 2 / (3 * Real.pi) * (2 * (eLpNorm ν 1 volume).toReal) * ‖x‖ ^ (m₀ - 1) *
          (R ^ m₀)⁻¹ := by gcongr
      _ = 4 / (3 * Real.pi) * (eLpNorm ν 1 volume).toReal * ‖x‖ ^ (m₀ - 1) * (R ^ m₀)⁻¹ := by
          ring

end NonUniqueEuler.BS
