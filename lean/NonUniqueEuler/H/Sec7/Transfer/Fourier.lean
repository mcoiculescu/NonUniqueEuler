import NonUniqueEuler.Defs.Infra.Multipole
import NonUniqueEuler.I.Infra.Multipole.Geometric
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Helper for `lem:transfer`(1): the Laurent coefficients are bounded by the field on a circle

Helper of `P/Sec7/Transfer.lean` (`07_several_rings.tex:150-157`). If `F(z) = Σ_{l≥0} c_l z^{-l-1}`
with `|c_l| ≤ K ϱ^l` and `ϱ < R₀`, then `c_l R₀^{-l-1}` is the Fourier coefficient of
`θ ↦ F(R₀e^{iθ})` at the frequency `-(l+1)`, so `|c_l| ≤ sup_{|z|=R₀}|F| · R₀^{l+1}`
(`norm_coeff_le_of_sphere`). The proof integrates the series termwise
(`intervalIntegral.hasSum_integral_of_dominated_convergence`) against `z^{l+1}`, using
`∫₀^{2π} (R₀e^{iθ})^k dθ = 2π δ_{k0}` (`Multipole.intervalIntegral_circleMap_zpow`).
-/

noncomputable section

open MeasureTheory Set Metric Real

namespace NonUniqueEuler.Rings.TransferAux

/-- **Cauchy's coefficient estimate for an exterior Laurent series** (`07_several_rings.tex:150-157`):
if `|c_l| ≤ K ϱ^l`, `0 ≤ ϱ < R₀` and `|Σ_l c_l z^{-l-1}| ≤ M` on `|z| = R₀`, then
`|c_l| ≤ M R₀^{l+1}`. -/
theorem norm_coeff_le_of_sphere {c : ℕ → ℂ} {K ϱ R₀ M : ℝ} (hϱ : 0 ≤ ϱ) (hR₀ : ϱ < R₀)
    (hc : ∀ l, ‖c l‖ ≤ K * ϱ ^ l)
    (hM : ∀ z : ℂ, ‖z‖ = R₀ → ‖Multipole.laurentTail c z‖ ≤ M) (l : ℕ) :
    ‖c l‖ ≤ M * R₀ ^ (l + 1) := by
  have hR0 : 0 < R₀ := hϱ.trans_lt hR₀
  set w : ℝ → ℂ := circleMap 0 R₀ with hw
  have hwn : ∀ θ, ‖w θ‖ = R₀ := fun θ => by simp [hw, abs_of_pos hR0]
  have hw0 : ∀ θ, w θ ≠ 0 := fun θ h => by
    have := hwn θ
    rw [h, norm_zero] at this
    linarith
  set F : ℕ → ℝ → ℂ := fun n θ => c n * w θ ^ ((l : ℤ) - n) with hF
  set f : ℝ → ℂ := fun θ => Multipole.laurentTail c (w θ) * w θ ^ (l + 1) with hf
  have hterm : ∀ n θ, c n * (w θ ^ (n + 1))⁻¹ * w θ ^ (l + 1) = F n θ := by
    intro n θ
    simp only [hF]
    rw [mul_assoc]
    congr 1
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ (hw0 θ)]
    congr 1
    push_cast
    ring
  have hr : ‖ϱ / R₀‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hϱ hR0.le)]
    exact (div_lt_one hR0).mpr hR₀
  have hsumG : Summable (fun n : ℕ => K * ϱ ^ n * (R₀ ^ (n + 1))⁻¹) := by
    have := (summable_geometric_of_norm_lt_one hr).mul_left (K * R₀⁻¹)
    refine this.congr fun n => ?_
    rw [div_pow, pow_succ]
    field_simp
  have hsum_bound : Summable (fun n : ℕ => K * ϱ ^ n * (R₀ ^ (n + 1))⁻¹ * R₀ ^ (l + 1)) :=
    hsumG.mul_right _
  have hFle : ∀ n θ, ‖F n θ‖ ≤ K * ϱ ^ n * (R₀ ^ (n + 1))⁻¹ * R₀ ^ (l + 1) := by
    intro n θ
    rw [← hterm, norm_mul, norm_mul, norm_inv, norm_pow, norm_pow, hwn]
    gcongr
    exact hc n
  have hlim : ∀ θ, HasSum (fun n => F n θ) (f θ) := by
    intro θ
    have hs : Summable (fun n => c n * (w θ ^ (n + 1))⁻¹) := by
      refine Summable.of_norm_bounded hsumG fun n => ?_
      rw [norm_mul, norm_inv, norm_pow, hwn]
      gcongr
      exact hc n
    have h1 := hs.hasSum.mul_right (w θ ^ (l + 1))
    have h2 : (fun n => c n * (w θ ^ (n + 1))⁻¹ * w θ ^ (l + 1)) = fun n => F n θ :=
      funext fun n => hterm n θ
    rw [h2] at h1
    exact h1
  have hcont : ∀ n, Continuous (F n) := by
    intro n
    exact continuous_const.mul
      ((continuous_circleMap 0 R₀).zpow₀ _ fun θ => Or.inl (hw0 θ))
  have hint : HasSum (fun n => ∫ θ in (0 : ℝ)..2 * π, F n θ) (∫ θ in (0 : ℝ)..2 * π, f θ) :=
    intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n _ => K * ϱ ^ n * (R₀ ^ (n + 1))⁻¹ * R₀ ^ (l + 1))
      (fun n => (hcont n).aestronglyMeasurable) (fun n => ae_of_all _ fun θ _ => hFle n θ)
      (ae_of_all _ fun _ _ => hsum_bound) intervalIntegrable_const
      (ae_of_all _ fun θ _ => hlim θ)
  have hIn : ∀ n, ∫ θ in (0 : ℝ)..2 * π, F n θ = if n = l then 2 * (π : ℂ) * c l else 0 := by
    intro n
    simp only [hF]
    rw [intervalIntegral.integral_const_mul, hw, Multipole.intervalIntegral_circleMap_zpow]
    by_cases h : n = l
    · subst h
      simp only [sub_self, ite_true]
      ring
    · have h' : (l : ℤ) - n ≠ 0 := by omega
      simp [h', h]
  have hval : ∫ θ in (0 : ℝ)..2 * π, f θ = 2 * (π : ℂ) * c l := by
    have h2 : HasSum (fun n => if n = l then 2 * (π : ℂ) * c l else 0) (2 * (π : ℂ) * c l) :=
      hasSum_ite_eq l _
    have h3 : (fun n => ∫ θ in (0 : ℝ)..2 * π, F n θ) =
        fun n => if n = l then 2 * (π : ℂ) * c l else 0 := funext hIn
    rw [h3] at hint
    exact hint.unique h2
  have hbd : ‖∫ θ in (0 : ℝ)..2 * π, f θ‖ ≤ M * R₀ ^ (l + 1) * |2 * π - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ => by
      simp only [hf]
      rw [norm_mul, norm_pow, hwn]
      gcongr
      exact hM _ (hwn θ)
  rw [hval, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, sub_zero, abs_of_pos Real.two_pi_pos] at hbd
  have hpi : 0 < 2 * π := Real.two_pi_pos
  nlinarith

end NonUniqueEuler.Rings.TransferAux
