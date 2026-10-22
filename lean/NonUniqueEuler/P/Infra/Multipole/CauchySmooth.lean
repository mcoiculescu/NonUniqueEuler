import NonUniqueEuler.Defs.Infra.Multipole
import NonUniqueEuler.I.Infra.Multipole.Holomorphic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Proof: the Cauchy transform and the velocity off the support of the vorticity (I-MULT)

Proof of `NonUniqueEuler/I/Infra/Multipole/CauchySmooth.lean` (same declarations, same
statements). Differentiation under the integral sign
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`, over `𝕜 = ℂ`) applied to the kernels
`w ↦ g(w) (x - w)^{-(k+1)}`, which are dominated by `(2/δ)^{k+1} |g(w)|` for `x ∈ ball z (δ/2)`
when `g = 0` a.e. on `ball z δ`; induction on `q` for the iterated derivatives. The velocity is
`conj ((2πi)⁻¹ C[g])` (`velocity_eq_conj_cauchyTransform`), and the real-derivative facts for the
conjugate of a holomorphic function come from `I/Infra/Multipole/Holomorphic.lean`.
-/

noncomputable section

open MeasureTheory Set Metric Real ComplexConjugate Filter Topology
open scoped ContDiff Nat

namespace NonUniqueEuler.Multipole

/-! ### Kernel bounds -/

private lemma norm_inv_pow_le_of_le {u : ℂ} {ε : ℝ} (hε : 0 < ε) (h : ε ≤ ‖u‖) (n : ℕ) :
    ‖(u ^ n)⁻¹‖ ≤ (ε ^ n)⁻¹ := by
  rw [norm_inv, norm_pow]
  exact inv_anti₀ (pow_pos hε n) (pow_le_pow_left₀ hε.le h n)

/-- Pointwise domination of `g(w) (x - w)^{-n}` when `g` vanishes on `ball z δ` and
`dist x z + ε ≤ δ`. -/
private lemma norm_mul_inv_pow_le {g : ℂ → ℂ} {z x w : ℂ} {δ ε : ℝ} (hε : 0 < ε)
    (hx : dist x z + ε ≤ δ) (hw : w ∈ ball z δ → g w = 0) (n : ℕ) :
    ‖g w * ((x - w) ^ n)⁻¹‖ ≤ (ε ^ n)⁻¹ * ‖g w‖ := by
  by_cases hwb : w ∈ ball z δ
  · simp [hw hwb]
  · have hzw : δ ≤ dist w z := not_lt.1 hwb
    have h1 : ε ≤ ‖x - w‖ := by
      rw [← dist_eq_norm]
      have := dist_triangle w x z
      rw [dist_comm w x] at this
      linarith
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (norm_inv_pow_le_of_le hε h1 n) (norm_nonneg _)

private lemma aestronglyMeasurable_mul_inv_pow {g : ℂ → ℂ}
    (hg : AEStronglyMeasurable g volume) (x : ℂ) (n : ℕ) :
    AEStronglyMeasurable (fun w => g w * ((x - w) ^ n)⁻¹) volume :=
  hg.mul (by fun_prop : Measurable fun w : ℂ => ((x - w) ^ n)⁻¹).aestronglyMeasurable

private lemma integrable_mul_inv_pow {g : ℂ → ℂ} (hg : Integrable g) {z x : ℂ} {δ ε : ℝ}
    (hε : 0 < ε) (hx : dist x z + ε ≤ δ) (hsupp : ∀ᵐ w, w ∈ ball z δ → g w = 0) (n : ℕ) :
    Integrable (fun w => g w * ((x - w) ^ n)⁻¹) :=
  (hg.norm.const_mul (ε ^ n)⁻¹).mono' (aestronglyMeasurable_mul_inv_pow hg.1 x n)
    (hsupp.mono fun _ hw => norm_mul_inv_pow_le hε hx hw n)

/-! ### Differentiation under the integral sign -/

private lemma hasDerivAt_inv_pow_sub {w x : ℂ} (hx : x ≠ w) (n : ℕ) :
    HasDerivAt (fun y => ((y - w) ^ (n + 1))⁻¹)
      (-((n : ℂ) + 1) * ((x - w) ^ (n + 1 + 1))⁻¹) x := by
  have hxw : x - w ≠ 0 := sub_ne_zero.2 hx
  have h1 : HasDerivAt (fun y => (y - w) ^ (n + 1)) (((n + 1 : ℕ) : ℂ) * (x - w) ^ n) x := by
    simpa using ((hasDerivAt_id x).sub_const w).fun_pow (n + 1)
  have hne : (x - w) ^ (n + 1) ≠ 0 := pow_ne_zero _ hxw
  refine (h1.fun_inv hne).congr_deriv ?_
  field_simp
  push_cast
  ring

/-- `d/dx ∫ g(w) (x - w)^{-(k+1)} dw = -(k+1) ∫ g(w) (x - w)^{-(k+2)} dw` at `z` when `g = 0`
a.e. on `ball z δ`. -/
private lemma hasDerivAt_integral_mul_inv_pow {g : ℂ → ℂ} (hg : Integrable g) {z : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hsupp : ∀ᵐ w, w ∈ ball z δ → g w = 0) (k : ℕ) :
    HasDerivAt (fun x => ∫ w, g w * ((x - w) ^ (k + 1))⁻¹)
      (-((k : ℂ) + 1) * ∫ w, g w * ((z - w) ^ (k + 1 + 1))⁻¹) z := by
  have hδ2 : 0 < δ / 2 := half_pos hδ
  have hx_of : ∀ x ∈ ball z (δ / 2), dist x z + δ / 2 ≤ δ := fun x hx => by
    rw [mem_ball] at hx; linarith
  have hk : ‖-((k : ℂ) + 1)‖ = (k : ℝ) + 1 := by
    rw [norm_neg]
    exact_mod_cast Complex.norm_natCast (k + 1)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun x w => g w * ((x - w) ^ (k + 1))⁻¹)
    (F' := fun x w => -((k : ℂ) + 1) * (g w * ((x - w) ^ (k + 1 + 1))⁻¹))
    (bound := fun w => ((k : ℝ) + 1) * (((δ / 2) ^ (k + 1 + 1))⁻¹ * ‖g w‖))
    (x₀ := z) (s := ball z (δ / 2)) (ball_mem_nhds z hδ2)
    (Eventually.of_forall fun x => aestronglyMeasurable_mul_inv_pow hg.1 x (k + 1))
    (integrable_mul_inv_pow hg hδ (by simp) hsupp (k + 1))
    ((aestronglyMeasurable_mul_inv_pow hg.1 z (k + 1 + 1)).const_mul _)
    ?_ ((hg.norm.const_mul _).const_mul _) ?_
  · have h2 := key.2
    rw [integral_const_mul] at h2
    exact h2
  · filter_upwards [hsupp] with w hw x hx
    rw [norm_mul, hk]
    exact mul_le_mul_of_nonneg_left (norm_mul_inv_pow_le hδ2 (hx_of x hx) hw _)
      (by positivity)
  · filter_upwards [hsupp] with w hw x hx
    by_cases hwb : w ∈ ball z δ
    · simp only [hw hwb, zero_mul, mul_zero]
      exact hasDerivAt_const _ _
    · have hxw : x ≠ w := by
        rintro rfl
        exact hwb (ball_subset_ball (half_le_self hδ.le) hx)
      exact ((hasDerivAt_inv_pow_sub hxw k).const_mul (g w)).congr_deriv (by ring)

/-! ### The Cauchy transform -/

private lemma cauchyTransform_eq (g : ℂ → ℂ) :
    cauchyTransform g = fun x => ∫ w, g w * ((x - w) ^ (0 + 1))⁻¹ := by
  funext x
  simp [cauchyTransform]

set_option linter.unusedVariables false in
/-- The Cauchy transform is holomorphic where `g` vanishes nearby. -/
theorem differentiableOn_cauchyTransform {g : ℂ → ℂ} (hg : Integrable g) {U : Set ℂ}
    (hU : IsOpen U) (hsep : ∀ z ∈ U, ∃ δ > 0, ∀ᵐ w, w ∈ ball z δ → g w = 0) :
    DifferentiableOn ℂ (cauchyTransform g) U := by
  intro z hz
  obtain ⟨δ, hδ, h⟩ := hsep z hz
  rw [cauchyTransform_eq]
  exact (hasDerivAt_integral_mul_inv_pow hg hδ h 0).differentiableAt.differentiableWithinAt

/-- `C[g]^{(q)}(z) = (-1)^q q! ∫ g(w) (z-w)^{-(q+1)} dw` where `g` vanishes nearby. -/
theorem iteratedDeriv_cauchyTransform {g : ℂ → ℂ} (hg : Integrable g) {U : Set ℂ}
    (hU : IsOpen U) (hsep : ∀ z ∈ U, ∃ δ > 0, ∀ᵐ w, w ∈ ball z δ → g w = 0) (q : ℕ)
    {z : ℂ} (hz : z ∈ U) :
    iteratedDeriv q (cauchyTransform g) z =
      (-1) ^ q * (q ! : ℂ) * ∫ w, g w * ((z - w) ^ (q + 1))⁻¹ := by
  induction q generalizing z with
  | zero => simp [cauchyTransform]
  | succ q ih =>
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv q (cauchyTransform g) =ᶠ[𝓝 z]
        fun x => (-1) ^ q * (q ! : ℂ) * ∫ w, g w * ((x - w) ^ (q + 1))⁻¹ :=
      Filter.eventually_of_mem (hU.mem_nhds hz) fun x hx => ih hx
    rw [hev.deriv_eq]
    obtain ⟨δ, hδ, h⟩ := hsep z hz
    rw [((hasDerivAt_integral_mul_inv_pow hg hδ h q).const_mul ((-1) ^ q * (q ! : ℂ))).deriv,
      Nat.factorial_succ]
    push_cast
    ring

/-! ### The velocity -/

/-- Away from the support, the Biot–Savart integral converges absolutely. -/
theorem integrable_biotSavart_of_vanishing {g : ℂ → ℝ} (hg : Integrable g) {z : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hsupp : ∀ᵐ w, w ∈ ball z δ → g w = 0) :
    Integrable (fun y => biotSavartKernel (z - y) * (g y : ℂ)) := by
  have hK : Measurable biotSavartKernel := by
    unfold biotSavartKernel
    fun_prop
  have hmeas : AEStronglyMeasurable (fun y => biotSavartKernel (z - y) * (g y : ℂ)) volume :=
    (hK.comp (measurable_const.sub measurable_id)).aestronglyMeasurable.mul
      hg.ofReal.aestronglyMeasurable
  refine (hg.norm.const_mul (2 * π * δ)⁻¹).mono' hmeas ?_
  filter_upwards [hsupp] with w hw
  by_cases hwb : w ∈ ball z δ
  · simp [hw hwb]
  · have hzw : δ ≤ ‖z - w‖ := by
      rw [← dist_eq_norm, dist_comm]
      exact not_lt.1 hwb
    have hnK : ‖biotSavartKernel (z - w)‖ = (2 * π * ‖z - w‖)⁻¹ := by
      rw [← Complex.norm_conj, conj_biotSavartKernel, norm_inv, norm_mul, norm_mul,
        Complex.norm_I, mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
      norm_num
    rw [norm_mul, hnK, Complex.norm_real]
    gcongr

private lemma velocity_eq_conj (g : ℂ → ℝ) :
    velocity g = fun x =>
      conj ((2 * π * Complex.I)⁻¹ * cauchyTransform (fun w => (g w : ℂ)) x) :=
  funext (velocity_eq_conj_cauchyTransform g)

private lemma hsep_ofReal {g : ℂ → ℝ} {U : Set ℂ}
    (hsep : ∀ z ∈ U, ∃ δ > 0, ∀ᵐ w, w ∈ ball z δ → g w = 0) :
    ∀ z ∈ U, ∃ δ > 0, ∀ᵐ w, w ∈ ball z δ → (fun w => (g w : ℂ)) w = 0 := by
  intro z hz
  obtain ⟨δ, hδ, h⟩ := hsep z hz
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [h] with w hw hwb
  simp [hw hwb]

private lemma integrable_ofReal {g : ℂ → ℝ} (hg : Integrable g) :
    Integrable (fun w => (g w : ℂ)) :=
  hg.ofReal

private lemma differentiableOn_velocityHol {g : ℂ → ℝ} (hg : Integrable g) {U : Set ℂ}
    (hU : IsOpen U) (hsep : ∀ z ∈ U, ∃ δ > 0, ∀ᵐ w, w ∈ ball z δ → g w = 0) :
    DifferentiableOn ℂ
      (fun x => (2 * π * Complex.I)⁻¹ * cauchyTransform (fun w => (g w : ℂ)) x) U :=
  (differentiableOn_cauchyTransform (integrable_ofReal hg) hU (hsep_ofReal hsep)).const_mul _

/-- The velocity is `C^∞` where the vorticity vanishes nearby. -/
theorem contDiffOn_velocity {g : ℂ → ℝ} (hg : Integrable g) {U : Set ℂ} (hU : IsOpen U)
    (hsep : ∀ z ∈ U, ∃ δ > 0, ∀ᵐ w, w ∈ ball z δ → g w = 0) :
    ContDiffOn ℝ ∞ (velocity g) U := by
  rw [velocity_eq_conj]
  exact (contDiffOn_real_of_differentiableOn hU (differentiableOn_velocityHol hg hU hsep)).2

/-- `‖D^q (K ⋆ g)(z)‖ = (2π)⁻¹ q! |∫ g(w)(z-w)^{-(q+1)} dw|` where `g` vanishes nearby. -/
theorem norm_iteratedFDeriv_velocity {g : ℂ → ℝ} (hg : Integrable g) {U : Set ℂ}
    (hU : IsOpen U) (hsep : ∀ z ∈ U, ∃ δ > 0, ∀ᵐ w, w ∈ ball z δ → g w = 0) (q : ℕ)
    {z : ℂ} (hz : z ∈ U) :
    ‖iteratedFDeriv ℝ q (velocity g) z‖ =
      (2 * π)⁻¹ * q ! * ‖∫ w, (g w : ℂ) * ((z - w) ^ (q + 1))⁻¹‖ := by
  rw [velocity_eq_conj,
    norm_iteratedFDeriv_real_conj_eq hU (differentiableOn_velocityHol hg hU hsep) hz q,
    iteratedDeriv_const_mul_field,
    iteratedDeriv_cauchyTransform (integrable_ofReal hg) hU (hsep_ofReal hsep) q hz]
  simp only [norm_mul, norm_inv, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    Complex.norm_natCast]
  norm_num
  ring

/-- `‖D^q (K ⋆ g)(z)‖ ≤ (2π)⁻¹ q! ‖g‖₁ δ^{-(q+1)}` when `g = 0` a.e. on `ball z δ`. -/
theorem norm_iteratedFDeriv_velocity_le {g : ℂ → ℝ} (hg : Integrable g) {z : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hsupp : ∀ᵐ w, w ∈ ball z δ → g w = 0) (q : ℕ) :
    ‖iteratedFDeriv ℝ q (velocity g) z‖ ≤ (2 * π)⁻¹ * q ! * (∫ w, |g w|) * (δ ^ (q + 1))⁻¹ := by
  have hsep : ∀ z' ∈ ball z δ, ∃ δ' > 0, ∀ᵐ w, w ∈ ball z' δ' → g w = 0 := by
    intro z' hz'
    rw [mem_ball] at hz'
    refine ⟨δ - dist z' z, by linarith, ?_⟩
    filter_upwards [hsupp] with w hw hw'
    apply hw
    rw [mem_ball] at hw' ⊢
    linarith [dist_triangle w z' z]
  rw [norm_iteratedFDeriv_velocity hg isOpen_ball hsep q (mem_ball_self hδ)]
  have hb : ‖∫ w, (g w : ℂ) * ((z - w) ^ (q + 1))⁻¹‖ ≤ ∫ w, (δ ^ (q + 1))⁻¹ * |g w| := by
    refine norm_integral_le_of_norm_le (hg.abs.const_mul _) ?_
    filter_upwards [hsupp] with w hw
    have := norm_mul_inv_pow_le (g := fun w => (g w : ℂ)) (z := z) (x := z) (δ := δ) hδ (by simp)
      (w := w) (fun h => by simp [hw h]) (q + 1)
    simpa [Complex.norm_real] using this
  rw [integral_const_mul] at hb
  calc (2 * π)⁻¹ * q ! * ‖∫ w, (g w : ℂ) * ((z - w) ^ (q + 1))⁻¹‖
      ≤ (2 * π)⁻¹ * q ! * ((δ ^ (q + 1))⁻¹ * ∫ w, |g w|) := by gcongr
    _ = (2 * π)⁻¹ * q ! * (∫ w, |g w|) * (δ ^ (q + 1))⁻¹ := by ring

end NonUniqueEuler.Multipole
