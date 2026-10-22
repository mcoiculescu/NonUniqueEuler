import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Data.ENNReal.Holder
import NonUniqueEuler.Defs.Infra.SobolevOneD
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv
import NonUniqueEuler.H.Infra.SobolevOneD.Energy.Conv

/-!
# Helper for `P/Infra/SobolevOneD/Energy`: `yukawa ℓ f` and its first two derivatives

For `ℓ ≠ 0`, `L = |ℓ|`, `f ∈ L²` vanishing a.e. outside `[a, b]`:
* `ψ = yukawa ℓ f = -(2L)⁻¹ psi0 L f` is differentiable with `ψ' = Y1 = (1/2) psi1 L f`
  (`hasDerivAt_yukawa`);
* tested against `TestLike` functions: `∫ ψ φ' = -∫ Y1 φ` and `∫ Y1 φ' = -∫ Y2 φ` with
  `Y2 = ℓ² ψ + f`; hence the weak derivatives `ψ' = Y1`, `Y1' = Y2`, `ψ'' = Y2`;
* `ψ, Y1, Y2 ∈ L²`;
* the energy identity `∫|f|² = ℓ⁴∫|ψ|² + 2ℓ²∫|Y1|² + ∫|Y2|²`, from `∫ Y1 conj Y1 = -∫ Y2 conj ψ`
  (the second identity tested against `φ = conj ψ`).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff ComplexConjugate

namespace NonUniqueEuler.Sob.EnergyAux

/-- The first derivative of `yukawa ℓ f`. -/
def Y1 (ℓ : ℤ) (f : ℝ → ℂ) (x : ℝ) : ℂ := (1 / 2 : ℂ) * psi1 |(ℓ : ℝ)| f x

/-- The second derivative of `yukawa ℓ f`: `ℓ² ψ + f`. -/
def Y2 (ℓ : ℤ) (f : ℝ → ℂ) (x : ℝ) : ℂ := (ℓ : ℂ) ^ 2 * yukawa ℓ f x + f x

theorem yukawa_eq (ℓ : ℤ) (f : ℝ → ℂ) (x : ℝ) :
    yukawa ℓ f x = -(((2 * |(ℓ : ℝ)|)⁻¹ : ℝ) : ℂ) * psi0 |(ℓ : ℝ)| f x := rfl

theorem abs_pos_of_ne {ℓ : ℤ} (hℓ : ℓ ≠ 0) : 0 < |(ℓ : ℝ)| :=
  abs_pos.2 (Int.cast_ne_zero.2 hℓ)

theorem sq_abs_cast (ℓ : ℤ) : ((|(ℓ : ℝ)| : ℝ) : ℂ) ^ 2 = (ℓ : ℂ) ^ 2 := by
  rw [← Complex.ofReal_pow, sq_abs]
  push_cast
  ring

/-- An `L²` function vanishing a.e. outside a compact interval is integrable. -/
theorem integrable_of_memLp_two {f : ℝ → ℂ} (hf : MemLp f 2 volume) {a b : ℝ}
    (hfab : ∀ᵐ x, x ∉ Icc a b → f x = 0) : Integrable f := by
  have : IsFiniteMeasure (volume.restrict (Icc a b)) :=
    isFiniteMeasure_restrict.2 measure_Icc_lt_top.ne
  have h1 : IntegrableOn f (Icc a b) := (hf.restrict _).integrable one_le_two
  exact h1.integrable_of_ae_notMem_eq_zero hfab

/-! ### Classical regularity and bounds -/

section Bounds

variable {ℓ : ℤ} (hℓ : ℓ ≠ 0) {f : ℝ → ℂ} (hf : Integrable f) {a b : ℝ}
  (hfab : ∀ᵐ x, x ∉ Icc a b → f x = 0)
include hℓ hf

theorem hasDerivAt_yukawa (x : ℝ) : HasDerivAt (yukawa ℓ f) (Y1 ℓ f x) x := by
  have hL := abs_pos_of_ne hℓ
  have h := (hasDerivAt_psi0 hL.le hf x).const_mul (-(((2 * |(ℓ : ℝ)|)⁻¹ : ℝ) : ℂ))
  refine h.congr_deriv ?_
  unfold Y1
  have hL' : ((|(ℓ : ℝ)| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hL.ne'
  push_cast
  field_simp

theorem continuous_yukawa : Continuous (yukawa ℓ f) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_yukawa hℓ hf x).continuousAt

omit hℓ in
theorem aestronglyMeasurable_Y1 : AEStronglyMeasurable (Y1 ℓ f) :=
  (aestronglyMeasurable_psi1 _ hf).const_mul _

include hfab

/-- `‖ψ(x)‖ ≤ C e^{-L|x-a|}`. -/
theorem exists_yukawa_bound :
    ∃ C, 0 ≤ C ∧ ∀ x, ‖yukawa ℓ f x‖ ≤ C * k0 |(ℓ : ℝ)| (x - a) ∧
      ‖Y1 ℓ f x‖ ≤ C * k0 |(ℓ : ℝ)| (x - a) := by
  have hL := abs_pos_of_ne hℓ
  set B := Real.exp (|(ℓ : ℝ)| * (b - a)) * ∫ y, ‖f y‖ with hB
  have hB0 : 0 ≤ B := bound_nonneg _ _ _ _
  refine ⟨((2 * |(ℓ : ℝ)|)⁻¹ + 1) * B, by positivity, fun x => ⟨?_, ?_⟩⟩
  · rw [yukawa_eq, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    have h := norm_psi0_le hL.le hf hfab x
    have hk := (k0_pos |(ℓ : ℝ)| (x - a)).le
    calc (2 * |(ℓ : ℝ)|)⁻¹ * ‖psi0 |(ℓ : ℝ)| f x‖ ≤ (2 * |(ℓ : ℝ)|)⁻¹ * (B * k0 _ (x - a)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ ≤ ((2 * |(ℓ : ℝ)|)⁻¹ + 1) * B * k0 |(ℓ : ℝ)| (x - a) := by nlinarith [mul_nonneg hB0 hk]
  · unfold Y1
    rw [norm_mul]
    have h := norm_psi1_le hL.le hf hfab x
    have hk := (k0_pos |(ℓ : ℝ)| (x - a)).le
    have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [h2]
    have hinv : 0 ≤ (2 * |(ℓ : ℝ)|)⁻¹ := by positivity
    calc 1 / 2 * ‖psi1 |(ℓ : ℝ)| f x‖ ≤ 1 / 2 * (B * k0 _ (x - a)) :=
          mul_le_mul_of_nonneg_left h (by norm_num)
      _ ≤ ((2 * |(ℓ : ℝ)|)⁻¹ + 1) * B * k0 |(ℓ : ℝ)| (x - a) := by
          nlinarith [mul_nonneg hB0 hk, mul_nonneg (mul_nonneg hB0 hk) hinv]

theorem memLp_yukawa : MemLp (yukawa ℓ f) 2 := by
  obtain ⟨C, -, hC⟩ := exists_yukawa_bound hℓ hf hfab
  exact memLp_two_of_le_k0 (abs_pos_of_ne hℓ) (continuous_yukawa hℓ hf).aestronglyMeasurable
    fun x => (hC x).1

theorem memLp_Y1 : MemLp (Y1 ℓ f) 2 := by
  obtain ⟨C, -, hC⟩ := exists_yukawa_bound hℓ hf hfab
  exact memLp_two_of_le_k0 (abs_pos_of_ne hℓ) (aestronglyMeasurable_Y1 hf) fun x => (hC x).2

theorem integrable_yukawa : Integrable (yukawa ℓ f) := by
  obtain ⟨C, -, hC⟩ := exists_yukawa_bound hℓ hf hfab
  exact integrable_of_le_k0 (abs_pos_of_ne hℓ) (continuous_yukawa hℓ hf).aestronglyMeasurable
    fun x => (hC x).1

theorem integrable_Y1 : Integrable (Y1 ℓ f) := by
  obtain ⟨C, -, hC⟩ := exists_yukawa_bound hℓ hf hfab
  exact integrable_of_le_k0 (abs_pos_of_ne hℓ) (aestronglyMeasurable_Y1 hf) fun x => (hC x).2

theorem exists_yukawa_bdd : ∃ M, ∀ x, ‖yukawa ℓ f x‖ ≤ M := by
  obtain ⟨C, hC0, hC⟩ := exists_yukawa_bound hℓ hf hfab
  refine ⟨C, fun x => (hC x).1.trans ?_⟩
  calc C * k0 |(ℓ : ℝ)| (x - a) ≤ C * 1 :=
        mul_le_mul_of_nonneg_left (k0_le_one (abs_nonneg _) _) hC0
    _ = C := mul_one C

end Bounds

/-! ### Testing against `TestLike` functions -/

section Tests

variable {ℓ : ℤ} (hℓ : ℓ ≠ 0) {f : ℝ → ℂ} (hf : Integrable f) {a b : ℝ}
  (hfab : ∀ᵐ x, x ∉ Icc a b → f x = 0)
include hℓ hf

/-- `∫ ψ φ' = -∫ Y1 φ`. -/
theorem integral_yukawa_mul_deriv {φ φ' : ℝ → ℂ} (hφ : TestLike φ φ') :
    ∫ x, yukawa ℓ f x * φ' x = -∫ x, Y1 ℓ f x * φ x := by
  have hL := abs_pos_of_ne hℓ
  simp_rw [yukawa_eq, mul_assoc]
  rw [integral_const_mul, integral_psi0_mul_deriv hL hf hφ]
  unfold Y1
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  have hL' : ((|(ℓ : ℝ)| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hL.ne'
  push_cast
  field_simp

/-- `∫ Y1 φ' = -∫ Y2 φ` (requires `f φ` integrable and `ψ φ` integrable). -/
theorem integral_Y1_mul_deriv {φ φ' : ℝ → ℂ} (hφ : TestLike φ φ')
    (hfφ : Integrable fun x => f x * φ x) (hψφ : Integrable fun x => yukawa ℓ f x * φ x) :
    ∫ x, Y1 ℓ f x * φ' x = -∫ x, Y2 ℓ f x * φ x := by
  have hL := abs_pos_of_ne hℓ
  unfold Y1 Y2
  simp_rw [mul_assoc]
  rw [integral_const_mul, integral_psi1_mul_deriv hL hf hφ hfφ]
  have h1 : (fun x => ((ℓ : ℂ) ^ 2 * yukawa ℓ f x + f x) * φ x) =
      fun x => (ℓ : ℂ) ^ 2 * (yukawa ℓ f x * φ x) + f x * φ x := by
    funext x; ring
  rw [h1, integral_add (hψφ.const_mul _) hfφ, integral_const_mul]
  simp_rw [yukawa_eq, mul_assoc]
  rw [integral_const_mul]
  have hL' : ((|(ℓ : ℝ)| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hL.ne'
  rw [← sq_abs_cast ℓ]
  push_cast
  field_simp
  ring

end Tests

/-! ### Weak derivatives -/

theorem testLike_of_isTestFn {φ : ℝ → ℂ} (hφ : IsTestFn univ φ) : TestLike φ (deriv φ) where
  deriv x := ((hφ.smooth.differentiable (by simp)) x).hasDerivAt
  int := hφ.continuous.integrable_of_hasCompactSupport hφ.compact
  int' := (hφ.smooth.continuous_deriv (by simp)).integrable_of_hasCompactSupport hφ.compact.deriv
  bdd := hφ.compact.exists_bound_of_continuous hφ.continuous

theorem iterDirDeriv_derivList_one (φ : ℝ → ℂ) : iterDirDeriv (derivList 1) φ = deriv φ := by
  rw [iterDirDeriv_derivList, iteratedDeriv_one]

theorem integrable_mul_testFn {g φ : ℝ → ℂ} (hg : Integrable g) (hφ : IsTestFn univ φ) :
    Integrable fun x => g x * φ x := by
  obtain ⟨M, hM⟩ := hφ.compact.exists_bound_of_continuous hφ.continuous
  exact hg.mul_bdd hφ.continuous.aestronglyMeasurable (Eventually.of_forall hM)

section Weak

variable {ℓ : ℤ} (hℓ : ℓ ≠ 0) {f : ℝ → ℂ} (hf : Integrable f) {a b : ℝ}
  (hfab : ∀ᵐ x, x ∉ Icc a b → f x = 0)
include hℓ hf

theorem hasWeakDerivOn_yukawa_one :
    HasWeakDerivOn univ (derivList 1) (yukawa ℓ f) (Y1 ℓ f) := by
  intro φ hφ
  rw [iterDirDeriv_derivList_one, integral_yukawa_mul_deriv hℓ hf (testLike_of_isTestFn hφ)]
  simp

include hfab

theorem hasWeakDerivOn_Y1_one : HasWeakDerivOn univ (derivList 1) (Y1 ℓ f) (Y2 ℓ f) := by
  intro φ hφ
  rw [iterDirDeriv_derivList_one, integral_Y1_mul_deriv hℓ hf (testLike_of_isTestFn hφ)
    (integrable_mul_testFn hf hφ) (integrable_mul_testFn (integrable_yukawa hℓ hf hfab) hφ)]
  simp

theorem hasWeakDerivOn_yukawa_two :
    HasWeakDerivOn univ (derivList 2) (yukawa ℓ f) (Y2 ℓ f) := by
  have h := (hasWeakDerivOn_yukawa_one hℓ hf).trans (hasWeakDerivOn_Y1_one hℓ hf hfab)
  have hl : derivList 1 ++ derivList 1 = derivList 2 := rfl
  rwa [hl] at h

end Weak

/-! ### The energy identity -/

theorem l2_sq_eq_integral {g : ℝ → ℂ} (hg : MemLp g 2 volume) :
    l2 g ^ 2 = ∫ x, ‖g x‖ ^ 2 := by
  unfold l2
  rw [hg.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  have h0 : 0 ≤ ∫ x, ‖g x‖ ^ (2 : ENNReal).toReal := integral_nonneg fun x => by positivity
  rw [ENNReal.toReal_ofReal (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul h0]
  simp

theorem integrable_norm_sq {g : ℝ → ℂ} (hg : MemLp g 2 volume) :
    Integrable (fun x => ‖g x‖ ^ 2) := by
  have := hg.integrable_norm_rpow two_ne_zero ENNReal.ofNat_ne_top
  simpa using this

theorem integrable_conj {g : ℝ → ℂ} (hg : Integrable g) : Integrable fun x => conj (g x) :=
  hg.mono (Complex.continuous_conj.comp_aestronglyMeasurable hg.aestronglyMeasurable)
    (Eventually.of_forall fun x => by simp)

theorem norm_sub_real_mul_sq (u v : ℂ) (c : ℝ) :
    ‖u - (c : ℂ) * v‖ ^ 2 = ‖u‖ ^ 2 - 2 * c * (u * conj v).re + c ^ 2 * ‖v‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
    Complex.conj_im]
  ring

section Energy

variable {ℓ : ℤ} (hℓ : ℓ ≠ 0) {f : ℝ → ℂ} (hf2 : MemLp f 2 volume) {a b : ℝ}
  (hfab : ∀ᵐ x, x ∉ Icc a b → f x = 0)
include hℓ hf2 hfab

theorem memLp_Y2 : MemLp (Y2 ℓ f) 2 :=
  ((memLp_yukawa hℓ (integrable_of_memLp_two hf2 hfab) hfab).const_mul _).add hf2

/-- `∫ Y1 conj Y1 = -∫ Y2 conj ψ`. -/
theorem integral_Y1_mul_conj :
    ∫ x, Y1 ℓ f x * conj (Y1 ℓ f x) = -∫ x, Y2 ℓ f x * conj (yukawa ℓ f x) := by
  have hf := integrable_of_memLp_two hf2 hfab
  obtain ⟨M, hM⟩ := exists_yukawa_bdd hℓ hf hfab
  have hφ : TestLike (fun x => conj (yukawa ℓ f x)) (fun x => conj (Y1 ℓ f x)) :=
    { deriv := fun x => (hasDerivAt_yukawa hℓ hf x).star
      int := integrable_conj (integrable_yukawa hℓ hf hfab)
      int' := integrable_conj (integrable_Y1 hℓ hf hfab)
      bdd := ⟨M, fun x => by simpa only [Complex.norm_conj] using hM x⟩ }
  have hbdd : ∀ᵐ x, ‖conj (yukawa ℓ f x)‖ ≤ M :=
    Eventually.of_forall fun x => by simpa only [Complex.norm_conj] using hM x
  have hmeas : AEStronglyMeasurable (fun x => conj (yukawa ℓ f x)) :=
    (continuous_yukawa hℓ hf).star.aestronglyMeasurable
  exact integral_Y1_mul_deriv hℓ hf hφ (hf.mul_bdd hmeas hbdd)
    ((integrable_yukawa hℓ hf hfab).mul_bdd hmeas hbdd)

/-- The energy identity `∫|f|² = ℓ⁴∫|ψ|² + 2ℓ²∫|ψ'|² + ∫|ψ''|²`. -/
theorem energy_integral :
    ∫ x, ‖f x‖ ^ 2 = (ℓ : ℝ) ^ 4 * (∫ x, ‖yukawa ℓ f x‖ ^ 2) +
      2 * (ℓ : ℝ) ^ 2 * (∫ x, ‖Y1 ℓ f x‖ ^ 2) + ∫ x, ‖Y2 ℓ f x‖ ^ 2 := by
  have hf := integrable_of_memLp_two hf2 hfab
  have hψ := memLp_yukawa hℓ hf hfab
  have h1 := memLp_Y1 hℓ hf hfab
  have h2 := memLp_Y2 hℓ hf2 hfab
  -- pointwise expansion of `|f|² = |Y2 - ℓ²ψ|²`
  have hpt : ∀ x, ‖f x‖ ^ 2 = ‖Y2 ℓ f x‖ ^ 2 -
      2 * ((ℓ : ℝ) ^ 2) * (Y2 ℓ f x * conj (yukawa ℓ f x)).re +
      ((ℓ : ℝ) ^ 2) ^ 2 * ‖yukawa ℓ f x‖ ^ 2 := by
    intro x
    rw [← norm_sub_real_mul_sq]
    congr 2
    unfold Y2
    push_cast
    ring
  have hprod : Integrable fun x => Y2 ℓ f x * conj (yukawa ℓ f x) := by
    have := h2.integrable_mul (hψ.star)
    simpa [Pi.mul_def] using this
  have hre : Integrable fun x => (Y2 ℓ f x * conj (yukawa ℓ f x)).re := hprod.re
  have i2 := integrable_norm_sq h2
  have iψ := integrable_norm_sq hψ
  have hA : Integrable fun x => ‖Y2 ℓ f x‖ ^ 2 -
      2 * ((ℓ : ℝ) ^ 2) * (Y2 ℓ f x * conj (yukawa ℓ f x)).re := i2.sub (hre.const_mul _)
  simp_rw [hpt]
  rw [integral_add hA (iψ.const_mul _), integral_sub i2 (hre.const_mul _),
    integral_const_mul, integral_const_mul]
  -- `∫ Re(Y2 conj ψ) = -∫ |Y1|²`
  have hkey : ∫ x, (Y2 ℓ f x * conj (yukawa ℓ f x)).re = -∫ x, ‖Y1 ℓ f x‖ ^ 2 := by
    have e1 : ∫ x, (Y2 ℓ f x * conj (yukawa ℓ f x)).re =
        (∫ x, Y2 ℓ f x * conj (yukawa ℓ f x)).re := integral_re hprod
    have e2 : ∫ x, Y1 ℓ f x * conj (Y1 ℓ f x) = ((∫ x, ‖Y1 ℓ f x‖ ^ 2 : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      congr 1
      funext x
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have e3 := integral_Y1_mul_conj hℓ hf2 hfab
    rw [e2] at e3
    have e4 : ∫ x, Y2 ℓ f x * conj (yukawa ℓ f x) = -((∫ x, ‖Y1 ℓ f x‖ ^ 2 : ℝ) : ℂ) := by
      rw [e3]; ring
    rw [e1, e4]
    simp
  rw [hkey]
  ring

end Energy

end NonUniqueEuler.Sob.EnergyAux
