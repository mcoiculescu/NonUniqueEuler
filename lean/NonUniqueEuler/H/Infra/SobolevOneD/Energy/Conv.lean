import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import NonUniqueEuler.H.Infra.SobolevOneD.Energy.Kernel

/-!
# Helper for `P/Infra/SobolevOneD/Energy`: the convolutions `k0 ⋆ f` and `k1 ⋆ f`

For `f` integrable and vanishing a.e. outside `[a, b]`:
* `psi0 L f = k0 ⋆ f` is differentiable with `psi0' = -L psi1`, `psi1 = k1 ⋆ f`
  (`hasDerivAt_psi0`, differentiation under the integral sign with the Lipschitz bound of `k0`);
* both are bounded by `C e^{-L|x-a|}`, hence integrable, bounded and in `L²`;
* tested against a `TestLike` function (Fubini + `Kernel.lean`):
  `∫ psi0 φ' = L ∫ psi1 φ` and `∫ psi1 φ' = -2 ∫ f φ + L ∫ psi0 φ`.

Pitfall: `∫ x, A + B` parses as `∫ x, (A + B)`; parenthesize integrals followed by `+`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace NonUniqueEuler.Sob.EnergyAux

/-- `k0 ⋆ f`. -/
def psi0 (L : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ := ∫ y, (k0 L (x - y) : ℂ) * f y

/-- `k1 ⋆ f`. -/
def psi1 (L : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ := ∫ y, (k1 L (x - y) : ℂ) * f y

/-! ### Fubini -/

theorem aestronglyMeasurable_kernel_prod {K : ℝ → ℝ} (hK : Measurable K) {g θ : ℝ → ℂ}
    (hg : AEStronglyMeasurable g) (hθ : AEStronglyMeasurable θ) :
    AEStronglyMeasurable (fun z : ℝ × ℝ => (K (z.1 - z.2) : ℂ) * g z.2 * θ z.1)
      (volume.prod volume) := by
  refine (AEStronglyMeasurable.mul ?_ hg.comp_snd).mul hθ.comp_fst
  exact (Complex.measurable_ofReal.comp (hK.comp (measurable_fst.sub measurable_snd))).aestronglyMeasurable

theorem integrable_kernel_prod {K : ℝ → ℝ} (hK : Measurable K) (hKb : ∀ z, |K z| ≤ 1)
    {g θ : ℝ → ℂ} (hg : Integrable g) (hθ : Integrable θ) :
    Integrable (fun z : ℝ × ℝ => (K (z.1 - z.2) : ℂ) * g z.2 * θ z.1) (volume.prod volume) := by
  refine (hθ.norm.mul_prod hg.norm).mono'
    (aestronglyMeasurable_kernel_prod hK hg.aestronglyMeasurable hθ.aestronglyMeasurable) ?_
  refine Eventually.of_forall fun z => ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 := hKb (z.1 - z.2)
  have h2 := norm_nonneg (g z.2)
  have h3 := norm_nonneg (θ z.1)
  calc |K (z.1 - z.2)| * ‖g z.2‖ * ‖θ z.1‖ ≤ 1 * ‖g z.2‖ * ‖θ z.1‖ := by gcongr
    _ = ‖θ z.1‖ * ‖g z.2‖ := by ring

/-- Fubini for a bounded kernel: `∫ (K ⋆ g) θ = ∫ g (Kᵀ θ)`. -/
theorem integral_conv_mul {K : ℝ → ℝ} (hK : Measurable K) (hKb : ∀ z, |K z| ≤ 1)
    {g θ : ℝ → ℂ} (hg : Integrable g) (hθ : Integrable θ) :
    ∫ x, (∫ y, (K (x - y) : ℂ) * g y) * θ x = ∫ y, g y * ∫ x, (K (x - y) : ℂ) * θ x := by
  have hint := integrable_kernel_prod hK hKb hg hθ
  have h1 : ∀ x, (∫ y, (K (x - y) : ℂ) * g y) * θ x = ∫ y, (K (x - y) : ℂ) * g y * θ x :=
    fun x => (integral_mul_const _ _).symm
  have h2 : ∀ y, g y * ∫ x, (K (x - y) : ℂ) * θ x = ∫ x, (K (x - y) : ℂ) * g y * θ x := by
    intro y
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  simp_rw [h1, h2]
  exact integral_integral_swap (f := fun x y => (K (x - y) : ℂ) * g y * θ x) hint

theorem integrable_conv_dual {K : ℝ → ℝ} (hK : Measurable K) (hKb : ∀ z, |K z| ≤ 1)
    {g θ : ℝ → ℂ} (hg : Integrable g) (hθ : Integrable θ) :
    Integrable (fun y => g y * ∫ x, (K (x - y) : ℂ) * θ x) := by
  have hint := (integrable_kernel_prod hK hKb hg hθ).integral_prod_right
  refine hint.congr (Eventually.of_forall fun y => ?_)
  simp only
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

theorem aestronglyMeasurable_conv {K : ℝ → ℝ} (hK : Measurable K) {g : ℝ → ℂ}
    (hg : AEStronglyMeasurable g) :
    AEStronglyMeasurable (fun x => ∫ y, (K (x - y) : ℂ) * g y) := by
  have h : AEStronglyMeasurable (fun z : ℝ × ℝ => (K (z.1 - z.2) : ℂ) * g z.2)
      (volume.prod volume) :=
    (Complex.measurable_ofReal.comp (hK.comp (measurable_fst.sub measurable_snd))).aestronglyMeasurable.mul
      hg.comp_snd
  exact h.integral_prod_right'

/-! ### Pointwise bounds -/

theorem k0_le_shift {L : ℝ} (hL : 0 ≤ L) {a b y : ℝ} (hy : y ∈ Icc a b) (x : ℝ) :
    k0 L (x - y) ≤ Real.exp (L * (b - a)) * k0 L (x - a) := by
  unfold k0
  rw [← Real.exp_add, Real.exp_le_exp]
  have h1 : |x - a| ≤ |x - y| + |y - a| := abs_sub_le x y a
  have h2 : |y - a| = y - a := abs_of_nonneg (by linarith [hy.1])
  have h3 : |x - a| - |x - y| ≤ b - a := by linarith [hy.2]
  have := mul_le_mul_of_nonneg_left h3 hL
  nlinarith

/-- The common bound `‖K ⋆ f (x)‖ ≤ e^{L(b-a)} ‖f‖₁ e^{-L|x-a|}` for `|K| ≤ k0`. -/
theorem norm_conv_le {L : ℝ} (hL : 0 ≤ L) {K : ℝ → ℝ} (hK : ∀ z, |K z| ≤ k0 L z) {f : ℝ → ℂ}
    (hf : Integrable f) {a b : ℝ} (hfab : ∀ᵐ x, x ∉ Icc a b → f x = 0) (x : ℝ) :
    ‖∫ y, (K (x - y) : ℂ) * f y‖ ≤
      (Real.exp (L * (b - a)) * ∫ y, ‖f y‖) * k0 L (x - a) := by
  have hb : Integrable fun y => Real.exp (L * (b - a)) * k0 L (x - a) * ‖f y‖ :=
    hf.norm.const_mul _
  refine (norm_integral_le_of_norm_le hb ?_).trans_eq ?_
  · filter_upwards [hfab] with y hy
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    by_cases hmem : y ∈ Icc a b
    · exact mul_le_mul_of_nonneg_right ((hK _).trans (k0_le_shift hL hmem x)) (norm_nonneg _)
    · rw [hy hmem, norm_zero, mul_zero]
      exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (k0_pos _ _).le) le_rfl
  · rw [integral_const_mul]
    ring

/-- A function bounded by `C e^{-L|x-a|}` is integrable. -/
theorem integrable_of_le_k0 {L : ℝ} (hL : 0 < L) {g : ℝ → ℂ} (hg : AEStronglyMeasurable g)
    {C a : ℝ} (hgle : ∀ x, ‖g x‖ ≤ C * k0 L (x - a)) : Integrable g :=
  (((integrable_k0 hL).comp_sub_right a).const_mul C).mono' hg (Eventually.of_forall hgle)

/-- A function bounded by `C e^{-L|x-a|}` is in `L²`. -/
theorem memLp_two_of_le_k0 {L : ℝ} (hL : 0 < L) {g : ℝ → ℂ} (hg : AEStronglyMeasurable g)
    {C a : ℝ} (hgle : ∀ x, ‖g x‖ ≤ C * k0 L (x - a)) : MemLp g 2 := by
  have hm : MemLp (fun x => C * k0 L (x - a)) 2 := by
    rw [memLp_two_iff_integrable_sq (by
      exact (((continuous_k0 L).comp (continuous_id.sub continuous_const)).const_mul
        C).aestronglyMeasurable)]
    have : (fun x => (C * k0 L (x - a)) ^ 2) = fun x => C ^ 2 * k0 (2 * L) (x - a) := by
      funext x; rw [mul_pow, k0_sq]
    rw [this]
    exact ((integrable_k0 (by linarith)).comp_sub_right a).const_mul _
  refine hm.of_le hg (Eventually.of_forall fun x => ?_)
  refine (hgle x).trans ?_
  rw [Real.norm_eq_abs]
  exact le_abs_self _

/-! ### Regularity of `psi0` -/

theorem integrable_k0_sub_mul' (L : ℝ) {hL : 0 ≤ L} (x : ℝ) {g : ℝ → ℂ} (hg : Integrable g) :
    Integrable (fun y => (k0 L (x - y) : ℂ) * g y) :=
  integrable_ofReal_mul (e := fun y => k0 L (x - y))
    ((continuous_k0 L).measurable.comp (measurable_const.sub measurable_id))
    (fun y => by rw [abs_of_pos (k0_pos _ _)]; exact k0_le_one hL _) hg

theorem ae_ne_pt (x₀ : ℝ) : ∀ᵐ y : ℝ, y ≠ x₀ := by
  have : (volume : Measure ℝ) {x₀} = 0 := measure_singleton x₀
  filter_upwards [compl_mem_ae_iff.2 this] with y hy using hy

/-- `psi0' = -L psi1`. -/
theorem hasDerivAt_psi0 {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℂ} (hf : Integrable f) (x₀ : ℝ) :
    HasDerivAt (psi0 L f) (-L * psi1 L f x₀) x₀ := by
  have hmeas : ∀ x, AEStronglyMeasurable (fun y => (k0 L (x - y) : ℂ) * f y) :=
    fun x => (integrable_k0_sub_mul' L (hL := hL) x hf).aestronglyMeasurable
  have hF'm : AEStronglyMeasurable (fun y => ((-L * k1 L (x₀ - y) : ℝ) : ℂ) * f y) := by
    refine AEStronglyMeasurable.mul ?_ hf.aestronglyMeasurable
    exact (Complex.measurable_ofReal.comp (measurable_const.mul
      ((measurable_k1 L).comp (measurable_const.sub measurable_id)))).aestronglyMeasurable
  have key := hasDerivAt_integral_of_dominated_loc_of_lip (x₀ := x₀) (s := univ)
    (F := fun x y => (k0 L (x - y) : ℂ) * f y)
    (F' := fun y => ((-L * k1 L (x₀ - y) : ℝ) : ℂ) * f y)
    (bound := fun y => L * ‖f y‖) univ_mem (Eventually.of_forall hmeas)
    (integrable_k0_sub_mul' L (hL := hL) x₀ hf) hF'm
    (Eventually.of_forall fun y => by
      refine LipschitzOnWith.of_dist_le_mul fun x _ x' _ => ?_
      rw [dist_eq_norm, dist_eq_norm, ← sub_mul, norm_mul, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs, Real.coe_nnabs,
        abs_of_nonneg (mul_nonneg hL (norm_nonneg _))]
      have h := abs_k0_sub_le hL (x - y) (x' - y)
      rw [show x - y - (x' - y) = x - x' by ring] at h
      calc |k0 L (x - y) - k0 L (x' - y)| * ‖f y‖ ≤ (L * |x - x'|) * ‖f y‖ :=
            mul_le_mul_of_nonneg_right h (norm_nonneg _)
        _ = L * ‖f y‖ * ‖x - x'‖ := by rw [Real.norm_eq_abs]; ring)
    (hf.norm.const_mul L)
    (by
      filter_upwards [ae_ne_pt x₀] with y hy
      have hz : x₀ - y ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
      have h1 : HasDerivAt (fun x => k0 L (x - y)) (-L * k1 L (x₀ - y)) x₀ :=
        HasDerivAt.comp_sub_const x₀ y (hasDerivAt_k0 L hz)
      exact h1.ofReal_comp.mul_const (f y))
  refine key.2.congr_deriv ?_
  unfold psi1
  rw [← integral_const_mul]
  congr 1
  funext y
  push_cast
  ring

theorem continuous_psi0 {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (psi0 L f) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_psi0 hL hf x).continuousAt

theorem aestronglyMeasurable_psi1 (L : ℝ) {f : ℝ → ℂ} (hf : Integrable f) :
    AEStronglyMeasurable (psi1 L f) :=
  aestronglyMeasurable_conv (measurable_k1 L) hf.aestronglyMeasurable

theorem norm_psi0_le {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℂ} (hf : Integrable f) {a b : ℝ}
    (hfab : ∀ᵐ x, x ∉ Icc a b → f x = 0) (x : ℝ) :
    ‖psi0 L f x‖ ≤ (Real.exp (L * (b - a)) * ∫ y, ‖f y‖) * k0 L (x - a) :=
  norm_conv_le hL (fun z => (abs_of_pos (k0_pos L z)).le) hf hfab x

theorem norm_psi1_le {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℂ} (hf : Integrable f) {a b : ℝ}
    (hfab : ∀ᵐ x, x ∉ Icc a b → f x = 0) (x : ℝ) :
    ‖psi1 L f x‖ ≤ (Real.exp (L * (b - a)) * ∫ y, ‖f y‖) * k0 L (x - a) :=
  norm_conv_le hL (fun z => (abs_k1 L z).le) hf hfab x

theorem bound_nonneg (L a b : ℝ) (f : ℝ → ℂ) : 0 ≤ Real.exp (L * (b - a)) * ∫ y, ‖f y‖ :=
  mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => norm_nonneg _)

/-! ### Testing against `TestLike` functions -/

/-- `∫ psi0 φ' = L ∫ psi1 φ`. -/
theorem integral_psi0_mul_deriv {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ} (hf : Integrable f)
    {φ φ' : ℝ → ℂ} (hφ : TestLike φ φ') :
    ∫ x, psi0 L f x * φ' x = L * ∫ x, psi1 L f x * φ x := by
  unfold psi0 psi1
  rw [integral_conv_mul (continuous_k0 L).measurable
      (fun z => by rw [abs_of_pos (k0_pos _ _)]; exact k0_le_one hL.le z) hf hφ.int',
    integral_conv_mul (measurable_k1 L) (abs_k1_le_one hL.le) hf hφ.int,
    ← integral_const_mul]
  congr 1
  funext y
  rw [integral_k0_mul_deriv hL hφ y]
  ring

/-- `∫ psi1 φ' = -2 ∫ f φ + L ∫ psi0 φ`. -/
theorem integral_psi1_mul_deriv {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ} (hf : Integrable f)
    {φ φ' : ℝ → ℂ} (hφ : TestLike φ φ') (hfφ : Integrable fun x => f x * φ x) :
    ∫ x, psi1 L f x * φ' x = -2 * (∫ x, f x * φ x) + L * ∫ x, psi0 L f x * φ x := by
  have hk0b : ∀ z, |k0 L z| ≤ 1 := fun z => by
    rw [abs_of_pos (k0_pos _ _)]; exact k0_le_one hL.le z
  unfold psi0 psi1
  rw [integral_conv_mul (measurable_k1 L) (abs_k1_le_one hL.le) hf hφ.int',
    integral_conv_mul (continuous_k0 L).measurable hk0b hf hφ.int]
  have h2 := integrable_conv_dual (continuous_k0 L).measurable hk0b hf hφ.int
  have : ∀ y, f y * ∫ x, (k1 L (x - y) : ℂ) * φ' x =
      -2 * (f y * φ y) + L * (f y * ∫ x, (k0 L (x - y) : ℂ) * φ x) := by
    intro y
    rw [integral_k1_mul_deriv hL hφ y]
    ring
  simp_rw [this]
  rw [integral_add (hfφ.const_mul _) (h2.const_mul _), integral_const_mul, integral_const_mul]

end NonUniqueEuler.Sob.EnergyAux
