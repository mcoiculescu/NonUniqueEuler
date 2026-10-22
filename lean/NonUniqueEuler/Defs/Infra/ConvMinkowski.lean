import NonUniqueEuler.Statement.WeakSolution
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Convolution

/-!
# Convolution majorants on `ℂ` (definitions; library I-CONV)

Manuscript-independent infrastructure (library I-CONV). The manuscript's
convolution bounds (`lem:BS-basic`(b),(c),(e), `lem:velocity`(a),(b) with `p = 2` (D9),
`lem:LpLinf`) are all bounds on the nonnegative majorant `(|K| ⋆ |g|)(x)`. We define it as a
lower Lebesgue integral, so that it is always meaningful (possibly `∞`) and no integrability
side condition is needed to *state* a bound.

Definition.
* `convAbs K g x = ∫⁻ y, ‖K (x - y)‖ₑ * ‖g y‖ₑ`, i.e. `(|K| ⋆ |g|)(x)` in `ℝ≥0∞`.

Fully proved basic lemmas:
* `enorm_integral_conv_le : ‖∫ y, K (x - y) * g y‖ₑ ≤ convAbs K g x`;
* `enorm_velocity_le : ‖velocity g x‖ₑ ≤ convAbs biotSavartKernel g x`;
* `convAbs_mono_kernel`, `convAbs_mono_right`: monotonicity in `|K|` and `|g|`;
* `velocity_eq_convolution`: `velocity g` is Mathlib's convolution
  `(ofReal ∘ g) ⋆[mul ℝ ℂ] biotSavartKernel` (so `MeasureTheory.convolution` lemmas apply, e.g.
  `HasCompactSupport.hasFDerivAt_convolution_left` for `g ∈ C_c^∞`, `lem:BS-basic`(d)).

The theorems that need work (Minkowski's integral inequality, `L¹ ⋆ L^p`, `L^∞ ⋆ L¹`, Hölder,
measurability, a.e. finiteness) are in `NonUniqueEuler/I/Infra/ConvMinkowski/*.lean`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace NonUniqueEuler.Conv

/-- The convolution majorant `(|K| ⋆ |g|)(x) = ∫⁻ ‖K(x - y)‖ ‖g(y)‖ dy`. -/
def convAbs {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (K : ℂ → E) (g : ℂ → F) (x : ℂ) : ℝ≥0∞ :=
  ∫⁻ y, ‖K (x - y)‖ₑ * ‖g y‖ₑ

/-! ### Basic lemmas (fully proved) -/

theorem convAbs_mono_kernel {E E' F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup E']
    [NormedAddCommGroup F] {K : ℂ → E} {K' : ℂ → E'} (g : ℂ → F)
    (h : ∀ z, ‖K z‖ₑ ≤ ‖K' z‖ₑ) (x : ℂ) : convAbs K g x ≤ convAbs K' g x :=
  lintegral_mono fun y => mul_le_mul_left (h (x - y)) _

theorem convAbs_mono_right {E F F' : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedAddCommGroup F'] (K : ℂ → E) {g : ℂ → F} {g' : ℂ → F'}
    (h : ∀ y, ‖g y‖ₑ ≤ ‖g' y‖ₑ) (x : ℂ) : convAbs K g x ≤ convAbs K g' x :=
  lintegral_mono fun y => mul_le_mul_right (h y) _

/-- The modulus of a convolution integral is bounded by the majorant (with no integrability
hypothesis: the Bochner integral is `0` when the integrand is not integrable). -/
theorem enorm_integral_conv_le (K : ℂ → ℂ) (g : ℂ → ℝ) (x : ℂ) :
    ‖∫ y, K (x - y) * (g y : ℂ)‖ₑ ≤ convAbs K g x := by
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  refine lintegral_congr fun y => ?_
  rw [enorm_mul]
  congr 1
  simp only [enorm, Complex.nnnorm_real]

theorem enorm_velocity_le (g : ℂ → ℝ) (x : ℂ) :
    ‖velocity g x‖ₑ ≤ convAbs biotSavartKernel g x :=
  enorm_integral_conv_le biotSavartKernel g x

/-- The velocity is Mathlib's convolution `g ⋆ K` (with the product `ℂ × ℂ → ℂ`). -/
theorem velocity_eq_convolution (g : ℂ → ℝ) :
    velocity g = MeasureTheory.convolution (fun y => (g y : ℂ)) biotSavartKernel
      (ContinuousLinearMap.mul ℝ ℂ) volume := by
  funext x
  simp only [velocity, MeasureTheory.convolution_def, ContinuousLinearMap.mul_apply']
  congr 1
  funext y
  ring

end NonUniqueEuler.Conv
