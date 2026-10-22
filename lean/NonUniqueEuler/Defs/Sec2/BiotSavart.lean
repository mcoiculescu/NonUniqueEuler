import NonUniqueEuler.Defs.Sec2.Conventions
import NonUniqueEuler.Defs.Infra.Multipole
import NonUniqueEuler.Defs.Infra.ConvMinkowski
import Mathlib.Data.Real.ConjExponents

/-!
# Section 2: the Biot–Savart law (definitions)

Definitions for `02_prelim.tex` §2.2 (`02_prelim.tex:133-512`):
`lem:BS-basic`, `lem:velocity`, `lem:LpLinf`, `lem:hollow`, `lem:ext-multipole`, and the complex
form of the velocity.

The kernel `K_BS = biotSavartKernel` and the velocity `v = K_BS ∗ g = velocity g` of a **real**
vorticity `g : ℂ → ℝ` are in the statement layer (`Statement/Plane.lean`; a real vector field is
encoded in `ℂ`, D1, D6). This file adds:

* `kernelNear = 1_{B₁} K_BS`, `kernelFar = 1_{ℝ²∖B₁} K_BS` (`02_prelim.tex:135-139`);
* `kernelComp i z = (K_BS)_i(z)`, the two real components (`lem:BS-basic`(a));
* `velocityRe g`, `velocityIm g`: the Biot–Savart law for a **complex** vorticity
  `g = g₁ + i g₂` (functions are complex valued unless said otherwise, `02_prelim.tex:52`): the
  complex vector field `K_BS ∗ g = K_BS ∗ g₁ + i K_BS ∗ g₂` is represented by its real part
  `K_BS ∗ g₁ = velocityRe g` and its imaginary part `K_BS ∗ g₂ = velocityIm g`, each a real vector
  field encoded in `ℂ` (used by `lem:Hk-calculus`(3) and Section 5);
* `normHC2 k u₁ u₂`: the `H^k` norm of the complex vector field `u₁ + i u₂` (`u₁, u₂` real vector
  fields in `ℂ`), summed over the entries (`02_prelim.tex:62-64`);
* `complexVelocity g = u₁ - i u₂ = conj (velocity g)`, with
  `complexVelocity_eq : u₁ - i u₂ = (2πi)⁻¹ ∫ g(w)/(z - w) dw` (`02_prelim.tex:430-433`,
  eq:complex-velocity of `07_several_rings.tex:49`; from I-MULT);
* `monopole g`, `extField g = velocity g - monopole g` (the field `E` of `lem:ext-multipole`);
* the explicit constants `cLpLinf p = c_p` (`lem:LpLinf`) and `cExtMultipole m q = C_{m,q}`
  (`lem:ext-multipole`), which later definitions use (`06_datum.tex:365`,
  `07_several_rings.tex:126`).

Majorants `(|K_BS| ∗ |g|)(x)` are `Conv.convAbs biotSavartKernel g x : ℝ≥0∞` (I-CONV); the
angular average `ν̄` of `lem:hollow` is `Polar.angAvg ν`; the stream function `ψ` of
`lem:BS-basic`(d) is `Multipole.logPotentialReal g`. All lemmas in this file are fully proved.
-/

noncomputable section

open MeasureTheory Set Metric ComplexConjugate
open scoped ENNReal

namespace NonUniqueEuler.BS

/-- The near part `K_near = 1_{B₁} K_BS` of the Biot–Savart kernel (`02_prelim.tex:135-136`). -/
def kernelNear (z : ℂ) : ℂ :=
  (ball (0 : ℂ) 1).indicator biotSavartKernel z

/-- The far part `K_far = 1_{ℝ²∖B₁} K_BS` of the Biot–Savart kernel (`02_prelim.tex:135-136`). -/
def kernelFar (z : ℂ) : ℂ :=
  (ball (0 : ℂ) 1)ᶜ.indicator biotSavartKernel z

/-- The real components `(K_BS)₁(z) = -z₂/(2π|z|²)`, `(K_BS)₂(z) = z₁/(2π|z|²)` of the kernel
(`lem:BS-basic`(a), `02_prelim.tex:184-185`); index `0, 1` for the manuscript's `1, 2`. -/
def kernelComp (i : Fin 2) (z : ℂ) : ℝ :=
  Prelim.comp2 i (biotSavartKernel z)

/-- The real part `K_BS ∗ (Re g)` of the Biot–Savart velocity of a complex vorticity `g`
(a real vector field in `ℂ`). -/
def velocityRe (g : ℂ → ℂ) : ℂ → ℂ :=
  velocity fun y => (g y).re

/-- The imaginary part `K_BS ∗ (Im g)` of the Biot–Savart velocity of a complex vorticity `g`
(a real vector field in `ℂ`). -/
def velocityIm (g : ℂ → ℂ) : ℂ → ℂ :=
  velocity fun y => (g y).im

/-- `‖u₁ + i u₂‖_{H^k}` for the complex vector field with real part `u₁` and imaginary part `u₂`
(real vector fields in `ℂ`): `(‖u₁‖²_{H^k} + ‖u₂‖²_{H^k})^{1/2}`, which is the sum over the
entries of `02_prelim.tex:62-64`. Junk unless `Sob.MemH k u₁` and `Sob.MemH k u₂`. -/
def normHC2 (k : ℕ) (u₁ u₂ : ℂ → ℂ) : ℝ :=
  Real.sqrt (Sob.normH k u₁ ^ 2 + Sob.normH k u₂ ^ 2)

/-- The complex velocity `u₁ - i u₂ = conj (K_BS ∗ g)` of a real vorticity
(`02_prelim.tex:430-433`, `07_several_rings.tex:49`). -/
def complexVelocity (g : ℂ → ℝ) (z : ℂ) : ℂ :=
  conj (velocity g z)

/-- The monopole `(2π)⁻¹ (∫ g) x^⊥/|x|² = (∫ g) K_BS(x)` of a real vorticity
(`lem:ext-multipole`, `02_prelim.tex:477-478`). -/
def monopole (g : ℂ → ℝ) (x : ℂ) : ℂ :=
  ((∫ y, g y : ℝ) : ℂ) * biotSavartKernel x

/-- The field `E = K_BS ∗ g - monopole` of `lem:ext-multipole` (`02_prelim.tex:476-478`). -/
def extField (g : ℂ → ℝ) (x : ℂ) : ℂ :=
  velocity g x - monopole g x

/-- The constant `c_p = (2π/(2 - p'))^{1/p'}`, `p' = p/(p-1)`, of `lem:LpLinf`
(`02_prelim.tex:389-390`); meaningful for `2 < p < ∞`. -/
def cLpLinf (p : ℝ) : ℝ :=
  (2 * Real.pi / (2 - p.conjExponent)) ^ (1 / p.conjExponent)

/-- The constant `C_{m,q} = 2^q/(2π) · sup_{0<ρ≤1/2} ρ^{-m} Σ_{l ∈ mℕ} (l+q)^q ρ^l` of
`lem:ext-multipole` (`02_prelim.tex:479-482`), with `l = m(j+1)`, `j ≥ 0`. Its finiteness (the
supremum is attained at `ρ = 1/2`) is part of the lemma. -/
def cExtMultipole (m q : ℕ) : ℝ :=
  2 ^ q / (2 * Real.pi) *
    ⨆ ρ : Ioc (0 : ℝ) (1 / 2),
      ((ρ : ℝ) ^ m)⁻¹ * ∑' j : ℕ, (((m * (j + 1) + q : ℕ) : ℝ)) ^ q * (ρ : ℝ) ^ (m * (j + 1))

/-! ### Basic lemmas (fully proved) -/

theorem kernelNear_add_kernelFar (z : ℂ) : kernelNear z + kernelFar z = biotSavartKernel z :=
  indicator_self_add_compl_apply _ _ _

theorem kernelNear_of_norm_lt {z : ℂ} (hz : ‖z‖ < 1) : kernelNear z = biotSavartKernel z := by
  simp [kernelNear, indicator_of_mem, mem_ball_zero_iff.mpr hz]

theorem kernelNear_of_one_le_norm {z : ℂ} (hz : 1 ≤ ‖z‖) : kernelNear z = 0 := by
  apply indicator_of_notMem
  simpa [mem_ball_zero_iff] using hz

theorem kernelFar_of_norm_lt {z : ℂ} (hz : ‖z‖ < 1) : kernelFar z = 0 := by
  apply indicator_of_notMem
  simpa [mem_ball_zero_iff] using hz

theorem kernelFar_of_one_le_norm {z : ℂ} (hz : 1 ≤ ‖z‖) : kernelFar z = biotSavartKernel z := by
  apply indicator_of_mem
  simpa [mem_ball_zero_iff] using hz

theorem kernelComp_zero (z : ℂ) : kernelComp 0 z = -z.im / (2 * Real.pi * ‖z‖ ^ 2) := by
  simp only [kernelComp, Prelim.comp2_zero, biotSavartKernel]
  rw [Complex.div_ofReal_re]
  simp

theorem kernelComp_one (z : ℂ) : kernelComp 1 z = z.re / (2 * Real.pi * ‖z‖ ^ 2) := by
  simp only [kernelComp, Prelim.comp2_one, biotSavartKernel]
  rw [Complex.div_ofReal_im]
  simp

@[simp] theorem velocityRe_ofReal (g : ℂ → ℝ) : velocityRe (fun y => (g y : ℂ)) = velocity g := by
  simp [velocityRe]

@[simp] theorem velocityIm_ofReal (g : ℂ → ℝ) : velocityIm (fun y => (g y : ℂ)) = 0 := by
  funext x
  simp [velocityIm, velocity]

theorem normHC2_nonneg (k : ℕ) (u₁ u₂ : ℂ → ℂ) : 0 ≤ normHC2 k u₁ u₂ := Real.sqrt_nonneg _

/-- The complex form of the Biot–Savart law, `u₁ - i u₂ = (2πi)⁻¹ ∫ g(w)/(z - w) dw`, for every
`z` (I-MULT, `Multipole.velocity_eq_conj_cauchyTransform`). -/
theorem complexVelocity_eq (g : ℂ → ℝ) (z : ℂ) :
    complexVelocity g z =
      (2 * Real.pi * Complex.I)⁻¹ * Multipole.cauchyTransform (fun w => (g w : ℂ)) z := by
  rw [complexVelocity, Multipole.velocity_eq_conj_cauchyTransform, Complex.conj_conj]

theorem velocity_eq_conj_complexVelocity (g : ℂ → ℝ) (z : ℂ) :
    velocity g z = conj (complexVelocity g z) := by
  rw [complexVelocity, Complex.conj_conj]

theorem extField_add_monopole (g : ℂ → ℝ) (x : ℂ) :
    extField g x + monopole g x = velocity g x := by
  simp [extField]

end NonUniqueEuler.BS
