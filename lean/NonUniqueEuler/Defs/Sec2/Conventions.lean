import NonUniqueEuler.Statement.Plane
import NonUniqueEuler.Defs.Infra.Sobolev
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Section 2 conventions: coordinates, derivatives of vector fields, `⟨t⟩`, the `L²` pairing

Definitions for the conventions of `02_prelim.tex` §2.1
(`02_prelim.tex:11-131`).

The plane is `ℂ` (decision D1); a real vector field `u = (u₁, u₂)` is a function `u : ℂ → ℂ`,
`u x = u₁ x + i u₂ x`; derivatives are Fréchet derivatives, `∂₁ = ∂_1`, `∂₂ = ∂_i` (D2).
Sobolev norms are those of I-HK (`NonUniqueEuler.Sob`, `Defs/Infra/Sobolev.lean`).

* `e2`, `comp2`: the standard basis `e₁ = 1`, `e₂ = i` of `ℝ² = ℂ` and the coordinates `x₁, x₂`;
* `pd l h x = ∂_l h(x)` (classical), `gradEntry u i l x = ∂_l u_i(x)` (an entry of the matrix
  `∇u = (∂_l u_i)_{i,l}`, `02_prelim.tex:48-50`);
* `divergence u = ∂₁u₁ + ∂₂u₂ = tr ∇u`, `curl u = ∂₁u₂ - ∂₂u₁` (`02_prelim.tex:42-50`);
* `grad g`, `perpGrad g = ∇^⊥ g = (-∂₂ g, ∂₁ g)` of a real scalar `g`, as complex numbers
  (`02_prelim.tex:36-37`);
* `jap t = ⟨t⟩ = (1 + t²)^{1/2}` (`02_prelim.tex:82`);
* `innerL2 f g = ⟨f, g⟩_{L²} = ∫ f ḡ` (the manuscript's convention, `04_ring.tex:583`);
* `normL1Lp p g = ‖g‖_{L¹ ∩ L^p} = ‖g‖_{L¹} + ‖g‖_{L^p}` (`02_prelim.tex:122-124`);
* `gradL2 u = ‖∇u‖_{L²}`, `gradNormH k u = ‖∇u‖_{H^k}` (sums over the entries, weak derivatives,
  `02_prelim.tex:62-66`) and `HasGradH k u` (`∇u ∈ H^k`, i.e. the weak first derivatives exist
  and lie in `H^k`);
* `partialDR γ g = ∂^γ g` for a real function `g` (classical; `Sob.partialD` is for complex `g`);
* `gradAbs g x = |∇g(x)| = (|∂₁g|² + |∂₂g|²)^{1/2}` (classical; complex scalars, and real vector
  fields in `ℂ`, where it is the Euclidean norm of the matrix `∇u`, `02_prelim.tex:14-17`);
* `IsWeaklyDivFree u`: `div u = 0` in `𝒟'(ℝ²)` (`lem:BS-basic`(e)), with the integrability of
  `u · ∇φ` included (so that Lean's junk value `∫ = 0` cannot make it vacuous).

Reused, not redefined: `rot` (`O_θ`), `IsMFoldSymmetric`, `IsRadial`, `biotSavartKernel`
(`K_BS`), `velocity` (statement layer); `Polar.circ` (`Circ_g`), `Polar.angularSector` (`g_ℓ`),
`Polar.angAvg`; `Ip` (eq:Ip); `Equimeas.IsLipO` (`Lip₀`); `Sob.MemH`, `Sob.normH`, `Sob.partialD`,
`Sob.weakPartial`, `Sob.dotGrad`, `Sob.normW1infOn`; `normCk`, `iterDerivArrayNorm` (`|∇^q h|`);
Mathlib's `Real.posLog` (`log₊`), `Real.conjExponent` (`p'`), the Laplacian `Δ` (`open Laplacian`)
and `Metric.ball 0 r` (`B_r`).

All lemmas in this file are fully proved.
-/

noncomputable section

open MeasureTheory Set ComplexConjugate
open scoped ENNReal

namespace NonUniqueEuler.Prelim

/-- The standard basis `e₁ = 1`, `e₂ = i` of `ℝ² = ℂ` (`02_prelim.tex:13-14`; decision D2:
`∂₁ = ∂_{e₁}`, `∂₂ = ∂_{e₂}`). -/
def e2 : Fin 2 → ℂ := ![1, Complex.I]

/-- The coordinates of `z = z₁ + i z₂ ∈ ℝ² = ℂ` (`02_prelim.tex:13-14`):
`comp2 0 z = z₁ = Re z`, `comp2 1 z = z₂ = Im z`. -/
def comp2 (i : Fin 2) (z : ℂ) : ℝ := ![z.re, z.im] i

/-- The classical partial derivative `∂_l h(x) = Dh(x) e_l` (`02_prelim.tex:52-53`), for `h`
with values in any real normed space. -/
def pd {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (l : Fin 2) (h : ℂ → F) (x : ℂ) :
    F :=
  fderiv ℝ h x (e2 l)

/-- The entry `∂_l u_i(x)` of the matrix `∇u = (∂_l u_i)_{i,l=1,2}` of a real vector field
`u = u₁ + i u₂ : ℂ → ℂ` (`02_prelim.tex:48-50`; classical derivative). Indices are `0, 1` for the
manuscript's `1, 2`. -/
def gradEntry (u : ℂ → ℂ) (i l : Fin 2) (x : ℂ) : ℝ :=
  comp2 i (pd l u x)

/-- The divergence `div u = ∂₁u₁ + ∂₂u₂ = tr ∇u` of a real vector field (`02_prelim.tex:49-50`;
classical derivative). -/
def divergence (u : ℂ → ℂ) (x : ℂ) : ℝ :=
  gradEntry u 0 0 x + gradEntry u 1 1 x

/-- The scalar curl `∂₁u₂ - ∂₂u₁` of a real vector field (`02_prelim.tex:42-43`, `lem:BS-basic`(d);
classical derivative). -/
def curl (u : ℂ → ℂ) (x : ℂ) : ℝ :=
  gradEntry u 1 0 x - gradEntry u 0 1 x

/-- The gradient `∇g = (∂₁g, ∂₂g)` of a real scalar function, as the complex number
`∂₁g + i ∂₂g` (classical derivative). Its modulus is the Euclidean norm `|∇g(x)|`, which equals
the operator norm `‖Dg(x)‖` (`norm_fderiv_eq_norm_grad`). -/
def grad (g : ℂ → ℝ) (x : ℂ) : ℂ :=
  ((pd 0 g x : ℝ) : ℂ) + ((pd 1 g x : ℝ) : ℂ) * Complex.I

/-- `∇^⊥ g = (-∂₂g, ∂₁g) = i ∇g` (`02_prelim.tex:36-37`). -/
def perpGrad (g : ℂ → ℝ) (x : ℂ) : ℂ :=
  Complex.I * grad g x

/-- The Japanese bracket `⟨t⟩ = (1 + t²)^{1/2}` (`02_prelim.tex:82`). -/
def jap (t : ℝ) : ℝ :=
  Real.sqrt (1 + t ^ 2)

/-- The `L²` pairing `⟨f, g⟩ = ∫ f ḡ` of complex functions on the plane (the manuscript's
convention, `04_ring.tex:583`; used in `lem:Hk-calculus`(1), `02_prelim.tex:657-660`). The
Bochner integral is `0` if `f ḡ` is not integrable. -/
def innerL2 (f g : ℂ → ℂ) : ℂ :=
  ∫ x, f x * conj (g x)

/-- `‖g‖_{L¹ ∩ L^p} = ‖g‖_{L¹} + ‖g‖_{L^p}` (`02_prelim.tex:122-124`), as a real number (each
term is `0` if infinite: carry `MemLp g 1`, `MemLp g p` next to it). -/
def normL1Lp {E : Type*} [NormedAddCommGroup E] (p : ℝ≥0∞) (g : ℂ → E) : ℝ :=
  (eLpNorm g 1 volume).toReal + (eLpNorm g p volume).toReal

/-- `‖∇u‖_{L²} = (‖∂₁u‖²_{L²} + ‖∂₂u‖²_{L²})^{1/2}` with weak derivatives on the plane
(`02_prelim.tex:62-66`; for a vector field `u : ℂ → ℂ` this is the sum over the four entries
`∂_l u_i`). -/
def gradL2 (u : ℂ → ℂ) : ℝ :=
  Real.sqrt (Sob.l2 (Sob.weakPartial (1, 0) u) ^ 2 + Sob.l2 (Sob.weakPartial (0, 1) u) ^ 2)

/-- `‖∇u‖_{H^k} = (‖∂₁u‖²_{H^k} + ‖∂₂u‖²_{H^k})^{1/2}` with weak derivatives on the plane
(`02_prelim.tex:62-64`: "`‖∇u‖²_{H^k} = Σ_{i,l} ‖∂_l u_i‖²_{H^k}`"). Junk unless `HasGradH k u`. -/
def gradNormH (k : ℕ) (u : ℂ → ℂ) : ℝ :=
  Real.sqrt (Sob.normH k (Sob.weakPartial (1, 0) u) ^ 2 +
    Sob.normH k (Sob.weakPartial (0, 1) u) ^ 2)

/-- `∇u ∈ H^k`: the weak first derivatives `∂₁u`, `∂₂u` on the plane exist and lie in `H^k`
(`k = 0`: `∇u ∈ L²`, as in `lem:velocity`(c)). `u` should be locally integrable for the weak
derivatives to be meaningful. -/
structure HasGradH (k : ℕ) (u : ℂ → ℂ) : Prop where
  deriv : ∀ l : Fin 2, ∃ G : ℂ → ℂ, Sob.MemH k G ∧ Sob.HasWeakDerivOn univ [e2 l] u G

/-- The classical partial derivative `∂^γ g` of a real function `g : ℂ → ℝ`
(`02_prelim.tex:52-53`): the real part of `Sob.partialD γ` of `g` viewed as complex valued (the
imaginary part vanishes). Used e.g. in `lem:BS-basic`(d): `∂^γ (K_BS ∗ g) = K_BS ∗ ∂^γ g`. -/
def partialDR (γ : ℕ × ℕ) (g : ℂ → ℝ) (x : ℂ) : ℝ :=
  (Sob.partialD γ (fun y => (g y : ℂ)) x).re

/-- `|∇g(x)| = (|∂₁g(x)|² + |∂₂g(x)|²)^{1/2}` (classical derivatives), the Euclidean norm of the
array of first derivatives (`02_prelim.tex:14-17`). For a real vector field `u : ℂ → ℂ` this is
the Euclidean (Frobenius) norm `|∇u(x)|` of the matrix `(∂_l u_i)`; for a real scalar `g`,
`gradAbs (fun y => (g y : ℂ)) x = ‖Dg(x)‖` when `g` is differentiable at `x`. -/
def gradAbs (g : ℂ → ℂ) (x : ℂ) : ℝ :=
  Real.sqrt (‖pd 0 g x‖ ^ 2 + ‖pd 1 g x‖ ^ 2)

/-- `div u = 0` in `𝒟'(ℝ²)` (`lem:BS-basic`(e), `02_prelim.tex:177-178`): for every real
`φ ∈ C_c^∞(ℝ²)`, `u · ∇φ` is integrable and `∫ u · ∇φ dx = 0`. -/
def IsWeaklyDivFree (u : ℂ → ℂ) : Prop :=
  ∀ φ : ℂ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
    Integrable (fun x => fderiv ℝ φ x (u x)) ∧ ∫ x, fderiv ℝ φ x (u x) = 0

/-! ### Basic lemmas (fully proved) -/

@[simp] theorem e2_zero : e2 0 = 1 := rfl

@[simp] theorem e2_one : e2 1 = Complex.I := rfl

@[simp] theorem comp2_zero (z : ℂ) : comp2 0 z = z.re := rfl

@[simp] theorem comp2_one (z : ℂ) : comp2 1 z = z.im := rfl

/-- `∂^{(1,0)}` and `∂^{(0,1)}` of I-HK are the derivatives in the directions `e₁`, `e₂`. -/
theorem pdList_one_zero : Sob.pdList (1, 0) = [e2 0] := by
  simp [Sob.pdList]

theorem pdList_zero_one : Sob.pdList (0, 1) = [e2 1] := by
  simp [Sob.pdList]

theorem divergence_eq (u : ℂ → ℂ) (x : ℂ) :
    divergence u x = (fderiv ℝ u x 1).re + (fderiv ℝ u x Complex.I).im := rfl

theorem curl_eq (u : ℂ → ℂ) (x : ℂ) :
    curl u x = (fderiv ℝ u x 1).im - (fderiv ℝ u x Complex.I).re := rfl

/-- The coordinates of `z` determine `z`: `z = comp2 0 z + i comp2 1 z`. -/
theorem eq_comp2 (z : ℂ) : z = ((comp2 0 z : ℝ) : ℂ) + ((comp2 1 z : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp

/-- `Dg(x) z = ⟨∇g(x), z⟩ = ∂₁g z₁ + ∂₂g z₂` for a real scalar `g`. -/
theorem fderiv_apply_eq_inner_grad (g : ℂ → ℝ) (x z : ℂ) :
    fderiv ℝ g x z = (grad g x).re * z.re + (grad g x).im * z.im := by
  have hz : z = (z.re : ℝ) • (1 : ℂ) + (z.im : ℝ) • Complex.I := by
    simp
  conv_lhs => rw [hz]
  rw [map_add, map_smul, map_smul]
  simp [grad, pd, e2, smul_eq_mul, mul_comm]

/-- The operator norm of the derivative of a real scalar function is the Euclidean norm of its
gradient: `‖Dg(x)‖ = |∇g(x)|`. -/
theorem norm_fderiv_eq_norm_grad (g : ℂ → ℝ) (x : ℂ) : ‖fderiv ℝ g x‖ = ‖grad g x‖ := by
  have h : InnerProductSpace.toDual ℝ ℂ (grad g x) = fderiv ℝ g x := by
    ext z
    rw [InnerProductSpace.toDual_apply_apply, fderiv_apply_eq_inner_grad, Complex.inner]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [← h, LinearIsometryEquiv.norm_map]

theorem perpGrad_eq (g : ℂ → ℝ) (x : ℂ) :
    perpGrad g x = ((-(pd 1 g x) : ℝ) : ℂ) + ((pd 0 g x : ℝ) : ℂ) * Complex.I := by
  simp only [perpGrad, grad]
  apply Complex.ext <;> simp

theorem jap_nonneg (t : ℝ) : 0 ≤ jap t := Real.sqrt_nonneg _

theorem one_le_jap (t : ℝ) : 1 ≤ jap t := by
  rw [jap, Real.one_le_sqrt]
  nlinarith [sq_nonneg t]

theorem jap_pos (t : ℝ) : 0 < jap t := lt_of_lt_of_le one_pos (one_le_jap t)

theorem abs_le_jap (t : ℝ) : |t| ≤ jap t := by
  rw [jap]
  apply Real.abs_le_sqrt
  nlinarith [sq_nonneg t]

@[simp] theorem jap_neg (t : ℝ) : jap (-t) = jap t := by simp [jap]

@[simp] theorem jap_zero : jap 0 = 1 := by simp [jap]

theorem jap_sq (t : ℝ) : jap t ^ 2 = 1 + t ^ 2 := by
  rw [jap, Real.sq_sqrt]
  positivity

theorem normL1Lp_nonneg {E : Type*} [NormedAddCommGroup E] (p : ℝ≥0∞) (g : ℂ → E) :
    0 ≤ normL1Lp p g :=
  add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

theorem gradL2_nonneg (u : ℂ → ℂ) : 0 ≤ gradL2 u := Real.sqrt_nonneg _

theorem gradNormH_nonneg (k : ℕ) (u : ℂ → ℂ) : 0 ≤ gradNormH k u := Real.sqrt_nonneg _

theorem gradAbs_nonneg (g : ℂ → ℂ) (x : ℂ) : 0 ≤ gradAbs g x := Real.sqrt_nonneg _

theorem HasGradH.mono_order {k k' : ℕ} {u : ℂ → ℂ} (h : HasGradH k' u) (hk : k ≤ k') :
    HasGradH k u :=
  ⟨fun l => by
    obtain ⟨G, hG, hd⟩ := h.deriv l
    exact ⟨G, hG.mono_order hk, hd⟩⟩

end NonUniqueEuler.Prelim
