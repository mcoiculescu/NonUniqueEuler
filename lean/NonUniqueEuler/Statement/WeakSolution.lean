import NonUniqueEuler.Statement.Plane
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Statement layer: the solution class

Statement layer: definitions and statements only, no proofs.

Manuscript sources (`manuscript/tex/sections/`):
* `02_prelim.tex:101-120`  functions of `(t, x)` and Bochner spaces, identified with
  measurable functions on `I × Ω`; `L^∞(I; L^b)` is "`t ↦ ‖u(t)‖_{L^b}` essentially bounded";
* `02_prelim.tex:122-127`  `X_q(T) = L^∞(0,T; L¹ ∩ L^q(ℝ²))`, the test class `𝒟_T`;
* `02_prelim.tex:515-519`  equimeasurable functions (`def:equimeasurable`);
* `02_prelim.tex:521-543`  weak and renormalized weak solutions (`def:weak`),
  solutions on `[0, T₀)`;
* `03_compactness.tex:46-66`  the same definition written as the transport identity
  `(te)` with field `v = K * ω`, together with the integrability requirements.
* `01_intro.tex:156-163`  `C([0,∞); L^p)` and "distinct elements of `X_q(T)`".

Representation choices (see also `FORMALIZATION_NOTES.md`).
* A space–time function is a curried function `ω : ℝ → ℂ → ℝ`, `ω t x = ω(t, x)`. Membership
  in `X_q(T)` asks for a.e.-strong measurability of `(t, x) ↦ ω t x` on `(0,T) × ℝ²` and for
  `t ↦ ‖ω(t)‖_{L¹} + ‖ω(t)‖_{L^q}` to be essentially bounded on `(0, T)`.
  Two elements of `X_q(T)` are equal iff they agree a.e. on `(0,T) × ℝ²` (`DistinctInX`).
* Test functions are real valued. Since `ω` and `v` are real, the complex-valued test
  functions of the manuscript's general convention give the same class of solutions
  (split `φ` into real and imaginary parts).
* `∂_t φ + v · ∇φ` is written with the partial derivatives `deriv` in `t` and the Fréchet
  derivative in `x` applied to the vector `v`.
* The absolute convergence of every integral in the weak formulation, which the manuscript
  derives from `ω ∈ X_q(T)`, `q > 4/3` (`02_prelim.tex:545-550`), is required explicitly.
  This changes nothing mathematically (the conditions are consequences of membership in
  `X_q(T)`), and it prevents Lean's convention `∫ f = 0` for non-integrable `f` from entering.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace NonUniqueEuler

/-- The space–time slab `(0, T) × ℝ²`. -/
def slab (T : ℝ) : Set (ℝ × ℂ) := Ioo (0 : ℝ) T ×ˢ (univ : Set ℂ)

/-- Membership in `X_q(T) = L^∞(0,T; L¹ ∩ L^q(ℝ²))` (`02_prelim.tex:101-124`):
`ω` is (a.e. strongly) measurable on `(0,T) × ℝ²`, and for almost every `t ∈ (0,T)`,
`ω(t) ∈ L¹ ∩ L^q` with `‖ω(t)‖_{L¹} + ‖ω(t)‖_{L^q} ≤ M` for a constant `M`. -/
structure MemX (q T : ℝ) (ω : ℝ → ℂ → ℝ) : Prop where
  aestronglyMeasurable :
    AEStronglyMeasurable (Function.uncurry ω) (volume.restrict (slab T))
  essBounded : ∃ M : ℝ, ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)),
    MemLp (ω t) 1 ∧ MemLp (ω t) (ENNReal.ofReal q) ∧
      (eLpNorm (ω t) 1 volume).toReal + (eLpNorm (ω t) (ENNReal.ofReal q) volume).toReal ≤ M

/-- Two space–time functions are distinct elements of `X_q(T)` iff they are not a.e. equal on
`(0,T) × ℝ²`. (Equality in `X_q(T)` does not depend on `q`.) -/
def DistinctInX (T : ℝ) (ω₁ ω₂ : ℝ → ℂ → ℝ) : Prop :=
  ¬ (Function.uncurry ω₁ =ᵐ[volume.restrict (slab T)] Function.uncurry ω₂)

/-- The test class `𝒟_T = {φ ∈ C_c^∞(ℝ × ℝ²) : supp φ ⊂ (-∞, T) × ℝ²}`
(`02_prelim.tex:125`), with real-valued `φ`. The smoothness order `((⊤ : ℕ∞) : WithTop ℕ∞)` is
`C^∞` (Mathlib's scoped notation `∞`; we do not open the `ContDiff` scope here because it makes
`ω` a token). -/
structure IsTestFunction (T : ℝ) (φ : ℝ × ℂ → ℝ) : Prop where
  contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ
  hasCompactSupport : HasCompactSupport φ
  support_lt : ∀ p ∈ tsupport φ, p.1 < T

/-- The partial time derivative `∂_t φ(t, x)`. -/
def timeDeriv (φ : ℝ × ℂ → ℝ) (t : ℝ) (x : ℂ) : ℝ :=
  deriv (fun s => φ (s, x)) t

/-- The derivative of `φ(t, ·)` at `x` in the direction `w ∈ ℝ² = ℂ`, i.e. `w · ∇_x φ(t, x)`. -/
def spaceDeriv (φ : ℝ × ℂ → ℝ) (t : ℝ) (x w : ℂ) : ℝ :=
  fderiv ℝ (fun y => φ (t, y)) x w

/-- The integrand `u (∂_t φ + w · ∇φ)` of the transport identity. -/
def transportIntegrand (u : ℝ → ℂ → ℝ) (w : ℝ → ℂ → ℂ) (φ : ℝ × ℂ → ℝ) (p : ℝ × ℂ) : ℝ :=
  u p.1 p.2 * (timeDeriv φ p.1 p.2 + spaceDeriv φ p.1 p.2 (w p.1 p.2))

/-- `u` satisfies the transport equation `(te)` on `[0, T)` with field `w` and datum `u₀`
(`03_compactness.tex:46-58`, with `t₀ = 0`):
`∫₀ᵀ ∫ u (∂_t φ + w · ∇φ) dx dt + ∫ u₀ φ(0, ·) dx = 0` for all `φ ∈ 𝒟_T`,
with both integrals absolutely convergent. -/
structure SolvesTransport (T : ℝ) (u : ℝ → ℂ → ℝ) (w : ℝ → ℂ → ℂ) (u₀ : ℂ → ℝ) : Prop where
  integrableOn : ∀ φ, IsTestFunction T φ → IntegrableOn (transportIntegrand u w φ) (slab T)
  datum_integrable : ∀ φ, IsTestFunction T φ → Integrable (fun x : ℂ => u₀ x * φ (0, x))
  identity : ∀ φ, IsTestFunction T φ →
    (∫ t in Ioo (0 : ℝ) T, ∫ x : ℂ, transportIntegrand u w φ (t, x)) +
      ∫ x : ℂ, u₀ x * φ (0, x) = 0

/-- The Biot–Savart velocity field `v(t) = K * ω(t)` of a space–time vorticity. -/
def velocityField (ω : ℝ → ℂ → ℝ) (t : ℝ) (x : ℂ) : ℂ :=
  velocity (ω t) x

/-- A weak solution with datum `ωin` in `X_q(T)` (`def:weak`, `02_prelim.tex:521-531`):
`4/3 < q < ∞` (`q` is real, hence finite), `T > 0`, `ωin ∈ L¹ ∩ L^q`, `ω ∈ X_q(T)`, and the
weak formulation `(weak)` with `v(t) = K * ω(t)`. The field `velocity_convergent` records that
the integral defining `v(t, x)` converges absolutely for a.e. `t ∈ (0, T)` and a.e. `x`
(a consequence of `ω(t) ∈ L¹`, `02_prelim.tex:172-176`, and of `lem:velocity`(a),
`02_prelim.tex:309-310`), so that `v` is the Biot–Savart integral itself and Lean's junk value
`∫ = 0` for non-integrable integrands never enters the weak formulation. -/
structure IsWeakSolution (q T : ℝ) (ωin : ℂ → ℝ) (ω : ℝ → ℂ → ℝ) : Prop where
  q_gt : 4 / 3 < q
  T_pos : 0 < T
  datum_memLp_one : MemLp ωin 1
  datum_memLp_q : MemLp ωin (ENNReal.ofReal q)
  memX : MemX q T ω
  velocity_convergent : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)), ∀ᵐ x : ℂ,
    Integrable (fun y : ℂ => biotSavartKernel (x - y) * (ω t y : ℂ))
  weak : SolvesTransport T ω (velocityField ω) ωin

/-- The renormalizations: `Υ ∈ C¹(ℝ)` with `Υ'` bounded and `Υ(0) = 0`
(`02_prelim.tex:532-533`). -/
structure IsRenormalization (Υ : ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ 1 Υ
  deriv_bounded : ∃ C : ℝ, ∀ s : ℝ, |deriv Υ s| ≤ C
  map_zero : Υ 0 = 0

/-- A renormalized weak solution in `X_q(T)` (`def:weak`, `02_prelim.tex:532-539`): a weak
solution such that `Υ(ω)` satisfies the same identity, with the same field `v = K * ω` and datum
`Υ(ωin)`, for every renormalization `Υ`. -/
structure IsRenormalizedWeakSolution (q T : ℝ) (ωin : ℂ → ℝ) (ω : ℝ → ℂ → ℝ) : Prop
    extends IsWeakSolution q T ωin ω where
  renormalized : ∀ Υ : ℝ → ℝ, IsRenormalization Υ →
    SolvesTransport T (fun t x => Υ (ω t x)) (velocityField ω) (fun x => Υ (ωin x))

/-- A renormalized weak solution on `[0, ∞)` (`02_prelim.tex:540-542` with `T₀ = ∞`): its
restriction to `[0, T)` is a renormalized weak solution in `X_q(T)` for every `T ∈ (0, ∞)`.
(The predicates above only look at `ω` on `(0, T)`, so no explicit restriction is needed.) -/
def IsRenormalizedWeakSolutionOnHalfLine (q : ℝ) (ωin : ℂ → ℝ) (ω : ℝ → ℂ → ℝ) : Prop :=
  ∀ T : ℝ, 0 < T → IsRenormalizedWeakSolution q T ωin ω

/-- Equimeasurable functions (`def:equimeasurable`, `02_prelim.tex:515-519`): `g, h ∈ L¹` and
`|{g > s}| = |{h > s}|`, `|{g < -s}| = |{h < -s}|` for every `s > 0`. -/
def Equimeasurable (g h : ℂ → ℝ) : Prop :=
  MemLp g 1 ∧ MemLp h 1 ∧ ∀ s : ℝ, 0 < s →
    volume {x | s < g x} = volume {x | s < h x} ∧
      volume {x | g x < -s} = volume {x | h x < -s}

/-- `ω ∈ C([0, ∞); L^p(ℝ²))`: `ω(t) ∈ L^p` for every `t ≥ 0`, and `t ↦ ω(t)` is continuous
on `[0, ∞)` for the `L^p` distance. -/
def ContinuousIntoLp (p : ℝ≥0∞) (ω : ℝ → ℂ → ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → MemLp (ω t) p) ∧
    ∀ t₀ : ℝ, 0 ≤ t₀ →
      Tendsto (fun t => eLpNorm (ω t - ω t₀) p volume) (𝓝[Ici 0] t₀) (𝓝 0)

end NonUniqueEuler
