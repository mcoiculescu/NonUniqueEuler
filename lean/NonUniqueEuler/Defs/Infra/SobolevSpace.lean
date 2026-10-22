import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.PiL2
import NonUniqueEuler.Defs.Infra.Sobolev

/-!
# The Hilbert space `H^k(ℝ²)` as a type (definitions; library I-HK)

Manuscript-independent infrastructure (library I-HK, decision D14). Consumers mostly work with the
function-level predicates `Sob.MemH`, `Sob.normH` (`Defs/Infra/Sobolev.lean`); this file provides
the complete type that the Banach-algebra exponentials of the sector spaces need (library I-SECT).

Construction. An element of `H^k` is stored with all its weak derivatives: `SobTuple k` is the
`L²`-product `PiLp 2 (fun γ : SobIdx k => L²(ℂ))` over the multi-indices `|γ| ≤ k`, whose norm
is `(∑_γ ‖F_γ‖²_{L²})^{1/2}`, the manuscript's `H^k` norm. `Hk k` is the submodule of tuples with
`F_γ = ∂^γ F_0` weakly, written as the intersection of the kernels of the continuous functionals
`F ↦ ⟪conj ∂^γ φ, F_0⟫ - (-1)^{|γ|} ⟪conj φ, F_γ⟫` (`φ` a test function). So `Hk k` is closed,
hence complete, with no further proof, and it is a Hilbert space with the inner product
`∑_γ ⟪∂^γ F, ∂^γ G⟫_{L²}`.

Definitions: `SobIdx k`, `idx0 k`, `SobTuple k`, `TestFnC`, `conjLp`, `weakFunctional`, `HkSub k`, `Hk k`
(with `CompleteSpace`), `Hk.fn F` (the function `F_0`), `Hk.der F γ` (the function `F_γ`),
`toHk k f` (the element of `Hk k` whose `F_0` is `f`, chosen; `0` if none).

Fully proved: `isClosed_Hk`, the `CompleteSpace` instance, `inner_conjLp`, `mem_HkSub_iff`
(membership is exactly "`F_γ` is the weak derivative `∂^γ F_0`"), `Hk.norm_eq`.
The bridge with `MemH`/`normH` is `I/Infra/Sobolev/Space.lean`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff ComplexConjugate

namespace NonUniqueEuler.Sob

/-- The index type of the multi-indices `|γ| ≤ k`. -/
abbrev SobIdx (k : ℕ) : Type := ↥(multiIdx k)

/-- The multi-index `0`. -/
def idx0 (k : ℕ) : SobIdx k := ⟨(0, 0), zero_mem_multiIdx k⟩

/-- Tuples `(F_γ)_{|γ| ≤ k}` of `L²` functions with the `ℓ²`-sum norm. -/
abbrev SobTuple (k : ℕ) : Type :=
  PiLp 2 (fun _ : SobIdx k => Lp ℂ 2 (volume : Measure ℂ))

/-- Complex-valued test functions on the plane. -/
abbrev TestFnC : Type := {φ : ℂ → ℂ // IsTestFn univ φ}

theorem IsTestFn.memLp_star {φ : ℂ → ℂ} (hφ : IsTestFn univ φ) :
    MemLp (fun x => star (φ x)) 2 (volume : Measure ℂ) :=
  (hφ.continuous.star).memLp_of_hasCompactSupport (hφ.compact.comp_left (by simp))

/-- The `L²` class of `conj ∘ φ` for a test function `φ`. -/
def conjLp (φ : ℂ → ℂ) (hφ : IsTestFn univ φ) : Lp ℂ 2 (volume : Measure ℂ) :=
  MemLp.toLp (fun x => star (φ x)) hφ.memLp_star

/-- The functional `F ↦ ⟪conj ∂^γ φ, F_0⟫ - (-1)^{|γ|} ⟪conj φ, F_γ⟫ = ∫ F_0 ∂^γ φ - (-1)^{|γ|} ∫ F_γ φ`
whose vanishing for all test functions `φ` says `F_γ = ∂^γ F_0` weakly. -/
def weakFunctional (k : ℕ) (γ : SobIdx k) (φ : TestFnC) : SobTuple k →L[ℂ] ℂ :=
  (innerSL ℂ (conjLp (partialD γ.1 φ.1) (φ.2.partialD γ.1))).comp
      (PiLp.proj 2 (fun _ : SobIdx k => Lp ℂ 2 (volume : Measure ℂ)) (idx0 k)) -
    ((-1 : ℂ) ^ (pdList γ.1).length) •
      (innerSL ℂ (conjLp φ.1 φ.2)).comp
        (PiLp.proj 2 (fun _ : SobIdx k => Lp ℂ 2 (volume : Measure ℂ)) γ)

/-- The Sobolev space `H^k(ℝ²)`, as the closed subspace of `SobTuple k` of tuples
`(∂^γ f)_{|γ| ≤ k}`. -/
def HkSub (k : ℕ) : Submodule ℂ (SobTuple k) :=
  ⨅ (γ : SobIdx k) (φ : TestFnC),
    LinearMap.ker (weakFunctional k γ φ : SobTuple k →ₗ[ℂ] ℂ)

/-- The Hilbert space `H^k(ℝ²)` (the type of `HkSub k`). Its norm is the manuscript's
`(∑_{|γ| ≤ k} ‖∂^γ f‖²_{L²})^{1/2}` (`Hk.norm_eq`). -/
abbrev Hk (k : ℕ) : Type := ↥(HkSub k)

theorem isClosed_HkSub (k : ℕ) : IsClosed (HkSub k : Set (SobTuple k)) := by
  rw [HkSub, Submodule.coe_iInf]
  refine isClosed_iInter fun γ => ?_
  rw [Submodule.coe_iInf]
  exact isClosed_iInter fun φ => (weakFunctional k γ φ).isClosed_ker

instance (k : ℕ) : CompleteSpace (Hk k) :=
  haveI : IsClosed (HkSub k : Set (SobTuple k)) := isClosed_HkSub k
  IsClosed.completeSpace_coe

/-- The function `F_0` of a tuple. -/
def tupleFn {k : ℕ} (F : SobTuple k) : ℂ → ℂ :=
  (F.ofLp (idx0 k) : ℂ → ℂ)

/-- The function `F_0 = f` of an element of `H^k`. -/
def Hk.fn {k : ℕ} (F : Hk k) : ℂ → ℂ :=
  tupleFn (F : SobTuple k)

/-- The function `F_γ = ∂^γ f` of an element of `H^k`. -/
def Hk.der {k : ℕ} (F : Hk k) (γ : SobIdx k) : ℂ → ℂ :=
  ((F : SobTuple k).ofLp γ : ℂ → ℂ)

open Classical in
/-- The element of `H^k` whose function is `f` (unique when it exists, by uniqueness of weak
derivatives); `0` if `f ∉ H^k`. -/
def toHk (k : ℕ) (f : ℂ → ℂ) : Hk k :=
  if h : ∃ F : Hk k, F.fn =ᵐ[volume] f then h.choose else 0

/-! ### Basic lemmas (fully proved) -/

theorem inner_conjLp (φ : ℂ → ℂ) (hφ : IsTestFn univ φ) (f : Lp ℂ 2 (volume : Measure ℂ)) :
    inner ℂ (conjLp φ hφ) f = ∫ x, f x * φ x := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp hφ.memLp_star] with x hx
  rw [conjLp, hx, RCLike.inner_apply]
  simp

theorem weakFunctional_apply (k : ℕ) (γ : SobIdx k) (φ : TestFnC) (F : SobTuple k) :
    weakFunctional k γ φ F =
      (∫ x, (F.ofLp (idx0 k) : ℂ → ℂ) x * partialD γ.1 φ.1 x) -
        (-1 : ℂ) ^ (pdList γ.1).length * ∫ x, (F.ofLp γ : ℂ → ℂ) x * φ.1 x := by
  simp only [weakFunctional, sub_apply, smul_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, PiLp.proj_apply, smul_eq_mul]
  rw [inner_conjLp, inner_conjLp]

/-- Membership in `Hk k` is exactly: `F_γ` is the weak derivative `∂^γ F_0`, for `|γ| ≤ k`. -/
theorem mem_HkSub_iff {k : ℕ} (F : SobTuple k) :
    F ∈ HkSub k ↔ ∀ γ : SobIdx k,
      HasWeakDerivOn univ (pdList γ.1) (F.ofLp (idx0 k) : ℂ → ℂ) (F.ofLp γ : ℂ → ℂ) := by
  simp only [HkSub, Submodule.mem_iInf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    weakFunctional_apply, sub_eq_zero, HasWeakDerivOn, partialD]
  constructor
  · intro h γ φ hφ
    exact h γ ⟨φ, hφ⟩
  · intro h γ φ
    exact h γ φ.1 φ.2

theorem Hk.norm_eq {k : ℕ} (F : Hk k) :
    ‖F‖ = Real.sqrt (∑ γ : SobIdx k, ‖(F : SobTuple k).ofLp γ‖ ^ 2) := by
  rw [Submodule.coe_norm, PiLp.norm_eq_of_L2]

/-- The inner product of `H^k`: `⟪F, G⟫ = ∑_{|γ| ≤ k} ⟪∂^γ F, ∂^γ G⟫_{L²}`. -/
theorem Hk.inner_eq {k : ℕ} (F G : Hk k) :
    inner ℂ F G = ∑ γ : SobIdx k, inner ℂ ((F : SobTuple k).ofLp γ) ((G : SobTuple k).ofLp γ) := by
  rw [Submodule.coe_inner, PiLp.inner_apply]

theorem Hk.hasWeakDeriv {k : ℕ} (F : Hk k) (γ : SobIdx k) :
    HasWeakDerivOn univ (pdList γ.1) F.fn (F.der γ) :=
  (mem_HkSub_iff (F : SobTuple k)).1 F.2 γ

end NonUniqueEuler.Sob
