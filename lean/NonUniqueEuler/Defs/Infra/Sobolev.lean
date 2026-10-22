import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import NonUniqueEuler.Defs.Infra.CkNorm

/-!
# Weak derivatives and the Sobolev spaces `H^k` (definitions; library I-HK)

Manuscript-independent infrastructure (library I-HK, decision D7). Integer-order Sobolev spaces are
defined by weak derivatives in `L²`; there is no Fourier `H^s`.

The manuscript (`02_prelim.tex:58-66`): for an integer `k ≥ 0` and an open set `V ⊆ ℝ²`,
`H^k(V)` has the norm `‖g‖²_{H^k(V)} = ∑_{|γ| ≤ k} ‖∂^γ g‖²_{L²(V)}`, `H^k = H^k(ℝ²)`, with
`∂^γ = ∂₁^{γ₁} ∂₂^{γ₂}`; functions are complex valued.

## Generic part (any real normed space `E` with a measure, used for `E = ℂ` and `E = ℝ`)
* `dirDeriv v φ x = Dφ(x) v` (decision D2) and `iterDirDeriv [v₁, …, vₙ] φ = ∂_{v₁} ⋯ ∂_{vₙ} φ`;
* `IsTestFn V φ`: `φ : E → ℂ` is `C^∞`, compactly supported, with `tsupport φ ⊆ V`;
* `HasWeakDerivOn V vs f g`: `g = ∂_{vs} f` weakly on `V`, i.e.
  `∫ f · ∂_{vs} φ = (-1)^{|vs|} ∫ g · φ` for all test functions `φ` supported in `V`;
* `weakDerivOn V vs f`: a chosen locally integrable weak derivative (`0` if none exists).

## The plane `ℂ` (`∂₁ = ∂_1`, `∂₂ = ∂_I`)
* multi-indices are `γ : ℕ × ℕ`; `pdList γ = [1, …, 1, I, …, I]`; `partialD γ φ = ∂^γ φ`
  (classical); `multiIdx k = {γ | γ.1 + γ.2 ≤ k}`;
* `leIdx γ = {β | β ≤ γ}` (for Leibniz formulas);
* `weakPartialOn V γ f`, `weakPartial γ f` (weak `∂^γ f`);
* `dotGrad U w = U₁ ∂₁w + U₂ ∂₂w` (the transport term `U·∇w`, weak derivatives);
* `MemHOn k V f` (`f ∈ H^k(V)`), `normHOn k V f` (`‖f‖_{H^k(V)}`), and the whole-plane versions
  `MemH k f`, `normH k f`;
* `l2On V f = ‖f‖_{L²(V)}`, `l2 f = ‖f‖_{L²}` (real numbers);
* `MemW1infOn V U`, `normW1infOn V U`: the manuscript's `W^{1,∞}(V)` norm
  `ess sup_V |U| + ess sup_V |∇U|` of a vector field `U : ℂ → ℂ` (`02_prelim.tex:70-71`), with
  `|∇U|² = |∂₁U|² + |∂₂U|²` (Euclidean norm of the matrix `(∂_l U_i)`).

The Hilbert-space type `Sob.Hk k` is in `Defs/Infra/SobolevSpace.lean`. Vector fields `U : ℂ → ℂ`
are measured as complex functions; this is the manuscript's convention of summing over the
entries, because `|U|² = U₁² + U₂²`.

Junk values: `weakDerivOn` is `0` when no weak derivative exists, and `normHOn` is then
meaningless; consumers carry `MemHOn`/`MemH` hypotheses. For `V` open, a weak derivative in
`L¹_loc(V)` is unique a.e. on `V` (`I/Infra/Sobolev/WeakDeriv.lean`).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace NonUniqueEuler.Sob

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The directional derivative `v · ∇φ (x) = Dφ(x) v` (decision D2). -/
def dirDeriv (v : E) (φ : E → ℂ) : E → ℂ := fun x => fderiv ℝ φ x v

/-- The iterated directional derivative `∂_{v₁} ∂_{v₂} ⋯ ∂_{vₙ} φ` for `vs = [v₁, …, vₙ]`. -/
def iterDirDeriv (vs : List E) (φ : E → ℂ) : E → ℂ :=
  vs.foldr dirDeriv φ

/-- Test functions supported in `V`: smooth, compactly supported, with `tsupport φ ⊆ V`. -/
structure IsTestFn (V : Set E) (φ : E → ℂ) : Prop where
  smooth : ContDiff ℝ ∞ φ
  compact : HasCompactSupport φ
  subset : tsupport φ ⊆ V

variable [MeasureSpace E]

/-- `g = ∂_{vs} f` weakly on `V`: `∫ f · ∂_{vs} φ = (-1)^{|vs|} ∫ g · φ` for every test function
supported in `V`. Both integrals are over the whole space; their integrands vanish outside
`tsupport φ ⊆ V`. -/
def HasWeakDerivOn (V : Set E) (vs : List E) (f g : E → ℂ) : Prop :=
  ∀ φ : E → ℂ, IsTestFn V φ →
    ∫ x, f x * iterDirDeriv vs φ x = (-1 : ℂ) ^ vs.length * ∫ x, g x * φ x

open Classical in
/-- A chosen weak derivative `∂_{vs} f` on `V`, locally integrable on `V`; `0` if none exists.
For `V` open it is unique a.e. on `V`. -/
def weakDerivOn (V : Set E) (vs : List E) (f : E → ℂ) : E → ℂ :=
  if h : ∃ g : E → ℂ, LocallyIntegrableOn g V ∧ HasWeakDerivOn V vs f g then h.choose else 0

/-- `‖f‖_{L²(V)}` as a real number. -/
def l2On (V : Set E) (f : E → ℂ) : ℝ :=
  (eLpNorm f 2 (volume.restrict V)).toReal

/-- `‖f‖_{L²}` as a real number. -/
def l2 (f : E → ℂ) : ℝ :=
  (eLpNorm f 2 volume).toReal

end Generic

/-! ### The plane -/

/-- The list of directions of `∂^γ = ∂₁^{γ₁} ∂₂^{γ₂}`: `γ.1` copies of `1`, then `γ.2` copies
of `I` (decision D2: `∂₁ = ∂_1`, `∂₂ = ∂_I`). -/
def pdList (γ : ℕ × ℕ) : List ℂ :=
  List.replicate γ.1 (1 : ℂ) ++ List.replicate γ.2 Complex.I

/-- The classical partial derivative `∂^γ φ = ∂₁^{γ₁} ∂₂^{γ₂} φ`. -/
def partialD (γ : ℕ × ℕ) (φ : ℂ → ℂ) : ℂ → ℂ :=
  iterDirDeriv (pdList γ) φ

/-- The multi-indices `γ` with `|γ| = γ.1 + γ.2 ≤ k`. -/
def multiIdx (k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (k + 1) ×ˢ Finset.range (k + 1)).filter fun γ => γ.1 + γ.2 ≤ k

/-- The multi-indices `β ≤ γ` (componentwise), for Leibniz formulas
`∂^γ(fg) = ∑_{β ≤ γ} C(γ₁,β₁) C(γ₂,β₂) ∂^β f ∂^{γ-β} g`. -/
def leIdx (γ : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  Finset.range (γ.1 + 1) ×ˢ Finset.range (γ.2 + 1)

/-- The weak partial derivative `∂^γ f` on `V`. -/
def weakPartialOn (V : Set ℂ) (γ : ℕ × ℕ) (f : ℂ → ℂ) : ℂ → ℂ :=
  weakDerivOn V (pdList γ) f

/-- The weak partial derivative `∂^γ f` on the plane. -/
def weakPartial (γ : ℕ × ℕ) (f : ℂ → ℂ) : ℂ → ℂ :=
  weakPartialOn univ γ f

/-- `f ∈ H^k(V)`: `f ∈ L²(V)` and every weak derivative `∂^γ f`, `|γ| ≤ k`, exists in `L²(V)`.
(For `V` open, an `L²(V)` function is locally integrable on `V`.) -/
structure MemHOn (k : ℕ) (V : Set ℂ) (f : ℂ → ℂ) : Prop where
  memLp : MemLp f 2 (volume.restrict V)
  deriv : ∀ γ ∈ multiIdx k, ∃ g : ℂ → ℂ, MemLp g 2 (volume.restrict V) ∧
    HasWeakDerivOn V (pdList γ) f g

/-- `‖f‖_{H^k(V)} = (∑_{|γ| ≤ k} ‖∂^γ f‖²_{L²(V)})^{1/2}`. -/
def normHOn (k : ℕ) (V : Set ℂ) (f : ℂ → ℂ) : ℝ :=
  Real.sqrt (∑ γ ∈ multiIdx k, l2On V (weakPartialOn V γ f) ^ 2)

/-- `f ∈ H^k = H^k(ℝ²)`. -/
def MemH (k : ℕ) (f : ℂ → ℂ) : Prop :=
  MemHOn k univ f

/-- `‖f‖_{H^k}`. -/
def normH (k : ℕ) (f : ℂ → ℂ) : ℝ :=
  normHOn k univ f

/-- The pointwise norm `|∇U| = (|∂₁U|² + |∂₂U|²)^{1/2}` of the weak gradient of a vector field
`U : ℂ → ℂ` on `V` (Euclidean norm of the matrix `(∂_l U_i)`). -/
def gradNormOn (V : Set ℂ) (U : ℂ → ℂ) (x : ℂ) : ℝ :=
  Real.sqrt (‖weakPartialOn V (1, 0) U x‖ ^ 2 + ‖weakPartialOn V (0, 1) U x‖ ^ 2)

/-- `U ∈ W^{1,∞}(V)`: `U ∈ L^∞(V)` and its first weak derivatives exist in `L^∞(V)`
(and are locally integrable on `V`). -/
structure MemW1infOn (V : Set ℂ) (U : ℂ → ℂ) : Prop where
  memLp : MemLp U ⊤ (volume.restrict V)
  deriv : ∀ γ ∈ ({(1, 0), (0, 1)} : Finset (ℕ × ℕ)), ∃ g : ℂ → ℂ,
    MemLp g ⊤ (volume.restrict V) ∧ LocallyIntegrableOn g V ∧ HasWeakDerivOn V (pdList γ) U g

/-- The manuscript's `‖U‖_{W^{1,∞}(V)} = ess sup_V |U| + ess sup_V |∇U|`
(`02_prelim.tex:70-71`). -/
def normW1infOn (V : Set ℂ) (U : ℂ → ℂ) : ℝ :=
  (eLpNorm U ⊤ (volume.restrict V)).toReal +
    (eLpNorm (gradNormOn V U) ⊤ (volume.restrict V)).toReal

/-- The transport term `U · ∇w = U₁ ∂₁w + U₂ ∂₂w` of a vector field `U = U₁ + i U₂ : ℂ → ℂ`
acting on `w : ℂ → ℂ`, with weak derivatives of `w` on the plane. -/
def dotGrad (U w : ℂ → ℂ) (x : ℂ) : ℂ :=
  ((U x).re : ℂ) * weakPartial (1, 0) w x + ((U x).im : ℂ) * weakPartial (0, 1) w x

/-! ### Basic lemmas (fully proved) -/

section GenericLemmas

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

@[simp] theorem iterDirDeriv_nil (φ : E → ℂ) : iterDirDeriv [] φ = φ := rfl

@[simp] theorem iterDirDeriv_cons (v : E) (vs : List E) (φ : E → ℂ) :
    iterDirDeriv (v :: vs) φ = dirDeriv v (iterDirDeriv vs φ) := rfl

theorem iterDirDeriv_append (vs ws : List E) (φ : E → ℂ) :
    iterDirDeriv (vs ++ ws) φ = iterDirDeriv vs (iterDirDeriv ws φ) := by
  simp [iterDirDeriv, List.foldr_append]

theorem IsTestFn.mono {V V' : Set E} {φ : E → ℂ} (h : IsTestFn V φ) (hV : V ⊆ V') :
    IsTestFn V' φ :=
  ⟨h.smooth, h.compact, h.subset.trans hV⟩

theorem IsTestFn.continuous {V : Set E} {φ : E → ℂ} (h : IsTestFn V φ) : Continuous φ :=
  h.smooth.continuous

theorem IsTestFn.dirDeriv {V : Set E} {φ : E → ℂ} (h : IsTestFn V φ) (v : E) :
    IsTestFn V (Sob.dirDeriv v φ) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (ContDiff.fderiv_right (m := ∞) h.smooth (by simp)).clm_apply contDiff_const
  · have : Sob.dirDeriv v φ = (fun L : E →L[ℝ] ℂ => L v) ∘ fderiv ℝ φ := rfl
    rw [this]
    exact (h.compact.fderiv ℝ).comp_left (by simp)
  · have h1 : tsupport (Sob.dirDeriv v φ) ⊆ tsupport (fderiv ℝ φ) := by
      apply closure_mono
      intro x hx
      simp only [Function.mem_support, Sob.dirDeriv] at hx ⊢
      intro h0
      exact hx (by simp [h0])
    exact h1.trans ((tsupport_fderiv_subset ℝ).trans h.subset)

theorem IsTestFn.iterDirDeriv {V : Set E} {φ : E → ℂ} (h : IsTestFn V φ) (vs : List E) :
    IsTestFn V (Sob.iterDirDeriv vs φ) := by
  induction vs with
  | nil => simpa using h
  | cons v vs ih => simpa using ih.dirDeriv v

section Measure

variable [MeasureSpace E]

theorem HasWeakDerivOn.mono {V V' : Set E} {vs : List E} {f g : E → ℂ}
    (h : HasWeakDerivOn V vs f g) (hV : V' ⊆ V) : HasWeakDerivOn V' vs f g :=
  fun φ hφ => h φ (hφ.mono hV)

/-- The chosen weak derivative is a locally integrable weak derivative whenever one exists. -/
theorem weakDerivOn_spec {V : Set E} {vs : List E} {f g : E → ℂ} (hg : LocallyIntegrableOn g V)
    (h : HasWeakDerivOn V vs f g) :
    LocallyIntegrableOn (weakDerivOn V vs f) V ∧ HasWeakDerivOn V vs f (weakDerivOn V vs f) := by
  have hex : ∃ g : E → ℂ, LocallyIntegrableOn g V ∧ HasWeakDerivOn V vs f g := ⟨g, hg, h⟩
  unfold weakDerivOn
  split_ifs
  exact hex.choose_spec

end Measure

variable [MeasurableSpace E] [OpensMeasurableSpace E]

theorem IsTestFn.memLp {V : Set E} {φ : E → ℂ} (h : IsTestFn V φ) (p : ℝ≥0∞) (μ : Measure E)
    [IsFiniteMeasureOnCompacts μ] : MemLp φ p μ :=
  h.continuous.memLp_of_hasCompactSupport h.compact

end GenericLemmas

@[simp] theorem pdList_length (γ : ℕ × ℕ) : (pdList γ).length = γ.1 + γ.2 := by
  simp [pdList]

theorem IsTestFn.partialD {V : Set ℂ} {φ : ℂ → ℂ} (h : IsTestFn V φ) (γ : ℕ × ℕ) :
    IsTestFn V (Sob.partialD γ φ) :=
  h.iterDirDeriv _

theorem mem_multiIdx {k : ℕ} {γ : ℕ × ℕ} : γ ∈ multiIdx k ↔ γ.1 + γ.2 ≤ k := by
  simp only [multiIdx, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨⟨by omega, by omega⟩, h⟩

@[simp] theorem zero_mem_multiIdx (k : ℕ) : ((0 : ℕ), (0 : ℕ)) ∈ multiIdx k := by
  simp [mem_multiIdx]

theorem multiIdx_mono {k k' : ℕ} (h : k ≤ k') : multiIdx k ⊆ multiIdx k' := fun _ hγ =>
  mem_multiIdx.2 ((mem_multiIdx.1 hγ).trans h)

theorem normHOn_nonneg (k : ℕ) (V : Set ℂ) (f : ℂ → ℂ) : 0 ≤ normHOn k V f :=
  Real.sqrt_nonneg _

theorem normH_nonneg (k : ℕ) (f : ℂ → ℂ) : 0 ≤ normH k f :=
  Real.sqrt_nonneg _

theorem l2On_nonneg (V : Set ℂ) (f : ℂ → ℂ) : 0 ≤ l2On V f :=
  ENNReal.toReal_nonneg

theorem l2_nonneg (f : ℂ → ℂ) : 0 ≤ l2 f :=
  ENNReal.toReal_nonneg

@[simp] theorem l2On_univ (f : ℂ → ℂ) : l2On univ f = l2 f := by
  simp [l2On, l2]

theorem memH_iff {k : ℕ} {f : ℂ → ℂ} :
    MemH k f ↔ MemLp f 2 volume ∧ ∀ γ ∈ multiIdx k, ∃ g : ℂ → ℂ, MemLp g 2 volume ∧
      HasWeakDerivOn univ (pdList γ) f g := by
  constructor
  · intro h
    refine ⟨by simpa using h.memLp, fun γ hγ => ?_⟩
    obtain ⟨g, hg, hfg⟩ := h.deriv γ hγ
    exact ⟨g, by simpa using hg, hfg⟩
  · rintro ⟨hf, hd⟩
    refine ⟨by simpa using hf, fun γ hγ => ?_⟩
    obtain ⟨g, hg, hfg⟩ := hd γ hγ
    exact ⟨g, by simpa using hg, hfg⟩

theorem normH_eq (k : ℕ) (f : ℂ → ℂ) :
    normH k f = Real.sqrt (∑ γ ∈ multiIdx k, l2 (weakPartial γ f) ^ 2) := by
  simp [normH, normHOn, weakPartial]

theorem MemHOn.mono_order {k k' : ℕ} {V : Set ℂ} {f : ℂ → ℂ} (h : MemHOn k' V f)
    (hk : k ≤ k') : MemHOn k V f :=
  ⟨h.memLp, fun γ hγ => h.deriv γ (multiIdx_mono hk hγ)⟩

theorem MemH.mono_order {k k' : ℕ} {f : ℂ → ℂ} (h : MemH k' f) (hk : k ≤ k') : MemH k f :=
  MemHOn.mono_order h hk

end NonUniqueEuler.Sob
