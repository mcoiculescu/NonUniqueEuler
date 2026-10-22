import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Weak convergence in real Hilbert spaces (definitions; library I-WEAKL2)

Manuscript-independent infrastructure (library I-WEAKL2). Section 3 of the
manuscript (`03_compactness.tex`) works with weakly continuous `L²`-valued paths
(restructuring R5, decision D9: exponent `b = 2` only). This file fixes the vocabulary.

* `WeakTendsto u l x`: `u i ⇀ x` along the filter `l` in a real inner product space `E`,
  defined by `⟪u i, y⟫ → ⟪x, y⟫` for every `y : E`. By the Riesz representation theorem this is
  weak convergence (`weakTendsto_iff_forall_dual` in `I/Infra/WeakL2/Norm.lean`).
* `WeakContinuousOn u s`: `t ↦ ⟪u t, y⟫` is continuous on `s` for every `y`.
* `WeakTendstoUniformlyOn u U l s`: `⟪u i t, y⟫ → ⟪U t, y⟫` uniformly in `t ∈ s`, for every `y`
  (the convergence of `prop:compact`(i)).
* `IsTestFamily F`: a sequence `F : ℕ → ℂ → ℝ` of real `C_c^∞` functions which, inside every
  open ball, is dense in `C¹` among the `C_c^∞` functions supported in that ball (the family
  `𝓕` of the proof of `lem:weak-cont`, `03_compactness.tex:146-153`). Its existence and its
  density in `L²` are in `I/Infra/WeakL2/TestFamily.lean`.

Everything is stated for a general real inner product space `E`. The consumers instantiate
`E := Lp ℝ 2 (volume : Measure ℂ)` (vorticities at a fixed time) or
`E := Lp ℝ 2 ((volume.restrict (Ioo 0 T)).prod volume)` (space–time, `prop:stable`).
For `E = Lp ℝ 2 μ`, `inner_toLp_eq_integral` turns the inner product with a function into the
integral `∫ f ψ`, and `weakTendsto_toLp_iff` states weak convergence of functions `g i ⇀ g₀`
(through their classes `MemLp.toLp`) as convergence of `∫ g i ψ` for every `ψ ∈ L²`.

The instance `fact_two_ne_top : Fact ((2 : ℝ≥0∞) ≠ ⊤)` lets Mathlib's
`MeasureTheory.Lp.SecondCountableTopology` fire, so `Lp ℝ 2 volume` (on `ℂ`) and the space–time
`L²` are separable by `inferInstance`.

All lemmas in this file are fully proved. The theorems that need real work are in
`NonUniqueEuler/I/Infra/WeakL2/*.lean`.
-/

noncomputable section

open Filter Topology MeasureTheory Set
open scoped InnerProductSpace ENNReal ContDiff

namespace NonUniqueEuler.WeakL2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Weak convergence `u i ⇀ x` along the filter `l`: `⟪u i, y⟫ → ⟪x, y⟫` for every `y`. -/
def WeakTendsto {ι : Type*} (u : ι → E) (l : Filter ι) (x : E) : Prop :=
  ∀ y : E, Tendsto (fun i => ⟪u i, y⟫_ℝ) l (𝓝 ⟪x, y⟫_ℝ)

/-- Weak continuity on a set: `t ↦ ⟪u t, y⟫` is continuous on `s` for every `y`. -/
def WeakContinuousOn {τ : Type*} [TopologicalSpace τ] (u : τ → E) (s : Set τ) : Prop :=
  ∀ y : E, ContinuousOn (fun t => ⟪u t, y⟫_ℝ) s

/-- Uniform weak convergence on `s`: for every `y`, `⟪u i t, y⟫ → ⟪U t, y⟫` uniformly in
`t ∈ s` (`prop:compact`(i), `03_compactness.tex:262-263`). -/
def WeakTendstoUniformlyOn {ι τ : Type*} (u : ι → τ → E) (U : τ → E) (l : Filter ι)
    (s : Set τ) : Prop :=
  ∀ y : E, TendstoUniformlyOn (fun i t => ⟪u i t, y⟫_ℝ) (fun t => ⟪U t, y⟫_ℝ) l s

namespace WeakTendsto

variable {ι : Type*} {u v : ι → E} {l : Filter ι} {x x' z : E}

theorem tendsto_inner (h : WeakTendsto u l x) (y : E) :
    Tendsto (fun i => ⟪u i, y⟫_ℝ) l (𝓝 ⟪x, y⟫_ℝ) :=
  h y

/-- Weak limits are unique. -/
theorem unique [l.NeBot] (h : WeakTendsto u l x) (h' : WeakTendsto u l x') : x = x' := by
  have key : ⟪x - x', x - x'⟫_ℝ = 0 := by
    rw [inner_sub_left, tendsto_nhds_unique (h (x - x')) (h' (x - x')), sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp key)

/-- Composition with a map of filters (in particular, passing to a subsequence). -/
theorem comp {κ : Type*} {l' : Filter κ} {φ : κ → ι} (h : WeakTendsto u l x)
    (hφ : Tendsto φ l' l) : WeakTendsto (u ∘ φ) l' x :=
  fun y => (h y).comp hφ

/-- Passing to a subsequence. -/
theorem subseq {u : ℕ → E} (h : WeakTendsto u atTop x) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    WeakTendsto (u ∘ φ) atTop x :=
  h.comp hφ.tendsto_atTop

theorem mono_left {l' : Filter ι} (h : WeakTendsto u l x) (hl : l' ≤ l) :
    WeakTendsto u l' x :=
  fun y => (h y).mono_left hl

theorem add (h : WeakTendsto u l x) (h' : WeakTendsto v l z) :
    WeakTendsto (fun i => u i + v i) l (x + z) := by
  intro y
  simp only [inner_add_left]
  exact (h y).add (h' y)

theorem sub (h : WeakTendsto u l x) (h' : WeakTendsto v l z) :
    WeakTendsto (fun i => u i - v i) l (x - z) := by
  intro y
  simp only [inner_sub_left]
  exact (h y).sub (h' y)

theorem const_smul (h : WeakTendsto u l x) (c : ℝ) :
    WeakTendsto (fun i => c • u i) l (c • x) := by
  intro y
  simp only [real_inner_smul_left]
  exact (h y).const_mul c

theorem neg (h : WeakTendsto u l x) : WeakTendsto (fun i => -u i) l (-x) := by
  intro y
  simp only [inner_neg_left]
  exact (h y).neg

end WeakTendsto

/-- Strong convergence implies weak convergence. -/
theorem _root_.Filter.Tendsto.weakTendsto {ι : Type*} {u : ι → E} {l : Filter ι} {x : E}
    (h : Tendsto u l (𝓝 x)) : WeakTendsto u l x :=
  fun _ => h.inner tendsto_const_nhds

theorem weakTendsto_const {ι : Type*} (l : Filter ι) (x : E) :
    WeakTendsto (fun _ : ι => x) l x :=
  fun _ => tendsto_const_nhds

namespace WeakContinuousOn

variable {τ : Type*} [TopologicalSpace τ] {u : τ → E} {s t : Set τ}

theorem continuousOn_inner (h : WeakContinuousOn u s) (y : E) :
    ContinuousOn (fun t => ⟪u t, y⟫_ℝ) s :=
  h y

theorem mono (h : WeakContinuousOn u s) (hts : t ⊆ s) : WeakContinuousOn u t :=
  fun y => (h y).mono hts

/-- A weakly continuous path is weakly continuous at each point within `s`. -/
theorem weakTendsto (h : WeakContinuousOn u s) {t₀ : τ} (ht₀ : t₀ ∈ s) :
    WeakTendsto u (𝓝[s] t₀) (u t₀) :=
  fun y => h y t₀ ht₀

end WeakContinuousOn

/-- Strongly continuous paths are weakly continuous. -/
theorem _root_.ContinuousOn.weakContinuousOn {τ : Type*} [TopologicalSpace τ] {u : τ → E}
    {s : Set τ} (h : ContinuousOn u s) : WeakContinuousOn u s :=
  fun _ => h.inner continuousOn_const

/-- A uniform weak limit of weakly continuous paths is weakly continuous. -/
theorem WeakTendstoUniformlyOn.weakContinuousOn {ι τ : Type*} [TopologicalSpace τ]
    {u : ι → τ → E} {U : τ → E} {l : Filter ι} [l.NeBot] {s : Set τ}
    (h : WeakTendstoUniformlyOn u U l s) (hu : ∀ᶠ i in l, WeakContinuousOn (u i) s) :
    WeakContinuousOn U s :=
  fun y => (h y).continuousOn (hu.mono fun _ hi => hi y).frequently

/-- Uniform weak convergence on `s` gives weak convergence at every point of `s`. -/
theorem WeakTendstoUniformlyOn.weakTendsto {ι τ : Type*} {u : ι → τ → E} {U : τ → E}
    {l : Filter ι} {s : Set τ} (h : WeakTendstoUniformlyOn u U l s) {t : τ} (ht : t ∈ s) :
    WeakTendsto (fun i => u i t) l (U t) :=
  fun y => (h y).tendsto_at ht

/-! ### The space `L²(μ)` -/

/-- `2 ≠ ∞`, as an instance: with it Mathlib's `MeasureTheory.Lp.SecondCountableTopology` makes
`Lp ℝ 2 μ` second countable (hence separable) for separable `μ`, e.g. `volume` on `ℂ` and the
slab measure `(volume.restrict (Ioo 0 T)).prod volume` (`separableSpace_L2_plane`). -/
instance fact_two_ne_top : Fact ((2 : ℝ≥0∞) ≠ ⊤) :=
  ⟨ENNReal.ofNat_ne_top⟩

/-- `L²(ℂ)` is separable. -/
theorem separableSpace_L2_plane :
    TopologicalSpace.SeparableSpace (Lp ℝ 2 (volume : Measure ℂ)) :=
  inferInstance

section L2

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The `L²` inner product with (the class of) a function `ψ ∈ L²` is the integral `∫ f ψ`. -/
theorem inner_toLp_eq_integral (f : Lp ℝ 2 μ) {ψ : α → ℝ} (hψ : MemLp ψ 2 μ) :
    ⟪f, hψ.toLp ψ⟫_ℝ = ∫ x, f x * ψ x ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hψ.coeFn_toLp] with x hx
  rw [hx]
  simp [mul_comm]

/-- Weak convergence in `L²(μ)` tested against a function `ψ ∈ L²`. -/
theorem WeakTendsto.integral_mul_tendsto {ι : Type*} {u : ι → Lp ℝ 2 μ} {l : Filter ι}
    {x : Lp ℝ 2 μ} (h : WeakTendsto u l x) {ψ : α → ℝ} (hψ : MemLp ψ 2 μ) :
    Tendsto (fun i => ∫ a, u i a * ψ a ∂μ) l (𝓝 (∫ a, x a * ψ a ∂μ)) := by
  have := h (hψ.toLp ψ)
  simpa only [inner_toLp_eq_integral _ hψ] using this

/-- The `L²` inner product of the classes of two functions in `L²`. -/
theorem inner_toLp_toLp {f ψ : α → ℝ} (hf : MemLp f 2 μ) (hψ : MemLp ψ 2 μ) :
    ⟪hf.toLp f, hψ.toLp ψ⟫_ℝ = ∫ x, f x * ψ x ∂μ := by
  rw [inner_toLp_eq_integral _ hψ]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

/-- Weak `L²` convergence of (the classes of) functions, tested against functions in `L²`. -/
theorem weakTendsto_toLp_iff {ι : Type*} {l : Filter ι} {g : ι → α → ℝ} {g₀ : α → ℝ}
    (hg : ∀ i, MemLp (g i) 2 μ) (hg₀ : MemLp g₀ 2 μ) :
    WeakTendsto (fun i => (hg i).toLp (g i)) l (hg₀.toLp g₀) ↔
      ∀ ψ : α → ℝ, MemLp ψ 2 μ →
        Tendsto (fun i => ∫ a, g i a * ψ a ∂μ) l (𝓝 (∫ a, g₀ a * ψ a ∂μ)) := by
  constructor
  · intro h ψ hψ
    have := h (hψ.toLp ψ)
    simpa only [inner_toLp_toLp (hg _) hψ, inner_toLp_toLp hg₀ hψ] using this
  · intro h y
    have hy : y = (Lp.memLp y).toLp y := (Lp.toLp_coeFn y (Lp.memLp y)).symm
    have := h y (Lp.memLp y)
    rw [hy]
    simpa only [inner_toLp_toLp (hg _) (Lp.memLp y), inner_toLp_toLp hg₀ (Lp.memLp y)]
      using this

end L2

/-! ### A countable test family in `C_c^∞(ℂ)` -/

/-- A countable family of real `C_c^∞` functions on the plane such that for every `R` and every
`ψ ∈ C_c^∞` with `tsupport ψ ⊆ B_R`, there are members of the family, also supported in `B_R`,
arbitrarily close to `ψ` in the `C¹` norm (sup of the values and of the derivatives). This is
the family `𝓕` of `03_compactness.tex:146-153` (proof of `lem:weak-cont`). -/
structure IsTestFamily (F : ℕ → ℂ → ℝ) : Prop where
  contDiff : ∀ i, ContDiff ℝ ∞ (F i)
  hasCompactSupport : ∀ i, HasCompactSupport (F i)
  dense_C1 : ∀ (R : ℝ) (ψ : ℂ → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
    tsupport ψ ⊆ Metric.ball 0 R → ∀ ε : ℝ, 0 < ε → ∃ i, tsupport (F i) ⊆ Metric.ball 0 R ∧
      (∀ x, |F i x - ψ x| ≤ ε) ∧ ∀ x, ‖fderiv ℝ (F i) x - fderiv ℝ ψ x‖ ≤ ε

namespace IsTestFamily

variable {F : ℕ → ℂ → ℝ}

/-- The members of a test family are in every `L^p`. -/
theorem memLp (hF : IsTestFamily F) (i : ℕ) (p : ℝ≥0∞) : MemLp (F i) p (volume : Measure ℂ) :=
  ((hF.contDiff i).continuous).memLp_of_hasCompactSupport (hF.hasCompactSupport i)

/-- The members of a test family as elements of `L²(ℂ)`. -/
def toL2 (hF : IsTestFamily F) (i : ℕ) : Lp ℝ 2 (volume : Measure ℂ) :=
  (hF.memLp i 2).toLp (F i)

theorem coeFn_toL2 (hF : IsTestFamily F) (i : ℕ) : (hF.toL2 i : ℂ → ℝ) =ᵐ[volume] F i :=
  (hF.memLp i 2).coeFn_toLp

theorem inner_toL2 (hF : IsTestFamily F) (f : Lp ℝ 2 (volume : Measure ℂ)) (i : ℕ) :
    ⟪f, hF.toL2 i⟫_ℝ = ∫ x, f x * F i x :=
  inner_toLp_eq_integral f (hF.memLp i 2)

end IsTestFamily

end NonUniqueEuler.WeakL2
