import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# `C^k` norms on sets (definitions; library I-CK)

Manuscript-independent infrastructure (library I-CK).

The manuscript (`02_prelim.tex:72-79`) puts, for an integer `k ≥ 0`, a closed set `U ⊆ ℝ²` and
`h` of class `C^k` on a neighbourhood of `U`,
`‖h‖_{C^k(U)} = ∑_{q=0}^k sup_{x∈U} |∇^q h(x)|`,
where `|∇^q h(x)|` is the Euclidean norm of the array of all partial derivatives of order `q`.

**Convention (deviation).** Here `|∇^q h(x)|` is replaced by the operator
norm `‖iteratedFDeriv ℝ q h x‖` of Mathlib's iterated Fréchet derivative. On `ℂ = ℝ²` the two
are equivalent: `‖D^q h x‖ ≤ |∇^q h(x)| ≤ 2^{q/2} ‖D^q h x‖`
(`I/Infra/CkNorm/ArrayNorm.lean`, with the array norm `iterDerivArrayNorm` defined below). The
two properties the manuscript uses hold verbatim: `|∂^γ h(x)| ≤ ‖h‖_{C^k(U)}` for `x ∈ U`,
`|γ| ≤ k` (`Sob.norm_partialD_le_normCk`, `I/Infra/Sobolev/Smooth.lean`), and the scaling rule
`∇^q (c V(c' ·))(y) = c c'^q (∇^q V)(c' y)` (`I/Infra/CkNorm/Scaling.lean`). All constants built
from `C^k` norms are existential (D11), so no later choice changes.

Definitions.
* `supIterDerivE q U h = sup_{x ∈ U} ‖D^q h x‖ₑ ∈ [0, ∞]`;
* `normCkE k U h = ∑_{q ≤ k} supIterDerivE q U h ∈ [0, ∞]`;
* `normCk k U h = (normCkE k U h).toReal` (junk value `0` when the norm is infinite);
* `IsCkNear k U h`: `h` is `C^k` on an open set containing `U`;
* `MemCk k U h`: `IsCkNear k U h` and `normCkE k U h < ∞` (the manuscript's `h ∈ C^k(U)`);
* `iterDerivArrayNorm q h x`: the manuscript's array norm `|∇^q h(x)|` on `ℂ`.

Consumers should always carry `MemCk k U h` next to a bound on `normCk k U h`, as for
`MemLp`/`eLpNorm`. The derivative `iteratedFDeriv ℝ q h x` is the global one; it depends only on
the germ of `h` at `x`, so it is the right object when `h` is `C^k` near `U`.
-/

noncomputable section

open scoped ENNReal ContDiff
open Set

namespace NonUniqueEuler

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- `sup_{x ∈ U} ‖D^q h x‖`, in `[0, ∞]`. -/
def supIterDerivE (q : ℕ) (U : Set E) (h : E → F) : ℝ≥0∞ :=
  ⨆ x ∈ U, ‖iteratedFDeriv ℝ q h x‖ₑ

/-- The `C^k(U)` norm `∑_{q ≤ k} sup_{x ∈ U} ‖D^q h x‖`, in `[0, ∞]`. -/
def normCkE (k : ℕ) (U : Set E) (h : E → F) : ℝ≥0∞ :=
  ∑ q ∈ Finset.range (k + 1), supIterDerivE q U h

/-- The `C^k(U)` norm as a real number (`02_prelim.tex:76`). It is `0` when `normCkE` is
infinite; use it together with `MemCk`. -/
def normCk (k : ℕ) (U : Set E) (h : E → F) : ℝ :=
  (normCkE k U h).toReal

/-- `h` is of class `C^k` on an open set containing `U`. -/
def IsCkNear (k : ℕ) (U : Set E) (h : E → F) : Prop :=
  ∃ V : Set E, IsOpen V ∧ U ⊆ V ∧ ContDiffOn ℝ k h V

/-- The manuscript's `h ∈ C^k(U)`: `h` is `C^k` near `U` and `‖h‖_{C^k(U)} < ∞`. -/
structure MemCk (k : ℕ) (U : Set E) (h : E → F) : Prop where
  near : IsCkNear k U h
  finite : normCkE k U h ≠ ⊤

/-- The manuscript's array norm `|∇^q h(x)|` on `ℂ = ℝ²`: the Euclidean norm of the array of all
partial derivatives of order `q`, one entry for each ordered `q`-tuple of directions in
`{∂₁, ∂₂} = {1, I}`. -/
def iterDerivArrayNorm (q : ℕ) (h : ℂ → F) (x : ℂ) : ℝ :=
  Real.sqrt (∑ i : Fin q → Fin 2,
    ‖iteratedFDeriv ℝ q h x (fun j => ![(1 : ℂ), Complex.I] (i j))‖ ^ 2)

/-! ### Basic lemmas (fully proved) -/

theorem normCk_nonneg (k : ℕ) (U : Set E) (h : E → F) : 0 ≤ normCk k U h :=
  ENNReal.toReal_nonneg

theorem enorm_iteratedFDeriv_le_supIterDerivE {q : ℕ} {U : Set E} (h : E → F) {x : E}
    (hx : x ∈ U) : ‖iteratedFDeriv ℝ q h x‖ₑ ≤ supIterDerivE q U h :=
  le_iSup₂_of_le x hx le_rfl

theorem supIterDerivE_le_normCkE {q k : ℕ} (hq : q ≤ k) (U : Set E) (h : E → F) :
    supIterDerivE q U h ≤ normCkE k U h :=
  Finset.single_le_sum (f := fun q => supIterDerivE q U h) (fun _ _ => zero_le)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hq))

theorem enorm_iteratedFDeriv_le_normCkE {q k : ℕ} (hq : q ≤ k) {U : Set E} (h : E → F) {x : E}
    (hx : x ∈ U) : ‖iteratedFDeriv ℝ q h x‖ₑ ≤ normCkE k U h :=
  (enorm_iteratedFDeriv_le_supIterDerivE h hx).trans (supIterDerivE_le_normCkE hq U h)

theorem supIterDerivE_mono {q : ℕ} {U U' : Set E} (hU : U ⊆ U') (h : E → F) :
    supIterDerivE q U h ≤ supIterDerivE q U' h :=
  iSup₂_le fun _ hx => enorm_iteratedFDeriv_le_supIterDerivE h (hU hx)

theorem normCkE_mono_set (k : ℕ) {U U' : Set E} (hU : U ⊆ U') (h : E → F) :
    normCkE k U h ≤ normCkE k U' h :=
  Finset.sum_le_sum fun _ _ => supIterDerivE_mono hU h

theorem normCkE_mono_order {k k' : ℕ} (hk : k ≤ k') (U : Set E) (h : E → F) :
    normCkE k U h ≤ normCkE k' U h :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
    (fun _ _ _ => zero_le)

/-- The defining property used throughout the manuscript: every derivative of order `q ≤ k`
is bounded on `U` by the `C^k(U)` norm. -/
theorem norm_iteratedFDeriv_le_normCk {k q : ℕ} {U : Set E} {h : E → F} (hh : MemCk k U h)
    (hq : q ≤ k) {x : E} (hx : x ∈ U) : ‖iteratedFDeriv ℝ q h x‖ ≤ normCk k U h := by
  have h1 := enorm_iteratedFDeriv_le_normCkE hq h hx
  have h2 : ‖iteratedFDeriv ℝ q h x‖ₑ.toReal ≤ (normCkE k U h).toReal :=
    ENNReal.toReal_mono hh.finite h1
  simpa [normCk] using h2

theorem norm_le_normCk {k : ℕ} {U : Set E} {h : E → F} (hh : MemCk k U h) {x : E} (hx : x ∈ U) :
    ‖h x‖ ≤ normCk k U h := by
  have := norm_iteratedFDeriv_le_normCk hh (Nat.zero_le k) hx
  simpa using this

theorem supIterDerivE_le_ofReal {q : ℕ} {U : Set E} {h : E → F} {M : ℝ}
    (hM : ∀ x ∈ U, ‖iteratedFDeriv ℝ q h x‖ ≤ M) :
    supIterDerivE q U h ≤ ENNReal.ofReal M :=
  iSup₂_le fun x hx => by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hM x hx)

/-- A bound on every derivative of order `q ≤ k` on `U` bounds the `C^k(U)` norm. -/
theorem normCkE_le_of_bound {k : ℕ} {U : Set E} {h : E → F} (M : ℕ → ℝ)
    (hM : ∀ q ≤ k, ∀ x ∈ U, ‖iteratedFDeriv ℝ q h x‖ ≤ M q) :
    normCkE k U h ≤ ∑ q ∈ Finset.range (k + 1), ENNReal.ofReal (M q) :=
  Finset.sum_le_sum fun q hq =>
    supIterDerivE_le_ofReal (hM q (Nat.lt_succ_iff.1 (Finset.mem_range.1 hq)))

theorem normCkE_ne_top_of_bound {k : ℕ} {U : Set E} {h : E → F} (M : ℕ → ℝ)
    (hM : ∀ q ≤ k, ∀ x ∈ U, ‖iteratedFDeriv ℝ q h x‖ ≤ M q) : normCkE k U h ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.sum_ne_top.2 fun _ _ => ENNReal.ofReal_ne_top)
    (normCkE_le_of_bound M hM)

theorem normCk_le_of_bound {k : ℕ} {U : Set E} {h : E → F} (M : ℕ → ℝ) (hM0 : ∀ q, 0 ≤ M q)
    (hM : ∀ q ≤ k, ∀ x ∈ U, ‖iteratedFDeriv ℝ q h x‖ ≤ M q) :
    normCk k U h ≤ ∑ q ∈ Finset.range (k + 1), M q := by
  have h1 := normCkE_le_of_bound M hM
  have h2 : (∑ q ∈ Finset.range (k + 1), ENNReal.ofReal (M q)).toReal =
      ∑ q ∈ Finset.range (k + 1), M q := by
    rw [ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)]
    exact Finset.sum_congr rfl fun q _ => ENNReal.toReal_ofReal (hM0 q)
  rw [normCk, ← h2]
  exact ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun _ _ => ENNReal.ofReal_ne_top) h1

theorem IsCkNear.mono_set {k : ℕ} {U U' : Set E} {h : E → F} (hh : IsCkNear k U' h)
    (hU : U ⊆ U') : IsCkNear k U h := by
  obtain ⟨V, hV, hUV, hcd⟩ := hh
  exact ⟨V, hV, hU.trans hUV, hcd⟩

theorem IsCkNear.mono_order {k k' : ℕ} {U : Set E} {h : E → F} (hh : IsCkNear k' U h)
    (hk : k ≤ k') : IsCkNear k U h := by
  obtain ⟨V, hV, hUV, hcd⟩ := hh
  exact ⟨V, hV, hUV, hcd.of_le (by exact_mod_cast hk)⟩

theorem MemCk.mono_set {k : ℕ} {U U' : Set E} {h : E → F} (hh : MemCk k U' h) (hU : U ⊆ U') :
    MemCk k U h :=
  ⟨hh.near.mono_set hU, ne_top_of_le_ne_top hh.finite (normCkE_mono_set k hU h)⟩

theorem MemCk.mono_order {k k' : ℕ} {U : Set E} {h : E → F} (hh : MemCk k' U h) (hk : k ≤ k') :
    MemCk k U h :=
  ⟨hh.near.mono_order hk, ne_top_of_le_ne_top hh.finite (normCkE_mono_order hk U h)⟩

theorem normCk_mono_set {k : ℕ} {U U' : Set E} {h : E → F} (hh : MemCk k U' h) (hU : U ⊆ U') :
    normCk k U h ≤ normCk k U' h :=
  ENNReal.toReal_mono hh.finite (normCkE_mono_set k hU h)

theorem normCk_mono_order {k k' : ℕ} {U : Set E} {h : E → F} (hh : MemCk k' U h) (hk : k ≤ k') :
    normCk k U h ≤ normCk k' U h :=
  ENNReal.toReal_mono hh.finite (normCkE_mono_order hk U h)

end NonUniqueEuler
