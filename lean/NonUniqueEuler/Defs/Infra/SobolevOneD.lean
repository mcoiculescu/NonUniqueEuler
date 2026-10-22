import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import NonUniqueEuler.Defs.Infra.Sobolev

/-!
# One-dimensional weighted Sobolev norms (definitions; library I-SOB1)

Manuscript-independent infrastructure (library I-SOB1; restructuring R4). Used by `lem:norm-equiv`,
`lem:elliptic`, `cor:K-bound` and `lem:semigroup-construct`(1) (`04_ring.tex:836-1013`).

Weak derivatives on the line are the generic ones of `Defs/Infra/Sobolev.lean` with
`E = ℝ` and the direction list `derivList j = [1, …, 1]` (`j` times), so a classical
`j`-th derivative is `iteratedDeriv j` (`iterDirDeriv_derivList`).

Definitions.
* `derivList j`, `weakDeriv1On V j g` (the weak `j`-th derivative of `g` on `V ⊆ ℝ`);
* `MemH1On k V g`: `g ∈ H^k(V)` on the line (`L²` for Lebesgue measure `dr`);
* `secNormSq k ℓ I g = ∑_{j ≤ k} (1+ℓ²)^{k-j} ∫_I |∂_r^j g|² r dr` and `secNorm = √secNormSq`:
  the manuscript's `‖g‖²_{k,ℓ;I}` (`04_ring.tex:838-841`; `‖g‖_{k,ℓ}` is `I = [ρ₋, ρ₊]`).
  Radial profiles live on `(0, ∞)`: the weak derivatives are taken on `Ioi 0`;
* `logNormSqOn k ℓ J u = ∑_{j ≤ k} (1+ℓ²)^{k-j} ∫_J |∂_x^j u|² dx` and
  `logNormSq k ℓ u = logNormSqOn k ℓ univ u`: the manuscript's `|u|²_{k,ℓ}` in the log variable
  `x = log r` (`04_ring.tex:881`), weak derivatives on `ℝ`;
* `yukawa ℓ f x = -(2|ℓ|)⁻¹ ∫ e^{-|ℓ||x-y|} f(y) dy`, the decaying solution of
  `ψ'' - ℓ²ψ = f` (`04_ring.tex:878-880`).

Junk values: if a weak derivative does not exist, `weakDeriv1On` is `0`; a non-integrable
integrand gives `0`. Consumers carry `MemH1On` hypotheses.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace NonUniqueEuler.Sob

/-- The direction list of the `j`-th derivative on the line: `j` copies of `1`. -/
def derivList (j : ℕ) : List ℝ :=
  List.replicate j (1 : ℝ)

/-- The weak `j`-th derivative of `g` on `V ⊆ ℝ` (chosen; `0` if none exists). -/
def weakDeriv1On (V : Set ℝ) (j : ℕ) (g : ℝ → ℂ) : ℝ → ℂ :=
  weakDerivOn V (derivList j) g

/-- `g ∈ H^k(V)` on the line: `g ∈ L²(V)` and the weak derivatives of order `≤ k` exist in
`L²(V)`. -/
structure MemH1On (k : ℕ) (V : Set ℝ) (g : ℝ → ℂ) : Prop where
  memLp : MemLp g 2 (volume.restrict V)
  deriv : ∀ j ≤ k, ∃ h : ℝ → ℂ, MemLp h 2 (volume.restrict V) ∧
    HasWeakDerivOn V (derivList j) g h

/-- The weight `(1 + ℓ²)^{k-j}` of the sector norms. -/
def secWeight (k j : ℕ) (ℓ : ℤ) : ℝ :=
  (1 + (ℓ : ℝ) ^ 2) ^ (k - j)

/-- The manuscript's `‖g‖²_{k,ℓ;I} = ∑_{j ≤ k} (1+ℓ²)^{k-j} ‖∂_r^j g‖²_{L²(I, r dr)}`
(`04_ring.tex:838-841`), with weak derivatives on `(0, ∞)`. -/
def secNormSq (k : ℕ) (ℓ : ℤ) (I : Set ℝ) (g : ℝ → ℂ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1),
    secWeight k j ℓ * ∫ r in I, ‖weakDeriv1On (Ioi 0) j g r‖ ^ 2 * r

/-- `‖g‖_{k,ℓ;I}`. -/
def secNorm (k : ℕ) (ℓ : ℤ) (I : Set ℝ) (g : ℝ → ℂ) : ℝ :=
  Real.sqrt (secNormSq k ℓ I g)

/-- The log-variable norm `∑_{j ≤ k} (1+ℓ²)^{k-j} ‖∂_x^j u‖²_{L²(J)}`, weak derivatives on `ℝ`. -/
def logNormSqOn (k : ℕ) (ℓ : ℤ) (J : Set ℝ) (u : ℝ → ℂ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1),
    secWeight k j ℓ * ∫ x in J, ‖weakDeriv1On univ j u x‖ ^ 2

/-- The manuscript's `|u|²_{k,ℓ} = ∑_{j ≤ k} (1+ℓ²)^{k-j} ‖∂_x^j u‖²_{L²(ℝ)}` (`04_ring.tex:881`). -/
def logNormSq (k : ℕ) (ℓ : ℤ) (u : ℝ → ℂ) : ℝ :=
  logNormSqOn k ℓ univ u

/-- The decaying solution `ψ = -(2|ℓ|)⁻¹ e^{-|ℓ||·|} ⋆ f` of `ψ'' - ℓ²ψ = f` on `ℝ`
(`04_ring.tex:878-880`, the Green function of `lem:elliptic` in the log variable). -/
def yukawa (ℓ : ℤ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  -(((2 * |(ℓ : ℝ)|)⁻¹ : ℝ) : ℂ) *
    ∫ y, ((Real.exp (-|(ℓ : ℝ)| * |x - y|) : ℝ) : ℂ) * f y

/-! ### Basic lemmas (fully proved) -/

@[simp] theorem derivList_length (j : ℕ) : (derivList j).length = j := by
  simp [derivList]

/-- Classical derivatives along `derivList j` are iterated derivatives. -/
theorem iterDirDeriv_derivList (j : ℕ) (φ : ℝ → ℂ) :
    iterDirDeriv (derivList j) φ = iteratedDeriv j φ := by
  induction j with
  | zero => simp [derivList]
  | succ j ih =>
    rw [iteratedDeriv_succ, ← ih]
    simp only [derivList, List.replicate_succ, iterDirDeriv_cons]
    rfl

theorem secWeight_nonneg (k j : ℕ) (ℓ : ℤ) : 0 ≤ secWeight k j ℓ :=
  pow_nonneg (by positivity) _

theorem one_le_secWeight (k j : ℕ) (ℓ : ℤ) : 1 ≤ secWeight k j ℓ :=
  one_le_pow₀ (by nlinarith [sq_nonneg (ℓ : ℝ)])

theorem secNormSq_nonneg (k : ℕ) (ℓ : ℤ) {I : Set ℝ} (hIm : MeasurableSet I) (hI : I ⊆ Ici 0)
    (g : ℝ → ℂ) : 0 ≤ secNormSq k ℓ I g := by
  refine Finset.sum_nonneg fun j _ => mul_nonneg (secWeight_nonneg k j ℓ) ?_
  refine setIntegral_nonneg hIm fun r hr => ?_
  exact mul_nonneg (sq_nonneg _) (hI hr)

theorem logNormSqOn_nonneg (k : ℕ) (ℓ : ℤ) (J : Set ℝ) (u : ℝ → ℂ) :
    0 ≤ logNormSqOn k ℓ J u :=
  Finset.sum_nonneg fun j _ => mul_nonneg (secWeight_nonneg k j ℓ)
    (setIntegral_nonneg_of_ae_restrict (Filter.Eventually.of_forall fun _ => sq_nonneg _))

theorem MemH1On.mono_order {k k' : ℕ} {V : Set ℝ} {g : ℝ → ℂ} (h : MemH1On k' V g)
    (hk : k ≤ k') : MemH1On k V g :=
  ⟨h.memLp, fun j hj => h.deriv j (hj.trans hk)⟩

end NonUniqueEuler.Sob
