import NonUniqueEuler.Defs.Infra.CkNorm
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Proof: basic algebra of `C^k(U)` norms (library I-CK)

Proves the declarations of `NonUniqueEuler/I/Infra/CkNorm/Basic.lean` (same names, statements
copied verbatim): finiteness on compact sets, the triangle inequality, homogeneity, constants,
and `‖h‖_{C^0(U)} = sup_U |h|` (`02_prelim.tex:72-79`).

Proof outline.
* `memCk_of_isCompact`: `iteratedFDeriv ℝ q h` is continuous on the open set where `h` is `C^k`
  (`ContinuousOn.continuousOn_iteratedFDeriv`), hence bounded on the compact `U`.
* `add`/`sub`: pointwise `iteratedFDeriv_add_apply`/`iteratedFDeriv_sub_apply` at each `x ∈ U`
  (where `h` is `C^k` at `x`), then the triangle inequality for `‖·‖ₑ` and sums in `ℝ≥0∞`.
* `smul`: for `c ≠ 0`, `c • ·` is a continuous linear equivalence, which commutes with
  `iteratedFDeriv` unconditionally (`ContinuousLinearEquiv.iteratedFDeriv_comp_left`); `c = 0`
  is trivial. Hence `normCkE k U (c • f) = ‖c‖ₑ * normCkE k U f` with no regularity hypothesis.
* `neg`: `iteratedFDeriv_neg_apply` (unconditional).
* `const`: `iteratedFDeriv_const_of_ne` for `q ≠ 0`, `norm_iteratedFDeriv_zero` for `q = 0`.
-/

noncomputable section

open scoped ENNReal ContDiff
open Set

namespace NonUniqueEuler

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-! ### Auxiliary lemmas -/

private lemma isCkNear_contDiffAt {k : ℕ} {U : Set E} {f : E → F} (hf : IsCkNear k U f)
    {x : E} (hx : x ∈ U) {q : ℕ} (hq : q ≤ k) : ContDiffAt ℝ q f x := by
  obtain ⟨V, hV, hUV, hcd⟩ := hf
  exact (hcd.contDiffAt (hV.mem_nhds (hUV hx))).of_le (by exact_mod_cast hq)

private lemma isCkNear_add {k : ℕ} {U : Set E} {f g : E → F} (hf : IsCkNear k U f)
    (hg : IsCkNear k U g) : IsCkNear k U (f + g) := by
  obtain ⟨V, hV, hUV, hcf⟩ := hf
  obtain ⟨W, hW, hUW, hcg⟩ := hg
  exact ⟨V ∩ W, hV.inter hW, subset_inter hUV hUW,
    (hcf.mono inter_subset_left).add (hcg.mono inter_subset_right)⟩

private lemma isCkNear_sub {k : ℕ} {U : Set E} {f g : E → F} (hf : IsCkNear k U f)
    (hg : IsCkNear k U g) : IsCkNear k U (f - g) := by
  obtain ⟨V, hV, hUV, hcf⟩ := hf
  obtain ⟨W, hW, hUW, hcg⟩ := hg
  exact ⟨V ∩ W, hV.inter hW, subset_inter hUV hUW,
    (hcf.mono inter_subset_left).sub (hcg.mono inter_subset_right)⟩

private lemma supIterDerivE_add_le {k q : ℕ} {U : Set E} {f g : E → F} (hf : IsCkNear k U f)
    (hg : IsCkNear k U g) (hq : q ≤ k) :
    supIterDerivE q U (f + g) ≤ supIterDerivE q U f + supIterDerivE q U g := by
  refine iSup₂_le fun x hx => ?_
  rw [iteratedFDeriv_add_apply (isCkNear_contDiffAt hf hx hq) (isCkNear_contDiffAt hg hx hq)]
  have h1 := enorm_iteratedFDeriv_le_supIterDerivE (q := q) f hx
  have h2 := enorm_iteratedFDeriv_le_supIterDerivE (q := q) g hx
  exact (enorm_add_le (iteratedFDeriv ℝ q f x) (iteratedFDeriv ℝ q g x)).trans
    (add_le_add h1 h2)

private lemma supIterDerivE_sub_le {k q : ℕ} {U : Set E} {f g : E → F} (hf : IsCkNear k U f)
    (hg : IsCkNear k U g) (hq : q ≤ k) :
    supIterDerivE q U (f - g) ≤ supIterDerivE q U f + supIterDerivE q U g := by
  refine iSup₂_le fun x hx => ?_
  rw [iteratedFDeriv_sub_apply (isCkNear_contDiffAt hf hx hq) (isCkNear_contDiffAt hg hx hq)]
  have h1 := enorm_iteratedFDeriv_le_supIterDerivE (q := q) f hx
  have h2 := enorm_iteratedFDeriv_le_supIterDerivE (q := q) g hx
  exact enorm_sub_le.trans (add_le_add h1 h2)

private lemma normCkE_add_le {k : ℕ} {U : Set E} {f g : E → F} (hf : IsCkNear k U f)
    (hg : IsCkNear k U g) : normCkE k U (f + g) ≤ normCkE k U f + normCkE k U g := by
  unfold normCkE
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun q hq =>
    supIterDerivE_add_le hf hg (Nat.lt_succ_iff.1 (Finset.mem_range.1 hq))

private lemma normCkE_sub_le {k : ℕ} {U : Set E} {f g : E → F} (hf : IsCkNear k U f)
    (hg : IsCkNear k U g) : normCkE k U (f - g) ≤ normCkE k U f + normCkE k U g := by
  unfold normCkE
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun q hq =>
    supIterDerivE_sub_le hf hg (Nat.lt_succ_iff.1 (Finset.mem_range.1 hq))

/-- Iterated derivatives commute with real scalar multiplication, with no regularity
hypothesis. -/
private lemma iteratedFDeriv_const_smul_apply_any (q : ℕ) (c : ℝ) (f : E → F) (x : E) :
    iteratedFDeriv ℝ q (c • f) x = c • iteratedFDeriv ℝ q f x := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [zero_smul, iteratedFDeriv_zero]
  · let L : F ≃L[ℝ] F := ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)
    have hL : c • f = L ∘ f := by
      funext y
      simp [L, Units.smul_def]
    rw [hL, L.iteratedFDeriv_comp_left]
    ext m
    simp [L, Units.smul_def]

private lemma supIterDerivE_smul (q : ℕ) (U : Set E) (c : ℝ) (f : E → F) :
    supIterDerivE q U (c • f) = ‖c‖ₑ * supIterDerivE q U f := by
  simp only [supIterDerivE, iteratedFDeriv_const_smul_apply_any, enorm_smul, ENNReal.mul_iSup]

private lemma normCkE_smul (k : ℕ) (U : Set E) (c : ℝ) (f : E → F) :
    normCkE k U (c • f) = ‖c‖ₑ * normCkE k U f := by
  simp only [normCkE, supIterDerivE_smul, Finset.mul_sum]

private lemma enorm_iteratedFDeriv_zero_eq (h : E → F) (x : E) :
    ‖iteratedFDeriv ℝ 0 h x‖ₑ = ‖h x‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, norm_iteratedFDeriv_zero]

/-! ### The interface declarations -/

/-- A function that is `C^k` near a compact set has finite `C^k` norm on it. -/
theorem IsCkNear.memCk_of_isCompact {k : ℕ} {U : Set E} {h : E → F} (hh : IsCkNear k U h)
    (hU : IsCompact U) : MemCk k U h := by
  refine ⟨hh, ?_⟩
  obtain ⟨V, hV, hUV, hcd⟩ := hh
  have hbd : ∀ q, q ≤ k → ∃ C, ∀ x ∈ U, ‖iteratedFDeriv ℝ q h x‖ ≤ C := fun q hq =>
    hU.exists_bound_of_continuousOn
      ((ContinuousOn.continuousOn_iteratedFDeriv hcd hV (by exact_mod_cast hq)).mono hUV)
  choose! M hM using hbd
  exact normCkE_ne_top_of_bound M hM

/-- The triangle inequality for `C^k(U)` norms. -/
theorem MemCk.add {k : ℕ} {U : Set E} {f g : E → F} (hf : MemCk k U f) (hg : MemCk k U g) :
    MemCk k U (f + g) ∧ normCk k U (f + g) ≤ normCk k U f + normCk k U g := by
  have hle := normCkE_add_le hf.near hg.near
  have hsum : normCkE k U f + normCkE k U g ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hf.finite, hg.finite⟩
  refine ⟨⟨isCkNear_add hf.near hg.near, ne_top_of_le_ne_top hsum hle⟩, ?_⟩
  unfold normCk
  rw [← ENNReal.toReal_add hf.finite hg.finite]
  exact ENNReal.toReal_mono hsum hle

theorem MemCk.sub {k : ℕ} {U : Set E} {f g : E → F} (hf : MemCk k U f) (hg : MemCk k U g) :
    MemCk k U (f - g) ∧ normCk k U (f - g) ≤ normCk k U f + normCk k U g := by
  have hle := normCkE_sub_le hf.near hg.near
  have hsum : normCkE k U f + normCkE k U g ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hf.finite, hg.finite⟩
  refine ⟨⟨isCkNear_sub hf.near hg.near, ne_top_of_le_ne_top hsum hle⟩, ?_⟩
  unfold normCk
  rw [← ENNReal.toReal_add hf.finite hg.finite]
  exact ENNReal.toReal_mono hsum hle

/-- Homogeneity, for real scalars (no regularity hypothesis is needed). -/
theorem normCk_smul (k : ℕ) (U : Set E) (c : ℝ) (f : E → F) :
    normCk k U (c • f) = |c| * normCk k U f := by
  rw [normCk, normCkE_smul, ENNReal.toReal_mul, toReal_enorm, Real.norm_eq_abs, normCk]

theorem MemCk.smul {k : ℕ} {U : Set E} {f : E → F} (hf : MemCk k U f) (c : ℝ) :
    MemCk k U (c • f) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨V, hV, hUV, hcd⟩ := hf.near
    exact ⟨V, hV, hUV, hcd.const_smul c⟩
  · rw [normCkE_smul]
    exact ENNReal.mul_ne_top enorm_ne_top hf.finite

theorem normCk_neg (k : ℕ) (U : Set E) (f : E → F) : normCk k U (-f) = normCk k U f := by
  simp only [normCk, normCkE, supIterDerivE, iteratedFDeriv_neg_apply, enorm_neg]

/-- Constants: `‖c‖_{C^k(U)} = ‖c‖` on a nonempty set. -/
theorem memCk_const_and_normCk (k : ℕ) {U : Set E} (hU : U.Nonempty) (c : F) :
    MemCk k U (fun _ => c) ∧ normCk k U (fun _ => c) = ‖c‖ := by
  have hsup : ∀ q, supIterDerivE q U (fun _ : E => c) = if q = 0 then ‖c‖ₑ else 0 := by
    intro q
    rcases eq_or_ne q 0 with rfl | hq
    · simp only [supIterDerivE, enorm_iteratedFDeriv_zero_eq, ite_true]
      exact biSup_const hU
    · simp [supIterDerivE, iteratedFDeriv_const_of_ne hq, hq, ← ofReal_norm]
  have hE : normCkE k U (fun _ : E => c) = ‖c‖ₑ := by
    simp only [normCkE, hsup, Finset.sum_ite_eq', Finset.mem_range]
    simp
  refine ⟨⟨⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩, ?_⟩, ?_⟩
  · rw [hE]
    exact enorm_ne_top
  · rw [normCk, hE, toReal_enorm]

/-- `‖h‖_{C^0(U)} = sup_{x ∈ U} ‖h x‖`, as an `ℝ≥0∞` identity. -/
theorem normCkE_zero (U : Set E) (h : E → F) : normCkE 0 U h = ⨆ x ∈ U, ‖h x‖ₑ := by
  simp only [normCkE, supIterDerivE, zero_add, Finset.sum_range_one,
    enorm_iteratedFDeriv_zero_eq]

end NonUniqueEuler
