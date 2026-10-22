import NonUniqueEuler.Defs.Infra.CkNorm
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Proof: the Leibniz bound for `C^k(U)` norms (library I-CK)

Proof of `NonUniqueEuler/I/Infra/CkNorm/Leibniz.lean`.

`‖f g‖_{C^k(U)} ≤ 2^k ‖f‖_{C^k(U)} ‖g‖_{C^k(U)}`, for a real scalar function times a
vector-valued one and for two complex functions (used in `lem:bilinear`(2),
`05_single_ring.tex:258-263`).

Proof. At `x ∈ U` both factors are `C^k` on the open set `V ∩ W ⊇ U`; Mathlib's
`norm_iteratedFDerivWithin_smul_le` / `norm_iteratedFDerivWithin_mul_le` on `V ∩ W`, together with
`iteratedFDerivWithin_of_isOpen`, give the pointwise Leibniz bound
`‖D^q(fg)(x)‖ ≤ ∑_{i ≤ q} C(q,i) ‖D^i f(x)‖ ‖D^{q-i} g(x)‖`. With `a_i = sup_U ‖D^i f‖`,
`b_j = sup_U ‖D^j g‖`, the elementary inequality
`∑_{q ≤ k} ∑_{i ≤ q} C(q,i) a_i b_{q-i} ≤ 2^k (∑_{i ≤ k} a_i)(∑_{j ≤ k} b_j)`
(`C(q,i) ≤ 2^q ≤ 2^k`, and each pair `(i, j)` with `i + j ≤ k` occurs once) concludes.
-/

noncomputable section

open scoped ENNReal ContDiff
open Set

namespace NonUniqueEuler

namespace LeibnizAux

/-- `∑_{q ≤ k} ∑_{i ≤ q} a_i b_{q-i} ≤ (∑_{i ≤ k} a_i)(∑_{j ≤ k} b_j)` for nonnegative `a`, `b`. -/
theorem sum_antidiag_le (k : ℕ) (a b : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j) :
    ∑ q ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (q + 1), a i * b (q - i) ≤
      (∑ i ∈ Finset.range (k + 1), a i) * ∑ j ∈ Finset.range (k + 1), b j := by
  rw [Finset.sum_comm' (t' := Finset.range (k + 1)) (s' := fun i => Finset.Ico i (k + 1))]
  · rw [Finset.sum_mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (ha i)
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (Nat.sub_le _ _))
      (fun j _ _ => hb j)
  · intro q i
    simp only [Finset.mem_range, Finset.mem_Ico]
    omega

/-- The combinatorial inequality
`∑_{q ≤ k} ∑_{i ≤ q} C(q,i) a_i b_{q-i} ≤ 2^k (∑_{i ≤ k} a_i)(∑_{j ≤ k} b_j)`. -/
theorem sum_choose_mul_le (k : ℕ) (a b : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j) :
    ∑ q ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * a i * b (q - i) ≤
      2 ^ k * (∑ i ∈ Finset.range (k + 1), a i) * ∑ j ∈ Finset.range (k + 1), b j := by
  have h1 : ∀ q ∈ Finset.range (k + 1), ∀ i ∈ Finset.range (q + 1),
      (q.choose i : ℝ) * a i * b (q - i) ≤ 2 ^ k * (a i * b (q - i)) := by
    intro q hq i _
    have hq' : q ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hq)
    have hc : (q.choose i : ℝ) ≤ 2 ^ k :=
      calc (q.choose i : ℝ) ≤ 2 ^ q := by exact_mod_cast Nat.choose_le_two_pow q i
        _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hq'
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right hc (mul_nonneg (ha i) (hb _))
  calc _ ≤ ∑ q ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (q + 1), 2 ^ k * (a i * b (q - i)) :=
        Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun i hi => h1 q hq i hi
    _ = 2 ^ k * ∑ q ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (q + 1), a i * b (q - i) := by
        rw [Finset.mul_sum]
        simp_rw [Finset.mul_sum]
    _ ≤ 2 ^ k * ((∑ i ∈ Finset.range (k + 1), a i) * ∑ j ∈ Finset.range (k + 1), b j) :=
        mul_le_mul_of_nonneg_left (sum_antidiag_le k a b ha hb) (by positivity)
    _ = _ := by ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `normCk` is the sum of the (finite) real suprema. -/
theorem normCk_eq_sum {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {k : ℕ} {U : Set E}
    {f : E → G} (hf : normCkE k U f ≠ ⊤) :
    normCk k U f = ∑ i ∈ Finset.range (k + 1), (supIterDerivE i U f).toReal := by
  rw [normCk, normCkE, ENNReal.toReal_sum]
  intro i hi
  exact ne_top_of_le_ne_top hf
    (supIterDerivE_le_normCkE (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) U f)

/-- The pointwise bound by the real supremum. -/
theorem norm_iteratedFDeriv_le_sup {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {k i : ℕ} (hi : i ≤ k) {U : Set E} {f : E → G} (hf : normCkE k U f ≠ ⊤) {x : E}
    (hx : x ∈ U) : ‖iteratedFDeriv ℝ i f x‖ ≤ (supIterDerivE i U f).toReal := by
  have hfin : supIterDerivE i U f ≠ ⊤ :=
    ne_top_of_le_ne_top hf (supIterDerivE_le_normCkE hi U f)
  have h := ENNReal.toReal_mono hfin (enorm_iteratedFDeriv_le_supIterDerivE (q := i) f hx)
  simpa using h

/-- From a pointwise Leibniz bound on `U` to the `C^k(U)` bound. -/
theorem normCk_le_of_pointwise {G H K : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup K] [NormedSpace ℝ K]
    {k : ℕ} {U : Set E} {f : E → G} {g : E → H} {h : E → K}
    (hf : normCkE k U f ≠ ⊤) (hg : normCkE k U g ≠ ⊤)
    (hpt : ∀ q ≤ k, ∀ x ∈ U, ‖iteratedFDeriv ℝ q h x‖ ≤
      ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
        ‖iteratedFDeriv ℝ (q - i) g x‖) :
    normCkE k U h ≠ ⊤ ∧ normCk k U h ≤ 2 ^ k * normCk k U f * normCk k U g := by
  set a : ℕ → ℝ := fun i => (supIterDerivE i U f).toReal with ha_def
  set b : ℕ → ℝ := fun j => (supIterDerivE j U g).toReal with hb_def
  have ha0 : ∀ i, 0 ≤ a i := fun _ => ENNReal.toReal_nonneg
  have hb0 : ∀ j, 0 ≤ b j := fun _ => ENNReal.toReal_nonneg
  set M : ℕ → ℝ := fun q =>
    ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * a i * b (q - i) with hM_def
  have hM0 : ∀ q, 0 ≤ M q := fun q =>
    Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (ha0 i)) (hb0 _)
  have hM : ∀ q ≤ k, ∀ x ∈ U, ‖iteratedFDeriv ℝ q h x‖ ≤ M q := by
    intro q hq x hx
    refine (hpt q hq x hx).trans (Finset.sum_le_sum fun i hi => ?_)
    have hi' : i ≤ q := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have h1 := norm_iteratedFDeriv_le_sup (hi'.trans hq) hf hx
    have h2 := norm_iteratedFDeriv_le_sup ((Nat.sub_le q i).trans hq) hg hx
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2 (norm_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (ha0 i))
  refine ⟨normCkE_ne_top_of_bound M hM, (normCk_le_of_bound M hM0 hM).trans ?_⟩
  rw [normCk_eq_sum hf, normCk_eq_sum hg]
  exact sum_choose_mul_le k a b ha0 hb0

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Pointwise Leibniz bound for `f • g` with `f` real, both `C^k` near `U`. -/
theorem pointwise_smul {k q : ℕ} (hq : q ≤ k) {U : Set E} {f : E → ℝ} {g : E → F}
    (hf : IsCkNear k U f) (hg : IsCkNear k U g) {x : E} (hx : x ∈ U) :
    ‖iteratedFDeriv ℝ q (fun y => f y • g y) x‖ ≤
      ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
        ‖iteratedFDeriv ℝ (q - i) g x‖ := by
  obtain ⟨V, hV, hUV, hfV⟩ := hf
  obtain ⟨W, hW, hUW, hgW⟩ := hg
  have hVW : IsOpen (V ∩ W) := hV.inter hW
  have hxVW : x ∈ V ∩ W := ⟨hUV hx, hUW hx⟩
  have h := norm_iteratedFDerivWithin_smul_le (hfV.mono inter_subset_left)
    (hgW.mono inter_subset_right) hVW.uniqueDiffOn hxVW (n := q) (by exact_mod_cast hq)
  have ef : ∀ n : ℕ, iteratedFDerivWithin ℝ n f (V ∩ W) x = iteratedFDeriv ℝ n f x :=
    fun n => iteratedFDerivWithin_of_isOpen n hVW hxVW
  have eg : ∀ n : ℕ, iteratedFDerivWithin ℝ n g (V ∩ W) x = iteratedFDeriv ℝ n g x :=
    fun n => iteratedFDerivWithin_of_isOpen n hVW hxVW
  have efg : iteratedFDerivWithin ℝ q (fun y => f y • g y) (V ∩ W) x =
      iteratedFDeriv ℝ q (fun y => f y • g y) x := iteratedFDerivWithin_of_isOpen q hVW hxVW
  simp only [ef, eg, efg] at h
  exact h

/-- Pointwise Leibniz bound for `f * g` with `f, g` complex, both `C^k` near `U`. -/
theorem pointwise_mul {k q : ℕ} (hq : q ≤ k) {U : Set E} {f g : E → ℂ}
    (hf : IsCkNear k U f) (hg : IsCkNear k U g) {x : E} (hx : x ∈ U) :
    ‖iteratedFDeriv ℝ q (fun y => f y * g y) x‖ ≤
      ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
        ‖iteratedFDeriv ℝ (q - i) g x‖ := by
  obtain ⟨V, hV, hUV, hfV⟩ := hf
  obtain ⟨W, hW, hUW, hgW⟩ := hg
  have hVW : IsOpen (V ∩ W) := hV.inter hW
  have hxVW : x ∈ V ∩ W := ⟨hUV hx, hUW hx⟩
  have h := norm_iteratedFDerivWithin_mul_le (hfV.mono inter_subset_left)
    (hgW.mono inter_subset_right) hVW.uniqueDiffOn hxVW (n := q) (by exact_mod_cast hq)
  have ef : ∀ n : ℕ, iteratedFDerivWithin ℝ n f (V ∩ W) x = iteratedFDeriv ℝ n f x :=
    fun n => iteratedFDerivWithin_of_isOpen n hVW hxVW
  have eg : ∀ n : ℕ, iteratedFDerivWithin ℝ n g (V ∩ W) x = iteratedFDeriv ℝ n g x :=
    fun n => iteratedFDerivWithin_of_isOpen n hVW hxVW
  have efg : iteratedFDerivWithin ℝ q (fun y => f y * g y) (V ∩ W) x =
      iteratedFDeriv ℝ q (fun y => f y * g y) x := iteratedFDerivWithin_of_isOpen q hVW hxVW
  simp only [ef, eg, efg] at h
  exact h

theorem isCkNear_smul {k : ℕ} {U : Set E} {f : E → ℝ} {g : E → F}
    (hf : IsCkNear k U f) (hg : IsCkNear k U g) : IsCkNear k U (fun x => f x • g x) := by
  obtain ⟨V, hV, hUV, hfV⟩ := hf
  obtain ⟨W, hW, hUW, hgW⟩ := hg
  exact ⟨V ∩ W, hV.inter hW, subset_inter hUV hUW,
    (hfV.mono inter_subset_left).smul (hgW.mono inter_subset_right)⟩

theorem isCkNear_mul {k : ℕ} {U : Set E} {f g : E → ℂ}
    (hf : IsCkNear k U f) (hg : IsCkNear k U g) : IsCkNear k U (fun x => f x * g x) := by
  obtain ⟨V, hV, hUV, hfV⟩ := hf
  obtain ⟨W, hW, hUW, hgW⟩ := hg
  exact ⟨V ∩ W, hV.inter hW, subset_inter hUV hUW,
    (hfV.mono inter_subset_left).mul (hgW.mono inter_subset_right)⟩

end LeibnizAux

open LeibnizAux

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- Leibniz bound for a real function times a vector-valued function. -/
theorem MemCk.smul_fun {k : ℕ} {U : Set E} {f : E → ℝ} {g : E → F} (hf : MemCk k U f)
    (hg : MemCk k U g) :
    MemCk k U (fun x => f x • g x) ∧
      normCk k U (fun x => f x • g x) ≤ 2 ^ k * normCk k U f * normCk k U g := by
  obtain ⟨hfin, hle⟩ := normCk_le_of_pointwise (h := fun x => f x • g x) hf.finite hg.finite
    (fun q hq x hx => pointwise_smul hq hf.near hg.near hx)
  exact ⟨⟨isCkNear_smul hf.near hg.near, hfin⟩, hle⟩

/-- Leibniz bound for a product of complex functions. -/
theorem MemCk.mul {k : ℕ} {U : Set E} {f g : E → ℂ} (hf : MemCk k U f) (hg : MemCk k U g) :
    MemCk k U (fun x => f x * g x) ∧
      normCk k U (fun x => f x * g x) ≤ 2 ^ k * normCk k U f * normCk k U g := by
  obtain ⟨hfin, hle⟩ := normCk_le_of_pointwise (h := fun x => f x * g x) hf.finite hg.finite
    (fun q hq x hx => pointwise_mul hq hf.near hg.near hx)
  exact ⟨⟨isCkNear_mul hf.near hg.near, hfin⟩, hle⟩

/-- The pointwise Leibniz bound at a point of `U`, for each order `q ≤ k`. -/
theorem norm_iteratedFDeriv_mul_le_of_memCk {k q : ℕ} (hq : q ≤ k) {U : Set E} {f g : E → ℂ}
    (hf : MemCk k U f) (hg : MemCk k U g) {x : E} (hx : x ∈ U) :
    ‖iteratedFDeriv ℝ q (fun y => f y * g y) x‖ ≤
      ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
        ‖iteratedFDeriv ℝ (q - i) g x‖ :=
  pointwise_mul hq hf.near hg.near hx

end NonUniqueEuler
