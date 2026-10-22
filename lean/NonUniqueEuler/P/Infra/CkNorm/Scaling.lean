import NonUniqueEuler.Defs.Infra.CkNorm
import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Data.ENNReal.Inv
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Proof: the scaling rule for `C^k` norms (library I-CK)

Proof of `NonUniqueEuler/I/Infra/CkNorm/Scaling.lean`: the manuscript's scaling rule
(`07_several_rings.tex:39-41`): if `W(y) = a V(c y)` then `∇^q W(y) = a c^q (∇^q V)(c y)`, and
`‖W‖_{C^k(U)} ≤ |a| max(1, |c|^k) ‖V‖_{C^k(c U)}`.

For `c ≠ 0` (resp. `a ≠ 0`), `y ↦ c • y` (resp. `v ↦ a • v`) is a continuous linear
equivalence, and composition with a continuous linear equivalence commutes with
`iteratedFDeriv` with no regularity hypothesis. The degenerate cases `c = 0` (constant function)
and `a = 0` (zero function) are treated directly.
-/

noncomputable section

open scoped ENNReal ContDiff Pointwise
open Set

namespace NonUniqueEuler

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- Right composition with `z ↦ c • z`, `c ≠ 0`. -/
theorem iteratedFDeriv_comp_smul_right_of_ne (q : ℕ) (h : E → F) {c : ℝ} (hc : c ≠ 0) (y : E) :
    iteratedFDeriv ℝ q (fun z => h (c • z)) y = c ^ q • iteratedFDeriv ℝ q h (c • y) := by
  set g : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (Units.mk0 c hc) with hgdef
  have hg : ∀ z, g z = c • z := fun z => rfl
  have hfun : (fun z => h (c • z)) = h ∘ g := by
    funext z
    simp [hg]
  have key := g.iteratedFDerivWithin_comp_right h uniqueDiffOn_univ (mem_univ (g y)) q
  rw [preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at key
  rw [hfun, key, hg]
  ext m
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    smul_apply, ContinuousLinearEquiv.coe_coe, hg]
  rw [show (fun i => c • m i) = fun i => (fun _ : Fin q => c) i • m i from rfl,
    ContinuousMultilinearMap.map_smul_univ]
  simp [Finset.prod_const]

/-- Left multiplication by a scalar commutes with `iteratedFDeriv` (no regularity needed). -/
theorem iteratedFDeriv_const_smul_left (q : ℕ) (f : E → F) (a : ℝ) (y : E) :
    iteratedFDeriv ℝ q (fun z => a • f z) y = a • iteratedFDeriv ℝ q f y := by
  by_cases ha : a = 0
  · subst ha
    simp only [zero_smul]
    cases q with
    | zero => ext m; simp
    | succ n => rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]; rfl
  · set g : F ≃L[ℝ] F := ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (Units.mk0 a ha) with hgdef
    have hg : ∀ v, g v = a • v := fun v => rfl
    have hfun : (fun z => a • f z) = g ∘ f := by
      funext z
      simp [hg]
    rw [hfun, g.iteratedFDeriv_comp_left]
    ext m
    simp [hg]

/-- The scaling rule `∇^q (a V(c ·))(y) = a c^q (∇^q V)(c y)` (no regularity hypothesis). -/
theorem iteratedFDeriv_comp_smul (q : ℕ) (h : E → F) (a c : ℝ) (y : E) :
    iteratedFDeriv ℝ q (fun z => a • h (c • z)) y = (a * c ^ q) • iteratedFDeriv ℝ q h (c • y) := by
  rw [iteratedFDeriv_const_smul_left q (fun z => h (c • z)) a y, mul_smul]
  congr 1
  by_cases hc : c = 0
  · subst hc
    simp only [zero_smul]
    cases q with
    | zero => ext m; simp
    | succ n =>
      rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]
      simp
  · exact iteratedFDeriv_comp_smul_right_of_ne q h hc y

/-- The sup of the `q`-th derivative of `a V(c ·)` over `U` is `|a| |c|^q` times the sup of the
`q`-th derivative of `V` over `c • U`. -/
theorem supIterDerivE_comp_smul (q : ℕ) (U : Set E) (h : E → F) (a c : ℝ) :
    supIterDerivE q U (fun z => a • h (c • z)) =
      ‖a‖ₑ * ‖c‖ₑ ^ q * supIterDerivE q (c • U) h := by
  unfold supIterDerivE
  rw [← Set.image_smul, iSup_image]
  simp_rw [iteratedFDeriv_comp_smul, enorm_smul, enorm_mul, enorm_pow, ENNReal.mul_iSup]

/-- `|c|^q ≤ max 1 (|c|^k)` for `q ≤ k`. -/
theorem abs_pow_le_max_one_abs_pow {q k : ℕ} (hq : q ≤ k) (c : ℝ) :
    |c| ^ q ≤ max 1 (|c| ^ k) := by
  rcases le_total |c| 1 with h1 | h1
  · exact le_max_of_le_left (pow_le_one₀ (abs_nonneg c) h1)
  · exact le_max_of_le_right (pow_le_pow_right₀ h1 hq)

/-- `a V(c ·)` is `C^k` near `U` when `V` is `C^k` near `c • U` (the open set is the preimage of
the one for `V` under `z ↦ c • z`). -/
theorem IsCkNear.comp_smul {k : ℕ} {U : Set E} {h : E → F} {c : ℝ} (hh : IsCkNear k (c • U) h)
    (a : ℝ) : IsCkNear k U (fun z => a • h (c • z)) := by
  obtain ⟨V, hV, hUV, hcd⟩ := hh
  refine ⟨(fun z : E => c • z) ⁻¹' V, hV.preimage (continuous_const_smul c), ?_, ?_⟩
  · intro x hx
    exact hUV (Set.smul_mem_smul_set hx)
  · have hlin : ContDiff ℝ k (fun z : E => c • z) := contDiff_const_smul c
    exact (hcd.comp hlin.contDiffOn (fun _ hx => hx)).const_smul a

/-- The `C^k` norm of `a V(c ·)` on `U` in terms of that of `V` on `c • U`. -/
theorem MemCk.comp_smul {k : ℕ} {U : Set E} {h : E → F} {c : ℝ} (hh : MemCk k (c • U) h)
    (a : ℝ) :
    MemCk k U (fun z => a • h (c • z)) ∧
      normCk k U (fun z => a • h (c • z)) ≤ |a| * max 1 (|c| ^ k) * normCk k (c • U) h := by
  have hsup : ∀ q ∈ Finset.range (k + 1), supIterDerivE q (c • U) h ≠ ⊤ := fun q hq =>
    ne_top_of_le_ne_top hh.finite
      (supIterDerivE_le_normCkE (Nat.lt_succ_iff.1 (Finset.mem_range.1 hq)) _ h)
  have hE : normCkE k U (fun z => a • h (c • z)) =
      ∑ q ∈ Finset.range (k + 1), ‖a‖ₑ * ‖c‖ₑ ^ q * supIterDerivE q (c • U) h := by
    unfold normCkE
    exact Finset.sum_congr rfl fun q _ => supIterDerivE_comp_smul q U h a c
  have hfin : normCkE k U (fun z => a • h (c • z)) ≠ ⊤ := by
    rw [hE]
    exact ENNReal.sum_ne_top.2 fun q hq =>
      ENNReal.mul_ne_top (ENNReal.mul_ne_top enorm_ne_top (ENNReal.pow_ne_top enorm_ne_top))
        (hsup q hq)
  refine ⟨⟨hh.near.comp_smul a, hfin⟩, ?_⟩
  have hR : normCk k U (fun z => a • h (c • z)) =
      ∑ q ∈ Finset.range (k + 1), |a| * |c| ^ q * (supIterDerivE q (c • U) h).toReal := by
    unfold normCk
    rw [hE, ENNReal.toReal_sum fun q hq =>
      ENNReal.mul_ne_top (ENNReal.mul_ne_top enorm_ne_top (ENNReal.pow_ne_top enorm_ne_top))
        (hsup q hq)]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, toReal_enorm, toReal_enorm,
      Real.norm_eq_abs, Real.norm_eq_abs]
  have hN : normCk k (c • U) h =
      ∑ q ∈ Finset.range (k + 1), (supIterDerivE q (c • U) h).toReal := by
    unfold normCk normCkE
    exact ENNReal.toReal_sum hsup
  rw [hR, hN, Finset.mul_sum]
  refine Finset.sum_le_sum fun q hq => ?_
  have hq' : q ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hq)
  have h0 : 0 ≤ (supIterDerivE q (c • U) h).toReal := ENNReal.toReal_nonneg
  gcongr
  exact abs_pow_le_max_one_abs_pow hq' c

end NonUniqueEuler
