import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import NonUniqueEuler.Defs.Infra.SobolevOneD
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv

/-!
# Proof: basic facts on one-dimensional weighted norms (library I-SOB1)

Proof of `NonUniqueEuler/I/Infra/SobolevOneD/Basic.lean`.

* Classical derivatives are weak: `hasWeakDerivOn_of_contDiffOn` with `iterDirDeriv_derivList`,
  then `weakDerivOn_ae_eq` (the classical derivative is continuous on the open set `V`, hence
  locally integrable there).
* Monotonicity in `k`: `secWeight` is monotone in `k`, the extra terms are nonnegative.
* Monotonicity in `I`: `setIntegral_mono_set`, integrability on `I' ⊆ (0, R]` from the `L²`
  bound on `(0, ∞)` and `r ≤ R`.
* Weights: the binomial theorem (`add_pow`) and `1 ≤ C(p,n) ≤ 2^p`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace NonUniqueEuler.Sob

/-- On an open set, the classical `j`-th derivative of a `C^k` function (`j ≤ k`) is continuous
on that set. -/
private theorem continuousOn_iteratedDeriv_of_isOpen {k : ℕ} {V : Set ℝ} (hV : IsOpen V)
    {g : ℝ → ℂ} (hg : ContDiffOn ℝ k g V) {j : ℕ} (hj : j ≤ k) :
    ContinuousOn (iteratedDeriv j g) V := by
  have h := hg.continuousOn_iteratedDerivWithin (m := j) (by exact_mod_cast hj)
    hV.uniqueDiffOn
  exact h.congr fun r hr => (iteratedDerivWithin_of_isOpen hV hr).symm

/-- Classical derivatives of a `C^k` function on an open set `V ⊆ ℝ` are its weak derivatives,
a.e. on `V`. -/
theorem weakDeriv1On_ae_eq_iteratedDeriv {k : ℕ} {V : Set ℝ} (hV : IsOpen V) {g : ℝ → ℂ}
    (hg : ContDiffOn ℝ k g V) {j : ℕ} (hj : j ≤ k) :
    ∀ᵐ r, r ∈ V → weakDeriv1On V j g r = iteratedDeriv j g r := by
  have hw : HasWeakDerivOn V (derivList j) g (iteratedDeriv j g) := by
    rw [← iterDirDeriv_derivList]
    exact hasWeakDerivOn_of_contDiffOn hV (n := k) (by simpa using hj) hg
  have hloc : LocallyIntegrableOn (iteratedDeriv j g) V :=
    (continuousOn_iteratedDeriv_of_isOpen hV hg hj).locallyIntegrableOn hV.measurableSet
  exact weakDerivOn_ae_eq hV hloc hw

/-- A `C^k` function on an open `V`, with its derivatives in `L²(V)`, lies in `H^k(V)`. -/
theorem memH1On_of_contDiffOn {k : ℕ} {V : Set ℝ} (hV : IsOpen V) {g : ℝ → ℂ}
    (hg : ContDiffOn ℝ k g V) (hL2 : ∀ j ≤ k, MemLp (iteratedDeriv j g) 2 (volume.restrict V)) :
    MemH1On k V g := by
  refine ⟨?_, fun j hj => ⟨iteratedDeriv j g, hL2 j hj, ?_⟩⟩
  · simpa using hL2 0 (Nat.zero_le k)
  · rw [← iterDirDeriv_derivList]
    exact hasWeakDerivOn_of_contDiffOn hV (n := k) (by simpa using hj) hg

theorem secNormSq_mono_order {k k' : ℕ} (hk : k ≤ k') (ℓ : ℤ) {I : Set ℝ} (hIm : MeasurableSet I)
    (hI : I ⊆ Ici 0) (g : ℝ → ℂ) : secNormSq k ℓ I g ≤ secNormSq k' ℓ I g := by
  have hint : ∀ j, 0 ≤ ∫ r in I, ‖weakDeriv1On (Ioi 0) j g r‖ ^ 2 * r := fun j =>
    setIntegral_nonneg hIm fun r hr => mul_nonneg (sq_nonneg _) (hI hr)
  unfold secNormSq
  calc ∑ j ∈ Finset.range (k + 1),
        secWeight k j ℓ * ∫ r in I, ‖weakDeriv1On (Ioi 0) j g r‖ ^ 2 * r
      ≤ ∑ j ∈ Finset.range (k + 1),
        secWeight k' j ℓ * ∫ r in I, ‖weakDeriv1On (Ioi 0) j g r‖ ^ 2 * r := by
        refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right ?_ (hint j)
        unfold secWeight
        exact pow_le_pow_right₀ (by nlinarith [sq_nonneg (ℓ : ℝ)]) (Nat.sub_le_sub_right hk j)
    _ ≤ ∑ j ∈ Finset.range (k' + 1),
        secWeight k' j ℓ * ∫ r in I, ‖weakDeriv1On (Ioi 0) j g r‖ ^ 2 * r := by
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.2 (by omega)) fun j _ _ => ?_
        exact mul_nonneg (secWeight_nonneg k' j ℓ) (hint j)

/-- The chosen weak derivative of an `H^k((0,∞))` function, `j ≤ k`, is in `L²((0,∞))`. -/
private theorem memLp_weakDeriv1On_Ioi {k : ℕ} {g : ℝ → ℂ} (hg : MemH1On k (Ioi 0) g) {j : ℕ}
    (hj : j ≤ k) : MemLp (weakDeriv1On (Ioi 0) j g) 2 (volume.restrict (Ioi 0)) := by
  obtain ⟨h, hL2, hw⟩ := hg.deriv j hj
  have hloc : LocallyIntegrableOn h (Ioi (0 : ℝ)) := by
    have h1 : LocallyIntegrable h (volume.restrict (Ioi (0 : ℝ))) :=
      hL2.locallyIntegrable (by norm_num)
    rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
    intro K hK hKc
    have h2 : IntegrableOn h K (volume.restrict (Ioi (0 : ℝ))) :=
      h1.integrableOn_isCompact hKc
    rwa [IntegrableOn, Measure.restrict_restrict_of_subset hK] at h2
  have hae := weakDerivOn_ae_eq isOpen_Ioi hloc hw
  have hae' : h =ᵐ[volume.restrict (Ioi (0 : ℝ))] weakDeriv1On (Ioi 0) j g := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioi]
    filter_upwards [hae] with r hr hr0 using (hr hr0).symm
  exact hL2.ae_eq hae'

theorem secNormSq_mono_set {k : ℕ} (ℓ : ℤ) {I I' : Set ℝ} (hIm : MeasurableSet I)
    (hII' : I ⊆ I') {R : ℝ} (hI' : I' ⊆ Ioc 0 R) {g : ℝ → ℂ} (hg : MemH1On k (Ioi 0) g) :
    secNormSq k ℓ I g ≤ secNormSq k ℓ I' g := by
  unfold secNormSq
  refine Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left ?_ (secWeight_nonneg k j ℓ)
  have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  set w := weakDeriv1On (Ioi 0) j g
  have hI'0 : I' ⊆ Ioi 0 := fun r hr => (hI' hr).1
  have hmono : volume.restrict I' ≤ volume.restrict (Ioi (0 : ℝ)) := Measure.restrict_mono hI'0 le_rfl
  have hwL2 : MemLp w 2 (volume.restrict I') :=
    (memLp_weakDeriv1On_Ioi hg hjk).mono_measure hmono
  have hsq : Integrable (fun r => ‖w r‖ ^ 2) (volume.restrict I') := hwL2.norm.integrable_sq
  have hmemI' : ∀ᵐ r ∂(volume.restrict I'), r ∈ Ioi (0 : ℝ) :=
    ae_mono hmono (ae_restrict_mem measurableSet_Ioi)
  have hint : IntegrableOn (fun r => ‖w r‖ ^ 2 * r) I' := by
    refine hsq.mul_bdd (c := |R|) continuous_id.aestronglyMeasurable ?_
    have hRmem : ∀ᵐ r ∂(volume.restrict I'), r ≤ R := by
      have : ∀ᵐ r ∂(volume.restrict (Ioc (0 : ℝ) R)), r ∈ Ioc (0 : ℝ) R :=
        ae_restrict_mem measurableSet_Ioc
      filter_upwards [ae_mono (Measure.restrict_mono hI' le_rfl) this] with r hr
      exact hr.2
    filter_upwards [hRmem, hmemI'] with r hr hr0
    simp only [Real.norm_eq_abs]
    rw [abs_of_pos hr0]
    exact hr.trans (le_abs_self R)
  refine setIntegral_mono_set hint ?_ hII'.eventuallyLE
  filter_upwards [hmemI'] with r hr0
  exact mul_nonneg (sq_nonneg _) (le_of_lt hr0)

/-- `2^{-p}(1+x)^p ≤ ∑_{n ≤ p} x^n ≤ (1+x)^p` for `x ≥ 0` (`04_ring.tex:862`). -/
theorem pow_weights {x : ℝ} (hx : 0 ≤ x) (p : ℕ) :
    (2 : ℝ)⁻¹ ^ p * (1 + x) ^ p ≤ ∑ n ∈ Finset.range (p + 1), x ^ n ∧
      ∑ n ∈ Finset.range (p + 1), x ^ n ≤ (1 + x) ^ p := by
  have hexp : (1 + x) ^ p = ∑ n ∈ Finset.range (p + 1), x ^ n * (p.choose n : ℝ) := by
    rw [add_comm, add_pow]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp
  constructor
  · have h2 : (1 + x) ^ p ≤ 2 ^ p * ∑ n ∈ Finset.range (p + 1), x ^ n := by
      rw [hexp, Finset.mul_sum]
      refine Finset.sum_le_sum fun n _ => ?_
      rw [mul_comm ((2 : ℝ) ^ p)]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hx n)
      exact_mod_cast Nat.choose_le_two_pow p n
    calc (2 : ℝ)⁻¹ ^ p * (1 + x) ^ p ≤ (2 : ℝ)⁻¹ ^ p * (2 ^ p * ∑ n ∈ Finset.range (p + 1), x ^ n) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = ∑ n ∈ Finset.range (p + 1), x ^ n := by
          rw [← mul_assoc, ← mul_pow]; norm_num
  · rw [hexp]
    refine Finset.sum_le_sum fun n hn => ?_
    have hnp : n ≤ p := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
    have h1 : (1 : ℝ) ≤ p.choose n := by exact_mod_cast Nat.choose_pos hnp
    calc x ^ n = x ^ n * 1 := (mul_one _).symm
      _ ≤ x ^ n * (p.choose n : ℝ) := mul_le_mul_of_nonneg_left h1 (pow_nonneg hx n)

/-- `∑_{j ≤ k} A^{k-j} B^j ≤ (A+B)^k ≤ 2^k ∑_{j ≤ k} A^{k-j} B^j` for `A, B ≥ 0`
(`04_ring.tex:883`). -/
theorem binomial_weights {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), A ^ (k - j) * B ^ j ≤ (A + B) ^ k ∧
      (A + B) ^ k ≤ 2 ^ k * ∑ j ∈ Finset.range (k + 1), A ^ (k - j) * B ^ j := by
  have hexp : (A + B) ^ k =
      ∑ j ∈ Finset.range (k + 1), A ^ (k - j) * B ^ j * (k.choose j : ℝ) := by
    rw [add_comm, add_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hnn : ∀ j, 0 ≤ A ^ (k - j) * B ^ j := fun j =>
    mul_nonneg (pow_nonneg hA _) (pow_nonneg hB _)
  constructor
  · rw [hexp]
    refine Finset.sum_le_sum fun j hj => ?_
    have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have h1 : (1 : ℝ) ≤ k.choose j := by exact_mod_cast Nat.choose_pos hjk
    calc A ^ (k - j) * B ^ j = A ^ (k - j) * B ^ j * 1 := (mul_one _).symm
      _ ≤ A ^ (k - j) * B ^ j * (k.choose j : ℝ) := mul_le_mul_of_nonneg_left h1 (hnn j)
  · rw [hexp, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [mul_comm ((2 : ℝ) ^ k)]
    refine mul_le_mul_of_nonneg_left ?_ (hnn j)
    exact_mod_cast Nat.choose_le_two_pow k j

end NonUniqueEuler.Sob
