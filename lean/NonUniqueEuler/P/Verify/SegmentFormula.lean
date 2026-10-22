import NonUniqueEuler.Defs.Verify.Winding
import NonUniqueEuler.I.Verify.WindingLift
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Proof: Proposition A.4 (`prop:winding`), the segment formula for the winding number

Proof of `NonUniqueEuler/I/Verify/SegmentFormula.lean` (same declarations, statements copied
verbatim).

**Manuscript.** `A_verification.tex:466-512`.

* `hasArgChange_of_admits_P`: the lift is `arg ∘ c`, continuous on the slit plane.
* `hasArgChange_of_admits_N`: the lift is `arg (-c ·) + π`, continuous since `-c` stays in the
  slit plane; it equals `argN ∘ c` there (`argN_eq_arg_neg_add_pi`).
* `hasWinding_of_segments`: induction over the segments with `HasArgChange.append`
  (`I/Verify/WindingLift.lean`); the argument change along the first `m` segments is
  `arg (c (t m)) - arg (c (t 0)) + 2π Σ_{i<m, N} (x (i+1) - x i)`, and `c (t n) = c (t 0)`
  kills the `arg` terms.
* `junctionSum_eq_segIndicatorSum`: termwise, `seg_i - jun_i = g (cycNext n i) - g i` with
  `g j = 1[N (cycPrev n j) ∧ N j] · x j`; the sum of the right side vanishes because
  `cycNext n` permutes `range n` (`sum_range_comp_cycNext`).
* `junctionSum_congr`: every value read by `junctionSum` is at a junction index `< n`.
-/

open Set Real Finset

namespace NonUniqueEuler

/-! ### Helpers -/

/-- On `ℂ \ [0, ∞)`, `argN z = arg (-z) + π`. -/
private theorem argN_eq_arg_neg_add_pi {z : ℂ} (hz : -z ∈ Complex.slitPlane) :
    argN z = Complex.arg (-z) + π := by
  unfold argN negImInd
  rcases lt_trichotomy z.im 0 with h | h | h
  · rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg h]
    simp only [h, ↓reduceIte]
    push_cast
    ring
  · have hre : z.re < 0 := by
      rcases Complex.mem_slitPlane_iff.mp hz with h' | h'
      · simp only [Complex.neg_re] at h'
        linarith
      · simp [h] at h'
    have h1 : Complex.arg z = π := Complex.arg_eq_pi_iff.mpr ⟨hre, h⟩
    have h2 : Complex.arg (-z) = 0 :=
      Complex.arg_eq_zero_iff.mpr ⟨by simp only [Complex.neg_re]; linarith, by simp [h]⟩
    have h3 : ¬ z.im < 0 := by rw [h]; exact lt_irrefl 0
    rw [h1, h2]
    simp only [h3, ↓reduceIte]
    push_cast
    ring
  · have h3 : ¬ z.im < 0 := not_lt.mpr h.le
    rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos h]
    simp only [h3, ↓reduceIte]
    push_cast
    ring

/-- `z = |z| e^{i (arg (-z) + π)}`. -/
private theorem eq_norm_mul_exp_arg_neg_add_pi (z : ℂ) :
    z = ((‖z‖ : ℝ) : ℂ) * Complex.exp (((Complex.arg (-z) + π : ℝ) : ℂ) * Complex.I) := by
  have h := Complex.norm_mul_exp_arg_mul_I (-z)
  rw [norm_neg] at h
  rw [Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I, ← mul_assoc, h]
  ring

/-- A constant curve has argument change `0` along a degenerate interval. -/
private theorem hasArgChange_self {c : ℝ → ℂ} {a : ℝ} (h : c a ≠ 0) : HasArgChange c a a 0 := by
  refine ⟨le_rfl, ?_, ?_, ⟨fun _ => Complex.arg (c a), ⟨continuousOn_const, ?_⟩, sub_self _⟩⟩
  · rw [Set.Icc_self]
    exact continuousOn_singleton _ _
  · intro s hs
    rw [Set.Icc_self, mem_singleton_iff] at hs
    subst hs
    exact h
  · intro s hs
    rw [Set.Icc_self, mem_singleton_iff] at hs
    subst hs
    exact (Complex.norm_mul_exp_arg_mul_I _).symm

private theorem cycPrev_cycNext (n i : ℕ) : cycPrev n (cycNext n i) = i := by
  unfold cycPrev cycNext
  split_ifs <;> first | omega | contradiction

private theorem cycNext_cycPrev {n i : ℕ} (hi : i < n) : cycNext n (cycPrev n i) = i := by
  revert hi
  unfold cycPrev cycNext
  split_ifs <;> intro <;> omega

private theorem cycNext_lt {n i : ℕ} (hi : i < n) : cycNext n i < n := by
  unfold cycNext
  split_ifs <;> omega

private theorem cycPrev_lt {n i : ℕ} (hi : i < n) : cycPrev n i < n := by
  unfold cycPrev
  split_ifs <;> omega

/-- `cycNext n` permutes `range n`. -/
private theorem sum_range_comp_cycNext (n : ℕ) (g : ℕ → ℤ) :
    ∑ i ∈ range n, g (cycNext n i) = ∑ i ∈ range n, g i := by
  refine Finset.sum_nbij' (cycNext n) (cycPrev n) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_range] at ha ⊢
    exact cycNext_lt ha
  · intro a ha
    rw [Finset.mem_range] at ha ⊢
    exact cycPrev_lt ha
  · intro a ha
    exact cycPrev_cycNext n a
  · intro a ha
    exact cycNext_cycPrev (mem_range.mp ha)
  · intro a _
    rfl

/-! ### The declarations of the interface -/

/-- On a type-P segment the principal argument is a continuous argument. -/
theorem hasArgChange_of_admits_P {c : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn c (Icc a b)) (hP : ∀ t ∈ Icc a b, SegKind.P.Admits (c t)) :
    HasArgChange c a b (Complex.arg (c b) - Complex.arg (c a)) := by
  refine ⟨hab, hc, fun s hs => Complex.slitPlane_ne_zero (hP s hs),
    ⟨fun s => Complex.arg (c s), ⟨?_, ?_⟩, rfl⟩⟩
  · intro s hs
    exact (Complex.continuousAt_arg (hP s hs)).comp_continuousWithinAt (hc s hs)
  · intro s _
    exact (Complex.norm_mul_exp_arg_mul_I (c s)).symm

/-- On a type-N segment `argN = Arg + 2π·1[Im < 0]` is a continuous argument. -/
theorem hasArgChange_of_admits_N {c : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn c (Icc a b)) (hN : ∀ t ∈ Icc a b, SegKind.N.Admits (c t)) :
    HasArgChange c a b (argN (c b) - argN (c a)) := by
  have hN' : ∀ s ∈ Icc a b, -c s ∈ Complex.slitPlane := hN
  refine ⟨hab, hc, fun s hs => ?_, ⟨fun s => Complex.arg (-c s) + π, ⟨?_, ?_⟩, ?_⟩⟩
  · exact neg_ne_zero.mp (Complex.slitPlane_ne_zero (hN' s hs))
  · intro s hs
    exact ((Complex.continuousAt_arg (hN' s hs)).comp_continuousWithinAt
      (f := fun u => -c u) (hc s hs).neg).add continuousWithinAt_const
  · intro s _
    exact eq_norm_mul_exp_arg_neg_add_pi (c s)
  · rw [argN_eq_arg_neg_add_pi (hN' b ⟨hab, le_rfl⟩), argN_eq_arg_neg_add_pi (hN' a ⟨le_rfl, hab⟩)]

/-- **Proposition A.4** (segment formula). If each segment of a closed continuous curve is of
the assigned type, then the curve avoids `0` and its winding number is the indicator sum over
the type-N segments. -/
theorem hasWinding_of_segments {c : ℝ → ℂ} {n : ℕ} {t : ℕ → ℝ} {κ : ℕ → SegKind}
    (hn : 0 < n) (hmono : ∀ i < n, t i ≤ t (i + 1))
    (hc : ContinuousOn c (Icc (t 0) (t n))) (hcl : c (t 0) = c (t n))
    (hok : ∀ i < n, ∀ s ∈ Icc (t i) (t (i + 1)), (κ i).Admits (c s)) :
    HasWinding c (t 0) (t n) (segIndicatorSum n κ fun i => negImInd (c (t i))) := by
  -- monotonicity of the parameters
  have hle : ∀ j k, j ≤ k → k ≤ n → t j ≤ t k := by
    intro j k hjk hkn
    induction k, hjk using Nat.le_induction with
    | base => exact le_rfl
    | succ k _ ih => exact (ih (by omega)).trans (hmono k (by omega))
  -- the argument change along one segment
  have hseg : ∀ i < n, HasArgChange c (t i) (t (i + 1))
      (Complex.arg (c (t (i + 1))) - Complex.arg (c (t i)) +
        2 * π * (((if (κ i).isN then negImInd (c (t (i + 1))) - negImInd (c (t i)) else 0 : ℤ))
          : ℝ)) := by
    intro i hi
    have hsub : Icc (t i) (t (i + 1)) ⊆ Icc (t 0) (t n) :=
      Icc_subset_Icc (hle 0 i (Nat.zero_le _) hi.le) (hle (i + 1) n hi le_rfl)
    have hci := hc.mono hsub
    have hoki := hok i hi
    cases hκ : κ i with
    | P =>
      rw [hκ] at hoki
      have h := hasArgChange_of_admits_P (hmono i hi) hci hoki
      simpa [SegKind.isN] using h
    | N =>
      rw [hκ] at hoki
      have h := hasArgChange_of_admits_N (hmono i hi) hci hoki
      convert h using 1
      simp only [SegKind.isN, ↓reduceIte, argN]
      push_cast
      ring
  -- the argument change along the first `m` segments
  have hind : ∀ m ≤ n, HasArgChange c (t 0) (t m)
      (Complex.arg (c (t m)) - Complex.arg (c (t 0)) +
        2 * π * (((∑ i ∈ range m,
          if (κ i).isN then negImInd (c (t (i + 1))) - negImInd (c (t i)) else 0 : ℤ)) : ℝ)) := by
    intro m
    induction m with
    | zero =>
      intro _
      have h0 : c (t 0) ≠ 0 := (hok 0 hn (t 0) ⟨le_rfl, hmono 0 hn⟩).ne_zero
      simpa using hasArgChange_self h0
    | succ m ih =>
      intro hm
      have h := (ih (by omega)).append (hseg m (by omega))
      convert h using 1
      rw [Finset.sum_range_succ]
      push_cast
      ring
  have h := hind n le_rfl
  rw [hcl, sub_self, zero_add] at h
  exact ⟨hcl, h⟩

/-- The junction form of the indicator sum equals the full indicator sum (cyclic summation by
parts; deviation W1). -/
theorem junctionSum_eq_segIndicatorSum {n : ℕ} (hn : 0 < n) (κ : ℕ → SegKind) {x : ℕ → ℤ}
    (hx : x n = x 0) : junctionSum n κ x = segIndicatorSum n κ x := by
  let g : ℕ → ℤ := fun j => if (κ (cycPrev n j)).isN ∧ (κ j).isN then x j else 0
  have hterm : ∀ i ∈ range n,
      ((if (κ i).isN then x (i + 1) - x i else 0) -
        (if (κ i).isN then
          (if (κ (cycNext n i)).isN then 0 else x (cycNext n i)) -
            (if (κ (cycPrev n i)).isN then 0 else x i)
        else 0)) = g (cycNext n i) - g i := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hxi : x (i + 1) = x (cycNext n i) := by
      unfold cycNext
      split_ifs with h
      · rw [h, hx]
      · rfl
    simp only [g, cycPrev_cycNext n i, hxi]
    generalize (κ i).isN = A
    generalize (κ (cycNext n i)).isN = B
    generalize (κ (cycPrev n i)).isN = C
    cases A <;> cases B <;> cases C <;> simp
  have hdiff : segIndicatorSum n κ x - junctionSum n κ x = 0 := by
    unfold segIndicatorSum junctionSum
    rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl hterm, Finset.sum_sub_distrib,
      sum_range_comp_cycNext, sub_self]
  linarith

/-- `junctionSum` only reads the values at the junctions. -/
theorem junctionSum_congr {n : ℕ} (κ : ℕ → SegKind) {x y : ℕ → ℤ}
    (hxy : ∀ i < n, IsJunction n κ i → x i = y i) : junctionSum n κ x = junctionSum n κ y := by
  unfold junctionSum
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  by_cases h1 : (κ i).isN
  · simp only [h1, ↓reduceIte]
    congr 1
    · by_cases h2 : (κ (cycNext n i)).isN
      · simp only [h2, ↓reduceIte]
      · simp only [h2]
        refine hxy _ (cycNext_lt hi) ?_
        simp [IsJunction, cycPrev_cycNext n i, h1, h2]
    · by_cases h3 : (κ (cycPrev n i)).isN
      · simp only [h3, ↓reduceIte]
      · simp only [h3]
        refine hxy _ hi ?_
        simp [IsJunction, h1, h3]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]

/-- **Proposition A.4, as the certification evaluates it**: decided indicators `J i` at the
junctions (and nowhere else) give the winding number through `junctionSum`. -/
theorem hasWinding_of_segments_junction {c : ℝ → ℂ} {n : ℕ} {t : ℕ → ℝ} {κ : ℕ → SegKind}
    (hn : 0 < n) (hmono : ∀ i < n, t i ≤ t (i + 1))
    (hc : ContinuousOn c (Icc (t 0) (t n))) (hcl : c (t 0) = c (t n))
    (hok : ∀ i < n, ∀ s ∈ Icc (t i) (t (i + 1)), (κ i).Admits (c s)) {J : ℕ → ℤ}
    (hJ : ∀ i < n, IsJunction n κ i → J i = negImInd (c (t i))) :
    HasWinding c (t 0) (t n) (junctionSum n κ J) := by
  have h1 : junctionSum n κ J = junctionSum n κ (fun i => negImInd (c (t i))) :=
    junctionSum_congr κ hJ
  have hx : (fun i => negImInd (c (t i))) n = (fun i => negImInd (c (t i))) 0 := by
    simp only [hcl]
  rw [h1, junctionSum_eq_segIndicatorSum hn κ hx]
  exact hasWinding_of_segments hn hmono hc hcl hok

end NonUniqueEuler
