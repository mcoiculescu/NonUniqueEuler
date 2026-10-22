import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.InnerProductSpace.Calculus
import NonUniqueEuler.Defs.Infra.CkNorm
import NonUniqueEuler.Defs.Infra.SectorSpace

/-!
# Helpers for `P/Infra/SectorSpace/RadialMul`: the `C^s` norm of a radial function

For `0 < ρ₋` and `a : ℝ → ℂ` of class `C^s` near `[ρ₋, ρ₊]`, the radial function
`x ↦ a(|x|)` is of class `C^s` near the closed annulus `N = {ρ₋ ≤ |x| ≤ ρ₊}`, with
`‖a(|·|)‖_{C^s(N)} ≤ C(s, ρ₋, ρ₊) ‖a‖_{C^s([ρ₋, ρ₊])}`.

Proof: Faà di Bruno's bound (`norm_iteratedFDerivWithin_comp_le`) on the open set
`U = {x : |x| ∈ V, |x| > 0}` (with `V` the open set where `a` is `C^s`); the derivatives of
`x ↦ |x|` are continuous on `ℂ \ {0}` (`contDiffAt_norm`), hence bounded on the compact annulus.
-/

noncomputable section

open Set
open scoped ContDiff

namespace NonUniqueEuler.Sect.RadMulH

/-- `x ↦ ‖x‖` is smooth on `ℂ \ {0}`. -/
theorem contDiffOn_norm_ne (n : WithTop ℕ∞) :
    ContDiffOn ℝ n (fun x : ℂ => ‖x‖) {x : ℂ | x ≠ 0} :=
  fun _ hx => (contDiffAt_norm ℝ hx).contDiffWithinAt

theorem isOpen_ne_zero : IsOpen {x : ℂ | x ≠ 0} := isOpen_ne

theorem closedAnnulus_subset_ne_zero {ρm ρp : ℝ} (hρm : 0 < ρm) :
    closedAnnulus ρm ρp ⊆ {x : ℂ | x ≠ 0} := fun _ hx =>
  norm_pos_iff.1 (lt_of_lt_of_le hρm hx.1)

/-- The derivatives of `x ↦ ‖x‖` of orders `1 ≤ i ≤ s` are bounded on the annulus by `D^i`. -/
theorem exists_bound_iteratedFDeriv_norm (s : ℕ) {ρm ρp : ℝ} (hρm : 0 < ρm) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ i, 1 ≤ i → i ≤ s → ∀ x ∈ closedAnnulus ρm ρp,
      ‖iteratedFDeriv ℝ i (fun x : ℂ => ‖x‖) x‖ ≤ D ^ i := by
  have hb : ∀ i : ℕ, ∃ M : ℝ, ∀ x ∈ closedAnnulus ρm ρp,
      ‖iteratedFDeriv ℝ i (fun x : ℂ => ‖x‖) x‖ ≤ M := by
    intro i
    have hc : ContinuousOn (iteratedFDeriv ℝ i (fun x : ℂ => ‖x‖)) {x : ℂ | x ≠ 0} := by
      have h1 := (contDiffOn_norm_ne (i : WithTop ℕ∞)).continuousOn_iteratedFDerivWithin
        (m := i) le_rfl isOpen_ne_zero.uniqueDiffOn
      exact h1.congr fun x hx => (iteratedFDerivWithin_of_isOpen i isOpen_ne_zero hx).symm
    exact (isCompact_closedAnnulus ρm ρp).exists_bound_of_continuousOn
      (hc.mono (closedAnnulus_subset_ne_zero hρm))
  choose M hM using hb
  have hS : 0 ≤ ∑ j ∈ Finset.range (s + 1), |M j| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hD1 : (1 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (s + 1), |M j| := by linarith
  refine ⟨1 + ∑ j ∈ Finset.range (s + 1), |M j|, hD1, ?_⟩
  intro i hi1 his x hx
  calc ‖iteratedFDeriv ℝ i (fun x : ℂ => ‖x‖) x‖ ≤ M i := hM i x hx
    _ ≤ |M i| := le_abs_self _
    _ ≤ ∑ j ∈ Finset.range (s + 1), |M j| :=
        Finset.single_le_sum (f := fun j => |M j|) (fun _ _ => abs_nonneg _)
          (Finset.mem_range.2 (by omega))
    _ ≤ 1 + ∑ j ∈ Finset.range (s + 1), |M j| := by linarith
    _ = (1 + ∑ j ∈ Finset.range (s + 1), |M j|) ^ 1 := (pow_one _).symm
    _ ≤ (1 + ∑ j ∈ Finset.range (s + 1), |M j|) ^ i := pow_le_pow_right₀ hD1 hi1

/-- The radial function `x ↦ a(|x|)` lies in `C^s(N)` for `a ∈ C^s([ρ₋, ρ₊])`, with
`‖a(|·|)‖_{C^s(N)} ≤ C ‖a‖_{C^s([ρ₋, ρ₊])}`, `C` depending only on `s, ρ₋, ρ₊`. -/
theorem exists_memCk_radial (s : ℕ) {ρm ρp : ℝ} (hρm : 0 < ρm) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ → ℂ, MemCk s (Icc ρm ρp) a →
      MemCk s (closedAnnulus ρm ρp) (fun x : ℂ => a ‖x‖) ∧
        normCk s (closedAnnulus ρm ρp) (fun x : ℂ => a ‖x‖) ≤
          C * normCk s (Icc ρm ρp) a := by
  obtain ⟨D, hD1, hD⟩ := exists_bound_iteratedFDeriv_norm s (ρp := ρp) hρm
  have hD0 : 0 ≤ D := by linarith
  refine ⟨∑ q ∈ Finset.range (s + 1), (q.factorial : ℝ) * D ^ q, ?_, ?_⟩
  · exact Finset.sum_pos (fun q _ => mul_pos (Nat.cast_pos.2 (Nat.factorial_pos q))
      (pow_pos (by linarith) q)) Finset.nonempty_range_add_one
  intro a ha
  obtain ⟨V, hVo, hIV, hacd⟩ := ha.near
  set t : Set ℝ := V ∩ Ioi 0 with ht_def
  set U : Set ℂ := (fun x : ℂ => ‖x‖) ⁻¹' t with hU_def
  have ht : IsOpen t := hVo.inter isOpen_Ioi
  have hU : IsOpen U := ht.preimage continuous_norm
  have hKU : closedAnnulus ρm ρp ⊆ U := fun x hx =>
    ⟨hIV ⟨hx.1, hx.2⟩, lt_of_lt_of_le hρm hx.1⟩
  have hU0 : U ⊆ {x : ℂ | x ≠ 0} := fun x hx => norm_pos_iff.1 hx.2
  have hat : ContDiffOn ℝ s a t := hacd.mono inter_subset_left
  have hnU : ContDiffOn ℝ s (fun x : ℂ => ‖x‖) U := (contDiffOn_norm_ne _).mono hU0
  have hmaps : MapsTo (fun x : ℂ => ‖x‖) U t := fun _ hy => hy
  have hcd : ContDiffOn ℝ s (fun x : ℂ => a ‖x‖) U := hat.comp hnU hmaps
  have hpt : ∀ q ≤ s, ∀ x ∈ closedAnnulus ρm ρp,
      ‖iteratedFDeriv ℝ q (fun x : ℂ => a ‖x‖) x‖ ≤
        (q.factorial : ℝ) * normCk s (Icc ρm ρp) a * D ^ q := by
    intro q hq x hx
    have hxU : x ∈ U := hKU hx
    have hxt : ‖x‖ ∈ t := hxU
    have hC : ∀ i, i ≤ q → ‖iteratedFDerivWithin ℝ i a t ‖x‖‖ ≤ normCk s (Icc ρm ρp) a := by
      intro i hi
      rw [iteratedFDerivWithin_of_isOpen i ht hxt]
      exact norm_iteratedFDeriv_le_normCk ha (hi.trans hq) ⟨hx.1, hx.2⟩
    have hDq : ∀ i, 1 ≤ i → i ≤ q →
        ‖iteratedFDerivWithin ℝ i (fun x : ℂ => ‖x‖) U x‖ ≤ D ^ i := by
      intro i hi1 hiq
      rw [iteratedFDerivWithin_of_isOpen i hU hxU]
      exact hD i hi1 (hiq.trans hq) x hx
    have key := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (g := a)
      (f := fun x : ℂ => ‖x‖) (n := q) (N := (s : WithTop ℕ∞)) hat hnU
      (by exact_mod_cast hq) ht.uniqueDiffOn hU.uniqueDiffOn hmaps hxU hC hDq
    rw [iteratedFDerivWithin_of_isOpen q hU hxU] at key
    exact key
  refine ⟨⟨⟨U, hU, hKU, hcd⟩, normCkE_ne_top_of_bound _ hpt⟩, ?_⟩
  calc normCk s (closedAnnulus ρm ρp) (fun x : ℂ => a ‖x‖)
      ≤ ∑ q ∈ Finset.range (s + 1), (q.factorial : ℝ) * normCk s (Icc ρm ρp) a * D ^ q :=
        normCk_le_of_bound _ (fun q => mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
          (normCk_nonneg _ _ _)) (pow_nonneg hD0 _)) hpt
    _ = (∑ q ∈ Finset.range (s + 1), (q.factorial : ℝ) * D ^ q) *
          normCk s (Icc ρm ρp) a := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun q _ => by ring

end NonUniqueEuler.Sect.RadMulH
