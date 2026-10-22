import NonUniqueEuler.Defs.Verify.Taylor
import NonUniqueEuler.I.Verify.TaylorCoef
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.Basic

/-!
# Proof: Taylor's theorem with the Lagrange remainder, componentwise (box form)

Proof of the interface `I/Verify/TaylorRemainder.lean` (same declarations, same statements).

**Manuscript.** Proof of Proposition A.3, steps (i) and (iii) (`A_verification.tex:372-378`,
`:421-434`). Checker design decision D9 (see `FORMALIZATION_NOTES.md`).

**Restructuring (checker design decision D9, deviation T1).** The manuscript's integral remainder
and convexity of the box are replaced by Lagrange's form applied separately to `Re ∘ f` and
`Im ∘ f`.

Uses `taylorCoeff_deriv` of `I/Verify/TaylorCoef.lean`, and Mathlib's
`taylor_mean_remainder_lagrange_iteratedDeriv`.
-/

noncomputable section

open Set Finset
open scoped ContDiff

namespace NonUniqueEuler

namespace AppA

/-! ### Auxiliary lemmas (private to this proof) -/

/-- Iterated derivatives commute with a continuous `ℝ`-linear map, for smooth `f`. -/
private theorem iteratedDeriv_clm_comp {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] G) {f : ℝ → E}
    (hf : ContDiff ℝ ∞ f) (k : ℕ) (x : ℝ) :
    iteratedDeriv k (fun y => L (f y)) x = L (iteratedDeriv k f x) := by
  have h1 : ContDiffAt ℝ k f x := (contDiff_infty.mp hf k).contDiffAt
  have hcomp : (fun y => L (f y)) = L ∘ f := rfl
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv, hcomp,
    L.iteratedFDeriv_comp_left h1 le_rfl]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply]

private theorem taylorCoeff_clm_comp {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] G) {f : ℝ → E}
    (hf : ContDiff ℝ ∞ f) (k : ℕ) (x : ℝ) :
    taylorCoeff (fun y => L (f y)) k x = L (taylorCoeff f k x) := by
  unfold taylorCoeff
  rw [iteratedDeriv_clm_comp L hf k x, map_smul]

private theorem taylorPoly_clm_comp {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] G) {f : ℝ → E}
    (hf : ContDiff ℝ ∞ f) (N : ℕ) (s h : ℝ) :
    taylorPoly (fun y => L (f y)) N s h = L (taylorPoly f N s h) := by
  unfold taylorPoly
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [taylorCoeff_clm_comp L hf k s, map_smul]

/-- Taylor's theorem with the Lagrange remainder, in the form
`f(s+h) = Σ_{k<N} f_k(s) h^k + f_N(η) h^N`, `η ∈ [s, s+h]`. -/
theorem taylor_lagrange_real {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {s h : ℝ} (hh : 0 ≤ h)
    (N : ℕ) :
    ∃ η ∈ Icc s (s + h), f (s + h) = taylorPoly f N s h + h ^ N * taylorCoeff f N η := by
  rcases N with _ | n
  · -- order zero: `η = s + h`
    refine ⟨s + h, ⟨by linarith, le_rfl⟩, ?_⟩
    simp [taylorPoly, taylorCoeff_zero]
  rcases hh.eq_or_lt with h0 | hpos
  · -- zero step: `η = s`
    subst h0
    refine ⟨s, ⟨le_rfl, by simp⟩, ?_⟩
    simp only [taylorPoly, add_zero]
    rw [Finset.sum_range_succ']
    simp [taylorCoeff_zero]
  · -- `h > 0`, order `n + 1`
    have hne : s ≠ s + h := by linarith
    have hle : s ≤ s + h := by linarith
    have hcd : ContDiffOn ℝ ((n + 1 : ℕ)) f (uIcc s (s + h)) :=
      ((contDiff_infty.mp hf) (n + 1)).contDiffOn
    obtain ⟨x', hx', hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := n) hne
      (by exact_mod_cast hcd)
    rw [uIoo_of_le hle] at hx'
    refine ⟨x', ⟨hx'.1.le, hx'.2.le⟩, ?_⟩
    have hpoly : taylorWithinEval f n (uIcc s (s + h)) s (s + h) = taylorPoly f (n + 1) s h := by
      rw [taylor_within_apply]
      unfold taylorPoly taylorCoeff
      refine Finset.sum_congr rfl fun k _ => ?_
      have hu : UniqueDiffOn ℝ (uIcc s (s + h)) := uniqueDiffOn_uIcc hne
      have hmem : s ∈ uIcc s (s + h) := left_mem_uIcc
      rw [iteratedDerivWithin_eq_iteratedDeriv hu ((contDiff_infty.mp hf) k).contDiffAt hmem]
      simp only [smul_eq_mul, add_sub_cancel_left]
      ring
    rw [hpoly] at hrem
    have hcoef : h ^ (n + 1) * taylorCoeff f (n + 1) x' =
        iteratedDeriv (n + 1) f x' * (s + h - s) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
      unfold taylorCoeff
      rw [smul_eq_mul, add_sub_cancel_left]
      field_simp
    rw [hcoef, ← hrem]
    ring

/-- The componentwise Lagrange form for a complex-valued `f`: one intermediate point for the
real part and one for the imaginary part. -/
theorem taylor_lagrange_re_im {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) {s h : ℝ} (hh : 0 ≤ h)
    (N : ℕ) :
    ∃ η₁ ∈ Icc s (s + h), ∃ η₂ ∈ Icc s (s + h),
      (f (s + h)).re = (taylorPoly f N s h + h ^ N • taylorCoeff f N η₁).re ∧
      (f (s + h)).im = (taylorPoly f N s h + h ^ N • taylorCoeff f N η₂).im := by
  have hre : ContDiff ℝ ∞ (fun y => Complex.reCLM (f y)) := Complex.reCLM.contDiff.comp hf
  have him : ContDiff ℝ ∞ (fun y => Complex.imCLM (f y)) := Complex.imCLM.contDiff.comp hf
  obtain ⟨η₁, hη₁, h₁⟩ := taylor_lagrange_real hre hh N
  obtain ⟨η₂, hη₂, h₂⟩ := taylor_lagrange_real him hh N
  refine ⟨η₁, hη₁, η₂, hη₂, ?_, ?_⟩
  · rw [taylorPoly_clm_comp Complex.reCLM hf, taylorCoeff_clm_comp Complex.reCLM hf] at h₁
    rw [Complex.add_re, Complex.smul_re, smul_eq_mul]
    exact h₁
  · rw [taylorPoly_clm_comp Complex.imCLM hf, taylorCoeff_clm_comp Complex.imCLM hf] at h₂
    rw [Complex.add_im, Complex.smul_im, smul_eq_mul]
    exact h₂

/-- **Box form of the Taylor step.** If, for every `η ∈ [s, s+h]`, the Taylor polynomial plus
the remainder term with the coefficient at `η` lies in the box `S ×ℂ T`, then `f(s+h)` lies in
it. -/
theorem taylor_mem_reProdIm {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) {s h : ℝ} (hh : 0 ≤ h)
    (N : ℕ) {S T : Set ℝ}
    (hB : ∀ η ∈ Icc s (s + h), taylorPoly f N s h + h ^ N • taylorCoeff f N η ∈ S ×ℂ T) :
    f (s + h) ∈ S ×ℂ T := by
  obtain ⟨η₁, hη₁, η₂, hη₂, h₁, h₂⟩ := taylor_lagrange_re_im hf hh N
  rw [Complex.mem_reProdIm, h₁, h₂]
  exact ⟨(Complex.mem_reProdIm.mp (hB η₁ hη₁)).1, (Complex.mem_reProdIm.mp (hB η₂ hη₂)).2⟩

/-- Box form of the Taylor step for the derivative, written with the coefficients of `f`:
`f'(s+h) = Σ_{k<N} (k+1) f_{k+1}(s) h^k + (N+1) f_{N+1}(η) h^N` componentwise
(the manuscript's `P'_new = Σ_{k=1}^N kΨ_k h^{k-1} + (N+1)Ψ^st_{N+1} h^N`). -/
theorem taylor_deriv_mem_reProdIm {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) {s h : ℝ} (hh : 0 ≤ h)
    (N : ℕ) {S T : Set ℝ}
    (hB : ∀ η ∈ Icc s (s + h),
      (∑ k ∈ range N, ((k + 1 : ℝ) * h ^ k) • taylorCoeff f (k + 1) s) +
        ((N + 1 : ℝ) * h ^ N) • taylorCoeff f (N + 1) η ∈ S ×ℂ T) :
    deriv f (s + h) ∈ S ×ℂ T := by
  have hd : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  refine taylor_mem_reProdIm hd hh N fun η hη => ?_
  have heq : taylorPoly (deriv f) N s h + h ^ N • taylorCoeff (deriv f) N η =
      (∑ k ∈ range N, ((k + 1 : ℝ) * h ^ k) • taylorCoeff f (k + 1) s) +
        ((N + 1 : ℝ) * h ^ N) • taylorCoeff f (N + 1) η := by
    unfold taylorPoly
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [taylorCoeff_deriv, smul_smul, mul_comm]
    · rw [taylorCoeff_deriv, smul_smul, mul_comm]
  rw [heq]
  exact hB η hη

/-- The increment of a primitive `g` of `q` over one step (step (i) of Proposition A.3):
`g(s+h) - g(s) = Σ_{k<N} q_k(s) h^{k+1}/(k+1) + q_N(η) h^{N+1}/(N+1)`, `η ∈ [s, s+h]`. -/
theorem taylor_increment_real {g q : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hq : ∀ x, deriv g x = q x)
    {s h : ℝ} (hh : 0 ≤ h) (N : ℕ) :
    ∃ η ∈ Icc s (s + h), g (s + h) - g s =
      (∑ k ∈ range N, taylorCoeff q k s * (h ^ (k + 1) / ((k : ℝ) + 1))) +
        taylorCoeff q N η * (h ^ (N + 1) / ((N : ℝ) + 1)) := by
  have hdq : deriv g = q := funext hq
  -- `g_{k+1} = q_k / (k+1)`
  have hshift : ∀ (k : ℕ) (x : ℝ), taylorCoeff g (k + 1) x = taylorCoeff q k x / ((k : ℝ) + 1) := by
    intro k x
    have h1 := taylorCoeff_deriv g k x
    rw [hdq, smul_eq_mul] at h1
    have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
    rw [h1]
    field_simp
  obtain ⟨η, hη, hrem⟩ := taylor_lagrange_real hg hh (N + 1)
  refine ⟨η, hη, ?_⟩
  rw [hrem]
  unfold taylorPoly
  rw [Finset.sum_range_succ', taylorCoeff_zero, hshift N η]
  simp only [pow_zero, smul_eq_mul, hshift]
  have hsum : ∀ k ∈ range N, h ^ (k + 1) * (taylorCoeff q k s / ((k : ℝ) + 1)) =
      taylorCoeff q k s * (h ^ (k + 1) / ((k : ℝ) + 1)) := fun k _ => by ring
  rw [Finset.sum_congr rfl hsum]
  ring

end AppA

end NonUniqueEuler
