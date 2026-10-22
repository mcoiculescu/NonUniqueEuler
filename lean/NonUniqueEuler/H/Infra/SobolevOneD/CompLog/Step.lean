import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import NonUniqueEuler.Defs.Infra.SobolevOneD
import NonUniqueEuler.H.Infra.SobolevOneD.CompLog.Change
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv

/-!
# Helpers for `P/Infra/SobolevOneD/CompLog`: first-order weak chain rules

Adapted from `H/Infra/SobolevOneD/LogVariable/TestFn.lean` and `.../Step.lean` (restated in the
namespace `CompLogH` because the helpers of another proof may not be imported). Only the direction
`x ↦ r = e^x` (from the line to the half-line) is needed here.

* `isTestFn_comp_exp`, `hasDerivAt_comp_exp`: for a test function `ψ` on `(0, ∞)`, `ψ ∘ exp` is
  a test function on `ℝ`, with `(ψ ∘ exp)'(x) = e^x ψ'(e^x)`;
* `hasWeakDerivOn_comp_log`: if `W' = ∂_x W` weakly on `ℝ`, then
  `∂_r (W ∘ log) = r⁻¹ W'(log r)` weakly on `(0, ∞)`;
* `hasWeakDerivOn_expMul`: Leibniz rule with the smooth multiplier `e^{cx}` on `ℝ`;
* `hasWeakDerivOn_sum`: finite sums of weak derivatives;
* `hasWeakDerivOn_one_of_succ`: `∂^{p+1} f = ∂(∂^p f)`;
* `hasWeakDerivOn_nil_self`, `derivList_succ_eq`.

These are the identities `∂_r = e^{-x} ∂_x` of `04_ring.tex:888-897` for weak derivatives.
All proofs are complete.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace NonUniqueEuler.Sob.CompLogH

/-! ### Test functions -/

theorem iterDirDeriv_derivList_one (φ : ℝ → ℂ) : iterDirDeriv (derivList 1) φ = deriv φ := by
  rw [iterDirDeriv_derivList, iteratedDeriv_one]

theorem testFn_eq_zero {V : Set ℝ} {ψ : ℝ → ℂ} (hψ : IsTestFn V ψ) {r : ℝ}
    (hr : r ∉ V) : ψ r = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hr (hψ.subset h)

theorem testFn_deriv_eq_zero {V : Set ℝ} {ψ : ℝ → ℂ} (hψ : IsTestFn V ψ) {r : ℝ}
    (hr : r ∉ V) : deriv ψ r = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hr (hψ.subset (tsupport_deriv_subset h))

theorem testFn_hasDerivAt {V : Set ℝ} {ψ : ℝ → ℂ} (hψ : IsTestFn V ψ) (x : ℝ) :
    HasDerivAt ψ (deriv ψ x) x :=
  ((hψ.smooth.differentiable (by simp)).differentiableAt).hasDerivAt

/-- The pushforward `ψ ∘ exp` of a test function on `(0, ∞)` is a test function on `ℝ`. -/
theorem isTestFn_comp_exp {ψ : ℝ → ℂ} (hψ : IsTestFn (Ioi 0) ψ) :
    IsTestFn univ (fun x => ψ (Real.exp x)) := by
  refine ⟨hψ.smooth.comp Real.contDiff_exp, ?_, subset_univ _⟩
  have hK : IsCompact (Real.log '' tsupport ψ) :=
    (HasCompactSupport.isCompact hψ.compact).image_of_continuousOn
      (Real.continuousOn_log.mono fun r hr => (hψ.subset hr).ne')
  refine HasCompactSupport.intro hK fun x hx => ?_
  by_contra h
  exact hx ⟨Real.exp x, subset_tsupport _ h, Real.log_exp x⟩

theorem hasDerivAt_comp_exp {ψ : ℝ → ℂ} (hψ : IsTestFn (Ioi 0) ψ) (x : ℝ) :
    HasDerivAt (fun x => ψ (Real.exp x)) (Real.exp x • deriv ψ (Real.exp x)) x :=
  (testFn_hasDerivAt hψ (Real.exp x)).scomp x (Real.hasDerivAt_exp x)

/-! ### First-order rules -/

theorem hasWeakDerivOn_nil_self {V : Set ℝ} (f : ℝ → ℂ) :
    HasWeakDerivOn V (derivList 0) f f := by
  intro φ _
  simp [derivList]

theorem derivList_succ_eq (j : ℕ) : derivList (j + 1) = derivList 1 ++ derivList j := by
  simp [derivList, List.replicate_succ]

/-- If `W' = ∂_x W` weakly on `ℝ`, then `∂_r (W ∘ log) = r⁻¹ W'(log r)` weakly on `(0, ∞)`. -/
theorem hasWeakDerivOn_comp_log {W W' : ℝ → ℂ} (h : HasWeakDerivOn univ (derivList 1) W W') :
    HasWeakDerivOn (Ioi 0) (derivList 1) (fun r => W (Real.log r))
      (fun r => ((r⁻¹ : ℝ) : ℂ) * W' (Real.log r)) := by
  intro ψ hψ
  have hφ := isTestFn_comp_exp hψ
  have key := h _ hφ
  simp only [iterDirDeriv_derivList_one, derivList_length] at key ⊢
  have e1 : ∫ r, W (Real.log r) * deriv ψ r =
      ∫ x, W x * deriv (fun x => ψ (Real.exp x)) x := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi 0)
      (fun r hr => by rw [testFn_deriv_eq_zero hψ hr, mul_zero]), integral_Ioi_eq]
    congr 1
    ext x
    rw [(hasDerivAt_comp_exp hψ x).deriv, Real.log_exp, mul_smul_comm]
  have e2 : ∫ r, ((r⁻¹ : ℝ) : ℂ) * W' (Real.log r) * ψ r = ∫ x, W' x * ψ (Real.exp x) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi 0)
      (fun r hr => by rw [testFn_eq_zero hψ hr, mul_zero]), integral_Ioi_eq]
    congr 1
    ext x
    rw [Real.log_exp, Complex.real_smul]
    have hx : (Real.exp x : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos x).ne'
    push_cast
    field_simp
  rw [e1, key, e2]

/-- `F` locally integrable times a continuous compactly supported `g` is integrable. -/
theorem integrable_mul_of_hasCompactSupport {F g : ℝ → ℂ} (hF : LocallyIntegrable F)
    (hg : Continuous g) (hgc : HasCompactSupport g) : Integrable (fun x => F x * g x) := by
  simpa [smul_eq_mul] using hF.integrable_smul_right_of_hasCompactSupport hg hgc

/-- Leibniz rule with the smooth multiplier `e^{cx}` on `ℝ`. -/
theorem hasWeakDerivOn_expMul {F F' : ℝ → ℂ} (hF : LocallyIntegrable F)
    (hF' : LocallyIntegrable F') (h : HasWeakDerivOn univ (derivList 1) F F') (c : ℝ) :
    HasWeakDerivOn univ (derivList 1) (fun x => (Real.exp (c * x) : ℂ) * F x)
      (fun x => (c : ℂ) * (Real.exp (c * x) : ℂ) * F x + (Real.exp (c * x) : ℂ) * F' x) := by
  intro φ hφ
  set m : ℝ → ℂ := fun x => (Real.exp (c * x) : ℂ) with hm_def
  have hm : ContDiff ℝ ∞ m :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))
  have hmd : ∀ x, HasDerivAt m ((c : ℂ) * (Real.exp (c * x) : ℂ)) x := by
    intro x
    have h1 : HasDerivAt (fun x => Real.exp (c * x)) (Real.exp (c * x) * (c * 1)) x :=
      ((hasDerivAt_id x).const_mul c).exp
    have h2 := h1.ofReal_comp
    convert h2 using 1
    push_cast
    ring
  set χ : ℝ → ℂ := fun x => m x * φ x with hχ_def
  have hχ : IsTestFn univ χ := ⟨hm.mul hφ.smooth, hφ.compact.mul_left, subset_univ _⟩
  have hχd : ∀ x, deriv χ x = (c : ℂ) * (Real.exp (c * x) : ℂ) * φ x + m x * deriv φ x := by
    intro x
    exact ((hmd x).mul (testFn_hasDerivAt hφ x)).deriv
  have key := h χ hχ
  simp only [iterDirDeriv_derivList_one, derivList_length] at key ⊢
  have hcont1 : Continuous (fun x => (c : ℂ) * (Real.exp (c * x) : ℂ) * φ x) :=
    (continuous_const.mul hm.continuous).mul hφ.continuous
  have hcs1 : HasCompactSupport (fun x => (c : ℂ) * (Real.exp (c * x) : ℂ) * φ x) :=
    hφ.compact.mul_left
  have i1 : Integrable (fun x => F x * deriv χ x) :=
    integrable_mul_of_hasCompactSupport hF (hχ.smooth.continuous_deriv (by simp))
      hχ.compact.deriv
  have i2 : Integrable (fun x => F x * ((c : ℂ) * (Real.exp (c * x) : ℂ) * φ x)) :=
    integrable_mul_of_hasCompactSupport hF hcont1 hcs1
  have i3 : Integrable (fun x => F' x * χ x) :=
    integrable_mul_of_hasCompactSupport hF' hχ.continuous hχ.compact
  have eL : ∫ x, (Real.exp (c * x) : ℂ) * F x * deriv φ x =
      (∫ x, F x * deriv χ x) - ∫ x, F x * ((c : ℂ) * (Real.exp (c * x) : ℂ) * φ x) := by
    refine Eq.trans ?_ (integral_sub i1 i2)
    congr 1
    ext x
    rw [hχd x]
    ring
  have eR : ∫ x, ((c : ℂ) * (Real.exp (c * x) : ℂ) * F x + (Real.exp (c * x) : ℂ) * F' x) * φ x =
      (∫ x, F x * ((c : ℂ) * (Real.exp (c * x) : ℂ) * φ x)) + ∫ x, F' x * χ x := by
    refine Eq.trans ?_ (integral_add i2 i3)
    congr 1
    ext x
    rw [hχ_def, hm_def]
    ring
  rw [eL, eR]
  rw [key]
  ring

/-- Finite sums of weak derivatives (with local integrability of the partial sums). -/
theorem hasWeakDerivOn_sum {V : Set ℝ} (hV : IsOpen V) {vs : List ℝ} (n : ℕ)
    (f g : ℕ → ℝ → ℂ) (hf : ∀ p < n, LocallyIntegrableOn (f p) V)
    (hg : ∀ p < n, LocallyIntegrableOn (g p) V) (h : ∀ p < n, HasWeakDerivOn V vs (f p) (g p)) :
    HasWeakDerivOn V vs (fun x => ∑ p ∈ Finset.range n, f p x)
        (fun x => ∑ p ∈ Finset.range n, g p x) ∧
      LocallyIntegrableOn (fun x => ∑ p ∈ Finset.range n, f p x) V ∧
      LocallyIntegrableOn (fun x => ∑ p ∈ Finset.range n, g p x) V := by
  induction n with
  | zero =>
    refine ⟨fun φ _ => by simp, ?_, ?_⟩
    · simpa using (locallyIntegrableOn_zero : LocallyIntegrableOn (fun _ : ℝ => (0 : ℂ)) V)
    · simpa using (locallyIntegrableOn_zero : LocallyIntegrableOn (fun _ : ℝ => (0 : ℂ)) V)
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih (fun p hp => hf p (by omega)) (fun p hp => hg p (by omega))
      (fun p hp => h p (by omega))
    have e1 : (fun x => ∑ p ∈ Finset.range (n + 1), f p x) =
        (fun x => ∑ p ∈ Finset.range n, f p x) + f n := by
      ext x; simp [Finset.sum_range_succ]
    have e2 : (fun x => ∑ p ∈ Finset.range (n + 1), g p x) =
        (fun x => ∑ p ∈ Finset.range n, g p x) + g n := by
      ext x; simp [Finset.sum_range_succ]
    rw [e1, e2]
    exact ⟨HasWeakDerivOn.add hV h2 (hf n (by omega)) h3 (hg n (by omega)) h1 (h n (by omega)),
      h2.add (hf n (by omega)), h3.add (hg n (by omega))⟩

/-- Weak derivatives of consecutive orders form a first-order chain:
`∂^{p+1} f = ∂(∂^p f)`. -/
theorem hasWeakDerivOn_one_of_succ {V : Set ℝ} {f g h : ℝ → ℂ} {p : ℕ}
    (hg : HasWeakDerivOn V (derivList p) f g) (hh : HasWeakDerivOn V (derivList (p + 1)) f h) :
    HasWeakDerivOn V (derivList 1) g h := by
  intro φ hφ
  have h1 := hg _ (hφ.iterDirDeriv (derivList 1))
  have h2 := hh φ hφ
  have hl : derivList p ++ derivList 1 = derivList (p + 1) := by
    simp [derivList, List.replicate_add]
  rw [← iterDirDeriv_append, hl, h2] at h1
  simp only [derivList_length] at h1 ⊢
  have hne : ((-1 : ℂ)) ^ p ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [pow_succ, mul_assoc] at h1
  rw [pow_one]
  exact (mul_left_cancel₀ hne h1).symm

end NonUniqueEuler.Sob.CompLogH
