import NonUniqueEuler.I.SmoothB.Iterates
import NonUniqueEuler.I.SmoothB.IterLip
import NonUniqueEuler.I.SmoothB.Constants
import NonUniqueEuler.I.Infra.Sobolev.Smooth

/-!
# Helper for `lem:iter-Hs`: the time slices of the iterates and classical `H^k` norms

Helper of `P/SmoothB/IterHs.lean` (`B_global_smooth.tex:302-349`).

* Sobolev norms of smooth compactly supported functions, computed classically
  (`normH_sq_eq`, `l2_partialD_le_normH`), and the splitting of `multiIdx (k+1)` into
  `multiIdx k` and the multi-indices of length `k + 1` (`sum_multiIdx_succ`, `normH_succ_sq_eq`).
* The time slices `ω^{[j]}(t)` of the iterates are smooth, vanish outside
  `\bar B_{R₀' + U_*|t|}` (`exists_iter_support`), hence lie in every `H^k`.
* Derivatives of a real function viewed as complex valued (`fderiv_ofReal_apply`), and
  `|∇ω^{[j]}(t,x)|` computed through `Prelim.gradAbs` (`gradAbs_ofReal`).
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ContDiff ENNReal Topology

namespace NonUniqueEuler.Smooth.IterHsH

open Sob

/-! ### Sobolev norms of smooth compactly supported functions -/

theorem normH_sq_eq {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (k : ℕ) :
    normH k f ^ 2 = ∑ γ ∈ multiIdx k, l2 (partialD γ f) ^ 2 := by
  rw [(memH_of_contDiff_hasCompactSupport hf hc k).2.2, Real.sq_sqrt]
  exact Finset.sum_nonneg fun γ _ => sq_nonneg _

theorem l2_partialD_le_normH {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    {k : ℕ} {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx k) : l2 (partialD γ f) ≤ normH k f := by
  rw [(memH_of_contDiff_hasCompactSupport hf hc k).2.2]
  apply Real.le_sqrt_of_sq_le
  exact Finset.single_le_sum (f := fun γ => l2 (partialD γ f) ^ 2) (fun γ _ => sq_nonneg _) hγ

/-- `{|γ| ≤ k + 1} = {|γ| ≤ k} ⊔ {|γ| = k + 1}`. -/
theorem sum_multiIdx_succ {M : Type*} [AddCommMonoid M] (k : ℕ) (F : ℕ × ℕ → M) :
    ∑ γ ∈ multiIdx (k + 1), F γ =
      ∑ γ ∈ multiIdx k, F γ + ∑ γ ∈ Finset.antidiagonal (k + 1), F γ := by
  rw [← Finset.sum_filter_add_sum_filter_not (multiIdx (k + 1)) (fun γ => γ.1 + γ.2 ≤ k)]
  congr 1
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext γ
    simp only [Finset.mem_filter, mem_multiIdx]
    omega
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext γ
    simp only [Finset.mem_filter, mem_multiIdx, Finset.mem_antidiagonal]
    omega

theorem normH_succ_sq_eq {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (k : ℕ) :
    normH (k + 1) f ^ 2 =
      normH k f ^ 2 + ∑ α ∈ Finset.antidiagonal (k + 1), l2 (partialD α f) ^ 2 := by
  rw [normH_sq_eq hf hc, normH_sq_eq hf hc, sum_multiIdx_succ]

theorem antidiagonal_subset_multiIdx (k : ℕ) : Finset.antidiagonal k ⊆ multiIdx k := by
  intro γ hγ
  rw [Finset.mem_antidiagonal] at hγ
  exact mem_multiIdx.2 hγ.le

/-! ### Derivatives of real functions viewed as complex valued -/

theorem fderiv_ofReal_apply {g : ℂ → ℝ} {x : ℂ} (hg : DifferentiableAt ℝ g x) (v : ℂ) :
    fderiv ℝ (fun y => (g y : ℂ)) x v = ((fderiv ℝ g x v : ℝ) : ℂ) := by
  have h := Complex.ofRealCLM.hasFDerivAt.comp x hg.hasFDerivAt
  rw [show (fun y => (g y : ℂ)) = Complex.ofRealCLM ∘ g from rfl, h.fderiv]
  rfl

/-- `|∇g(x)|` for a real scalar `g`, computed on `g` viewed as complex valued. -/
theorem gradAbs_ofReal {g : ℂ → ℝ} {x : ℂ} (hg : DifferentiableAt ℝ g x) :
    Prelim.gradAbs (fun y => (g y : ℂ)) x = ‖fderiv ℝ g x‖ := by
  rw [Prelim.norm_fderiv_eq_norm_grad, Prelim.gradAbs, Prelim.grad, Complex.norm_add_mul_I]
  simp only [Prelim.pd, fderiv_ofReal_apply hg, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- `|∂₁g|² + |∂₂g|²` is `|∇g|²`, with `∂^{(1,0)}`, `∂^{(0,1)}` of I-HK. -/
theorem norm_partialD_sq_add {g : ℂ → ℝ} {x : ℂ} (hg : DifferentiableAt ℝ g x) :
    ‖partialD (1, 0) (fun y => (g y : ℂ)) x‖ ^ 2 + ‖partialD (0, 1) (fun y => (g y : ℂ)) x‖ ^ 2 =
      ‖fderiv ℝ g x‖ ^ 2 := by
  rw [← gradAbs_ofReal hg, Prelim.gradAbs, Real.sq_sqrt (by positivity)]
  rfl

/-! ### The time slices of the iterates -/

variable {ω₀ : ℂ → ℝ} {R₀ : ℝ}

theorem contDiff_iter_slice (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (j : ℕ) (t : ℝ) :
    ContDiff ℝ ∞ (iter ω₀ j t) :=
  (iterates_smooth_support h hne j).1.comp ((contDiff_const (c := t)).prodMk contDiff_id)

theorem contDiff_iter_sliceC (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (j : ℕ) (t : ℝ) :
    ContDiff ℝ ∞ (fun x => (iter ω₀ j t x : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_iter_slice h hne j t)

/-- A common inner radius: `ω^{[j]}(t, x) = 0` for `|x| > R₀' + U_*|t|`, with `R₀' < R₀`. -/
theorem exists_iter_support (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) :
    ∃ R₀' : ℝ, R₀' < R₀ ∧
      ∀ j : ℕ, ∀ t : ℝ, ∀ x : ℂ, R₀' + Ustar ω₀ * |t| < ‖x‖ → iter ω₀ j t x = 0 := by
  obtain ⟨R₀', hlt, hR⟩ := exists_inner_radius h
  exact ⟨R₀', hlt, fun j => (iterates_smooth_support h hne j).2 R₀' hR⟩

theorem hasCompactSupport_iter_slice (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (j : ℕ) (t : ℝ) :
    HasCompactSupport (iter ω₀ j t) := by
  obtain ⟨R₀', -, hR⟩ := exists_iter_support h hne
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (R₀' + Ustar ω₀ * |t|))
    fun x hx => ?_
  have hx' : R₀' + Ustar ω₀ * |t| < ‖x‖ := by
    simpa [mem_closedBall, dist_zero_right, not_le] using hx
  exact hR j t x hx'

theorem hasCompactSupport_iter_sliceC (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (j : ℕ)
    (t : ℝ) : HasCompactSupport (fun x => (iter ω₀ j t x : ℂ)) :=
  (hasCompactSupport_iter_slice h hne j t).comp_left Complex.ofReal_zero

theorem memH_iter_slice (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (k j : ℕ) (t : ℝ) :
    MemH k (fun x => (iter ω₀ j t x : ℂ)) :=
  (memH_of_contDiff_hasCompactSupport (contDiff_iter_sliceC h hne j t)
    (hasCompactSupport_iter_sliceC h hne j t) k).1

/-- Outside `\bar B_{R₀' + U_*|t|}` the gradient of `ω^{[j]}(t)` vanishes. -/
theorem fderiv_iter_eq_zero {R₀' : ℝ}
    (hR : ∀ j : ℕ, ∀ t : ℝ, ∀ x : ℂ, R₀' + Ustar ω₀ * |t| < ‖x‖ → iter ω₀ j t x = 0)
    (j : ℕ) (t : ℝ) {x : ℂ} (hx : R₀' + Ustar ω₀ * |t| < ‖x‖) :
    fderiv ℝ (iter ω₀ j t) x = 0 := by
  have hev : iter ω₀ j t =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    have hopen : IsOpen {y : ℂ | R₀' + Ustar ω₀ * |t| < ‖y‖} :=
      isOpen_lt continuous_const continuous_norm
    filter_upwards [hopen.mem_nhds hx] with y hy using hR j t y hy
  rw [hev.fderiv_eq]
  simp

/-- `|∇ω^{[j]}(t, x)| ≤ Ψ(T)` for `|t| ≤ T`. -/
theorem norm_fderiv_iter_le (h : IsSmoothDatum ω₀ R₀) (hne : ω₀ ≠ 0) (j : ℕ) {t T : ℝ}
    (ht : |t| ≤ T) (x : ℂ) : ‖fderiv ℝ (iter ω₀ j t) x‖ ≤ Psi ω₀ T := by
  have hT : |t| ≤ |T| := ht.trans (le_abs_self T)
  exact (iter_lip h hne j t x).1.trans (Psi_mono ω₀ hT)

end NonUniqueEuler.Smooth.IterHsH
