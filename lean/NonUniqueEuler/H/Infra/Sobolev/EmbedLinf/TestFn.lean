import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Function.L2Space
import NonUniqueEuler.Defs.Infra.Sobolev
import NonUniqueEuler.I.Infra.Sobolev.Smooth
import NonUniqueEuler.H.Infra.Sobolev.EmbedLinf.LineFTC

/-!
# Helper for `lem:embed` (E2): the pointwise bound for test functions

Helper of `P/Infra/Sobolev/EmbedLinf.lean` (manuscript `02_prelim.tex:604-606, 624-630`).

For a test function `g` and `h = |g|² = ⟪g, g⟫_ℝ`, the fundamental theorem of calculus along
the lines `t ↦ x + t i` and `s ↦ y + s` gives
`h(x) = ∫_{t ≤ 0} ∫_{s ≤ 0} ∂₁∂₂h(x + t i + s) ds dt`, and
`∂₁∂₂h = 2⟪g, ∂₁∂₂g⟫ + 2⟪∂₁g, ∂₂g⟫` is bounded by `|g|² + |∂₁∂₂g|² + |∂₁g|² + |∂₂g|²`.
Hence `|g(x)|² ≤ ‖g‖²_{L²} + ‖∂₁g‖²_{L²} + ‖∂₂g‖²_{L²} + ‖∂₁∂₂g‖²_{L²} ≤ ‖g‖²_{H²}`
(`norm_le_normH_two_of_testFn`).

**Deviation from the manuscript.** The manuscript proves (E2) with the Fourier transform. This
file uses the elementary argument above (no Fourier transform), which gives the same constant
`1` (the statement is the manuscript's).
-/

noncomputable section

open MeasureTheory Set Filter Complex
open scoped Topology ContDiff RealInnerProductSpace

namespace NonUniqueEuler.Sob.EmbedLinfAux

/-- `‖f‖²_{L²} = ∫ |f|²`. -/
theorem l2_sq_eq_integral {f : ℂ → ℂ} (hf : MemLp f 2 volume) :
    l2 f ^ 2 = ∫ z, ‖f z‖ ^ 2 := by
  have hnn : 0 ≤ ∫ z, ‖f z‖ ^ (2 : ℝ) := integral_nonneg fun z => by positivity
  rw [l2, hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofReal (by positivity)]
  simp only [ENNReal.toReal_ofNat]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hnn]
  norm_num

theorem integrable_norm_sq_of_testFn {f : ℂ → ℂ} (hf : IsTestFn univ f) :
    Integrable (fun z => ‖f z‖ ^ 2) := by
  refine (hf.continuous.norm.pow 2).integrable_of_hasCompactSupport ?_
  refine hf.compact.mono fun z hz => ?_
  simp only [Function.mem_support, ne_eq] at hz ⊢
  intro h0
  exact hz (by simp [h0])

/-- The pointwise bound for test functions:
`|g(x)|² ≤ ∫ (|g|² + |∂₁g|² + |∂₂g|² + |∂₁∂₂g|²)`. -/
theorem sq_norm_le_integral_of_testFn {g : ℂ → ℂ} (hg : IsTestFn univ g) (x : ℂ) :
    ‖g x‖ ^ 2 ≤ ∫ z, (‖g z‖ ^ 2 + ‖dirDeriv 1 g z‖ ^ 2 + ‖dirDeriv I g z‖ ^ 2 +
      ‖dirDeriv 1 (dirDeriv I g) z‖ ^ 2) := by
  -- notation
  set gI : ℂ → ℂ := dirDeriv I g with hgI_def
  set g1 : ℂ → ℂ := dirDeriv 1 g with hg1_def
  set g12 : ℂ → ℂ := dirDeriv 1 gI with hg12_def
  have hgI : IsTestFn univ gI := hg.dirDeriv I
  have hg1 : IsTestFn univ g1 := hg.dirDeriv 1
  have hg12 : IsTestFn univ g12 := hgI.dirDeriv 1
  have hgd : Differentiable ℝ g := hg.smooth.differentiable (by simp)
  have hgId : Differentiable ℝ gI := hgI.smooth.differentiable (by simp)
  set h : ℂ → ℝ := fun z => ⟪g z, g z⟫ with hh_def
  set hI : ℂ → ℝ := fun z => ⟪g z, gI z⟫ + ⟪gI z, g z⟫ with hhI_def
  -- smoothness and supports
  have hh_smooth : ContDiff ℝ ∞ h := hg.smooth.inner ℝ hg.smooth
  have hhI_smooth : ContDiff ℝ ∞ hI :=
    (hg.smooth.inner ℝ hgI.smooth).add (hgI.smooth.inner ℝ hg.smooth)
  have hh_supp : HasCompactSupport h := by
    refine hg.compact.mono fun z hz => ?_
    simp only [Function.mem_support, ne_eq, hh_def] at hz ⊢
    intro h0
    exact hz (by simp [h0])
  have hhI_supp : HasCompactSupport hI := by
    refine hg.compact.mono fun z hz => ?_
    simp only [Function.mem_support, ne_eq, hhI_def] at hz ⊢
    intro h0
    exact hz (by simp [h0])
  -- first derivative
  have hderI : ∀ y, fderiv ℝ h y I = hI y := by
    intro y
    rw [hh_def, fderiv_inner_apply ℝ (hgd y) (hgd y)]
    rfl
  -- second derivative
  set F : ℂ → ℝ := fun y => fderiv ℝ hI y 1 with hF_def
  have hF_eq : ∀ y, F y = (⟪g y, g12 y⟫ + ⟪g1 y, gI y⟫) + (⟪gI y, g1 y⟫ + ⟪g12 y, g y⟫) := by
    intro y
    have h1 : DifferentiableAt ℝ (fun z => ⟪g z, gI z⟫) y := (hgd y).inner ℝ (hgId y)
    have h2 : DifferentiableAt ℝ (fun z => ⟪gI z, g z⟫) y := (hgId y).inner ℝ (hgd y)
    simp only [hF_def, hhI_def]
    rw [fderiv_fun_add h1 h2, add_apply, fderiv_inner_apply ℝ (hgd y) (hgId y),
      fderiv_inner_apply ℝ (hgId y) (hgd y)]
    rfl
  -- integrability of `F`
  have hF_cont : Continuous F :=
    (hhI_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hF_supp : HasCompactSupport F := by
    have : F = (fun L : ℂ →L[ℝ] ℝ => L 1) ∘ fderiv ℝ hI := rfl
    rw [this]
    exact (hhI_supp.fderiv ℝ).comp_left (by simp)
  have hF_int : Integrable F := hF_cont.integrable_of_hasCompactSupport hF_supp
  -- the double fundamental theorem of calculus
  have hftc : h x = ∫ t in Iic (0 : ℝ), ∫ s in Iic (0 : ℝ), F (x + t • I + s • (1 : ℂ)) := by
    rw [← integral_Iic_fderiv_line (hh_smooth.of_le (by simp)) hh_supp x I I_ne_zero]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [hderI]
    exact (integral_Iic_fderiv_line (hhI_smooth.of_le (by simp)) hhI_supp (x + t • I) 1
      one_ne_zero).symm
  -- pointwise bound on `F`
  have hF_le : ∀ y, |F y| ≤ ‖g y‖ ^ 2 + ‖g1 y‖ ^ 2 + ‖gI y‖ ^ 2 + ‖g12 y‖ ^ 2 := by
    intro y
    rw [hF_eq y]
    have a1 := abs_real_inner_le_norm (g y) (g12 y)
    have a2 := abs_real_inner_le_norm (g1 y) (gI y)
    have a3 := abs_real_inner_le_norm (gI y) (g1 y)
    have a4 := abs_real_inner_le_norm (g12 y) (g y)
    have b1 := two_mul_le_add_sq ‖g y‖ ‖g12 y‖
    have b2 := two_mul_le_add_sq ‖g1 y‖ ‖gI y‖
    calc |(⟪g y, g12 y⟫ + ⟪g1 y, gI y⟫) + (⟪gI y, g1 y⟫ + ⟪g12 y, g y⟫)|
        ≤ |⟪g y, g12 y⟫| + |⟪g1 y, gI y⟫| + (|⟪gI y, g1 y⟫| + |⟪g12 y, g y⟫|) := by
          refine (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (abs_add_le _ _))
      _ ≤ ‖g y‖ ^ 2 + ‖g1 y‖ ^ 2 + ‖gI y‖ ^ 2 + ‖g12 y‖ ^ 2 := by
          nlinarith [norm_nonneg (g y), norm_nonneg (g12 y), norm_nonneg (g1 y),
            norm_nonneg (gI y)]
  -- integrate
  have hsum_int : Integrable fun z => ‖g z‖ ^ 2 + ‖g1 z‖ ^ 2 + ‖gI z‖ ^ 2 + ‖g12 z‖ ^ 2 :=
    (((integrable_norm_sq_of_testFn hg).add (integrable_norm_sq_of_testFn hg1)).add
      (integrable_norm_sq_of_testFn hgI)).add (integrable_norm_sq_of_testFn hg12)
  have hsq : ‖g x‖ ^ 2 = h x := by
    simp only [hh_def, real_inner_self_eq_norm_sq]
  calc ‖g x‖ ^ 2 = h x := hsq
    _ ≤ |h x| := le_abs_self _
    _ ≤ ∫ z, |F z| := by
        rw [hftc]
        exact abs_integral_Iic_Iic_le hF_int x
    _ ≤ ∫ z, (‖g z‖ ^ 2 + ‖g1 z‖ ^ 2 + ‖gI z‖ ^ 2 + ‖g12 z‖ ^ 2) :=
        integral_mono hF_int.abs hsum_int hF_le

theorem partialD_zero_zero (f : ℂ → ℂ) : partialD (0, 0) f = f := rfl
theorem partialD_one_zero (f : ℂ → ℂ) : partialD (1, 0) f = dirDeriv 1 f := rfl
theorem partialD_zero_one (f : ℂ → ℂ) : partialD (0, 1) f = dirDeriv I f := rfl
theorem partialD_one_one (f : ℂ → ℂ) : partialD (1, 1) f = dirDeriv 1 (dirDeriv I f) := rfl

/-- (E2) for test functions, squared form: `|g(x)|² ≤ ‖g‖²_{H²}`. -/
theorem sq_norm_le_normH_two_sq_of_testFn {g : ℂ → ℂ} (hg : IsTestFn univ g) (x : ℂ) :
    ‖g x‖ ^ 2 ≤ normH 2 g ^ 2 := by
  obtain ⟨-, -, hnorm⟩ := memH_of_contDiff_hasCompactSupport hg.smooth hg.compact 2
  rw [hnorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  have hsub : ({(0, 0), (1, 0), (0, 1), (1, 1)} : Finset (ℕ × ℕ)) ⊆ multiIdx 2 := by
    intro γ hγ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hγ
    rw [mem_multiIdx]
    rcases hγ with rfl | rfl | rfl | rfl <;> norm_num
  refine (sq_norm_le_integral_of_testFn hg x).trans ?_
  refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _))
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, partialD_zero_zero, partialD_one_zero, partialD_zero_one,
    partialD_one_one]
  have hgI : IsTestFn univ (dirDeriv I g) := hg.dirDeriv I
  have hg1 : IsTestFn univ (dirDeriv 1 g) := hg.dirDeriv 1
  have hg12 : IsTestFn univ (dirDeriv 1 (dirDeriv I g)) := hgI.dirDeriv 1
  have i0 := integrable_norm_sq_of_testFn hg
  have i1 := integrable_norm_sq_of_testFn hg1
  have i2 := integrable_norm_sq_of_testFn hgI
  have i3 := integrable_norm_sq_of_testFn hg12
  have i01 : Integrable fun z => ‖g z‖ ^ 2 + ‖dirDeriv 1 g z‖ ^ 2 := i0.add i1
  have i012 : Integrable fun z => ‖g z‖ ^ 2 + ‖dirDeriv 1 g z‖ ^ 2 + ‖dirDeriv I g z‖ ^ 2 :=
    i01.add i2
  rw [l2_sq_eq_integral (hg.memLp 2 volume), l2_sq_eq_integral (hg1.memLp 2 volume),
    l2_sq_eq_integral (hgI.memLp 2 volume), l2_sq_eq_integral (hg12.memLp 2 volume),
    integral_add i012 i3, integral_add i01 i2, integral_add i0 i1]
  linarith

/-- (E2) for test functions: `|g(x)| ≤ ‖g‖_{H²}`. -/
theorem norm_le_normH_two_of_testFn {g : ℂ → ℂ} (hg : IsTestFn univ g) (x : ℂ) :
    ‖g x‖ ≤ normH 2 g :=
  (pow_le_pow_iff_left₀ (norm_nonneg _) (normH_nonneg 2 g) two_ne_zero).1
    (sq_norm_le_normH_two_sq_of_testFn hg x)

end NonUniqueEuler.Sob.EmbedLinfAux
