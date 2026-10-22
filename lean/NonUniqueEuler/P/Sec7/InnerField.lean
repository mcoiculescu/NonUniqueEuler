import NonUniqueEuler.Defs.Sec7.All
import NonUniqueEuler.I.Sec2.ExtMultipole
import NonUniqueEuler.I.Sec6.RegionsBasic
import NonUniqueEuler.I.Sec6.InnerCirc
import NonUniqueEuler.I.Sec7.FieldUnits
import NonUniqueEuler.I.Infra.CkNorm.ArrayNorm
import NonUniqueEuler.I.Infra.CkNorm.Scaling
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Proof: `lem:inner-field` (the inner field under a mass hypothesis)

Proof of `I/Sec7/InnerField.lean` (`07_several_rings.tex:243-272`).

1. `inner_field`. `C_in = M_vort Σ_{q≤M_h} C_{3,q} (4/a)^{4+q}`. For `g = ω_{≥k+1}(t)` (real,
   `C_c^∞`, `3`-fold symmetric by `lem:regions-basic`(3)), supported in `\bar B_R`, every
   `y ∈ N'` has `|r_k y| ≥ a r_k/4 ≥ 2R`; `lem:ext-multipole` (with the array norm dominating the
   operator norm) and the scaling rule `D^q(E_{[k]})(y) = (A_k r_k)⁻¹ r_k^q D^qE(r_k y)` give
   `‖D^q E_{[k]}(y)‖ ≤ M_vort C_{3,q} (4/a)^{4+q} μ s_k² (R/r_k)³`, using `A_{k+1} = μ A_k`,
   `r_{k+1} = s_k r_k`. Smoothness of `E` on `{|x| > R}` gives `E_{[k]}` smooth on the open set
   `{|y| > R/r_k} ⊇ N'`.
2. `inner_field_eq`. Homogeneity of `K_BS` (`fields_scaleVort`) turns `E_{[k]}` into the
   non-monopole field of `ν^in_k = A_k⁻¹ ω_{≥k+1}(t, r_k ·)`; `∫ ν^in_k = A_k⁻¹ r_k⁻² ∫ ω_{≥k+1}(t)
   = A_k⁻¹ r_k⁻² ∫ ω_{≥k+1}(0) = 2π G_k` (change of variables and `lem:inner-circ`), so the
   monopole of `ν^in_k` is `G_k y^⊥/|y|²`.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Rings

open RingData Datum

/-- A field in ring-`k` units as a scaled composition `y ↦ (A_k r_k)⁻¹ • V(r_k • y)`. -/
private theorem unitsField_eq_smul (P : Approx) (k : ℕ) (V : ℂ → ℂ) :
    P.unitsField k V = fun z => (P.A k * P.r k)⁻¹ • V (P.r k • z) := by
  funext z
  simp only [Approx.unitsField, scaleField, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_mul, div_eq_inv_mul]

/-- The scaling rule for a field in ring-`k` units. -/
private theorem norm_iteratedFDeriv_unitsField (P : Approx) (hP : P.Valid) (k q : ℕ)
    (V : ℂ → ℂ) (y : ℂ) :
    ‖iteratedFDeriv ℝ q (P.unitsField k V) y‖ =
      (P.A k * P.r k)⁻¹ * P.r k ^ q * ‖iteratedFDeriv ℝ q V (P.r k • y)‖ := by
  have hA := hP.A_pos k
  have hr := hP.r_pos k
  rw [unitsField_eq_smul, iteratedFDeriv_comp_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity)]

/-- The bound of `lem:inner-field` for a fixed approximation, with the explicit constant
`C_in = M_vort Σ_{q≤M_h} C_{3,q} (4/a)^{4+q}` (`07_several_rings.tex:255-263`). -/
private theorem inner_field_bound (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ)
    (Mh : ℕ) {k : ℕ} (hk : 1 ≤ k) (hkn : k < P.n) {t : ℝ} (ht : 0 ≤ t) {R : ℝ} (hR : 0 < R)
    (hRa : R ≤ a * P.r k / 8) (hsupp : tsupport (P.omegaGe (k + 1) t) ⊆ closedBall 0 R)
    (hL1 : eLpNorm (P.omegaGe (k + 1) t) 1 volume ≤
        ENNReal.ofReal (Mvort * P.A (k + 1) * P.r (k + 1) ^ 2)) :
    MemCk Mh annN' (P.unitsField k (BS.extField (P.omegaGe (k + 1) t))) ∧
      normCk Mh annN' (P.unitsField k (BS.extField (P.omegaGe (k + 1) t))) ≤
        (Mvort * ∑ q ∈ Finset.range (Mh + 1), BS.cExtMultipole 3 q * (4 / a) ^ (3 + 1 + q)) *
          P.μ * P.s k ^ 2 * (R / P.r k) ^ 3 := by
  set g := P.omegaGe (k + 1) t with hg_def
  have ha : 0 < a := Real.exp_pos _
  have hA := hP.A_pos k
  have hr := hP.r_pos k
  have hμ : 0 < P.μ := by linarith [hP.datumParams.one_lt_μ]
  have hs := hP.s_pos k
  have hMv := Mvort_pos
  have hk1 : k + 1 ∈ Finset.Icc 1 P.n := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  obtain ⟨-, -, -, -, -, -, -, ⟨hgsmooth, hgcpt, -, hgrot⟩⟩ :=
    Approx.regions_basic_three P hP hN hk1 ht
  have hgint : Integrable g volume := hgsmooth.continuous.integrable_of_hasCompactSupport hgcpt
  have hgmem : MemLp g 1 volume := memLp_one_iff_integrable.2 hgint
  have hgsym : IsMFoldSymmetric 3 g := by
    refine Filter.Eventually.of_forall fun x => ?_
    have h3 : (2 * Real.pi / ((3 : ℕ) : ℝ)) = 2 * Real.pi / 3 := by norm_num
    show g (rot (2 * Real.pi / ((3 : ℕ) : ℝ)) x) = g x
    rw [h3]
    exact hgrot x
  have hgsupp : ∀ᵐ y ∂(volume : Measure ℂ), R < ‖y‖ → g y = 0 := by
    refine Filter.Eventually.of_forall fun y hy => ?_
    apply image_eq_zero_of_notMem_tsupport
    intro hy'
    have := hsupp hy'
    rw [mem_closedBall_zero_iff] at this
    linarith
  have hAk1 : P.A (k + 1) = P.μ * P.A k := amp_succ _ _ hk
  have hrk1 : P.r (k + 1) = P.s k * P.r k := radius_succ _ _ hk
  have hgL1 : (eLpNorm g 1 volume).toReal ≤ Mvort * (P.μ * P.A k) * (P.s k * P.r k) ^ 2 := by
    rw [← hAk1, ← hrk1]
    exact ENNReal.toReal_le_of_le_ofReal (by rw [hAk1, hrk1]; positivity) hL1
  obtain ⟨-, hEsmooth⟩ := BS.extField_smooth hR hgmem hgsupp
  -- the pointwise derivative bound on `N'`
  set M : ℕ → ℝ := fun q =>
    Mvort * (BS.cExtMultipole 3 q * (4 / a) ^ (3 + 1 + q)) * P.μ * P.s k ^ 2 * (R / P.r k) ^ 3
    with hM_def
  have hM0 : ∀ q, 0 ≤ M q := by
    intro q
    have hc := (BS.cExtMultipole_finite (m := 3) (by norm_num) q).2.2
    simp only [hM_def]
    positivity
  have hbound : ∀ q ≤ Mh, ∀ y ∈ annN',
      ‖iteratedFDeriv ℝ q (P.unitsField k (BS.extField g)) y‖ ≤ M q := by
    intro q _ y hy
    have hy1 : a / 4 ≤ ‖y‖ := hy.1
    have hc := (BS.cExtMultipole_finite (m := 3) (by norm_num) q).2.2
    rw [norm_iteratedFDeriv_unitsField P hP]
    have hxn : ‖P.r k • y‖ = P.r k * ‖y‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    have hx : 2 * R ≤ ‖P.r k • y‖ := by
      rw [hxn]
      have : P.r k * (a / 4) ≤ P.r k * ‖y‖ := mul_le_mul_of_nonneg_left hy1 hr.le
      linarith
    have h1 := (norm_iteratedFDeriv_le_arrayNorm q (BS.extField g) (P.r k • y)).trans
      (BS.iterDerivArrayNorm_extField_le (m := 3) (q := q) (by norm_num) hR hgmem hgsym hgsupp hx)
    rw [hxn] at h1
    have h2 : ((P.r k * ‖y‖) ^ (3 + 1 + q))⁻¹ ≤ ((P.r k * (a / 4)) ^ (3 + 1 + q))⁻¹ :=
      inv_anti₀ (by positivity)
        (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hy1 hr.le) _)
    have hL0 : 0 ≤ (eLpNorm g 1 volume).toReal := ENNReal.toReal_nonneg
    calc (P.A k * P.r k)⁻¹ * P.r k ^ q * ‖iteratedFDeriv ℝ q (BS.extField g) (P.r k • y)‖
        ≤ (P.A k * P.r k)⁻¹ * P.r k ^ q * (BS.cExtMultipole 3 q * (eLpNorm g 1 volume).toReal *
            R ^ 3 * ((P.r k * ‖y‖) ^ (3 + 1 + q))⁻¹) := by gcongr
      _ ≤ (P.A k * P.r k)⁻¹ * P.r k ^ q * (BS.cExtMultipole 3 q *
            (Mvort * (P.μ * P.A k) * (P.s k * P.r k) ^ 2) * R ^ 3 *
            ((P.r k * (a / 4)) ^ (3 + 1 + q))⁻¹) := by gcongr
      _ = M q := by
        have e1 : (4 / a) ^ (3 + 1 + q) = ((a / 4) ^ (3 + 1 + q))⁻¹ := by
          rw [← inv_pow, inv_div]
        have e2 : (P.r k * (a / 4)) ^ (3 + 1 + q) =
            P.r k ^ (3 + 1) * P.r k ^ q * (a / 4) ^ (3 + 1 + q) := by
          rw [mul_pow, pow_add (P.r k) (3 + 1) q]
        have hX : 0 < (a / 4) ^ (3 + 1 + q) := by positivity
        show _ = Mvort * (BS.cExtMultipole 3 q * (4 / a) ^ (3 + 1 + q)) * P.μ * P.s k ^ 2 *
          (R / P.r k) ^ 3
        rw [e1, e2]
        generalize (a / 4) ^ (3 + 1 + q) = X at hX ⊢
        field_simp
  -- `E_{[k]}` is smooth near `N'`
  have hnear : IsCkNear Mh annN' (P.unitsField k (BS.extField g)) := by
    refine ⟨{y : ℂ | R / P.r k < ‖y‖}, isOpen_lt continuous_const continuous_norm, ?_, ?_⟩
    · intro y hy
      have hy1 : a / 4 ≤ ‖y‖ := hy.1
      have : R / P.r k ≤ a / 8 := by rw [div_le_iff₀ hr]; linarith
      show R / P.r k < ‖y‖
      linarith
    · rw [unitsField_eq_smul]
      have hmaps : MapsTo (fun z : ℂ => P.r k • z) {y : ℂ | R / P.r k < ‖y‖}
          {x : ℂ | R < ‖x‖} := by
        intro z hz
        have hz : R / P.r k < ‖z‖ := hz
        show R < ‖P.r k • z‖
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
        rw [div_lt_iff₀ hr] at hz
        linarith
      have hcomp := hEsmooth.comp (contDiff_const_smul (P.r k)).contDiffOn hmaps
      exact (hcomp.const_smul ((P.A k * P.r k)⁻¹)).of_le (by exact_mod_cast le_top)
  have hmem : MemCk Mh annN' (P.unitsField k (BS.extField g)) :=
    ⟨hnear, normCkE_ne_top_of_bound M hbound⟩
  refine ⟨hmem, ?_⟩
  refine (normCk_le_of_bound M hM0 hbound).trans (le_of_eq ?_)
  simp only [hM_def]
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]

/-- **`lem:inner-field`** (`07_several_rings.tex:243-250`), existence of `C_in`. Under (N1)–(N3),
for an admissible `χ` and `M_h ≥ 1` there is `C_in` such that for every valid approximation with
cutoff `χ`, `1 ≤ k < n`, `t ≥ 0` and `0 < R ≤ a r_k/8`: if `ω_{≥k+1}(t)` is supported in `\bar B_R`
and `‖ω_{≥k+1}(t)‖_{L¹} ≤ M_vort A_{k+1}r_{k+1}²`, then the non-monopole field `E` of `ω_{≥k+1}(t)`
satisfies `‖E_{[k]}‖_{C^{M_h}(N')} ≤ C_in μ s_k² (R/r_k)^m` (`Rings.IsInnerFieldConst`). -/
theorem inner_field (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    (Mh : ℕ) (hMh : 1 ≤ Mh) :
    ∃ C : ℝ, IsInnerFieldConst χ Mh C := by
  have ha : 0 < a := Real.exp_pos _
  have hc : ∀ q, 0 < BS.cExtMultipole 3 q := fun q =>
    (BS.cExtMultipole_finite (m := 3) (by norm_num) q).2.2
  refine ⟨Mvort * ∑ q ∈ Finset.range (Mh + 1), BS.cExtMultipole 3 q * (4 / a) ^ (3 + 1 + q),
    ?_, ?_⟩
  · exact mul_pos Mvort_pos (Finset.sum_pos (fun q _ => mul_pos (hc q) (by positivity))
      ⟨0, by simp⟩)
  · intro P hPχ hP k hk hkn t ht R hR hRa hsupp hL1
    subst hPχ
    exact inner_field_bound P hP hN Mh hk hkn ht hR hRa hsupp hL1

/-- **`lem:inner-field`, the identity** (`07_several_rings.tex:250-251`, proof `:264-271`). If
`D_{k+1}(t) ⊂ B_{a r_k/8}` (`1 ≤ k < n`, `t ≥ 0`), the non-monopole field of `ω_{≥k+1}(t)` in
ring-`k` units is the inner field `h^in_k(A_k t)` on `N'`. -/
theorem inner_field_eq (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k < P.n) {t : ℝ} (ht : 0 ≤ t) (hin : P.HInDefined k t) :
    ∀ y ∈ annN', P.unitsField k (BS.extField (P.omegaGe (k + 1) t)) y = P.hIn k (P.A k * t) y := by
  intro y hy
  have ha : 0 < a := Real.exp_pos _
  have hA := hP.A_pos k
  have hr := hP.r_pos k
  have hy0 : ‖y‖ ≠ 0 := by
    have : a / 4 ≤ ‖y‖ := hy.1
    exact (lt_of_lt_of_le (by positivity) this).ne'
  have hτ : P.A k * t / P.A k = t := by field_simp
  have hkI : k ∈ Finset.Icc 1 P.n := Finset.mem_Icc.2 ⟨hk, hkn.le⟩
  have hcirc := (Approx.inner_circ P hP hN).1 k hkI t ht
  -- `∫ ν^in_k = 2π G_k`
  have hint : ∫ x, P.nuIn k t x = 2 * Real.pi * P.G k := by
    have hcv : ∫ x, P.omegaGe (k + 1) t ((P.r k : ℂ) * x) =
        ((P.r k) ^ 2)⁻¹ * ∫ x, P.omegaGe (k + 1) t x := by
      have h := Measure.integral_comp_smul (volume : Measure ℂ) (P.omegaGe (k + 1) t) (P.r k)
      simp only [Complex.real_smul, Complex.finrank_real_complex] at h
      rw [h, abs_of_pos (by positivity), smul_eq_mul]
    simp only [Approx.nuIn, Approx.unitsVort, scaleVort]
    rw [integral_const_mul, hcv, hcirc, Approx.G]
    field_simp
  simp only [Approx.unitsField]
  rw [← (fields_scaleVort hA hr _).2.2 y, Approx.hIn, hτ, BS.extField, BS.monopole]
  change velocity (P.nuIn k t) y - ((∫ x, P.nuIn k t x : ℝ) : ℂ) * biotSavartKernel y = _
  rw [hint, biotSavartKernel]
  congr 1
  have hy0' : ((‖y‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy0
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  push_cast
  field_simp

end Rings

end NonUniqueEuler
