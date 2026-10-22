import NonUniqueEuler.Defs.Sec7.All
import NonUniqueEuler.I.Sec2.ExtMultipole
import NonUniqueEuler.I.Sec6.RegionsBasic
import NonUniqueEuler.I.Infra.CkNorm.ArrayNorm
import NonUniqueEuler.H.Sec7.Transfer.Units

/-!
# Helper for `lem:transfer`(3): the non-monopole field of the inner region

Helper of `P/Sec7/Transfer.lean` (`07_several_rings.tex:191-198`). For `g = ω_{≥j+1}(t)` (real,
`C_c^∞`, `3`-fold symmetric by `lem:regions-basic`(3)), supported in `\bar B_R`, `0 < R ≤ ar_j/8`,
with `‖g‖_{L¹} ≤ M A_{j+1}r_{j+1}²`: every `y ∈ N'` has `|r_jy| ≥ ar_j/4 ≥ 2R`;
`lem:ext-multipole` (with the array norm dominating the operator norm) and the scaling rule give
`‖D^q E_{[j]}(y)‖ ≤ M C_{3,q}(4/a)^{4+q} μ s_j² (R/r_j)³` (`inner_region_bound`). With `M = M_vort`
(`lem:speed` gives `‖g‖_{L¹} ≤ M_vort A_{j+1}r_{j+1}²`) this is the computation of the manuscript's
proof of item (3); the same computation is the proof of `lem:inner-field`
(`P/Sec7/InnerField.lean`, `inner_field_bound`, which a proof file may not import), and the proof
below is a copy of it.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler.Rings.TransferAux

open RingData Datum

/-- The bound of `lem:transfer`(3) for a fixed approximation (copy of the bound of `lem:inner-field`), with the explicit constant
`C_in = M_vort Σ_{q≤M_h} C_{3,q} (4/a)^{4+q}` (`07_several_rings.tex:255-263`). -/
theorem inner_region_bound (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ)
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

end NonUniqueEuler.Rings.TransferAux
