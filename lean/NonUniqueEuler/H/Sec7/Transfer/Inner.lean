import NonUniqueEuler.Defs.Sec7.All
import NonUniqueEuler.I.Sec2.ExtMultipole
import NonUniqueEuler.I.Sec6.RegionsBasic
import NonUniqueEuler.I.Sec7.SkSmall
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.I.Infra.Multipole.Holomorphic
import NonUniqueEuler.H.Sec7.Transfer.Fourier
import NonUniqueEuler.H.Sec7.Transfer.Series
import NonUniqueEuler.H.Sec7.Transfer.Fields
import NonUniqueEuler.H.Sec7.Transfer.Units

/-!
# Helper for `lem:transfer`(1), (2): fields induced by the inner material on ring `j`

Helper of `P/Sec7/Transfer.lean` (`07_several_rings.tex:141-189`), for a fixed valid
approximation and with the explicit constants
`C1 M_h = Σ_{q≤M_h} (4/a)^q · 8U_q` and `C2 M_h = Σ_{q≤M_h} (2π)⁻¹ 2^{-1-q} (8/a)^{4+q} · 8U_q`
(`U_q = Σ_l (l+q)^q 2^{-l}` replaces `S_{m,q}`; we bound operator norms of derivatives, which are
at most the manuscript's array norms, so the factor `2^{q/2}` is not needed).
* `inner_general_bound` (item (1)): `E_g = conj F`, `F = Σ_{l≥3} c_l z^{-l-1}` on `|x| > ϱ = ar_{j+1}/8`;
  by Cauchy's coefficient estimate on `|x| = R₀ = ar_{j+1}/4` (`norm_coeff_le_of_sphere`),
  `|c_l| ≤ A_{j+1}r_{j+1}𝓜R₀^{l+1}`, `𝓜 = sup_{|y|=a/4}|(E_g)_{[j+1]}(y)|`; for `y ∈ N'`,
  `|r_jy| ≥ R₀/s_j` and `tsum_ext_le` with the scaling rule give
  `‖D^q(E_g)_{[j]}(y)‖ ≤ ε_j𝓜 (4/a)^q 8U_q`.
* `next_ring_bound` (item (2)): `V_{[j+1]} = K * w_{j+1}(t) = E_{w_{j+1}(t)}` (`∫ w = 0`), the
  coefficients satisfy `|c_l| ≤ (2π)⁻¹‖w‖₁2^l`, and `V_{[j]}(y) = μs_jV_{[j+1]}(y/s_j)` with
  `|y/s_j| ≥ 2/σ`, `σ = 8s_j/a ≤ 1/4`.
-/

noncomputable section

open MeasureTheory Set Metric ComplexConjugate
open scoped ContDiff

namespace NonUniqueEuler.Rings.TransferAux

open RingData Datum

theorem a_pos' : 0 < a := Real.exp_pos _

theorem a_lt_one' : a < 1 := ringData_order.2.2.2.2.2.2.2.2

theorem norm_unitsField_apply (P : Approx) (hP : P.Valid) (k : ℕ) (V : ℂ → ℂ) (y : ℂ) :
    ‖P.unitsField k V y‖ = (P.A k * P.r k)⁻¹ * ‖V (P.r k • y)‖ := by
  have hA := hP.A_pos k
  have hr := hP.r_pos k
  rw [unitsField_eq_smul]
  show ‖(P.A k * P.r k)⁻¹ • V (P.r k • y)‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]

/-- `C^k` near `U` for a scaled composition. -/
theorem isCkNear_smul_comp {U V W : Set ℂ} {h : ℂ → ℂ} {c : ℝ} (lam : ℝ) (hV : IsOpen V)
    (hUV : U ⊆ V) (hh : ContDiffOn ℝ ∞ h W) (hmaps : MapsTo (fun y : ℂ => c • y) V W) (k : ℕ) :
    IsCkNear k U (fun y => lam • h (c • y)) :=
  ⟨V, hV, hUV, ((hh.comp (contDiff_const_smul c).contDiffOn hmaps).const_smul lam).of_le
    (by exact_mod_cast le_top)⟩

theorem isMFoldSymmetric_three_of_forall {g : ℂ → ℝ}
    (h : ∀ x, g (rot (2 * Real.pi / 3) x) = g x) : IsMFoldSymmetric 3 g := by
  refine Filter.Eventually.of_forall fun x => ?_
  have h3 : (2 * Real.pi / ((3 : ℕ) : ℝ)) = 2 * Real.pi / 3 := by norm_num
  show g (rot (2 * Real.pi / ((3 : ℕ) : ℝ)) x) = g x
  rw [h3]
  exact h x

/-! ### Item (1) -/

/-- The constant of item (1). -/
def C1 (Mh : ℕ) : ℝ := ∑ q ∈ Finset.range (Mh + 1), (4 / a) ^ q * (8 * Uq q)

theorem C1_nonneg (Mh : ℕ) : 0 ≤ C1 Mh :=
  Finset.sum_nonneg fun q _ => by
    have := Uq_nonneg q
    have := a_pos'
    positivity

/-- **`lem:transfer`(1)** for a fixed approximation (`07_several_rings.tex:141-171`). -/
theorem inner_general_bound (P : Approx) (hP : P.Valid) (Mh : ℕ) {j : ℕ} (hj : 1 ≤ j)
    {g : ℂ → ℝ} (hg : MemLp g 1 volume) (hsym : IsMFoldSymmetric 3 g)
    (hsupp : ∀ᵐ x ∂(volume : Measure ℂ), a * P.r (j + 1) / 8 < ‖x‖ → g x = 0) :
    MemCk Mh annN' (P.unitsField j (BS.extField g)) ∧
      normCk Mh annN' (P.unitsField j (BS.extField g)) ≤
        C1 Mh * P.eps j *
          sSup ((fun y => ‖P.unitsField (j + 1) (BS.extField g) y‖) '' sphere (0 : ℂ) (a / 4)) := by
  have ha := a_pos'
  have ha1 := a_lt_one'
  have hA := hP.A_pos j
  have hA1 := hP.A_pos (j + 1)
  have hr := hP.r_pos j
  have hr1 := hP.r_pos (j + 1)
  have hs := hP.s_pos j
  have hμ : 0 < P.μ := by linarith [hP.datumParams.one_lt_μ]
  have hsa : P.s j ≤ a / 32 := ((sk_small P hP).1 j hj).2.2
  have hs2 : P.s j ≤ 1 / 2 := by linarith
  have hAj1 : P.A (j + 1) = P.μ * P.A j := A_succ' P hj
  have hrj1 : P.r (j + 1) = P.s j * P.r j := r_succ' P hj
  have hϱ : 0 < a * P.r (j + 1) / 8 := by positivity
  have hR₀ : 0 < a * P.r (j + 1) / 4 := by positivity
  have hϱR : a * P.r (j + 1) / 8 < a * P.r (j + 1) / 4 := by
    have : 0 < a * P.r (j + 1) := by positivity
    linarith
  have hgi : Integrable g := memLp_one_iff_integrable.mp hg
  have hc := norm_extCoeff_le hϱ.le hgi hsupp
  have hU : IsOpen {z : ℂ | a * P.r (j + 1) / 8 < ‖z‖} :=
    isOpen_lt continuous_const continuous_norm
  have hrep : ∀ z ∈ {z : ℂ | a * P.r (j + 1) / 8 < ‖z‖},
      BS.extField g z = conj (Multipole.laurentTail (extCoeff g) z) :=
    fun z hz => extField_eq_conj_laurentTail hgi hsupp hz
  have hFdiff := Multipole.differentiableOn_laurentTail hϱ.le hc
  have hnormE : ∀ z : ℂ, a * P.r (j + 1) / 8 < ‖z‖ →
      ‖BS.extField g z‖ = ‖Multipole.laurentTail (extCoeff g) z‖ := fun z hz => by
    rw [hrep z hz, Complex.norm_conj]
  have hnormU := norm_unitsField_apply P hP (j + 1) (BS.extField g)
  have hsph : ∀ y ∈ sphere (0 : ℂ) (a / 4), ‖P.r (j + 1) • y‖ = a * P.r (j + 1) / 4 := by
    intro y hy
    rw [mem_sphere_zero_iff_norm] at hy
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr1, hy]
    ring
  set S := (fun y => ‖P.unitsField (j + 1) (BS.extField g) y‖) '' sphere (0 : ℂ) (a / 4) with hSdef
  have hSbdd : BddAbove S := by
    refine ⟨(P.A (j + 1) * P.r (j + 1))⁻¹ * ∑' l : ℕ, ‖extCoeff g l‖ * ((l : ℝ) + ((0 : ℕ) : ℝ)) ^ 0 *
      ((a * P.r (j + 1) / 4) ^ (l + 1 + 0))⁻¹, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    have hx := hsph y hy
    have hxϱ : a * P.r (j + 1) / 8 < ‖P.r (j + 1) • y‖ := by rw [hx]; exact hϱR
    have h0 := Multipole.norm_iteratedDeriv_laurentTail_le hϱ.le hc 0 hxϱ
    rw [iteratedDeriv_zero, hx] at h0
    show ‖P.unitsField (j + 1) (BS.extField g) y‖ ≤ _
    rw [hnormU, hnormE _ hxϱ]
    gcongr
  set M := sSup S with hMdef
  have hM0 : 0 ≤ M := Real.sSup_nonneg (by rintro _ ⟨y, -, rfl⟩; exact norm_nonneg _)
  have hMc : ∀ z : ℂ, ‖z‖ = a * P.r (j + 1) / 4 →
      ‖Multipole.laurentTail (extCoeff g) z‖ ≤ P.A (j + 1) * P.r (j + 1) * M := by
    intro z hz
    have hyz : P.r (j + 1) • ((P.r (j + 1))⁻¹ • z) = z := by
      rw [smul_smul, mul_inv_cancel₀ hr1.ne', one_smul]
    have hy : (P.r (j + 1))⁻¹ • z ∈ sphere (0 : ℂ) (a / 4) := by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr1, hz]
      field_simp
    have h1 : ‖P.unitsField (j + 1) (BS.extField g) ((P.r (j + 1))⁻¹ • z)‖ ≤ M :=
      le_csSup hSbdd ⟨_, hy, rfl⟩
    rw [hnormU, hyz, hnormE z (by rw [hz]; exact hϱR), inv_mul_le_iff₀ (by positivity)] at h1
    exact h1
  have hcoef : ∀ l, ‖extCoeff g l‖ ≤
      (P.A (j + 1) * P.r (j + 1) * M * (a * P.r (j + 1) / 4)) * (a * P.r (j + 1) / 4) ^ l := by
    intro l
    have h := norm_coeff_le_of_sphere hϱ.le hϱR hc hMc l
    calc ‖extCoeff g l‖ ≤ P.A (j + 1) * P.r (j + 1) * M * (a * P.r (j + 1) / 4) ^ (l + 1) := h
      _ = _ := by ring
  have hvan : ∀ l, l < 3 → extCoeff g l = 0 := fun l hl => extCoeff_eq_zero_of_lt_three hsym hl
  -- the pointwise bound on `N'`
  set Mq : ℕ → ℝ := fun q => P.eps j * M * ((4 / a) ^ q * (8 * Uq q)) with hMq
  have hMq0 : ∀ q, 0 ≤ Mq q := fun q => by
    have := Uq_nonneg q
    have := hP.eps_pos j
    simp only [hMq]
    positivity
  have hbound : ∀ q ≤ Mh, ∀ y ∈ annN',
      ‖iteratedFDeriv ℝ q (P.unitsField j (BS.extField g)) y‖ ≤ Mq q := by
    intro q _ y hy
    have hy1 : a / 4 ≤ ‖y‖ := hy.1
    rw [norm_iteratedFDeriv_unitsField P hP]
    have hxn : ‖P.r j • y‖ = P.r j * ‖y‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    have hxR : a * P.r (j + 1) / 4 / P.s j ≤ ‖P.r j • y‖ := by
      rw [hxn, div_le_iff₀ hs, hrj1]
      have h := mul_le_mul_of_nonneg_left hy1 (le_of_lt (mul_pos hr hs))
      calc a * (P.s j * P.r j) / 4 = P.r j * P.s j * (a / 4) := by ring
        _ ≤ P.r j * P.s j * ‖y‖ := h
        _ = P.r j * ‖y‖ * P.s j := by ring
    have hle : a * P.r (j + 1) / 4 ≤ a * P.r (j + 1) / 4 / P.s j :=
      le_div_self hR₀.le hs (by linarith)
    have hxϱ : a * P.r (j + 1) / 8 < ‖P.r j • y‖ := (hϱR.trans_le hle).trans_le hxR
    rw [norm_iteratedFDeriv_of_eqOn_conj hU hFdiff hrep q hxϱ]
    have h1 := Multipole.norm_iteratedDeriv_laurentTail_le hϱ.le hc q hxϱ
    have h2 := tsum_ext_le (by positivity) hR₀ hs hs2 hcoef hvan q hxR
    calc (P.A j * P.r j)⁻¹ * P.r j ^ q *
          ‖iteratedDeriv q (Multipole.laurentTail (extCoeff g)) (P.r j • y)‖
        ≤ (P.A j * P.r j)⁻¹ * P.r j ^ q *
            (P.A (j + 1) * P.r (j + 1) * M * (a * P.r (j + 1) / 4) *
              ((a * P.r (j + 1) / 4) ^ (1 + q))⁻¹ * P.s j ^ (4 + q) * (8 * Uq q)) := by
          gcongr
          exact h1.trans h2
      _ = Mq q := by
          simp only [hMq, Approx.eps_def]
          rw [hAj1, hrj1]
          simp only [div_pow, mul_pow]
          field_simp
          ring
  -- smoothness near `N'`
  have hnear : IsCkNear Mh annN' (P.unitsField j (BS.extField g)) := by
    rw [unitsField_eq_smul]
    refine isCkNear_smul_comp _ (V := {y : ℂ | a * P.r (j + 1) / 8 / P.r j < ‖y‖})
      (isOpen_lt continuous_const continuous_norm) ?_ (BS.extField_smooth hϱ hg hsupp).2 ?_ Mh
    · intro y hy
      have hy1 : a / 4 ≤ ‖y‖ := hy.1
      show a * P.r (j + 1) / 8 / P.r j < ‖y‖
      rw [hrj1]
      have : a * (P.s j * P.r j) / 8 / P.r j = a * P.s j / 8 := by field_simp
      rw [this]
      have : a * P.s j / 8 < a / 4 := by nlinarith
      linarith
    · intro z hz
      have hz : a * P.r (j + 1) / 8 / P.r j < ‖z‖ := hz
      show a * P.r (j + 1) / 8 < ‖P.r j • z‖
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      rw [div_lt_iff₀ hr] at hz
      linarith
  refine ⟨⟨hnear, normCkE_ne_top_of_bound Mq hbound⟩, ?_⟩
  refine (normCk_le_of_bound Mq hMq0 hbound).trans (le_of_eq ?_)
  simp only [hMq, C1]
  rw [Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun q _ => by ring

/-! ### Item (2) -/

/-- The constant of item (2). -/
def C2 (Mh : ℕ) : ℝ :=
  ∑ q ∈ Finset.range (Mh + 1), (2 * Real.pi)⁻¹ * (2 ^ (1 + q))⁻¹ * (8 / a) ^ (4 + q) * (8 * Uq q)

theorem C2_nonneg (Mh : ℕ) : 0 ≤ C2 Mh :=
  Finset.sum_nonneg fun q _ => by
    have := Uq_nonneg q
    have := a_pos'
    have := Real.pi_pos
    positivity

/-- **`lem:transfer`(2)**, `L¹` form, for a fixed approximation (`07_several_rings.tex:173-189`). -/
theorem next_ring_bound (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) (Mh : ℕ)
    {j : ℕ} (hj : 1 ≤ j) (hjn : j < P.n) {t : ℝ} (ht : 0 ≤ t) (hS : P.PertDefined (j + 1) t) :
    MemCk Mh annN' (P.unitsField j (velocity (P.wPhys (j + 1) t))) ∧
      normCk Mh annN' (P.unitsField j (velocity (P.wPhys (j + 1) t))) ≤
        C2 Mh * P.eps j * (eLpNorm (P.wR (j + 1) t) 1 volume).toReal := by
  have ha := a_pos'
  have ha1 := a_lt_one'
  have hA := hP.A_pos j
  have hA1 := hP.A_pos (j + 1)
  have hr := hP.r_pos j
  have hr1 := hP.r_pos (j + 1)
  have hs := hP.s_pos j
  have hμ : 0 < P.μ := by linarith [hP.datumParams.one_lt_μ]
  have hsa : P.s j ≤ a / 32 := ((sk_small P hP).1 j hj).2.2
  have hAj1 : P.A (j + 1) = P.μ * P.A j := A_succ' P hj
  have hrj1 : P.r (j + 1) = P.s j * P.r j := r_succ' P hj
  have hk : j + 1 ∈ Finset.Icc 1 P.n := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  obtain ⟨hwsm, hwcpt, hwsupp, hwrot, -, hwint, -, -⟩ := Approx.regions_basic_four P hP hN hk ht hS
  have hV : P.unitsField (j + 1) (velocity (P.wPhys (j + 1) t)) = velocity (P.wR (j + 1) t) :=
    unitsField_velocity_wPhys P hP (j + 1) t
  have hwi : Integrable (P.wR (j + 1) t) := hwsm.continuous.integrable_of_hasCompactSupport hwcpt
  have hwsym : IsMFoldSymmetric 3 (P.wR (j + 1) t) := isMFoldSymmetric_three_of_forall hwrot
  have hw2 : ∀ᵐ z ∂(volume : Measure ℂ), (2 : ℝ) < ‖z‖ → P.wR (j + 1) t z = 0 :=
    Filter.Eventually.of_forall fun z hz => image_eq_zero_of_notMem_tsupport fun hz' => by
      have := (hwsupp hz').2
      linarith
  have hvel : velocity (P.wR (j + 1) t) = BS.extField (P.wR (j + 1) t) := by
    funext z
    simp only [BS.extField, BS.monopole, hwint, Complex.ofReal_zero, zero_mul, sub_zero]
  have hc := norm_extCoeff_le (by norm_num : (0 : ℝ) ≤ 2) hwi hw2
  have hU : IsOpen {z : ℂ | (2 : ℝ) < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hrep : ∀ z ∈ {z : ℂ | (2 : ℝ) < ‖z‖}, velocity (P.wR (j + 1) t) z =
      conj (Multipole.laurentTail (extCoeff (P.wR (j + 1) t)) z) := fun z hz => by
    rw [hvel]
    exact extField_eq_conj_laurentTail hwi hw2 hz
  have hFdiff := Multipole.differentiableOn_laurentTail (by norm_num : (0 : ℝ) ≤ 2) hc
  have hL : ∫ x, ‖((P.wR (j + 1) t x : ℝ) : ℂ)‖ = (eLpNorm (P.wR (j + 1) t) 1 volume).toReal :=
    integral_norm_ofReal_eq hwi
  have hL0 : 0 ≤ (eLpNorm (P.wR (j + 1) t) 1 volume).toReal := ENNReal.toReal_nonneg
  have hσ0 : 0 < 8 * P.s j / a := by positivity
  have hσ : 8 * P.s j / a ≤ 1 / 2 := by
    rw [div_le_iff₀ ha]
    linarith
  have hσ1 : 8 * P.s j / a < 1 := by linarith
  set Mq : ℕ → ℝ := fun q => P.eps j * (eLpNorm (P.wR (j + 1) t) 1 volume).toReal *
    ((2 * Real.pi)⁻¹ * (2 ^ (1 + q))⁻¹ * (8 / a) ^ (4 + q) * (8 * Uq q)) with hMq
  have hMq0 : ∀ q, 0 ≤ Mq q := fun q => by
    have := Uq_nonneg q
    have := hP.eps_pos j
    have := Real.pi_pos
    simp only [hMq]
    positivity
  have hzn : ∀ y : ℂ, ‖(P.r j / P.r (j + 1)) • y‖ = ‖y‖ / P.s j := by
    intro y
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hr hr1), hrj1]
    field_simp
  have hbound : ∀ q ≤ Mh, ∀ y ∈ annN',
      ‖iteratedFDeriv ℝ q (P.unitsField j (velocity (P.wPhys (j + 1) t))) y‖ ≤ Mq q := by
    intro q _ y hy
    have hy1 : a / 4 ≤ ‖y‖ := hy.1
    rw [norm_iteratedFDeriv_unitsField_change P hP (j + 1) j q, hV]
    have hz2 : 2 / (8 * P.s j / a) ≤ ‖(P.r j / P.r (j + 1)) • y‖ := by
      rw [hzn]
      have he : 2 / (8 * P.s j / a) = a / 4 / P.s j := by field_simp; ring
      rw [he]
      exact div_le_div_of_nonneg_right hy1 hs.le
    have hz2' : (2 : ℝ) < ‖(P.r j / P.r (j + 1)) • y‖ := by
      refine lt_of_lt_of_le ?_ hz2
      rw [lt_div_iff₀ hσ0]
      linarith
    rw [norm_iteratedFDeriv_of_eqOn_conj hU hFdiff hrep q hz2']
    have h1 := Multipole.norm_iteratedDeriv_laurentTail_le (by norm_num : (0 : ℝ) ≤ 2) hc q hz2'
    have hK : 0 ≤ (2 * Real.pi)⁻¹ * ∫ x, ‖((P.wR (j + 1) t x : ℝ) : ℂ)‖ := by
      have := Real.pi_pos
      rw [hL]
      positivity
    have h2 := tsum_ext_le hK (by norm_num : (0 : ℝ) < 2) hσ0 hσ hc
      (fun l hl => extCoeff_eq_zero_of_lt_three hwsym hl) q hz2
    calc (P.A (j + 1) * P.r (j + 1)) / (P.A j * P.r j) * (P.r j / P.r (j + 1)) ^ q *
          ‖iteratedDeriv q (Multipole.laurentTail (extCoeff (P.wR (j + 1) t)))
            ((P.r j / P.r (j + 1)) • y)‖
        ≤ (P.A (j + 1) * P.r (j + 1)) / (P.A j * P.r j) * (P.r j / P.r (j + 1)) ^ q *
            ((2 * Real.pi)⁻¹ * (∫ x, ‖((P.wR (j + 1) t x : ℝ) : ℂ)‖) * ((2 : ℝ) ^ (1 + q))⁻¹ *
              (8 * P.s j / a) ^ (4 + q) * (8 * Uq q)) := by
          gcongr
          exact h1.trans h2
      _ = Mq q := by
          rw [hL]
          simp only [hMq, Approx.eps_def]
          rw [hAj1, hrj1]
          simp only [div_pow, mul_pow]
          field_simp
          ring
  have hnear : IsCkNear Mh annN' (P.unitsField j (velocity (P.wPhys (j + 1) t))) := by
    rw [unitsField_change P hP (j + 1) j, hV]
    refine isCkNear_smul_comp _ (V := {y : ℂ | 2 * P.s j < ‖y‖})
      (isOpen_lt continuous_const continuous_norm) ?_ (contDiffOn_of_eqOn_conj hU hFdiff hrep) ?_ Mh
    · intro y hy
      have hy1 : a / 4 ≤ ‖y‖ := hy.1
      show 2 * P.s j < ‖y‖
      linarith
    · intro y hy
      have hy : 2 * P.s j < ‖y‖ := hy
      show (2 : ℝ) < ‖(P.r j / P.r (j + 1)) • y‖
      rw [hzn, lt_div_iff₀ hs]
      linarith
  refine ⟨⟨hnear, normCkE_ne_top_of_bound Mq hbound⟩, ?_⟩
  refine (normCk_le_of_bound Mq hMq0 hbound).trans (le_of_eq ?_)
  simp only [hMq, C2]
  rw [Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun q _ => by ring

end NonUniqueEuler.Rings.TransferAux
