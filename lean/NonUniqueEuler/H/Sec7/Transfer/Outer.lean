import NonUniqueEuler.H.Sec7.Transfer.Inner

/-!
# Helper for `lem:transfer`(4): the field of an outer ring on an inner annulus

Helper of `P/Sec7/Transfer.lean` (`07_several_rings.tex:200-228`), for a fixed valid
approximation and with the explicit constant `C4 M_h = Σ_{q≤M_h} (2π)⁻¹ (2/a) (32/a)² V_q`,
`V_q = Σ_l l^q (3/16)^l`.

`outer_ring_bound`: for `1 ≤ i < k ≤ n` with `S_i(t) ⊂ N_i`, `w = w_i(t)` vanishes on `B_{a/2}`, so
`V_{[i]} = K * w = conj F` on `B_{a/2}` with `F = Σ_l d_l z^l`, `|d_l| ≤ (2π)⁻¹‖w‖₁(2/a)^{l+1}` and
`d_0 = d_1 = 0` (`3`-fold symmetry). With `σ = r_k/r_i ≤ a/32` (`eq:sk-small`) and
`λ = A_ir_i/(A_kr_k) = b_{i,k}σ⁻²`, `V_{[k]}(y) = λV_{[i]}(σy)`, and for `y ∈ N'`, `|σy| ≤ 3σ`:
`λσ^q|d_l||∏_{j<q}(l-j)||σy|^{l-q} ≤ b_{i,k}|d_l| l^q 3^l σ^{l-2}` (the terms with `l < q` or
`l < 2` vanish), which is at most `b_{i,k}(2π)⁻¹‖w‖₁(2/a)(32/a)² l^q(3/16)^l`.
-/

noncomputable section

open MeasureTheory Set Metric ComplexConjugate
open scoped ContDiff

namespace NonUniqueEuler.Rings.TransferAux

open RingData Datum

/-- The constant of item (4). -/
def C4 (Mh : ℕ) : ℝ := ∑ q ∈ Finset.range (Mh + 1), (2 * Real.pi)⁻¹ * (2 / a) * (32 / a) ^ 2 * Vq q

theorem C4_nonneg (Mh : ℕ) : 0 ≤ C4 Mh :=
  Finset.sum_nonneg fun q _ => by
    have := Vq_nonneg q
    have := a_pos'
    have := Real.pi_pos
    positivity

theorem outer_geom_identity (n : ℕ) :
    (2 / a) ^ (n + 3) * (3 : ℝ) ^ (n + 2) * (a / 32) ^ n =
      (2 / a) * (32 / a) ^ 2 * (3 / 16 : ℝ) ^ (n + 2) := by
  have ha := a_pos'
  have h1 : (2 / a) * 3 * (a / 32) = (3 / 16 : ℝ) := by field_simp; norm_num
  have h2 : (2 / a) ^ n * (3 : ℝ) ^ n * (a / 32) ^ n = (3 / 16 : ℝ) ^ n := by
    rw [← mul_pow, ← mul_pow, h1]
  calc (2 / a) ^ (n + 3) * (3 : ℝ) ^ (n + 2) * (a / 32) ^ n =
        ((2 / a) ^ n * (3 : ℝ) ^ n * (a / 32) ^ n) * ((2 / a) ^ 3 * 3 ^ 2) := by ring
    _ = (3 / 16 : ℝ) ^ n * ((2 / a) ^ 3 * 3 ^ 2) := by rw [h2]
    _ = _ := by ring

/-- `r_k / r_i ≤ a/32` for `1 ≤ i < k` (`eq:sk-small`). -/
theorem r_div_r_le (P : Approx) (hP : P.Valid) {i k : ℕ} (hi : 1 ≤ i) (hik : i < k) :
    P.r k / P.r i ≤ a / 32 := by
  have h := (sk_small P hP).2.1 i k hi hik
  have hsk := ((sk_small P hP).1 (k - 1) (by omega)).2.2
  have hsb0 := hP.datumParams.sbar_pos
  have hsb : P.sbar ≤ 1 := by
    have := hP.datumParams.sbar_le
    have := a_lt_one'
    linarith
  have hpow : P.sbar ^ (k - i - 1) ≤ 1 := pow_le_one₀ hsb0.le hsb
  have hs0 := (hP.s_pos (k - 1)).le
  calc P.r k / P.r i ≤ P.s (k - 1) * P.sbar ^ (k - i - 1) := h
    _ ≤ P.s (k - 1) * 1 := by gcongr
    _ ≤ a / 32 := by linarith

/-- **`lem:transfer`(4)**, `L¹` form, for a fixed approximation (`07_several_rings.tex:200-228`). -/
theorem outer_ring_bound (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) (Mh : ℕ)
    {i k : ℕ} (hi : 1 ≤ i) (hik : i < k) (hkn : k ≤ P.n) {t : ℝ} (ht : 0 ≤ t)
    (hS : P.PertDefined i t) :
    MemCk Mh annN' (P.unitsField k (velocity (P.wPhys i t))) ∧
      normCk Mh annN' (P.unitsField k (velocity (P.wPhys i t))) ≤
        C4 Mh * P.b i k * (eLpNorm (P.wR i t) 1 volume).toReal := by
  have ha := a_pos'
  have hAi := hP.A_pos i
  have hAk := hP.A_pos k
  have hri := hP.r_pos i
  have hrk := hP.r_pos k
  have hμ : 0 < P.μ := by linarith [hP.datumParams.one_lt_μ]
  have hσa : P.r k / P.r i ≤ a / 32 := r_div_r_le P hP hi hik
  have hσ0 : 0 < P.r k / P.r i := div_pos hrk hri
  have hb0 : 0 < P.b i k := by
    rw [Approx.b_def]
    exact mul_pos (zpow_pos hμ _) hσ0
  have hlam : (P.A i * P.r i) / (P.A k * P.r k) * (P.r k / P.r i) ^ 2 = P.b i k := by
    rw [Approx.b_def, ← A_div_A P hP hi (by omega)]
    field_simp
  have hiI : i ∈ Finset.Icc 1 P.n := Finset.mem_Icc.2 ⟨hi, by omega⟩
  obtain ⟨hwsm, hwcpt, hwsupp, hwrot, -, -, -, -⟩ := Approx.regions_basic_four P hP hN hiI ht hS
  have hV : P.unitsField i (velocity (P.wPhys i t)) = velocity (P.wR i t) :=
    unitsField_velocity_wPhys P hP i t
  have hwi : Integrable (P.wR i t) := hwsm.continuous.integrable_of_hasCompactSupport hwcpt
  have hwsym : IsMFoldSymmetric 3 (P.wR i t) := isMFoldSymmetric_three_of_forall hwrot
  have hwa : ∀ᵐ z ∂(volume : Measure ℂ), ‖z‖ < a / 2 → P.wR i t z = 0 :=
    Filter.Eventually.of_forall fun z hz => image_eq_zero_of_notMem_tsupport fun hz' => by
      have := (hwsupp hz').1
      linarith
  have ha2 : (0 : ℝ) < a / 2 := by positivity
  have hd := norm_intCoeff_le ha2 hwi hwa
  have hrep : ∀ z ∈ ball (0 : ℂ) (a / 2), velocity (P.wR i t) z =
      conj (powSer (intCoeff (P.wR i t)) z) := fun z hz =>
    velocity_eq_conj_powSer hwi hwa (mem_ball_zero_iff.mp hz)
  have hFdiff := differentiableOn_powSer ha2 hd
  have hL : ∫ x, ‖((P.wR i t x : ℝ) : ℂ)‖ = (eLpNorm (P.wR i t) 1 volume).toReal :=
    integral_norm_ofReal_eq hwi
  have hL0 : 0 ≤ (eLpNorm (P.wR i t) 1 volume).toReal := ENNReal.toReal_nonneg
  have hd' : ∀ l, ‖intCoeff (P.wR i t) l‖ ≤
      (2 * Real.pi)⁻¹ * (eLpNorm (P.wR i t) 1 volume).toReal * (2 / a) ^ (l + 1) := by
    intro l
    refine (hd l).trans (le_of_eq ?_)
    have he : (2 / a) ^ (l + 1) = ((a / 2) ^ (l + 1))⁻¹ := by rw [← inv_pow, inv_div]
    rw [hL, he, pow_succ, mul_inv]
    ring
  set Mq : ℕ → ℝ := fun q => P.b i k * (eLpNorm (P.wR i t) 1 volume).toReal *
    ((2 * Real.pi)⁻¹ * (2 / a) * (32 / a) ^ 2 * Vq q) with hMq
  have hMq0 : ∀ q, 0 ≤ Mq q := fun q => by
    have := Vq_nonneg q
    have := Real.pi_pos
    simp only [hMq]
    positivity
  have hzn : ∀ y : ℂ, ‖(P.r k / P.r i) • y‖ = P.r k / P.r i * ‖y‖ := by
    intro y
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hσ0]
  have hbound : ∀ q ≤ Mh, ∀ y ∈ annN',
      ‖iteratedFDeriv ℝ q (P.unitsField k (velocity (P.wPhys i t))) y‖ ≤ Mq q := by
    intro q _ y hy
    have hy3 : ‖y‖ ≤ 3 := hy.2
    set σ : ℝ := P.r k / P.r i with hσdef
    set lam : ℝ := (P.A i * P.r i) / (P.A k * P.r k) with hlamdef
    have hlam0 : 0 < lam := by positivity
    set z : ℂ := σ • y with hzdef
    have hz3 : ‖z‖ ≤ 3 * σ := by
      rw [hzdef, hzn]
      nlinarith
    have hz : ‖z‖ < a / 2 := by linarith
    rw [norm_iteratedFDeriv_unitsField_change P hP i k q, hV]
    rw [norm_iteratedFDeriv_of_eqOn_conj isOpen_ball hFdiff hrep q (mem_ball_zero_iff.mpr hz)]
    have h1 := norm_iteratedDeriv_powSer_le ha2 hd q hz
    -- the termwise bound
    set f : ℕ → ℝ := fun l => ‖intCoeff (P.wR i t) l‖ *
      ‖∏ j ∈ Finset.range q, ((l : ℂ) - j)‖ * ‖z‖ ^ (l - q) with hf
    set g : ℕ → ℝ := fun l => P.b i k * (eLpNorm (P.wR i t) 1 volume).toReal *
      ((2 * Real.pi)⁻¹ * (2 / a) * (32 / a) ^ 2) * ((l : ℝ) ^ q * (3 / 16 : ℝ) ^ l) with hg
    have hpi := Real.pi_pos
    have hf0 : ∀ l, 0 ≤ lam * σ ^ q * f l := fun l => by simp only [hf]; positivity
    have hterm : ∀ l, lam * σ ^ q * f l ≤ g l := by
      intro l
      have hg0 : 0 ≤ g l := by simp only [hg]; positivity
      rcases lt_or_ge l 2 with hl | hl
      · simp only [hf, intCoeff_eq_zero_of_lt_two hwsym hl, norm_zero, zero_mul, mul_zero]
        exact hg0
      rcases lt_or_ge l q with hlq | hlq
      · simp only [hf, prod_sub_eq_zero_of_lt hlq, norm_zero, zero_mul, mul_zero]
        exact hg0
      obtain ⟨n, rfl⟩ : ∃ n, l = n + 2 := ⟨l - 2, by omega⟩
      have hP' := norm_prod_sub_le (n + 2) q
      have hzp : ‖z‖ ^ (n + 2 - q) ≤ (3 * σ) ^ (n + 2 - q) :=
        pow_le_pow_left₀ (norm_nonneg _) hz3 _
      have hkey : lam * σ ^ q * (3 * σ) ^ (n + 2 - q) = P.b i k * 3 ^ (n + 2 - q) * σ ^ n := by
        rw [mul_pow, ← hlam]
        have hsplit : σ ^ q * σ ^ (n + 2 - q) = σ ^ 2 * σ ^ n := by
          rw [← pow_add, ← pow_add, Nat.add_sub_cancel' hlq, add_comm]
        calc lam * σ ^ q * (3 ^ (n + 2 - q) * σ ^ (n + 2 - q)) =
            lam * (σ ^ q * σ ^ (n + 2 - q)) * 3 ^ (n + 2 - q) := by ring
          _ = _ := by rw [hsplit]; ring
      have h3 : (3 : ℝ) ^ (n + 2 - q) ≤ 3 ^ (n + 2) :=
        pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
      have hσn : σ ^ n ≤ (a / 32) ^ n := pow_le_pow_left₀ hσ0.le hσa n
      have hdn := hd' (n + 2)
      calc lam * σ ^ q * f (n + 2)
          ≤ lam * σ ^ q * ((2 * Real.pi)⁻¹ * (eLpNorm (P.wR i t) 1 volume).toReal *
              (2 / a) ^ (n + 2 + 1) * (((n + 2 : ℕ) : ℝ)) ^ q * (3 * σ) ^ (n + 2 - q)) := by
            simp only [hf]
            gcongr
        _ = (2 * Real.pi)⁻¹ * (eLpNorm (P.wR i t) 1 volume).toReal * (2 / a) ^ (n + 3) *
              (((n + 2 : ℕ) : ℝ)) ^ q * (lam * σ ^ q * (3 * σ) ^ (n + 2 - q)) := by ring
        _ = (2 * Real.pi)⁻¹ * (eLpNorm (P.wR i t) 1 volume).toReal * (2 / a) ^ (n + 3) *
              (((n + 2 : ℕ) : ℝ)) ^ q * (P.b i k * 3 ^ (n + 2 - q) * σ ^ n) := by rw [hkey]
        _ ≤ (2 * Real.pi)⁻¹ * (eLpNorm (P.wR i t) 1 volume).toReal * (2 / a) ^ (n + 3) *
              (((n + 2 : ℕ) : ℝ)) ^ q * (P.b i k * 3 ^ (n + 2) * (a / 32) ^ n) := by gcongr
        _ = P.b i k * (eLpNorm (P.wR i t) 1 volume).toReal * (2 * Real.pi)⁻¹ *
              (((n + 2 : ℕ) : ℝ)) ^ q *
              ((2 / a) ^ (n + 3) * (3 : ℝ) ^ (n + 2) * (a / 32) ^ n) := by ring
        _ = g (n + 2) := by
            rw [outer_geom_identity]
            simp only [hg]
            ring
    have hgs : Summable g := (summable_Vq q).mul_left _
    have hfs : Summable (fun l => lam * σ ^ q * f l) :=
      Summable.of_nonneg_of_le hf0 hterm hgs
    calc lam * σ ^ q * ‖iteratedDeriv q (powSer (intCoeff (P.wR i t))) z‖
        ≤ lam * σ ^ q * ∑' l, f l := by gcongr
      _ = ∑' l, lam * σ ^ q * f l := (tsum_mul_left).symm
      _ ≤ ∑' l, g l := Summable.tsum_le_tsum hterm hfs hgs
      _ = Mq q := by
          simp only [hg, hMq, Vq]
          rw [tsum_mul_left]
          ring
  have hnear : IsCkNear Mh annN' (P.unitsField k (velocity (P.wPhys i t))) := by
    rw [unitsField_change P hP i k, hV]
    refine isCkNear_smul_comp _ (V := ball (0 : ℂ) 4) isOpen_ball ?_
      (contDiffOn_of_eqOn_conj isOpen_ball hFdiff hrep) ?_ Mh
    · intro y hy
      have hy3 : ‖y‖ ≤ 3 := hy.2
      rw [mem_ball_zero_iff]
      linarith
    · intro y hy
      rw [mem_ball_zero_iff] at hy
      show (P.r k / P.r i) • y ∈ ball (0 : ℂ) (a / 2)
      rw [mem_ball_zero_iff, hzn]
      nlinarith
  refine ⟨⟨hnear, normCkE_ne_top_of_bound Mq hbound⟩, ?_⟩
  refine (normCk_le_of_bound Mq hMq0 hbound).trans (le_of_eq ?_)
  simp only [hMq, C4]
  rw [Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun q _ => by ring

end NonUniqueEuler.Rings.TransferAux
