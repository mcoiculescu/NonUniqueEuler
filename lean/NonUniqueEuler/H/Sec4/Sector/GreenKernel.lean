import NonUniqueEuler.Defs.Sec4.Setting
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Helper for `lem:sector`(1): the kernel of the Green operator, one source point at a time

Helper file of `P/Sec4/Sector.lean` (fully proved). Manuscript `04_ring.tex:224-243`.

For a source point `ρ > 0` and `n ≥ 0`, the kernel of `𝒢_ℓ` (`n = |ℓ|`) is
`ker n t ρ = (min(t,ρ)/max(t,ρ))ⁿ ρ`, i.e. `(t/ρ)ⁿρ` for `t ≤ ρ` and `(ρ/t)ⁿρ` for `t ≥ ρ`.
* `dker n t ρ`: its `t`-derivative off the diagonal, `n(t/ρ)^{n-1}` for `t < ρ` and
  `-n(ρ/t)^{n+1}` for `t ≥ ρ` (the right derivative at `t = ρ`); `|dker| ≤ n`.
* `eker n t ρ = -dker/t + n² ker/t²`: by the radial equation of `tⁿ` and `t⁻ⁿ`, this is the
  second `t`-derivative off the diagonal.
* `integral_dker`: `∫_a^b dker = ker(b) - ker(a)` (FTC with right derivatives).
* `dker_sub_dker`: `dker(b) - dker(a) = ∫_a^b eker - 2n·[a < ρ ≤ b]` (the jump `-2n` of
  `dker` at `t = ρ`; this produces the source term `g` of the radial equation).
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace NonUniqueEuler.SectorH

/-- The kernel `(min(t,ρ)/max(t,ρ))ⁿ ρ` of the Green operator. -/
def ker (n : ℕ) (t ρ : ℝ) : ℝ := (min t ρ / max t ρ) ^ n * ρ

/-- The left branch `(t/ρ)ⁿρ` (for `t ≤ ρ`). -/
def kL (n : ℕ) (ρ t : ℝ) : ℝ := (t / ρ) ^ n * ρ

/-- The right branch `(ρ/t)ⁿρ` (for `t ≥ ρ`). -/
def kR (n : ℕ) (ρ t : ℝ) : ℝ := (ρ / t) ^ n * ρ

/-- The derivative of the left branch, `n(t/ρ)^{n-1}`. -/
def dL (n : ℕ) (ρ t : ℝ) : ℝ := n * (t / ρ) ^ (n - 1)

/-- The derivative of the right branch, `-n(ρ/t)^{n+1}`. -/
def dR (n : ℕ) (ρ t : ℝ) : ℝ := -(n * (ρ / t) ^ (n + 1))

/-- The `t`-derivative of the kernel off the diagonal (right derivative on it). -/
def dker (n : ℕ) (t ρ : ℝ) : ℝ := if t < ρ then dL n ρ t else dR n ρ t

/-- `-dker/t + n² ker/t²`, the second `t`-derivative of the kernel off the diagonal. -/
def eker (n : ℕ) (t ρ : ℝ) : ℝ := -(dker n t ρ / t) + (n : ℝ) ^ 2 * ker n t ρ / t ^ 2

/-- The left branch of `eker`. -/
def eL (n : ℕ) (ρ t : ℝ) : ℝ := -(dL n ρ t / t) + (n : ℝ) ^ 2 * kL n ρ t / t ^ 2

/-- The right branch of `eker`. -/
def eR (n : ℕ) (ρ t : ℝ) : ℝ := -(dR n ρ t / t) + (n : ℝ) ^ 2 * kR n ρ t / t ^ 2

/-! ### The branches -/

theorem ker_of_le {n : ℕ} {t ρ : ℝ} (h : t ≤ ρ) : ker n t ρ = kL n ρ t := by
  simp only [ker, kL, min_eq_left h, max_eq_right h]

theorem ker_of_ge {n : ℕ} {t ρ : ℝ} (h : ρ ≤ t) : ker n t ρ = kR n ρ t := by
  simp only [ker, kR, min_eq_right h, max_eq_left h]

theorem dker_of_lt {n : ℕ} {t ρ : ℝ} (h : t < ρ) : dker n t ρ = dL n ρ t := by
  simp only [dker, h, ↓reduceIte]

theorem dker_of_ge {n : ℕ} {t ρ : ℝ} (h : ρ ≤ t) : dker n t ρ = dR n ρ t := by
  simp only [dker, not_lt.2 h, ↓reduceIte]

theorem eker_of_lt {n : ℕ} {t ρ : ℝ} (h : t < ρ) : eker n t ρ = eL n ρ t := by
  simp only [eker, eL, dker_of_lt h, ker_of_le h.le]

theorem eker_of_ge {n : ℕ} {t ρ : ℝ} (h : ρ ≤ t) : eker n t ρ = eR n ρ t := by
  simp only [eker, eR, dker_of_ge h, ker_of_ge h]

theorem dL_self {n : ℕ} {ρ : ℝ} (hρ : ρ ≠ 0) : dL n ρ ρ = n := by
  simp [dL, div_self hρ]

theorem dR_self {n : ℕ} {ρ : ℝ} (hρ : ρ ≠ 0) : dR n ρ ρ = -n := by
  simp [dR, div_self hρ]

/-! ### Derivatives of the branches -/

theorem hasDerivAt_kL (n : ℕ) {ρ : ℝ} (hρ : ρ ≠ 0) (t : ℝ) :
    HasDerivAt (kL n ρ) (dL n ρ t) t := by
  have h1 : HasDerivAt (fun t : ℝ => t / ρ) (1 / ρ) t := (hasDerivAt_id t).div_const ρ
  have h2 := (h1.pow n).mul_const ρ
  refine h2.congr_deriv ?_
  simp only [dL]
  field_simp

theorem hasDerivAt_kR (n : ℕ) (ρ : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (kR n ρ) (dR n ρ t) t := by
  have h1 : HasDerivAt (fun t : ℝ => ρ / t) (-(ρ / t ^ 2)) t := by
    have := (hasDerivAt_inv ht).const_mul ρ
    simpa [div_eq_mul_inv] using this
  have h2 := (h1.pow n).mul_const ρ
  refine h2.congr_deriv ?_
  simp only [dR]
  rcases n with _ | m
  · simp
  · simp only [Nat.add_sub_cancel, pow_succ]
    field_simp

theorem hasDerivAt_dL (n : ℕ) {ρ t : ℝ} (hρ : ρ ≠ 0) (ht : t ≠ 0) :
    HasDerivAt (dL n ρ) (eL n ρ t) t := by
  have h1 : HasDerivAt (fun t : ℝ => t / ρ) (1 / ρ) t := (hasDerivAt_id t).div_const ρ
  have h2 := (h1.pow (n - 1)).const_mul (n : ℝ)
  refine h2.congr_deriv ?_
  simp only [eL, dL, kL]
  rcases n with _ | m
  · simp
  · rcases m with _ | k
    · norm_num
      field_simp
      ring
    · simp only [Nat.add_sub_cancel]
      simp only [pow_succ]
      field_simp
      push_cast
      ring

theorem hasDerivAt_dR (n : ℕ) (ρ : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (dR n ρ) (eR n ρ t) t := by
  have h1 : HasDerivAt (fun t : ℝ => ρ / t) (-(ρ / t ^ 2)) t := by
    have := (hasDerivAt_inv ht).const_mul ρ
    simpa [div_eq_mul_inv] using this
  have h2 := ((h1.pow (n + 1)).const_mul (n : ℝ)).neg
  refine h2.congr_deriv ?_
  simp only [eR, dR, kR, Nat.add_sub_cancel]
  simp only [pow_succ]
  field_simp
  push_cast
  ring

/-! ### Bounds, continuity, measurability -/

theorem ker_nonneg {n : ℕ} {t ρ : ℝ} (ht : 0 ≤ t) (hρ : 0 < ρ) : 0 ≤ ker n t ρ := by
  have hmax : 0 < max t ρ := lt_max_of_lt_right hρ
  exact mul_nonneg (pow_nonneg (div_nonneg (le_min ht hρ.le) hmax.le) n) hρ.le

theorem ker_le {n : ℕ} {t ρ : ℝ} (ht : 0 ≤ t) (hρ : 0 < ρ) : ker n t ρ ≤ ρ := by
  have hmax : 0 < max t ρ := lt_max_of_lt_right hρ
  have hq0 : 0 ≤ min t ρ / max t ρ := div_nonneg (le_min ht hρ.le) hmax.le
  have hq1 : min t ρ / max t ρ ≤ 1 := (div_le_one hmax).2 min_le_max
  calc ker n t ρ = (min t ρ / max t ρ) ^ n * ρ := rfl
    _ ≤ 1 * ρ := mul_le_mul_of_nonneg_right (pow_le_one₀ hq0 hq1) hρ.le
    _ = ρ := one_mul ρ

theorem abs_ker_le {n : ℕ} {t ρ : ℝ} (ht : 0 ≤ t) (hρ : 0 < ρ) : |ker n t ρ| ≤ ρ := by
  rw [abs_of_nonneg (ker_nonneg ht hρ)]
  exact ker_le ht hρ

theorem abs_dker_le {n : ℕ} {t ρ : ℝ} (ht : 0 < t) (hρ : 0 < ρ) : |dker n t ρ| ≤ n := by
  by_cases h : t < ρ
  · rw [dker_of_lt h, dL, abs_mul, Nat.abs_cast]
    have hq0 : 0 ≤ t / ρ := div_nonneg ht.le hρ.le
    have hq1 : t / ρ ≤ 1 := (div_le_one hρ).2 h.le
    rw [abs_of_nonneg (pow_nonneg hq0 _)]
    calc (n : ℝ) * (t / ρ) ^ (n - 1) ≤ n * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ hq0 hq1) (Nat.cast_nonneg n)
      _ = n := mul_one _
  · have h' : ρ ≤ t := not_lt.1 h
    rw [dker_of_ge h', dR, abs_neg, abs_mul, Nat.abs_cast]
    have hq0 : 0 ≤ ρ / t := div_nonneg hρ.le ht.le
    have hq1 : ρ / t ≤ 1 := (div_le_one ht).2 h'
    rw [abs_of_nonneg (pow_nonneg hq0 _)]
    calc (n : ℝ) * (ρ / t) ^ (n + 1) ≤ n * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ hq0 hq1) (Nat.cast_nonneg n)
      _ = n := mul_one _

theorem abs_eker_le {n : ℕ} {t ρ a : ℝ} (ha : 0 < a) (hat : a ≤ t) (hρ : 0 < ρ) :
    |eker n t ρ| ≤ n / a + (n : ℝ) ^ 2 * ρ / a ^ 2 := by
  have ht : 0 < t := ha.trans_le hat
  have h1 : |dker n t ρ / t| ≤ n / a := by
    rw [abs_div, abs_of_pos ht]
    calc |dker n t ρ| / t ≤ n / t := div_le_div_of_nonneg_right (abs_dker_le ht hρ) ht.le
      _ ≤ n / a := div_le_div_of_nonneg_left (Nat.cast_nonneg n) ha hat
  have h2 : |(n : ℝ) ^ 2 * ker n t ρ / t ^ 2| ≤ (n : ℝ) ^ 2 * ρ / a ^ 2 := by
    rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_pos (pow_pos ht 2)]
    calc (n : ℝ) ^ 2 * |ker n t ρ| / t ^ 2 ≤ (n : ℝ) ^ 2 * ρ / t ^ 2 := by
          gcongr
          exact abs_ker_le ht.le hρ
      _ ≤ (n : ℝ) ^ 2 * ρ / a ^ 2 := by
          gcongr
  calc |eker n t ρ| = |-(dker n t ρ / t) + (n : ℝ) ^ 2 * ker n t ρ / t ^ 2| := rfl
    _ ≤ |-(dker n t ρ / t)| + |(n : ℝ) ^ 2 * ker n t ρ / t ^ 2| := abs_add_le _ _
    _ ≤ n / a + (n : ℝ) ^ 2 * ρ / a ^ 2 := add_le_add (by rwa [abs_neg]) h2

theorem continuous_ker (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) : Continuous fun t => ker n t ρ := by
  unfold ker
  refine ((continuous_id.min continuous_const).div (continuous_id.max continuous_const)
    fun t => (lt_max_of_lt_right hρ).ne').pow n |>.mul continuous_const

theorem measurable_ker (n : ℕ) : Measurable fun p : ℝ × ℝ => ker n p.1 p.2 := by
  unfold ker
  fun_prop

theorem measurable_dker (n : ℕ) : Measurable fun p : ℝ × ℝ => dker n p.1 p.2 := by
  unfold dker dL dR
  refine Measurable.ite (measurableSet_lt measurable_fst measurable_snd) ?_ ?_ <;> fun_prop

theorem measurable_eker (n : ℕ) : Measurable fun p : ℝ × ℝ => eker n p.1 p.2 := by
  have h1 := measurable_dker n
  have h2 := measurable_ker n
  unfold eker
  fun_prop

theorem continuousAt_dker (n : ℕ) {t ρ : ℝ} (ht : 0 < t) (htρ : t ≠ ρ) :
    ContinuousAt (fun s => dker n s ρ) t := by
  rcases lt_or_gt_of_ne htρ with h | h
  · have hev : (fun s => dker n s ρ) =ᶠ[𝓝 t] dL n ρ := by
      filter_upwards [Iio_mem_nhds h] with s hs
      exact dker_of_lt hs
    refine ContinuousAt.congr ?_ hev.symm
    unfold dL
    fun_prop
  · have hev : (fun s => dker n s ρ) =ᶠ[𝓝 t] dR n ρ := by
      filter_upwards [Ioi_mem_nhds h] with s hs
      exact dker_of_ge (le_of_lt hs)
    refine ContinuousAt.congr ?_ hev.symm
    unfold dR
    exact ((continuousAt_const.div continuousAt_id ht.ne').pow _ |>.const_mul _).neg

theorem continuousOn_eL (n : ℕ) (ρ : ℝ) : ContinuousOn (eL n ρ) (Ioi 0) := by
  intro t ht
  have ht0 : t ≠ 0 := (ne_of_gt ht)
  refine ContinuousAt.continuousWithinAt ?_
  unfold eL dL kL
  refine ContinuousAt.add (ContinuousAt.neg (ContinuousAt.div (by fun_prop) continuousAt_id ht0))
    (ContinuousAt.div (by fun_prop) (by fun_prop) (pow_ne_zero 2 ht0))

theorem continuousOn_eR (n : ℕ) (ρ : ℝ) : ContinuousOn (eR n ρ) (Ioi 0) := by
  intro t ht
  have ht0 : t ≠ 0 := (ne_of_gt ht)
  refine ContinuousAt.continuousWithinAt ?_
  have hq : ContinuousAt (fun t : ℝ => ρ / t) t := continuousAt_const.div continuousAt_id ht0
  unfold eR dR kR
  refine ContinuousAt.add (ContinuousAt.neg (ContinuousAt.div ?_ continuousAt_id ht0))
    (ContinuousAt.div ?_ (by fun_prop) (pow_ne_zero 2 ht0))
  · exact ((hq.pow _).const_mul _).neg
  · exact ((hq.pow _).mul continuousAt_const).const_mul _

theorem intervalIntegrable_eL (n : ℕ) (ρ : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (eL n ρ) volume a b :=
  ((continuousOn_eL n ρ).mono fun _ ht => lt_of_lt_of_le (lt_min ha hb) ht.1).intervalIntegrable

theorem intervalIntegrable_eR (n : ℕ) (ρ : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (eR n ρ) volume a b :=
  ((continuousOn_eR n ρ).mono fun _ ht => lt_of_lt_of_le (lt_min ha hb) ht.1).intervalIntegrable

/-- A bounded measurable function on `[a, b]` is interval integrable. -/
theorem intervalIntegrable_of_bound {f : ℝ → ℝ} (hf : Measurable f) {a b M : ℝ}
    (hM : ∀ t ∈ uIoc a b, |f t| ≤ M) : IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := M) ?_ hf.aestronglyMeasurable ?_
  · exact (measure_mono uIoc_subset_uIcc).trans_lt measure_Icc_lt_top |>.ne
  · exact (ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun t ht => by
      rw [Real.norm_eq_abs]; exact hM t ht)

theorem intervalIntegrable_dker (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) : IntervalIntegrable (fun t => dker n t ρ) volume a b := by
  refine intervalIntegrable_of_bound ((measurable_dker n).comp (measurable_id.prodMk
    measurable_const)) (M := n) fun t ht => abs_dker_le ?_ hρ
  exact lt_of_lt_of_le (lt_min ha hb) (uIoc_subset_uIcc ht).1

theorem intervalIntegrable_eker (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) : IntervalIntegrable (fun t => eker n t ρ) volume a b := by
  have hm : 0 < min a b := lt_min ha hb
  refine intervalIntegrable_of_bound ((measurable_eker n).comp (measurable_id.prodMk
    measurable_const)) (M := n / min a b + (n : ℝ) ^ 2 * ρ / min a b ^ 2) fun t ht =>
    abs_eker_le hm (uIoc_subset_uIcc ht).1 hρ

/-! ### The two fundamental theorems of calculus, for a fixed source point -/

/-- `∫_a^b ∂_t ker(t, ρ) dt = ker(b, ρ) - ker(a, ρ)`. -/
theorem integral_dker (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b, dker n t ρ = ker n b ρ - ker n a ρ := by
  refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
    (continuous_ker n hρ).continuousOn (fun x hx => ?_)
    (intervalIntegrable_dker n hρ ha (ha.trans_le hab))
  have hx0 : 0 < x := ha.trans hx.1
  by_cases h : x < ρ
  · rw [dker_of_lt h]
    have hev : (fun t => ker n t ρ) =ᶠ[𝓝 x] kL n ρ := by
      filter_upwards [Iio_mem_nhds h] with s hs
      exact ker_of_le (le_of_lt hs)
    exact ((hasDerivAt_kL n hρ.ne' x).congr_of_eventuallyEq hev).hasDerivWithinAt
  · have h' : ρ ≤ x := not_lt.1 h
    rw [dker_of_ge h']
    refine (hasDerivAt_kR n ρ hx0.ne').hasDerivWithinAt.congr (fun s hs => ?_) (ker_of_ge h')
    exact ker_of_ge (h'.trans (le_of_lt hs))

theorem ae_ne_point (ρ : ℝ) : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ ρ := by
  have : (volume : Measure ℝ) {ρ} = 0 := Real.volume_singleton
  rw [ae_iff]
  simp [this]

/-- `∂_t ker(b, ρ) - ∂_t ker(a, ρ) = ∫_a^b eker(t, ρ) dt - 2n [a < ρ ≤ b]`. -/
theorem dker_sub_dker (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    dker n b ρ - dker n a ρ =
      (∫ t in a..b, eker n t ρ) - 2 * n * (Ioc a b).indicator (fun _ => (1 : ℝ)) ρ := by
  have hb : 0 < b := ha.trans_le hab
  by_cases h1 : ρ ≤ a
  · have hind : (Ioc a b).indicator (fun _ => (1 : ℝ)) ρ = 0 :=
      indicator_of_notMem (fun h => not_lt.2 h1 h.1) _
    have hcongr : ∫ t in a..b, eker n t ρ = ∫ t in a..b, eR n ρ t := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le hab] at ht
      exact eker_of_ge (h1.trans ht.1)
    rw [hind, mul_zero, sub_zero, hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hasDerivAt_dR n ρ (ne_of_gt (lt_of_lt_of_le (lt_min ha hb) ht.1)))
      (intervalIntegrable_eR n ρ ha hb), dker_of_ge (h1.trans hab), dker_of_ge h1]
  · have h1' : a < ρ := not_le.1 h1
    by_cases h2 : b < ρ
    · have hind : (Ioc a b).indicator (fun _ => (1 : ℝ)) ρ = 0 :=
        indicator_of_notMem (fun h => not_le.2 h2 h.2) _
      have hcongr : ∫ t in a..b, eker n t ρ = ∫ t in a..b, eL n ρ t := by
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [uIcc_of_le hab] at ht
        exact eker_of_lt (lt_of_le_of_lt ht.2 h2)
      rw [hind, mul_zero, sub_zero, hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t ht => hasDerivAt_dL n hρ.ne' (ne_of_gt (lt_of_lt_of_le (lt_min ha hb) ht.1)))
        (intervalIntegrable_eL n ρ ha hb), dker_of_lt h2, dker_of_lt h1']
    · have h2' : ρ ≤ b := not_lt.1 h2
      have hind : (Ioc a b).indicator (fun _ => (1 : ℝ)) ρ = 1 :=
        indicator_of_mem (show ρ ∈ Ioc a b from ⟨h1', h2'⟩) _
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_eker n hρ ha hρ) (intervalIntegrable_eker n hρ hρ hb)
      have hleft : ∫ t in a..ρ, eker n t ρ = ∫ t in a..ρ, eL n ρ t := by
        refine intervalIntegral.integral_congr_ae ?_
        filter_upwards [ae_ne_point ρ] with t htρ ht
        rw [uIoc_of_le h1'.le] at ht
        exact eker_of_lt (lt_of_le_of_ne ht.2 htρ)
      have hright : ∫ t in ρ..b, eker n t ρ = ∫ t in ρ..b, eR n ρ t := by
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [uIcc_of_le h2'] at ht
        exact eker_of_ge ht.1
      have hL := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t ht => hasDerivAt_dL n hρ.ne' (ne_of_gt (lt_of_lt_of_le (lt_min ha hρ) ht.1)))
        (intervalIntegrable_eL n ρ ha hρ)
      have hR := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t ht => hasDerivAt_dR n ρ (ne_of_gt (lt_of_lt_of_le (lt_min hρ hb) ht.1)))
        (intervalIntegrable_eR n ρ hρ hb)
      rw [hind, ← hsplit, hleft, hright, hL, hR, dL_self hρ.ne', dR_self hρ.ne',
        dker_of_ge h2', dker_of_lt h1']
      ring

end NonUniqueEuler.SectorH
