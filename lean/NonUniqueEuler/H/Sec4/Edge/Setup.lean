import NonUniqueEuler.Defs.Sec4.Setting
import NonUniqueEuler.I.Sec4.SectorSetting
import NonUniqueEuler.H.Sec4.Edge.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Helpers for `P/Sec4/Edge`: notation and pointwise facts for `lem:edge`

Manuscript `04_ring.tex:730-769`. Objects of the proof (for a sector setting `S`):
* `dp S r = max(ω̄'(r), 0)`, `dn S r = max(-ω̄'(r), 0)`, so `|ω̄'| = dp + dn` and `ω̄' = dp - dn`
  (`dp > 0` exactly on `𝒰₊`, `dn > 0` exactly on `𝒰₋`);
* `K0 n r ρ = (min(r,ρ)/max(r,ρ))^n`, the (unnormalized) kernel of `𝒢_ℓ`, `n = |ℓ|`;
* `mres S ℓ z G r = λ + iℓΩ(r;G)` (the inverse of the manuscript's `M_λ`), `Re = Re λ`;
* `Zp S n`, `Zn S n`: the two factors of `Z_n = Z₊ Z₋` (`Zedge_eq_mul`), integrals over
  `I = [r₁, r₂]`.

The key pointwise identity is `K0_mul_cross`: under `S.EdgeSplit`,
`K0(r,ρ)(|ω̄'(r)|ω̄'(ρ) - ω̄'(r)|ω̄'(ρ)|) = 2 r^{-n} dn(r) ρ^n dp(ρ) - 2 r^n dp(r) ρ^{-n} dn(ρ)`:
only the cross terms `𝒰₊ × 𝒰₋`, `𝒰₋ × 𝒰₊` survive, where the kernel factorizes.
-/

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace NonUniqueEuler.EdgeH

open SectorSetting

variable (S : SectorSetting)

/-- `d⁺ = max(ω̄', 0)`. -/
def dp (r : ℝ) : ℝ := max (S.dom r) 0

/-- `d⁻ = max(-ω̄', 0)`. -/
def dn (r : ℝ) : ℝ := max (-S.dom r) 0

/-- The kernel `(min(r,ρ)/max(r,ρ))^n` of the Green operator. -/
def K0 (n : ℕ) (r ρ : ℝ) : ℝ := (min r ρ / max r ρ) ^ n

/-- `λ + iℓΩ(r;G)`. -/
def mres (ℓ : ℤ) (z : ℂ) (G r : ℝ) : ℂ := z + Complex.I * (ℓ : ℂ) * ((S.Omega G r : ℝ) : ℂ)

/-- `Z₊ = ∫_{r₁}^{r₂} r^{2n} d⁺(r) dr`. -/
def Zp (n : ℕ) : ℝ := ∫ r in Icc S.r₁ S.r₂, (r ^ n) ^ 2 * dp S r

/-- `Z₋ = ∫_{r₁}^{r₂} r^{-2n} d⁻(r) dr`. -/
def Zn (n : ℕ) : ℝ := ∫ r in Icc S.r₁ S.r₂, ((r ^ n)⁻¹) ^ 2 * dn S r

variable {S}

/-! ### Pointwise facts -/

theorem continuous_dom (hS : S.Valid) : Continuous S.dom := by
  have h : ContDiff ℝ ∞ S.omR := by
    have : S.omR = S.om ∘ Complex.ofRealCLM := by
      funext r
      simp [omR]
    rw [this]
    exact hS.contDiff.comp Complex.ofRealCLM.contDiff
  exact h.continuous_deriv (by simp)

theorem continuous_dp (hS : S.Valid) : Continuous (dp S) :=
  (continuous_dom hS).max continuous_const

theorem continuous_dn (hS : S.Valid) : Continuous (dn S) :=
  (continuous_dom hS).neg.max continuous_const

theorem dp_nonneg (r : ℝ) : 0 ≤ dp S r := le_max_right _ _

theorem dn_nonneg (r : ℝ) : 0 ≤ dn S r := le_max_right _ _

theorem dp_of_pos {r : ℝ} (h : 0 < S.dom r) : dp S r = S.dom r := max_eq_left h.le

theorem dn_of_pos {r : ℝ} (h : 0 < S.dom r) : dn S r = 0 := max_eq_right (by linarith)

theorem dp_of_neg {r : ℝ} (h : S.dom r < 0) : dp S r = 0 := max_eq_right h.le

theorem dn_of_neg {r : ℝ} (h : S.dom r < 0) : dn S r = -S.dom r := max_eq_left (by linarith)

theorem dp_of_eq {r : ℝ} (h : S.dom r = 0) : dp S r = 0 := by simp [dp, h]

theorem dn_of_eq {r : ℝ} (h : S.dom r = 0) : dn S r = 0 := by simp [dn, h]

theorem abs_dom_eq (r : ℝ) : |S.dom r| = dp S r + dn S r := by
  rcases lt_trichotomy (S.dom r) 0 with h | h | h
  · rw [dp_of_neg h, dn_of_neg h, abs_of_neg h]; ring
  · rw [dp_of_eq h, dn_of_eq h, h]; simp
  · rw [dp_of_pos h, dn_of_pos h, abs_of_pos h]; ring

theorem mem_Icc_of_dom_ne_zero (hS : S.Valid) {r : ℝ} (hr : 0 < r) (h : S.dom r ≠ 0) :
    r ∈ Icc S.r₁ S.r₂ := by
  by_contra hc
  exact h (hS.dom_eq_zero r hr hc)

theorem pos_of_mem_Icc (hS : S.Valid) {r : ℝ} (hr : r ∈ Icc S.r₁ S.r₂) : 0 < r :=
  hS.r₁_pos.trans_le hr.1

theorem Icc_subset_Ioi (hS : S.Valid) : Icc S.r₁ S.r₂ ⊆ Ioi 0 :=
  fun _ hr => pos_of_mem_Icc hS hr

theorem K0_symm (n : ℕ) (r ρ : ℝ) : K0 n r ρ = K0 n ρ r := by
  simp only [K0, min_comm, max_comm]

theorem K0_of_le {n : ℕ} {r ρ : ℝ} (h : r ≤ ρ) : K0 n r ρ = r ^ n * (ρ ^ n)⁻¹ := by
  rw [K0, min_eq_left h, max_eq_right h, div_pow, div_eq_mul_inv]

theorem K0_of_ge {n : ℕ} {r ρ : ℝ} (h : ρ ≤ r) : K0 n r ρ = ρ ^ n * (r ^ n)⁻¹ := by
  rw [K0_symm, K0_of_le h]

/-- The cross-term identity: only `𝒰₊ × 𝒰₋` and `𝒰₋ × 𝒰₊` contribute, where the kernel
factorizes. -/
theorem K0_mul_cross (hsplit : S.EdgeSplit) (n : ℕ) {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) :
    K0 n r ρ * (|S.dom r| * S.dom ρ - S.dom r * |S.dom ρ|) =
      2 * ((r ^ n)⁻¹ * dn S r) * (ρ ^ n * dp S ρ) -
        2 * (r ^ n * dp S r) * ((ρ ^ n)⁻¹ * dn S ρ) := by
  rcases lt_trichotomy (S.dom r) 0 with h1 | h1 | h1 <;>
    rcases lt_trichotomy (S.dom ρ) 0 with h2 | h2 | h2
  · rw [abs_of_neg h1, abs_of_neg h2, dp_of_neg h1, dp_of_neg h2]; ring
  · rw [h2, dp_of_eq h2, dn_of_eq h2]; ring
  · have hlt : ρ < r := hsplit ρ r hρ hr h2 h1
    rw [abs_of_neg h1, abs_of_pos h2, dp_of_neg h1, dn_of_neg h1, dp_of_pos h2, dn_of_pos h2,
      K0_of_ge hlt.le]
    ring
  · rw [h1, dp_of_eq h1, dn_of_eq h1]; ring
  · rw [h1, dp_of_eq h1, dn_of_eq h1]; ring
  · rw [h1, dp_of_eq h1, dn_of_eq h1]; ring
  · have hlt : r < ρ := hsplit r ρ hr hρ h1 h2
    rw [abs_of_pos h1, abs_of_neg h2, dp_of_pos h1, dn_of_pos h1, dp_of_neg h2, dn_of_neg h2,
      K0_of_le hlt.le]
    ring
  · rw [h2, dp_of_eq h2, dn_of_eq h2]; ring
  · rw [abs_of_pos h1, abs_of_pos h2, dn_of_pos h1, dn_of_pos h2]; ring

theorem mres_re (ℓ : ℤ) (z : ℂ) (G r : ℝ) : (mres S ℓ z G r).re = z.re := by
  simp [mres]

theorem mres_ne_zero {ℓ : ℤ} {z : ℂ} (hz : 0 < z.re) (G r : ℝ) : mres S ℓ z G r ≠ 0 := by
  intro h
  have := mres_re (S := S) ℓ z G r
  rw [h, Complex.zero_re] at this
  linarith

theorem continuousOn_mres (hS : S.Valid) (ℓ : ℤ) (z : ℂ) (G : ℝ) :
    ContinuousOn (mres S ℓ z G) (Ioi 0) := by
  have hΩ : ContinuousOn (S.Omega G) (Ioi 0) := (contDiffOn_Omega S hS G).continuousOn
  exact continuousOn_const.add (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hΩ))

theorem continuousOn_K0 {a b : ℝ} (ha : 0 < a) (n : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => K0 n p.1 p.2) (Icc a b ×ˢ Icc a b) := by
  refine ContinuousOn.pow ?_ n
  refine ((continuous_fst.min continuous_snd).continuousOn).div
    ((continuous_fst.max continuous_snd).continuousOn) ?_
  intro p hp
  exact ne_of_gt (lt_max_of_lt_left (ha.trans_le hp.1.1))

theorem continuousOn_K0_right {a b : ℝ} (ha : 0 < a) (n : ℕ) (r : ℝ) :
    ContinuousOn (fun ρ => K0 n r ρ) (Icc a b) := by
  refine ContinuousOn.pow ?_ n
  refine ((continuous_const.min continuous_id).continuousOn).div
    ((continuous_const.max continuous_id).continuousOn) ?_
  intro ρ hρ
  exact ne_of_gt (lt_max_of_lt_right (ha.trans_le hρ.1))

/-! ### `Z_n = Z₊ Z₋` -/

theorem measurableSet_Up (hS : S.Valid) : MeasurableSet {r : ℝ | 0 < r ∧ 0 < S.dom r} :=
  (measurableSet_lt measurable_const measurable_id).inter
    (measurableSet_lt measurable_const (continuous_dom hS).measurable)

theorem measurableSet_Un (hS : S.Valid) : MeasurableSet {r : ℝ | 0 < r ∧ S.dom r < 0} :=
  (measurableSet_lt measurable_const measurable_id).inter
    (measurableSet_lt (continuous_dom hS).measurable measurable_const)

theorem Up_subset (hS : S.Valid) : {r : ℝ | 0 < r ∧ 0 < S.dom r} ⊆ Icc S.r₁ S.r₂ :=
  fun _ hr => mem_Icc_of_dom_ne_zero hS hr.1 hr.2.ne'

theorem Un_subset (hS : S.Valid) : {r : ℝ | 0 < r ∧ S.dom r < 0} ⊆ Icc S.r₁ S.r₂ :=
  fun _ hr => mem_Icc_of_dom_ne_zero hS hr.1 hr.2.ne

theorem Zp_eq (hS : S.Valid) (n : ℕ) :
    Zp S n = ∫ r in {r : ℝ | 0 < r ∧ 0 < S.dom r}, (r ^ n) ^ 2 * |S.dom r| := by
  rw [Zp, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc (Up_subset hS)]
  · refine setIntegral_congr_fun (measurableSet_Up hS) fun r hr => ?_
    rw [dp_of_pos hr.2, abs_of_pos hr.2]
  · intro r hr
    have hr0 : 0 < r := pos_of_mem_Icc hS hr.1
    have hd : S.dom r ≤ 0 := by
      by_contra hc
      exact hr.2 ⟨hr0, lt_of_not_ge hc⟩
    simp [dp, max_eq_right hd]

theorem Zn_eq (hS : S.Valid) (n : ℕ) :
    Zn S n = ∫ r in {r : ℝ | 0 < r ∧ S.dom r < 0}, ((r ^ n)⁻¹) ^ 2 * |S.dom r| := by
  rw [Zn, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc (Un_subset hS)]
  · refine setIntegral_congr_fun (measurableSet_Un hS) fun r hr => ?_
    rw [dn_of_neg hr.2, abs_of_neg hr.2]
  · intro r hr
    have hr0 : 0 < r := pos_of_mem_Icc hS hr.1
    have hd : 0 ≤ S.dom r := by
      by_contra hc
      exact hr.2 ⟨hr0, lt_of_not_ge hc⟩
    simp [dn, max_eq_right (neg_nonpos.2 hd)]

/-- `Z_n = Z₊ Z₋`: on `𝒰₊ × 𝒰₋` the integrand `(r/ρ)^{2n}|ω̄'(r)||ω̄'(ρ)|` factorizes. -/
theorem Zedge_eq_mul (hS : S.Valid) (n : ℕ) : S.Zedge n = Zp S n * Zn S n := by
  rw [Zp_eq hS, Zn_eq hS, Zedge, ← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  simp only
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ρ => ?_)
  simp only
  rw [pow_mul', div_pow, div_eq_mul_inv, mul_pow]
  ring

theorem Zp_nonneg (n : ℕ) : 0 ≤ Zp S n :=
  setIntegral_nonneg measurableSet_Icc fun r _ => mul_nonneg (sq_nonneg _) (dp_nonneg r)

theorem Zn_nonneg (n : ℕ) : 0 ≤ Zn S n :=
  setIntegral_nonneg measurableSet_Icc fun r _ => mul_nonneg (sq_nonneg _) (dn_nonneg r)

end NonUniqueEuler.EdgeH
