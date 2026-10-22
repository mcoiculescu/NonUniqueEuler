import NonUniqueEuler.Defs.Sec2.BiotSavart
import NonUniqueEuler.Defs.Infra.CkNorm
import NonUniqueEuler.I.Infra.Multipole.Moments
import NonUniqueEuler.I.Infra.Multipole.Laurent
import NonUniqueEuler.I.Infra.Multipole.Holomorphic
import NonUniqueEuler.I.Infra.Multipole.CauchySmooth
import NonUniqueEuler.I.Sec2.BSBasic
import NonUniqueEuler.H.Sec2.ExtMultipole.Series
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Proof of `lem:ext-multipole`, the exterior field of a confined `m`-fold symmetric body

Proof of the interface `NonUniqueEuler/I/Sec2/ExtMultipole.lean` (`02_prelim.tex:470-511`).

Structure (following the manuscript proof, `02_prelim.tex:482-511`).
* `cExtMultipole_finite`: the series part, in `H/Sec2/ExtMultipole/Series.lean`
  (`summable_extSeries`, `bddAbove_extSeries`, `cExtMultipole_pos`).
* `extField_smooth`: for `|x| > ϱ`, `g = 0` a.e. on `ball x (|x| - ϱ)`, so the Biot–Savart
  integral converges absolutely (`Multipole.integrable_biotSavart_of_vanishing`) and the velocity
  is smooth there (`Multipole.contDiffOn_velocity`); the monopole is smooth off `0`
  (`contDiffOn_biotSavartKernel`).
* `iterDerivArrayNorm_extField_le`: with `a_0 = 0`, `a_l = (2πi)⁻¹ Q_l` (`l ≥ 1`), `E = conj F`,
  `F = laurentTail a`, on `{|z| > ϱ}` (`extField_eq_conj_laurentTail`: the exterior expansion of
  the Cauchy transform minus its `l = 0` term, which is the monopole). The array norm of the
  `q`-th derivative of `conj F` is `2^{q/2} |F^{(q)}|` (`iterDerivArrayNorm_conj_eq`, from
  `Multipole.iteratedFDeriv_real_conj_apply_eq`), and `2^{q/2} ≤ 2^q`. The derivative bound
  `Multipole.norm_iteratedDeriv_laurentTail_le` and the vanishing of `Q_l` for `m ∤ l`
  (`Multipole.moment_eq_zero_of_isMFoldSymmetric`) reduce the estimate to the series
  `Σ_j (m(j+1)+q)^q ρ^{m(j+1)} ≤ ρ^m sup`, `ρ = ϱ/|x| ≤ 1/2` (`tsum_coeff_le`,
  `tsum_extSeries_le`).
-/

noncomputable section

open MeasureTheory Set Metric ComplexConjugate Filter Topology
open scoped ENNReal ContDiff

namespace NonUniqueEuler.BS

namespace ExtMultipoleAux

/-- The coefficients of `F = E₁ - iE₂`: `a_0 = 0` and `a_l = (2πi)⁻¹ Q_l` for `l ≥ 1`. -/
def extCoeff (g : ℂ → ℝ) (l : ℕ) : ℂ :=
  if l = 0 then 0 else (2 * Real.pi * Complex.I)⁻¹ * Multipole.moment (fun w => (g w : ℂ)) l

theorem norm_extCoeff_le {ϱ : ℝ} (hϱ : 0 ≤ ϱ) {g : ℂ → ℝ} (hg : Integrable g)
    (hsupp : ∀ᵐ y, ϱ < ‖y‖ → g y = 0) (l : ℕ) :
    ‖extCoeff g l‖ ≤ ((2 * Real.pi)⁻¹ * ∫ w, ‖(g w : ℂ)‖) * ϱ ^ l := by
  have hA : 0 ≤ ∫ w, ‖(g w : ℂ)‖ := integral_nonneg fun _ => norm_nonneg _
  have hpi := Real.pi_pos
  unfold extCoeff
  split_ifs with hl
  · rw [norm_zero]
    positivity
  · have hGs : ∀ᵐ w, ϱ < ‖w‖ → (g w : ℂ) = 0 := by
      filter_upwards [hsupp] with w hw h
      simp [hw h]
    have hm := Multipole.norm_moment_le hg.ofReal hϱ hGs l
    have hn : ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ = (2 * Real.pi)⁻¹ := by
      rw [norm_inv, norm_mul, Complex.norm_I, mul_one, norm_mul, Complex.norm_ofNat,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]
    rw [norm_mul, hn, mul_assoc]
    exact mul_le_mul_of_nonneg_left hm (by positivity)

theorem extCoeff_eq_zero_of_not_dvd {m : ℕ} (hm : 0 < m) {g : ℂ → ℝ}
    (hsym : IsMFoldSymmetric m g) {l : ℕ} (hl : ¬ m ∣ l) : extCoeff g l = 0 := by
  unfold extCoeff
  split_ifs with h0
  · rfl
  · rw [Multipole.moment_eq_zero_of_isMFoldSymmetric hm hsym
      (fun h => hl (Int.natCast_dvd_natCast.mp h)), mul_zero]

/-- `∫ g = Q_0`. -/
theorem moment_zero_ofReal (g : ℂ → ℝ) :
    Multipole.moment (fun w => (g w : ℂ)) ((0 : ℕ) : ℤ) = ((∫ y, g y : ℝ) : ℂ) := by
  simp only [Multipole.moment, Nat.cast_zero, zpow_zero, mul_one]
  exact integral_complex_ofReal

/-- On `{|z| > ϱ}`, `E = conj F` with `F = laurentTail (extCoeff g)`. -/
theorem extField_eq_conj_laurentTail {ϱ : ℝ} {g : ℂ → ℝ} (hg : Integrable g)
    (hsupp : ∀ᵐ y, ϱ < ‖y‖ → g y = 0) {z : ℂ} (hz : ϱ < ‖z‖) :
    extField g z = conj (Multipole.laurentTail (extCoeff g) z) := by
  set G : ℂ → ℂ := fun w => (g w : ℂ) with hG
  set c : ℂ := (2 * Real.pi * Complex.I)⁻¹ with hc
  have hGs : ∀ᵐ w, ϱ < ‖w‖ → G w = 0 := by
    filter_upwards [hsupp] with w hw h
    simp [hG, hw h]
  have hs := (Multipole.hasSum_cauchyTransform_exterior hg.ofReal hGs hz).mul_left c
  have h0 := hasSum_ite_eq (0 : ℕ) (c * (Multipole.moment G ((0 : ℕ) : ℤ) * (z ^ (0 + 1))⁻¹))
  have hs2 := hs.sub h0
  have hfun : (fun l : ℕ => c * (Multipole.moment G l * (z ^ (l + 1))⁻¹) -
      (if l = 0 then c * (Multipole.moment G ((0 : ℕ) : ℤ) * (z ^ (0 + 1))⁻¹) else 0)) =
      fun l => extCoeff g l * (z ^ (l + 1))⁻¹ := by
    funext l
    rcases eq_or_ne l 0 with rfl | hl
    · simp [extCoeff]
    · simp only [extCoeff, hl, ite_false, sub_zero, ← hG, ← hc]
      ring
  have hs3 : HasSum (fun l : ℕ => extCoeff g l * (z ^ (l + 1))⁻¹)
      (c * Multipole.cauchyTransform G z -
        c * (Multipole.moment G ((0 : ℕ) : ℤ) * (z ^ (0 + 1))⁻¹)) := by
    rw [← hfun]
    exact hs2
  have hlt : Multipole.laurentTail (extCoeff g) z =
      c * Multipole.cauchyTransform G z -
        c * (Multipole.moment G ((0 : ℕ) : ℤ) * (z ^ (0 + 1))⁻¹) := hs3.tsum_eq
  rw [extField, Multipole.velocity_eq_conj_cauchyTransform, monopole, hlt, map_sub, ← hG, ← hc]
  congr 1
  rw [← Complex.conj_conj (((∫ y, g y : ℝ) : ℂ) * biotSavartKernel z)]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Multipole.conj_biotSavartKernel, moment_zero_ofReal, hc,
    zero_add, pow_one, mul_inv, mul_inv]
  ring

/-- The `C^k` array norm of `conj F` for holomorphic `F`: `|∇^q conj F| = 2^{q/2} |F^{(q)}|`. -/
theorem iterDerivArrayNorm_conj_eq {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {z : ℂ} (hz : z ∈ U) (q : ℕ) :
    iterDerivArrayNorm q (fun x => conj (F x)) z = Real.sqrt (2 ^ q) * ‖iteratedDeriv q F z‖ := by
  have hdir : ∀ k : Fin 2, ‖(![(1 : ℂ), Complex.I] : Fin 2 → ℂ) k‖ = 1 := by
    intro k
    fin_cases k <;> simp
  have hentry : ∀ i : Fin q → Fin 2,
      ‖iteratedFDeriv ℝ q (fun x => conj (F x)) z (fun j => ![(1 : ℂ), Complex.I] (i j))‖ ^ 2 =
        ‖iteratedDeriv q F z‖ ^ 2 := by
    intro i
    rw [Multipole.iteratedFDeriv_real_conj_apply_eq hU hF hz q, Complex.norm_conj, norm_mul,
      norm_prod, Finset.prod_eq_one (fun j _ => hdir (i j)), mul_one]
  unfold iterDerivArrayNorm
  rw [Finset.sum_congr rfl (fun i _ => hentry i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow,
    Nat.cast_ofNat, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]

theorem sqrt_two_pow_le (q : ℕ) : Real.sqrt (2 ^ q) ≤ 2 ^ q := by
  rw [Real.sqrt_le_left (by positivity)]
  have h1 : (1 : ℝ) ≤ 2 ^ q := one_le_pow₀ (by norm_num)
  nlinarith

/-- `n ∉ range (j ↦ m(j+1))` forces `n = 0` or `m ∤ n`. -/
theorem zero_or_not_dvd_of_not_mem_range {m n : ℕ}
    (hn : n ∉ Set.range fun j : ℕ => m * (j + 1)) : n = 0 ∨ ¬ m ∣ n := by
  by_contra h
  push Not at h
  obtain ⟨hn0, k, rfl⟩ := h
  have hk : k ≠ 0 := by rintro rfl; simp at hn0
  exact hn ⟨k - 1, by
    show m * (k - 1 + 1) = m * k
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk)]⟩

/-- The series bound: only the coefficients `a_{m(j+1)}` survive, and
`Σ_l |a_l| (l+q)^q r^{-l-1-q} ≤ A r^{-1-q} Σ_j (m(j+1)+q)^q (ϱ/r)^{m(j+1)}`. -/
theorem tsum_coeff_le {m q : ℕ} (hm : 1 ≤ m) {ϱ A r : ℝ} (hϱ : 0 < ϱ) (hr : ϱ < r)
    {a : ℕ → ℂ} (ha : ∀ l, ‖a l‖ ≤ A * ϱ ^ l) (hvan : ∀ l, (l = 0 ∨ ¬ m ∣ l) → a l = 0) :
    ∑' l : ℕ, ‖a l‖ * ((l : ℝ) + q) ^ q * (r ^ (l + 1 + q))⁻¹ ≤
      A * (r ^ (1 + q))⁻¹ * ∑' j, extTerm m q (ϱ / r) j := by
  have hr0 : 0 < r := hϱ.trans hr
  set φ : ℕ → ℕ := fun j => m * (j + 1) with hφ
  have hφinj : Function.Injective φ := by
    intro a b hab
    have := Nat.eq_of_mul_eq_mul_left (by omega) hab
    omega
  set f : ℕ → ℝ := fun l => ‖a l‖ * ((l : ℝ) + q) ^ q * (r ^ (l + 1 + q))⁻¹ with hf
  have hf0 : ∀ l, 0 ≤ f l := fun l => by simp only [hf]; positivity
  have hsupp : Function.support f ⊆ Set.range φ := by
    intro l hl
    by_contra hlr
    apply hl
    simp only [hf, hvan l (zero_or_not_dvd_of_not_mem_range hlr), norm_zero, zero_mul]
  rw [← hφinj.tsum_eq hsupp, ← tsum_mul_left]
  have hρ0 : 0 ≤ ϱ / r := by positivity
  have hρ1 : ϱ / r < 1 := (div_lt_one hr0).mpr hr
  have hterm : ∀ j, f (φ j) ≤ A * (r ^ (1 + q))⁻¹ * extTerm m q (ϱ / r) j := by
    intro j
    simp only [hf, hφ, extTerm]
    have hpow : ϱ ^ (m * (j + 1)) * (r ^ (m * (j + 1) + 1 + q))⁻¹ =
        (r ^ (1 + q))⁻¹ * (ϱ / r) ^ (m * (j + 1)) := by
      rw [div_pow, show m * (j + 1) + 1 + q = m * (j + 1) + (1 + q) by ring, pow_add]
      field_simp
    have hcast : ((m * (j + 1) : ℕ) : ℝ) + q = ((m * (j + 1) + q : ℕ) : ℝ) := by push_cast; ring
    calc ‖a (m * (j + 1))‖ * (((m * (j + 1) : ℕ) : ℝ) + q) ^ q *
          (r ^ (m * (j + 1) + 1 + q))⁻¹
        ≤ A * ϱ ^ (m * (j + 1)) * (((m * (j + 1) : ℕ) : ℝ) + q) ^ q *
          (r ^ (m * (j + 1) + 1 + q))⁻¹ := by
          gcongr
          exact ha _
      _ = A * (r ^ (1 + q))⁻¹ *
          ((((m * (j + 1) + q : ℕ) : ℝ)) ^ q * (ϱ / r) ^ (m * (j + 1))) := by
          rw [hcast]
          linear_combination (A * (((m * (j + 1) + q : ℕ) : ℝ)) ^ q) * hpow
  have hsumR : Summable fun j => A * (r ^ (1 + q))⁻¹ * extTerm m q (ϱ / r) j :=
    (summable_extSeries hm q hρ0 hρ1).mul_left _
  exact Summable.tsum_le_tsum hterm
    (Summable.of_nonneg_of_le (fun j => hf0 (φ j)) hterm hsumR) hsumR

end ExtMultipoleAux

open ExtMultipoleAux

/-! ### The interface statements -/

/-- `lem:ext-multipole`: `C_{m,q} < ∞`. For `0 < ρ ≤ 1/2` the series
`Σ_{j≥0} (m(j+1)+q)^q ρ^{m(j+1)}` converges, the function under the supremum in
`cExtMultipole m q` is bounded above on `(0, 1/2]`, and `C_{m,q} > 0`. -/
theorem cExtMultipole_finite {m : ℕ} (hm : 1 ≤ m) (q : ℕ) :
    (∀ ρ ∈ Ioc (0 : ℝ) (1 / 2),
      Summable fun j : ℕ => (((m * (j + 1) + q : ℕ) : ℝ)) ^ q * ρ ^ (m * (j + 1))) ∧
    BddAbove (Set.range fun ρ : Ioc (0 : ℝ) (1 / 2) =>
      ((ρ : ℝ) ^ m)⁻¹ * ∑' j : ℕ, (((m * (j + 1) + q : ℕ) : ℝ)) ^ q * (ρ : ℝ) ^ (m * (j + 1))) ∧
    0 < cExtMultipole m q :=
  ⟨fun ρ hρ => summable_extSeries hm q hρ.1.le (by linarith [hρ.2]), bddAbove_extSeries hm q,
    cExtMultipole_pos hm q⟩

/-- `lem:ext-multipole`, first step of the proof: for `g ∈ L¹` with `supp g ⊂ B̄_ϱ`, the integral
defining `K ∗ g(x)` converges absolutely for `|x| > ϱ`, and `E = K ∗ g - monopole` is smooth on
`{|x| > ϱ}`. -/
theorem extField_smooth {ϱ : ℝ} (hϱ : 0 < ϱ) {g : ℂ → ℝ} (hg : MemLp g 1 volume)
    (hsupp : ∀ᵐ y, ϱ < ‖y‖ → g y = 0) :
    (∀ x : ℂ, ϱ < ‖x‖ → Integrable (fun y => biotSavartKernel (x - y) * (g y : ℂ)) volume) ∧
      ContDiffOn ℝ ∞ (extField g) {x : ℂ | ϱ < ‖x‖} := by
  have hgi : Integrable g := memLp_one_iff_integrable.mp hg
  have hsep : ∀ x : ℂ, ϱ < ‖x‖ → ∀ᵐ w, w ∈ ball x (‖x‖ - ϱ) → g w = 0 := by
    intro x _
    filter_upwards [hsupp] with w hw hwb
    apply hw
    rw [mem_ball, dist_eq_norm] at hwb
    have := norm_sub_norm_le x w
    rw [← norm_neg (w - x), neg_sub] at hwb
    linarith
  have hU : IsOpen {x : ℂ | ϱ < ‖x‖} := isOpen_lt continuous_const continuous_norm
  refine ⟨fun x hx => Multipole.integrable_biotSavart_of_vanishing hgi (by linarith)
    (hsep x hx), ?_⟩
  have hv : ContDiffOn ℝ ∞ (velocity g) {x : ℂ | ϱ < ‖x‖} :=
    Multipole.contDiffOn_velocity hgi hU fun x hx => ⟨‖x‖ - ϱ, by simp at hx; linarith,
      hsep x hx⟩
  have hK : ContDiffOn ℝ ∞ biotSavartKernel {x : ℂ | ϱ < ‖x‖} :=
    contDiffOn_biotSavartKernel.mono fun x hx => by
      change ϱ < ‖x‖ at hx
      simp only [mem_compl_iff, mem_singleton_iff]
      rintro rfl
      simp at hx
      linarith
  have hmono : ContDiffOn ℝ ∞ (monopole g) {x : ℂ | ϱ < ‖x‖} :=
    contDiffOn_const.mul hK
  exact hv.sub hmono

/-- `lem:ext-multipole`: for real `m`-fold symmetric `g ∈ L¹` with `supp g ⊂ B̄_ϱ` and
`|x| ≥ 2ϱ`, `|∇^q E(x)| ≤ C_{m,q} ‖g‖_{L¹} ϱ^m |x|^{-m-1-q}`. -/
theorem iterDerivArrayNorm_extField_le {m q : ℕ} (hm : 1 ≤ m) {ϱ : ℝ} (hϱ : 0 < ϱ)
    {g : ℂ → ℝ} (hg : MemLp g 1 volume) (hsym : IsMFoldSymmetric m g)
    (hsupp : ∀ᵐ y, ϱ < ‖y‖ → g y = 0) {x : ℂ} (hx : 2 * ϱ ≤ ‖x‖) :
    iterDerivArrayNorm q (extField g) x ≤
      cExtMultipole m q * (eLpNorm g 1 volume).toReal * ϱ ^ m * (‖x‖ ^ (m + 1 + q))⁻¹ := by
  have hgi : Integrable g := memLp_one_iff_integrable.mp hg
  set A : ℝ := ∫ w, ‖(g w : ℂ)‖ with hAdef
  have hA0 : 0 ≤ A := integral_nonneg fun _ => norm_nonneg _
  have hAn : A = (eLpNorm g 1 volume).toReal := by
    rw [toReal_eLpNorm hgi.aestronglyMeasurable,
      lpNorm_one_eq_integral_norm hgi.aestronglyMeasurable, hAdef]
    simp [Complex.norm_real]
  set U : Set ℂ := {z : ℂ | ϱ < ‖z‖} with hUdef
  have hU : IsOpen U := isOpen_lt continuous_const continuous_norm
  have hxU : x ∈ U := by
    show ϱ < ‖x‖
    linarith
  have hx0 : 0 < ‖x‖ := by linarith
  set a : ℕ → ℂ := extCoeff g with hadef
  have ha : ∀ l, ‖a l‖ ≤ ((2 * Real.pi)⁻¹ * A) * ϱ ^ l :=
    norm_extCoeff_le hϱ.le hgi hsupp
  have hF : DifferentiableOn ℂ (Multipole.laurentTail a) U :=
    Multipole.differentiableOn_laurentTail hϱ.le ha
  -- `E = conj F` near `x`, so their derivatives at `x` agree.
  have hloc : extField g =ᶠ[𝓝 x] fun z => conj (Multipole.laurentTail a z) := by
    filter_upwards [hU.mem_nhds hxU] with z hz
    exact extField_eq_conj_laurentTail hgi hsupp hz
  have hiter : iteratedFDeriv ℝ q (extField g) x =
      iteratedFDeriv ℝ q (fun z => conj (Multipole.laurentTail a z)) x :=
    (hloc.iteratedFDeriv ℝ q).eq_of_nhds
  have harr : iterDerivArrayNorm q (extField g) x =
      Real.sqrt (2 ^ q) * ‖iteratedDeriv q (Multipole.laurentTail a) x‖ := by
    rw [← iterDerivArrayNorm_conj_eq hU hF hxU q]
    simp only [iterDerivArrayNorm, hiter]
  -- The derivative bound.
  have hder := Multipole.norm_iteratedDeriv_laurentTail_le hϱ.le ha q hxU
  have hvan : ∀ l, (l = 0 ∨ ¬ m ∣ l) → a l = 0 := by
    rintro l (rfl | hl)
    · simp [hadef, extCoeff]
    · exact extCoeff_eq_zero_of_not_dvd (by omega) hsym hl
  have hser := tsum_coeff_le (q := q) hm hϱ (by linarith : ϱ < ‖x‖) ha hvan
  have hρ0 : 0 < ϱ / ‖x‖ := by positivity
  have hρ1 : ϱ / ‖x‖ ≤ 1 / 2 := by
    rw [div_le_iff₀ hx0]
    linarith
  have hsup := tsum_extSeries_le hm q hρ0 hρ1
  have hpi := Real.pi_pos
  have hS0 : 0 < extSup m q := extSup_pos hm q
  have hfin : (‖x‖ ^ (1 + q))⁻¹ * (ϱ / ‖x‖) ^ m = ϱ ^ m * (‖x‖ ^ (m + 1 + q))⁻¹ := by
    rw [div_pow]
    field_simp
    ring
  rw [harr, cExtMultipole_eq, ← hAn]
  calc Real.sqrt (2 ^ q) * ‖iteratedDeriv q (Multipole.laurentTail a) x‖
      ≤ 2 ^ q * ‖iteratedDeriv q (Multipole.laurentTail a) x‖ := by
        gcongr
        exact sqrt_two_pow_le q
    _ ≤ 2 ^ q * ((2 * Real.pi)⁻¹ * A * (‖x‖ ^ (1 + q))⁻¹ *
          ∑' j, extTerm m q (ϱ / ‖x‖) j) := by
        gcongr
        exact hder.trans hser
    _ ≤ 2 ^ q * ((2 * Real.pi)⁻¹ * A * (‖x‖ ^ (1 + q))⁻¹ *
          ((ϱ / ‖x‖) ^ m * extSup m q)) := by
        gcongr
    _ = 2 ^ q / (2 * Real.pi) * extSup m q * A * ϱ ^ m * (‖x‖ ^ (m + 1 + q))⁻¹ := by
        linear_combination (2 ^ q * (2 * Real.pi)⁻¹ * A * extSup m q) * hfin

end NonUniqueEuler.BS
