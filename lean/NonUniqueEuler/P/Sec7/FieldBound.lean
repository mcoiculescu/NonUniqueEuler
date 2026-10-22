import NonUniqueEuler.Defs.Sec7.All
import NonUniqueEuler.I.Sec7.Transfer
import NonUniqueEuler.I.Sec7.InnerField
import NonUniqueEuler.I.Sec7.SkSmall
import NonUniqueEuler.I.Sec7.FieldUnits
import NonUniqueEuler.I.Sec6.RegionsBasic

/-!
# Proof: `lem:field-bound` (the field of a quiet ring is small)

Proof of `I/Sec7/FieldBound.lean`, `07_several_rings.tex:483-515`.

`C_η = max{(a/8)^m C_M, 4‖Φ‖_{L¹} C_O}` with `C_M = C^T_M max(1, C_{L1})`,
`C_O = C^T_O max(1, C_{L1})` of `lem:transfer` (`Rings.transfer`).

* Inner part: `lem:inner-field` (`inner_field_eq`) identifies `h^in_j(A_j t)` with the
  non-monopole field `E` of `ω_{≥j+1}(t)` in ring-`j` units on `N'`. Since both differ by a
  multiple of `y^⊥/|y|²` everywhere (`fields_scaleVort`, the definitions of `h^in`, `extField`
  and the monopole), the identity at one point of `N'` (`y = 1`) gives `h^in_j(A_j t) = E` as
  functions on `ℂ`, so `C^{M_h}(N')` membership and norm transfer. `lem:transfer`(3) with
  `R = a r_j/8` gives `η^in_j ≤ C_M ε_j (a r_j/(8 r_{j+1}))^3 = (a/8)^3 C_M μ s_j² ≤ (a/8)^3 C_M μ s̄²`.
* Outer part: `h^out_j(A_j t)` is the field of `ω(t)1_{S_1(t)∪…∪S_{j-1}(t)}` in ring-`j` units
  (`fields_scaleVort`); `lem:transfer`(4) (`outer_sum`), `lem:regions-basic`(4)
  (`‖w_i(t)‖_{L¹} ≤ 2‖Φ‖_{L¹}`), `b_{i,j} ≤ s̄^{j-i}` (`eq:sk-small`, `μ^{i-j} ≤ 1`) and
  `Σ_{i<j} s̄^{j-i} ≤ 2 s̄` (`s̄ ≤ 1/2`) give `η^out_j ≤ 4‖Φ‖_{L¹} C_O s̄`. The case `j = 1` is the
  empty sum.

Deviation (minor): the manuscript invokes `lem:inner-field` with `R = a r_j/8` via `lem:speed`
only to identify `η^in_j`; here the identification uses the constant-free identity
`inner_field_eq` (whose hypothesis is `D_{j+1}(t) ⊂ B_{a r_j/8}`), so `lem:speed` is not needed.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Rings

open RingData Datum

namespace FieldBoundProof

theorem a_lt_one_aux : a < 1 := by
  unfold a
  rw [Real.exp_lt_one_iff]
  norm_num [ξL, ξR]

theorem one_mem_annN' : (1 : ℂ) ∈ annN' := by
  have h := a_lt_one_aux
  show a / 4 ≤ ‖(1 : ℂ)‖ ∧ ‖(1 : ℂ)‖ ≤ 3
  rw [norm_one]
  constructor <;> linarith

/-- `Σ_{1 ≤ i < j} x^{j-i} ≤ 2x` for `0 ≤ x ≤ 1/2`. -/
theorem sum_Ico_pow_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (j : ℕ) :
    ∑ i ∈ Finset.Ico 1 j, x ^ (j - i) ≤ 2 * x := by
  induction j with
  | zero => simp; linarith
  | succ j ih =>
    rcases Nat.lt_or_ge j 1 with hj | hj
    · interval_cases j
      simp
      linarith
    · rw [Finset.sum_Ico_succ_top hj]
      have hs : ∑ i ∈ Finset.Ico 1 j, x ^ (j + 1 - i) =
          x * ∑ i ∈ Finset.Ico 1 j, x ^ (j - i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hij : j + 1 - i = (j - i) + 1 := by
          have := (Finset.mem_Ico.1 hi).2
          omega
        rw [hij, pow_succ]
        ring
      rw [hs, show j + 1 - j = 1 by omega, pow_one]
      have h1 : x * ∑ i ∈ Finset.Ico 1 j, x ^ (j - i) ≤ x * (2 * x) :=
        mul_le_mul_of_nonneg_left ih hx0
      nlinarith

variable {P : Approx}

/-- `b_{i,j} ≤ s̄^{j-i}` for `1 ≤ i < j` (`07_several_rings.tex:511-512`). -/
theorem b_le_sbar_pow (hP : P.Valid) {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) :
    P.b i j ≤ P.sbar ^ (j - i) := by
  have hsk := sk_small P hP
  have hμ : 1 ≤ P.μ := hP.datumParams.one_lt_μ.le
  have hz : P.μ ^ ((i : ℤ) - j) ≤ 1 := zpow_le_one_of_nonpos₀ hμ (by omega)
  have hz0 : 0 < P.μ ^ ((i : ℤ) - j) := zpow_pos (by linarith) _
  have hr : P.r j / P.r i ≤ P.s (j - 1) * P.sbar ^ (j - i - 1) := hsk.2.1 i j hi hij
  have hs1 : P.s (j - 1) ≤ P.sbar / 2 := (hsk.1 (j - 1) (by omega)).2.1
  have hsbar : 0 < P.sbar := hP.datumParams.sbar_pos
  have hrr : 0 ≤ P.r j / P.r i := div_nonneg (hP.r_pos j).le (hP.r_pos i).le
  have hpow : P.sbar ^ (j - i) = P.sbar * P.sbar ^ (j - i - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hr' : P.r j / P.r i ≤ P.sbar ^ (j - i) := by
    rw [hpow]
    calc P.r j / P.r i ≤ P.s (j - 1) * P.sbar ^ (j - i - 1) := hr
      _ ≤ P.sbar * P.sbar ^ (j - i - 1) :=
          mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hsbar.le _)
  rw [Approx.b_def]
  calc P.μ ^ ((i : ℤ) - j) * (P.r j / P.r i) ≤ 1 * (P.r j / P.r i) :=
        mul_le_mul_of_nonneg_right hz hrr
    _ = P.r j / P.r i := one_mul _
    _ ≤ P.sbar ^ (j - i) := hr'

/-- The inner field is the non-monopole field of `ω_{≥j+1}(t)` in ring-`j` units, as functions
on `ℂ` (from `inner_field_eq` at the single point `y = 1 ∈ N'`). -/
theorem hIn_eq_unitsField_extField (hP : P.Valid) (hN : NumericalHypothesis P.χ)
    {j : ℕ} (hj : 1 ≤ j) (hjn : j < P.n) {t : ℝ} (ht : 0 ≤ t) (hin : P.HInDefined j t) :
    P.hIn j (P.A j * t) = P.unitsField j (BS.extField (P.omegaGe (j + 1) t)) := by
  have hA := hP.A_pos j
  have hr := hP.r_pos j
  have hτ : P.A j * t / P.A j = t := by field_simp
  have hE : ∀ y, P.unitsField j (BS.extField (P.omegaGe (j + 1) t)) y =
      velocity (P.nuIn j t) y - BS.monopole (P.nuIn j t) y := by
    intro y
    have h3 := (fields_scaleVort hA hr (P.omegaGe (j + 1) t)).2.2 y
    rw [Approx.unitsField, ← h3]
    rfl
  have hH : ∀ y, P.hIn j (P.A j * t) y =
      velocity (P.nuIn j t) y - (P.G j : ℂ) * (Complex.I * y) / ((‖y‖ ^ 2 : ℝ) : ℂ) := by
    intro y
    simp only [Approx.hIn, hτ]
  set α : ℝ := ∫ x, P.nuIn j t x with hα
  have hdiff : ∀ y, P.hIn j (P.A j * t) y - P.unitsField j (BS.extField (P.omegaGe (j + 1) t)) y =
      ((α / (2 * Real.pi) - P.G j : ℝ) : ℂ) * (Complex.I * y / ((‖y‖ ^ 2 : ℝ) : ℂ)) := by
    intro y
    rw [hH, hE, BS.monopole, biotSavartKernel]
    by_cases hy : y = 0
    · simp [hy]
    · have hy' : ((‖y‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
        have : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
        exact_mod_cast pow_ne_zero 2 this
      have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
      push_cast at hy' ⊢
      field_simp
      ring
  have h1 := inner_field_eq P hP hN hj hjn ht hin 1 one_mem_annN'
  have hc : α / (2 * Real.pi) - P.G j = 0 := by
    have h0 := hdiff 1
    rw [← h1, sub_self] at h0
    simp only [norm_one, one_pow, Complex.ofReal_one, div_one, mul_one] at h0
    have h0' := h0.symm
    rcases mul_eq_zero.1 h0' with h | h
    · exact_mod_cast h
    · exact absurd h Complex.I_ne_zero
  funext y
  have := hdiff y
  rw [hc, Complex.ofReal_zero, zero_mul, sub_eq_zero] at this
  exact this

/-- The outer field is the field of `ω(t)1_{S_1(t)∪…∪S_{j-1}(t)}` in ring-`j` units. -/
theorem hOut_eq_unitsField_velocity (hP : P.Valid) (j : ℕ) (t : ℝ) :
    P.hOut j (P.A j * t) = P.unitsField j (velocity (P.omegaOut j t)) := by
  have hA := hP.A_pos j
  have hr := hP.r_pos j
  have hτ : P.A j * t / P.A j = t := by field_simp
  funext y
  have h1 := (fields_scaleVort hA hr (P.omegaOut j t)).1 y
  simp only [Approx.hOut, hτ, Approx.nuOut, Approx.unitsVort, Approx.unitsField]
  exact h1

end FieldBoundProof

open FieldBoundProof in
/-- **`lem:field-bound`** (`07_several_rings.tex:483-491`), existence of `C_η`. Under (N1)–(N3),
for an admissible `χ` and `M_h ≥ 1` there is `C_η` such that for every valid approximation with
cutoff `χ` and `s̄^{m-2} ≤ 1/2`, every `1 ≤ j < n` and `t ≥ 0`: if `S_i(t) ⊂ N_i` and
`S_i(t) ∩ B_{6r_j} = ∅` for every `i < j` and `D_{j+1}(t) ⊂ B_{ar_j/8}`, then
`η_j(A_jt) ≤ C_η(μs̄² + s̄^{m-2})` (`Rings.IsFieldBoundConst`). -/
theorem field_bound (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    (Mh : ℕ) (hMh : 1 ≤ Mh) :
    ∃ C : ℝ, IsFieldBoundConst χ Mh C := by
  obtain ⟨CTM, CTO, hT⟩ := transfer χ hχ hN Mh hMh
  set CMv : ℝ := CTM * max 1 CL1 with hCMv
  set COv : ℝ := CTO * max 1 CL1 with hCOv
  have hCL : 0 < max 1 CL1 := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hCM : 0 < CMv := mul_pos hT.CTM_pos hCL
  have hCO : 0 < COv := mul_pos hT.CTO_pos hCL
  have ha : 0 < a := Real.exp_pos _
  have hΦ : 0 ≤ PhiL1 χ := PhiL1_nonneg χ
  refine ⟨max ((a / 8) ^ 3 * CMv) (4 * PhiL1 χ * COv), ?_, ?_⟩
  · exact lt_of_lt_of_le (by positivity) (le_max_left _ _)
  intro P hχP hP hsb j hj hjn t ht hS _hout hin
  have hN' : NumericalHypothesis P.χ := hχP ▸ hN
  have hsk := sk_small P hP
  have hsbar : 0 < P.sbar := hP.datumParams.sbar_pos
  have h32 : P.sbar ^ (3 - 2) = P.sbar := by norm_num
  rw [h32] at hsb
  -- the inner part
  set R : ℝ := a * P.r j / 8 with hR
  have hrj := hP.r_pos j
  have hRpos : 0 < R := by positivity
  have hDR : P.D (j + 1) t ⊆ closedBall 0 R := hin.trans ball_subset_closedBall
  obtain ⟨hinM, hinB⟩ := hT.inner_region P hχP hP j hj hjn t ht R hRpos le_rfl hDR
  have hEq := hIn_eq_unitsField_extField hP hN' hj hjn ht hin
  have hsj := hsk.1 j hj
  have hrsucc : P.r (j + 1) = P.s j * P.r j := by
    rw [Approx.r_def, Approx.r_def, Approx.s_def, radius_succ _ _ hj]
  have hinner : P.eps j * (R / P.r (j + 1)) ^ 3 = (a / 8) ^ 3 * (P.μ * P.s j ^ 2) := by
    rw [Approx.eps, hrsucc, hR]
    have := hsj.1.ne'
    field_simp
  have hsj2 : P.μ * P.s j ^ 2 ≤ P.μ * P.sbar ^ 2 := by
    have hμ : 0 < P.μ := by linarith [hP.datumParams.one_lt_μ]
    refine mul_le_mul_of_nonneg_left ?_ hμ.le
    exact pow_le_pow_left₀ hsj.1.le (by linarith [hsj.2.1]) 2
  have hetaIn : P.etaIn Mh j (P.A j * t) ≤ (a / 8) ^ 3 * CMv * (P.μ * P.sbar ^ 2) := by
    rw [Approx.etaIn, hEq]
    calc normCk Mh annN' (P.unitsField j (BS.extField (P.omegaGe (j + 1) t)))
        ≤ CTM * max 1 CL1 * P.eps j * (R / P.r (j + 1)) ^ 3 := hinB
      _ = (a / 8) ^ 3 * CMv * (P.μ * P.s j ^ 2) := by rw [mul_assoc, hinner, hCMv]; ring
      _ ≤ (a / 8) ^ 3 * CMv * (P.μ * P.sbar ^ 2) :=
          mul_le_mul_of_nonneg_left hsj2 (by positivity)
  -- the outer part
  obtain ⟨houtM, houtB⟩ := hT.outer_sum P hχP hP j hj hjn.le t ht hS
  have hOEq := hOut_eq_unitsField_velocity hP j t
  have hsum : ∑ i ∈ Finset.Ico 1 j, P.b i j * (eLpNorm (P.wR i t) 1 volume).toReal ≤
      4 * PhiL1 χ * P.sbar := by
    calc ∑ i ∈ Finset.Ico 1 j, P.b i j * (eLpNorm (P.wR i t) 1 volume).toReal
        ≤ ∑ i ∈ Finset.Ico 1 j, P.sbar ^ (j - i) * (2 * PhiL1 χ) := by
          refine Finset.sum_le_sum fun i hi => ?_
          obtain ⟨hi1, hij⟩ := Finset.mem_Ico.1 hi
          have hb := b_le_sbar_pow hP hi1 hij
          have hiI : i ∈ Finset.Icc 1 P.n := Finset.mem_Icc.2 ⟨hi1, by omega⟩
          have h4 := (Approx.regions_basic_four P hP hN' hiI ht (hS i hi)).2.2.2.2.2.2.1
          rw [hχP] at h4
          have hL : (eLpNorm (P.wR i t) 1 volume).toReal ≤ 2 * PhiL1 χ :=
            ENNReal.toReal_le_of_le_ofReal (by positivity) h4
          exact mul_le_mul hb hL ENNReal.toReal_nonneg (pow_nonneg hsbar.le _)
      _ = (∑ i ∈ Finset.Ico 1 j, P.sbar ^ (j - i)) * (2 * PhiL1 χ) := by
          rw [Finset.sum_mul]
      _ ≤ (2 * P.sbar) * (2 * PhiL1 χ) :=
          mul_le_mul_of_nonneg_right (sum_Ico_pow_sub_le hsbar.le hsb j) (by positivity)
      _ = 4 * PhiL1 χ * P.sbar := by ring
  have hetaOut : P.etaOut Mh j (P.A j * t) ≤ 4 * PhiL1 χ * COv * P.sbar := by
    rw [Approx.etaOut, hOEq]
    calc normCk Mh annN' (P.unitsField j (velocity (P.omegaOut j t)))
        ≤ CTO * max 1 CL1 *
            ∑ i ∈ Finset.Ico 1 j, P.b i j * (eLpNorm (P.wR i t) 1 volume).toReal := houtB
      _ ≤ COv * (4 * PhiL1 χ * P.sbar) := mul_le_mul_of_nonneg_left hsum hCO.le
      _ = 4 * PhiL1 χ * COv * P.sbar := by ring
  refine ⟨hEq ▸ hinM, hOEq ▸ houtM, ?_⟩
  rw [h32, Approx.eta]
  have hm1 : (a / 8) ^ 3 * CMv ≤ max ((a / 8) ^ 3 * CMv) (4 * PhiL1 χ * COv) := le_max_left _ _
  have hm2 : 4 * PhiL1 χ * COv ≤ max ((a / 8) ^ 3 * CMv) (4 * PhiL1 χ * COv) := le_max_right _ _
  have hμs : 0 ≤ P.μ * P.sbar ^ 2 := by
    have hμ : 0 < P.μ := by linarith [hP.datumParams.one_lt_μ]
    positivity
  calc P.etaIn Mh j (P.A j * t) + P.etaOut Mh j (P.A j * t)
      ≤ (a / 8) ^ 3 * CMv * (P.μ * P.sbar ^ 2) + 4 * PhiL1 χ * COv * P.sbar :=
        add_le_add hetaIn hetaOut
    _ ≤ max ((a / 8) ^ 3 * CMv) (4 * PhiL1 χ * COv) * (P.μ * P.sbar ^ 2) +
          max ((a / 8) ^ 3 * CMv) (4 * PhiL1 χ * COv) * P.sbar :=
        add_le_add (mul_le_mul_of_nonneg_right hm1 hμs) (mul_le_mul_of_nonneg_right hm2 hsbar.le)
    _ = max ((a / 8) ^ 3 * CMv) (4 * PhiL1 χ * COv) * (P.μ * P.sbar ^ 2 + P.sbar) := by ring

end Rings

end NonUniqueEuler
