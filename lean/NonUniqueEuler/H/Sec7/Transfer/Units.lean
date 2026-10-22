import NonUniqueEuler.Defs.Sec7.All
import NonUniqueEuler.I.Sec7.FieldUnits
import NonUniqueEuler.I.Infra.CkNorm.Scaling

/-!
# Helper for `lem:transfer`: ring units and the scaling rule

Helper of `P/Sec7/Transfer.lean` (`07_several_rings.tex:39-41`, `:138-140`, `:165-169`,
`:222-226`).
* `unitsField_eq_smul`, `norm_iteratedFDeriv_unitsField`: `V_{[k]}(y) = (A_kr_k)⁻¹V(r_ky)` and the
  scaling rule `|∇^qV_{[k]}(y)| = (A_kr_k)⁻¹ r_k^q |∇^qV(r_ky)|`;
* `unitsField_change`, `norm_iteratedFDeriv_unitsField_change`: from ring-`i` to ring-`k` units,
  `V_{[k]}(y) = (A_ir_i)/(A_kr_k) · V_{[i]}((r_k/r_i) y)`;
* `unitsVort_wPhys`, `unitsField_velocity_wPhys`: `A_kw_k(t,·/r_k)` is `w_k(t)` in ring-`k` units,
  so its field in ring-`k` units is `K * w_k(t)` (homogeneity of `K_BS`, `fields_scaleVort`);
* `A_succ'`, `r_succ'`, `A_div_A`: `A_{j+1} = μA_j`, `r_{j+1} = s_jr_j`, `A_i/A_k = μ^{i-k}`.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler.Rings.TransferAux

open RingData Datum

/-- A field in ring-`k` units as a scaled composition `y ↦ (A_k r_k)⁻¹ • V(r_k • y)`. -/
theorem unitsField_eq_smul (P : Approx) (k : ℕ) (V : ℂ → ℂ) :
    P.unitsField k V = fun z => (P.A k * P.r k)⁻¹ • V (P.r k • z) := by
  funext z
  simp only [Approx.unitsField, scaleField, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_mul, div_eq_inv_mul]

/-- The scaling rule for a field in ring-`k` units. -/
theorem norm_iteratedFDeriv_unitsField (P : Approx) (hP : P.Valid) (k q : ℕ)
    (V : ℂ → ℂ) (y : ℂ) :
    ‖iteratedFDeriv ℝ q (P.unitsField k V) y‖ =
      (P.A k * P.r k)⁻¹ * P.r k ^ q * ‖iteratedFDeriv ℝ q V (P.r k • y)‖ := by
  have hA := hP.A_pos k
  have hr := hP.r_pos k
  rw [unitsField_eq_smul, iteratedFDeriv_comp_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity)]

/-- From ring-`i` units to ring-`k` units. -/
theorem unitsField_change (P : Approx) (hP : P.Valid) (i k : ℕ) (V : ℂ → ℂ) :
    P.unitsField k V = fun y =>
      ((P.A i * P.r i) / (P.A k * P.r k)) • P.unitsField i V ((P.r k / P.r i) • y) := by
  funext y
  have hAi := (hP.A_pos i).ne'
  have hri := (hP.r_pos i).ne'
  have hAk := (hP.A_pos k).ne'
  have hrk := (hP.r_pos k).ne'
  have hri' : ((P.r i : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hri
  have harg : ((P.r i : ℝ) : ℂ) * ((P.r k / P.r i : ℝ) • y) = (P.r k : ℂ) * y := by
    rw [Complex.real_smul, Complex.ofReal_div]
    field_simp
  simp only [Approx.unitsField, scaleField]
  rw [harg, Complex.real_smul]
  have h1 : ((P.A i * P.r i : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (mul_ne_zero hAi hri)
  have h2 : ((P.A k * P.r k : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (mul_ne_zero hAk hrk)
  rw [Complex.ofReal_div]
  field_simp

/-- The scaling rule for the change of units. -/
theorem norm_iteratedFDeriv_unitsField_change (P : Approx) (hP : P.Valid) (i k q : ℕ)
    (V : ℂ → ℂ) (y : ℂ) :
    ‖iteratedFDeriv ℝ q (P.unitsField k V) y‖ =
      (P.A i * P.r i) / (P.A k * P.r k) * (P.r k / P.r i) ^ q *
        ‖iteratedFDeriv ℝ q (P.unitsField i V) ((P.r k / P.r i) • y)‖ := by
  have hAi := hP.A_pos i
  have hri := hP.r_pos i
  have hAk := hP.A_pos k
  have hrk := hP.r_pos k
  rw [unitsField_change P hP i k V, iteratedFDeriv_comp_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity)]

/-- `A_k w_k(t, ·/r_k)` in ring-`k` units is `w_k(t)`. -/
theorem unitsVort_wPhys (P : Approx) (hP : P.Valid) (k : ℕ) (t : ℝ) :
    P.unitsVort k (P.wPhys k t) = P.wR k t := by
  funext y
  have hA := (hP.A_pos k).ne'
  have hr : ((P.r k : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hP.r_pos k).ne'
  simp only [Approx.unitsVort, scaleVort, Approx.wPhys]
  rw [inv_mul_cancel_left₀ hr, inv_mul_cancel_left₀ hA]

/-- The field of `A_k w_k(t, ·/r_k)` in ring-`k` units is `K * w_k(t)`. -/
theorem unitsField_velocity_wPhys (P : Approx) (hP : P.Valid) (k : ℕ) (t : ℝ) :
    P.unitsField k (velocity (P.wPhys k t)) = velocity (P.wR k t) := by
  funext y
  have h := (fields_scaleVort (hP.A_pos k) (hP.r_pos k) (P.wPhys k t)).1 y
  have h2 : scaleVort (P.A k) (P.r k) (P.wPhys k t) = P.wR k t := unitsVort_wPhys P hP k t
  rw [h2] at h
  exact h.symm

theorem A_succ' (P : Approx) {j : ℕ} (hj : 1 ≤ j) : P.A (j + 1) = P.μ * P.A j :=
  amp_succ _ _ hj

theorem r_succ' (P : Approx) {j : ℕ} (hj : 1 ≤ j) : P.r (j + 1) = P.s j * P.r j :=
  radius_succ _ _ hj

/-- `A_i / A_k = μ^{i-k}` for `i, k ≥ 1`. -/
theorem A_div_A (P : Approx) (hP : P.Valid) {i k : ℕ} (hi : 1 ≤ i) (hk : 1 ≤ k) :
    P.A i / P.A k = P.μ ^ ((i : ℤ) - k) := by
  have hμ : P.μ ≠ 0 := by linarith [hP.datumParams.one_lt_μ]
  have hA1 : P.A₁ ≠ 0 := hP.datumParams.A₁_pos.ne'
  simp only [Approx.A, amp]
  rw [mul_div_mul_left _ _ hA1, ← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hμ]
  congr 1
  omega

end NonUniqueEuler.Rings.TransferAux
