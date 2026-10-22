import NonUniqueEuler.Defs.Sec2.BiotSavart
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Helper for `lem:ext-multipole`: the series defining `C_{m,q}`

Helper lemmas for `NonUniqueEuler/P/Sec2/ExtMultipole.lean` (`02_prelim.tex:479-482` and the
last sentence of the proof, `02_prelim.tex:508-510`).

Write `T_ρ(j) = (m(j+1)+q)^q ρ^{m(j+1)}`, so that `C_{m,q} = 2^q/(2π) sup_{0<ρ≤1/2} ρ^{-m} Σ_j T_ρ(j)`.
* `summable_extSeries`: `Σ_j T_ρ(j)` converges for `0 ≤ ρ < 1` (comparison with
  `(m+q)^q (j+1)^q (ρ^m)^{j+1}`, `summable_pow_mul_geometric_of_norm_lt_one`);
* `inv_pow_mul_tsum_extSeries_le`: `ρ^{-m} Σ_j T_ρ(j) = Σ_j (m(j+1)+q)^q ρ^{mj}` is bounded by its
  value at `ρ = 1/2` for `0 < ρ ≤ 1/2` (the manuscript's monotonicity in `ρ`; we only need the
  comparison with `ρ = 1/2`);
* `bddAbove_extSeries`, `cExtMultipole_pos`;
* `tsum_extSeries_le`: `Σ_j T_ρ(j) ≤ ρ^m · sup = ρ^m · 2π/2^q · C_{m,q}`, in the form used by the
  bound.
-/

noncomputable section

open Set

namespace NonUniqueEuler.BS.ExtMultipoleAux

/-- The terms `T_ρ(j) = (m(j+1)+q)^q ρ^{m(j+1)}` of the series in `C_{m,q}`. -/
def extTerm (m q : ℕ) (ρ : ℝ) (j : ℕ) : ℝ :=
  (((m * (j + 1) + q : ℕ) : ℝ)) ^ q * ρ ^ (m * (j + 1))

theorem extTerm_nonneg (m q : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) (j : ℕ) : 0 ≤ extTerm m q ρ j := by
  unfold extTerm
  positivity

/-- `(j+1)^q r^{j+1}` is summable for `|r| < 1`. -/
theorem summable_succ_pow_mul_geometric (q : ℕ) {r : ℝ} (hr : ‖r‖ < 1) :
    Summable fun j : ℕ => (((j + 1 : ℕ) : ℝ)) ^ q * r ^ (j + 1) :=
  (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ q * r ^ n) 1).mpr
    (summable_pow_mul_geometric_of_norm_lt_one q hr)

theorem summable_extSeries {m : ℕ} (hm : 1 ≤ m) (q : ℕ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Summable (extTerm m q ρ) := by
  have hr0 : 0 ≤ ρ ^ m := pow_nonneg hρ0 m
  have hr1 : ρ ^ m < 1 := pow_lt_one₀ hρ0 hρ1 (by omega)
  have hs := (summable_succ_pow_mul_geometric q (r := ρ ^ m)
    (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)).mul_left ((((m + q : ℕ) : ℝ)) ^ q)
  refine Summable.of_nonneg_of_le (fun j => extTerm_nonneg m q hρ0 j) (fun j => ?_) hs
  unfold extTerm
  have hnat : m * (j + 1) + q ≤ (m + q) * (j + 1) := by nlinarith
  have hcast : (((m * (j + 1) + q : ℕ) : ℝ)) ≤ ((m + q : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) := by
    rw [← Nat.cast_mul]
    exact_mod_cast hnat
  rw [← pow_mul, ← mul_assoc, ← mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hcast q)
    (pow_nonneg hρ0 _)

/-- `ρ^{-m} T_ρ(j) ≤ 2^m T_{1/2}(j)` for `0 < ρ ≤ 1/2`. -/
theorem inv_pow_mul_extTerm_le (m q : ℕ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2) (j : ℕ) :
    (ρ ^ m)⁻¹ * extTerm m q ρ j ≤ 2 ^ m * extTerm m q (1 / 2) j := by
  unfold extTerm
  have hpm : ρ ^ (m * (j + 1)) = ρ ^ m * ρ ^ (m * j) := by
    rw [← pow_add]; ring_nf
  have hpm' : (1 / 2 : ℝ) ^ (m * (j + 1)) = (1 / 2) ^ m * (1 / 2) ^ (m * j) := by
    rw [← pow_add]; ring_nf
  have hρm : ρ ^ m ≠ 0 := pow_ne_zero _ hρ0.ne'
  rw [hpm, hpm']
  have h1 : (ρ ^ m)⁻¹ * ((((m * (j + 1) + q : ℕ) : ℝ)) ^ q * (ρ ^ m * ρ ^ (m * j))) =
      (((m * (j + 1) + q : ℕ) : ℝ)) ^ q * ρ ^ (m * j) := by
    field_simp
  have h2 : (2 : ℝ) ^ m * ((((m * (j + 1) + q : ℕ) : ℝ)) ^ q *
      ((1 / 2) ^ m * (1 / 2) ^ (m * j))) =
      (((m * (j + 1) + q : ℕ) : ℝ)) ^ q * (1 / 2) ^ (m * j) := by
    rw [one_div, inv_pow]
    field_simp
  rw [h1, h2]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ0.le hρ1 _) (by positivity)

theorem inv_pow_mul_tsum_extSeries_le {m : ℕ} (hm : 1 ≤ m) (q : ℕ) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ ≤ 1 / 2) :
    (ρ ^ m)⁻¹ * ∑' j, extTerm m q ρ j ≤ 2 ^ m * ∑' j, extTerm m q (1 / 2) j := by
  rw [← tsum_mul_left, ← tsum_mul_left]
  exact Summable.tsum_le_tsum (inv_pow_mul_extTerm_le m q hρ0 hρ1)
    ((summable_extSeries hm q hρ0.le (by linarith)).mul_left _)
    ((summable_extSeries hm q (by norm_num) (by norm_num)).mul_left _)

/-- The function under the supremum in `cExtMultipole`. -/
theorem bddAbove_extSeries {m : ℕ} (hm : 1 ≤ m) (q : ℕ) :
    BddAbove (Set.range fun ρ : Ioc (0 : ℝ) (1 / 2) =>
      ((ρ : ℝ) ^ m)⁻¹ * ∑' j : ℕ, (((m * (j + 1) + q : ℕ) : ℝ)) ^ q * (ρ : ℝ) ^ (m * (j + 1))) := by
  refine ⟨2 ^ m * ∑' j, extTerm m q (1 / 2) j, ?_⟩
  rintro _ ⟨ρ, rfl⟩
  exact inv_pow_mul_tsum_extSeries_le hm q ρ.2.1 ρ.2.2

theorem tsum_extSeries_pos {m : ℕ} (hm : 1 ≤ m) (q : ℕ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    0 < ∑' j, extTerm m q ρ j := by
  refine Summable.tsum_pos (summable_extSeries hm q hρ0.le hρ1)
    (fun j => extTerm_nonneg m q hρ0.le j) 0 ?_
  unfold extTerm
  have : (0 : ℝ) < ((m * (0 + 1) + q : ℕ) : ℝ) := by
    have : 0 < m * (0 + 1) + q := by omega
    exact_mod_cast this
  positivity

/-- The supremum in `cExtMultipole m q`. -/
def extSup (m q : ℕ) : ℝ :=
  ⨆ ρ : Ioc (0 : ℝ) (1 / 2),
    ((ρ : ℝ) ^ m)⁻¹ * ∑' j : ℕ, (((m * (j + 1) + q : ℕ) : ℝ)) ^ q * (ρ : ℝ) ^ (m * (j + 1))

theorem cExtMultipole_eq (m q : ℕ) : cExtMultipole m q = 2 ^ q / (2 * Real.pi) * extSup m q :=
  rfl

theorem le_extSup {m : ℕ} (hm : 1 ≤ m) (q : ℕ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2) :
    (ρ ^ m)⁻¹ * ∑' j, extTerm m q ρ j ≤ extSup m q :=
  le_ciSup (f := fun ρ : Ioc (0 : ℝ) (1 / 2) =>
      ((ρ : ℝ) ^ m)⁻¹ * ∑' j : ℕ, (((m * (j + 1) + q : ℕ) : ℝ)) ^ q * (ρ : ℝ) ^ (m * (j + 1)))
    (bddAbove_extSeries hm q) ⟨ρ, hρ0, hρ1⟩

theorem extSup_pos {m : ℕ} (hm : 1 ≤ m) (q : ℕ) : 0 < extSup m q := by
  refine lt_of_lt_of_le ?_ (le_extSup hm q (ρ := 1 / 2) (by norm_num) le_rfl)
  have := tsum_extSeries_pos hm q (ρ := 1 / 2) (by norm_num) (by norm_num)
  positivity

theorem cExtMultipole_pos {m : ℕ} (hm : 1 ≤ m) (q : ℕ) : 0 < cExtMultipole m q := by
  rw [cExtMultipole_eq]
  have := extSup_pos hm q
  have := Real.pi_pos
  positivity

/-- `Σ_j T_ρ(j) ≤ ρ^m · sup` for `0 < ρ ≤ 1/2`. -/
theorem tsum_extSeries_le {m : ℕ} (hm : 1 ≤ m) (q : ℕ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2) :
    ∑' j, extTerm m q ρ j ≤ ρ ^ m * extSup m q := by
  have h := le_extSup hm q hρ0 hρ1
  have hρm : 0 < ρ ^ m := pow_pos hρ0 m
  rw [inv_mul_le_iff₀ hρm] at h
  exact h

end NonUniqueEuler.BS.ExtMultipoleAux
