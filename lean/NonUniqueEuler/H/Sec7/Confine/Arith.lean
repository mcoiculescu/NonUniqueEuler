import Mathlib.Analysis.SpecificLimits.Basic
import NonUniqueEuler.Defs.Sec7.All

/-!
# Helper for `prop:confine`: real-number estimates

Helper of `P/Sec7/Confine.lean` (`07_several_rings.tex:322-349`, `:375-380`).

* `Cstar_pos`: `C_* > 0`;
* `sum_Icc_half_pow_le`: `Σ_{j=1}^k 2^{j-k} ≤ 2` (`07_several_rings.tex:344-345`);
* `ring_term_le`: the per-ring bound of step (b), `07_several_rings.tex:334-343`, in the form
  `μ |K*g_j(x)| ≤ (4/3)(2/a)^3 Λ^2 s_k c A_{k+1} r_{k+1}` with `c = 2^{j-k}`;
* `confRadius_le_Cmom`: `M_vort (2 + 2C_*τ)^3 ≤ C_mom (1 + τ)^3` for `τ ≥ 0` (`:378-380`).
-/

noncomputable section

open Set

namespace NonUniqueEuler.Rings.ConfineH

open RingData Datum

/-- `C_* = (1 + c₄)/(2π) M_vort^{1/2} > 0` (`c₄ = (2π/(2 - 4/3))^{3/4} ≥ 0`). -/
theorem Cstar_pos : 0 < Cstar := by
  have hc : 0 ≤ BS.cLpLinf 4 := by
    unfold BS.cLpLinf
    apply Real.rpow_nonneg
    have h43 : (4 : ℝ).conjExponent = 4 / 3 := by
      unfold Real.conjExponent; norm_num
    rw [h43]
    have := Real.pi_pos
    apply div_nonneg <;> linarith
  unfold Cstar
  have hpi := Real.pi_pos
  have hM := Mvort_pos
  have : 0 < Real.sqrt Mvort := Real.sqrt_pos.mpr hM
  positivity

/-- `Σ_{j=1}^k (1/2)^{k-j} ≤ 2` (`07_several_rings.tex:344-345`). -/
theorem sum_Icc_half_pow_le (k : ℕ) :
    ∑ j ∈ Finset.Icc 1 k, (1 / (2 : ℝ)) ^ (k - j) ≤ 2 := by
  have h : ∑ j ∈ Finset.Icc 1 k, (1 / (2 : ℝ)) ^ (k - j) =
      ∑ i ∈ Finset.range k, (1 / (2 : ℝ)) ^ i := by
    apply Finset.sum_nbij' (fun j => k - j) (fun i => k - i)
    · intro j hj
      simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢
      omega
    · intro i hi
      simp only [Finset.mem_Icc, Finset.mem_range] at hi ⊢
      omega
    · intro j hj
      simp only [Finset.mem_Icc] at hj
      omega
    · intro i hi
      simp only [Finset.mem_range] at hi
      omega
    · intro j _
      rfl
  rw [h]
  exact sum_geometric_two_le k

/-- **The per-ring bound** of `prop:confine`(b) (`07_several_rings.tex:334-343`), as real
arithmetic: from the hollow bound `v ≤ (4/(3π)) L X² R_j^{-3}` with `R_j = (a/2) r_j`,
`L = ‖g_j‖_{L¹} ≤ π A_j r_j²`, `X = |x| ≤ Λ r_{k+1}`, `r_{k+1} ≤ s_k c r_j` and `μ A_j ≤ A_{k+1}`:
`μ v ≤ (4/3)(2/a)³ Λ² s_k c A_{k+1} r_{k+1}`. -/
theorem ring_term_le {v L X rj rk1 Aj Ak1 μ Λ sk c : ℝ} (ha : 0 < a) (hrj : 0 < rj)
    (hrk1 : 0 < rk1) (hAj : 0 ≤ Aj) (hμ : 0 < μ) (_hΛ : 0 ≤ Λ) (_hL0 : 0 ≤ L) (hX0 : 0 ≤ X)
    (hv : v ≤ 4 / (3 * Real.pi) * L * X ^ 2 * ((a / 2 * rj) ^ 3)⁻¹)
    (hL : L ≤ Real.pi * (Aj * rj ^ 2)) (hX : X ≤ Λ * rk1) (hr : rk1 ≤ sk * c * rj)
    (hA : μ * Aj ≤ Ak1) :
    μ * v ≤ 4 / 3 * (2 / a) ^ 3 * Λ ^ 2 * sk * c * (Ak1 * rk1) := by
  have hpi := Real.pi_pos
  have hR : 0 < (a / 2 * rj) ^ 3 := by positivity
  have h1 : v ≤ 4 / (3 * Real.pi) * (Real.pi * (Aj * rj ^ 2)) * (Λ * rk1) ^ 2 *
      ((a / 2 * rj) ^ 3)⁻¹ := by
    refine hv.trans ?_
    have hR' : 0 ≤ ((a / 2 * rj) ^ 3)⁻¹ := (inv_pos.mpr hR).le
    gcongr
  have h2 : 4 / (3 * Real.pi) * (Real.pi * (Aj * rj ^ 2)) * (Λ * rk1) ^ 2 *
      ((a / 2 * rj) ^ 3)⁻¹ = 4 / 3 * (2 / a) ^ 3 * Λ ^ 2 * Aj * rk1 * (rk1 / rj) := by
    field_simp
  have h3 : rk1 / rj ≤ sk * c := by
    rw [div_le_iff₀ hrj]
    exact hr
  have hK : 0 ≤ 4 / 3 * (2 / a) ^ 3 * Λ ^ 2 := by positivity
  calc μ * v ≤ μ * (4 / 3 * (2 / a) ^ 3 * Λ ^ 2 * Aj * rk1 * (rk1 / rj)) := by
        rw [← h2]
        exact mul_le_mul_of_nonneg_left h1 hμ.le
    _ = 4 / 3 * (2 / a) ^ 3 * Λ ^ 2 * (μ * Aj) * rk1 * (rk1 / rj) := by ring
    _ ≤ 4 / 3 * (2 / a) ^ 3 * Λ ^ 2 * Ak1 * rk1 * (sk * c) := by
        have hAk1 : 0 ≤ Ak1 := le_trans (mul_nonneg hμ.le hAj) hA
        have : 0 ≤ rk1 / rj := div_nonneg hrk1.le hrj.le
        gcongr
    _ = 4 / 3 * (2 / a) ^ 3 * Λ ^ 2 * sk * c * (Ak1 * rk1) := by ring

/-- `M_vort (2 + 2C_*τ)³ ≤ C_mom (1 + τ)³` for `τ ≥ 0` (`07_several_rings.tex:378-380`), since
`2 + 2C_*τ ≤ 2 max(1, C_*)(1 + τ)`. -/
theorem Mvort_mul_le_Cmom {τ : ℝ} (hτ : 0 ≤ τ) :
    Mvort * (2 + 2 * Cstar * τ) ^ 3 ≤ Cmom * (1 + τ) ^ 3 := by
  have hC := Cstar_pos
  have h1 : 2 + 2 * Cstar * τ ≤ 2 * max 1 Cstar * (1 + τ) := by
    have hm1 : 1 ≤ max 1 Cstar := le_max_left _ _
    have hm2 : Cstar ≤ max 1 Cstar := le_max_right _ _
    nlinarith
  have h0 : 0 ≤ 2 + 2 * Cstar * τ := by positivity
  have h2 : (2 + 2 * Cstar * τ) ^ 3 ≤ (2 * max 1 Cstar * (1 + τ)) ^ 3 :=
    pow_le_pow_left₀ h0 h1 3
  calc Mvort * (2 + 2 * Cstar * τ) ^ 3 ≤ Mvort * (2 * max 1 Cstar * (1 + τ)) ^ 3 :=
        mul_le_mul_of_nonneg_left h2 Mvort_pos.le
    _ = Cmom * (1 + τ) ^ 3 := by
        rw [Cmom]
        ring

end NonUniqueEuler.Rings.ConfineH
