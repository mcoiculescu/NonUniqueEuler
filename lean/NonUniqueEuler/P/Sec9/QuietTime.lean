import NonUniqueEuler.Defs.Sec9.All
import NonUniqueEuler.I.Sec9.Detuning
import NonUniqueEuler.I.Sec9.Standing
import NonUniqueEuler.I.Sec4.Uniform
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Proof of `lem:quiet-time` (the length of the quiet phase of a ring)

Proof of the interface `I/Sec9/QuietTime.lean` (`09_relay.tex:1496-1554`).

* **Locating `t`** (`09_relay.tex:1512-1523`). We take `i_*` least in `(j, n]` such that for every
  `i ∈ [i_*, n]`, `t♯_i` is defined and `t♯_i ≤ t` (`Nat.find`; `i = n` qualifies since
  `t♯_n = 0 ≤ t`). This variant of the manuscript's `i_*` (least `i` with `t♯_i` defined and
  `t♯_i ≤ t`) avoids the monotonicity of `t♯` and gives the same conclusion: with `k = i_* - 1`,
  the clock is defined up to level `k + 1`, `κ♯_i ≥ K_lo s_i⁵` for `k < i < n`, and `t ≤ t♯_k`
  (by `htj` if `k = j`, by minimality of `i_*` if `k > j`).
* **Unrolling the clock** (`tsh_eq_sum'`): `t♯_k = Σ_{i ∈ (k, n]} (T̂_i + T_pin)/A_i`, from
  `tsh_eq_T_add`, `T_of_ne` and `tsh_n` (pure algebra, no clock condition needed).
* **The three groups** (`09_relay.tex:1525-1547`), with `A_j/A_i = μ^{-(i-j)}` (`A_div_A`):
  pinning `≤ T_pin/(μ-1)`, active phases `≤ σ'⁻¹(log₊(δ₀/K_lo) + 5L)/(μ-1) +
  5σ'⁻¹log(2μ)·μ/(μ-1)²` (`L = log(1/s_j)`, geometric sums `sum_geom_le`, `sum_lin_geom_le`),
  seeded phase `≤ σ'⁻¹(log₊(δ₀/K_lo) + 6L)`; the final real algebra is `final_alg`.
* `K_lo > 0` and `K_lo ≤ K_up` come from `lem:uniform` (`0 < c_N ≤ C_N`) and `|z| ≥ σ > 0`
  (`standing_levels`); `σ_i > σ'` from `lem:detuning`.
* **The bound by `C_τ`** is `bound_alg` (`μ log(2μ) ≤ 3` suffices; the manuscript uses `< 1`).
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

open RingData Datum

namespace QuietTimeAux

/-! ### Generic real lemmas -/

/-- A finite sum `Σ_{i ∈ F} f(i - c)` over indices `i ≥ c` is at most the full sum of a
nonnegative series `f`. -/
theorem sum_comp_sub_le {f : ℕ → ℝ} {a : ℝ} (hf : HasSum f a) (h0 : ∀ m, 0 ≤ f m)
    (F : Finset ℕ) (c : ℕ) (hF : ∀ i ∈ F, c ≤ i) : ∑ i ∈ F, f (i - c) ≤ a := by
  classical
  calc ∑ i ∈ F, f (i - c) = ∑ m ∈ F.image (fun i => i - c), f m :=
        (Finset.sum_image (fun x hx y hy h => by
          have := hF x hx
          have := hF y hy
          have h' : x - c = y - c := h
          omega)).symm
    _ ≤ a := sum_le_hasSum _ (fun i _ => h0 i) hf

/-- `Σ_{i ∈ F} μ^{-(i-j)} ≤ 1/(μ-1)` for indices `i > j` (`Σ_{m ≥ 1} μ^{-m} = 1/(μ-1)`). -/
theorem sum_geom_le {μ : ℝ} (hμ : 1 < μ) (F : Finset ℕ) (j : ℕ) (hF : ∀ i ∈ F, j < i) :
    ∑ i ∈ F, μ⁻¹ ^ (i - j) ≤ 1 / (μ - 1) := by
  have hμ0 : 0 < μ := by linarith
  have hq0 : 0 ≤ μ⁻¹ := by positivity
  have hq1 : μ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hμ
  have hs := (hasSum_geometric_of_lt_one hq0 hq1).mul_left μ⁻¹
  have h := sum_comp_sub_le hs (fun m => by positivity) F (j + 1) (fun i hi => hF i hi)
  have he : μ⁻¹ * (1 - μ⁻¹)⁻¹ = 1 / (μ - 1) := by
    have h1 : (1 : ℝ) - μ⁻¹ = (μ - 1) / μ := by field_simp
    have h2 : μ - 1 ≠ 0 := by linarith
    rw [h1]
    field_simp
  calc ∑ i ∈ F, μ⁻¹ ^ (i - j) = ∑ i ∈ F, μ⁻¹ * μ⁻¹ ^ (i - (j + 1)) :=
        Finset.sum_congr rfl fun i hi => by
          have := hF i hi
          rw [← pow_succ']
          congr 1
          omega
    _ ≤ μ⁻¹ * (1 - μ⁻¹)⁻¹ := h
    _ = 1 / (μ - 1) := he

/-- `Σ_{i ∈ F} (i-j) μ^{-(i-j)} ≤ μ/(μ-1)²` for indices `i ≥ j`
(`Σ_{m ≥ 1} m μ^{-m} = μ/(μ-1)²`). -/
theorem sum_lin_geom_le {μ : ℝ} (hμ : 1 < μ) (F : Finset ℕ) (j : ℕ) (hF : ∀ i ∈ F, j < i) :
    ∑ i ∈ F, ((i - j : ℕ) : ℝ) * μ⁻¹ ^ (i - j) ≤ μ / (μ - 1) ^ 2 := by
  have hμ0 : 0 < μ := by linarith
  have hq1 : ‖μ⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact inv_lt_one_of_one_lt₀ hμ
  have hs := hasSum_coe_mul_geometric_of_norm_lt_one hq1
  have h := sum_comp_sub_le hs (fun m => by positivity) F j (fun i hi => (hF i hi).le)
  have he : μ⁻¹ / (1 - μ⁻¹) ^ 2 = μ / (μ - 1) ^ 2 := by
    have h1 : (1 : ℝ) - μ⁻¹ = (μ - 1) / μ := by field_simp
    have h2 : μ - 1 ≠ 0 := by linarith
    rw [h1]
    field_simp
  exact h.trans he.le

/-- `log(δ/κ) ≤ log c + log₊(δ/K) + 5 log(1/s)` when `K s⁵ ≤ c κ` (all positive). -/
theorem log_div_le {δ κ K s c : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (hK : 0 < K) (hs : 0 < s)
    (hc : 0 < c) (h : K * s ^ (3 + 2) ≤ c * κ) :
    Real.log (δ / κ) ≤ Real.log c + Real.posLog (δ / K) + (3 + 2) * Real.log (1 / s) := by
  have hKs : 0 < K * s ^ (3 + 2) := by positivity
  have h1 : δ / κ ≤ c * (δ / K) * (1 / s) ^ (3 + 2) := by
    rw [div_le_iff₀ hκ]
    have e : c * (δ / K) * (1 / s) ^ (3 + 2) * κ = δ * (c * κ) / (K * s ^ (3 + 2)) := by
      rw [one_div, inv_pow]
      field_simp
    rw [e, le_div_iff₀ hKs]
    exact mul_le_mul_of_nonneg_left h hδ.le
  have hlog : Real.log (δ / K) ≤ Real.posLog (δ / K) := by
    rw [Real.posLog_apply]
    exact le_max_right _ _
  calc Real.log (δ / κ) ≤ Real.log (c * (δ / K) * (1 / s) ^ (3 + 2)) :=
        Real.log_le_log (by positivity) h1
    _ = Real.log c + Real.log (δ / K) + (3 + 2) * Real.log (1 / s) := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
          (by positivity), Real.log_pow]
        push_cast
        ring
    _ ≤ Real.log c + Real.posLog (δ / K) + (3 + 2) * Real.log (1 / s) := by linarith

/-- `σ⁻¹ log(δ/κ) ≤ σ'⁻¹ log(δ/κ)` when `0 < σ' ≤ σ` and `κ ∈ (0, δ)`. -/
theorem inv_mul_log_le {σ σ' δ κ : ℝ} (hσ' : 0 < σ') (hσ : σ' ≤ σ) (hκ : 0 < κ)
    (hκδ : κ < δ) : σ⁻¹ * Real.log (δ / κ) ≤ σ'⁻¹ * Real.log (δ / κ) := by
  have hl : 0 ≤ Real.log (δ / κ) := Real.log_nonneg (by rw [le_div_iff₀ hκ]; linarith)
  exact mul_le_mul_of_nonneg_right (inv_anti₀ hσ' hσ) hl

/-- `σ⁻¹ log(δ/κ) ≥ 0` when `σ > 0` and `κ ∈ (0, δ)`. -/
theorem inv_mul_log_nonneg {σ δ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hκδ : κ < δ) :
    0 ≤ σ⁻¹ * Real.log (δ / κ) :=
  mul_nonneg (inv_nonneg.2 hσ.le) (Real.log_nonneg (by rw [le_div_iff₀ hκ]; linarith))

/-- The final real algebra of `lem:quiet-time` (`09_relay.tex:1544-1547`), with `e = μ - 1`. -/
theorem final_alg {e σ' Tp Pl L lg μ X Y Z : ℝ} (he : 0 < e) (he1 : e ≤ 1) (hσ' : 0 < σ')
    (hT : 0 ≤ Tp) (hP : 0 ≤ Pl) (hL : 0 ≤ L)
    (hX : X ≤ σ'⁻¹ * (Pl + 5 * L) * (1 / e) + σ'⁻¹ * (5 * lg) * (μ / e ^ 2))
    (hY : Y ≤ σ'⁻¹ * (Pl + 6 * L)) (hZ : Z ≤ 1 / e) :
    X + Y + Tp * Z ≤ (3 * (Tp + 1 + σ'⁻¹ * Pl) + (2 * 3 + 5) * σ'⁻¹ * L) / e +
      (3 + 2) * μ * lg / (σ' * e ^ 2) := by
  have ha : 0 < σ'⁻¹ := inv_pos.2 hσ'
  have hYn : 0 ≤ σ'⁻¹ * (Pl + 6 * L) := by positivity
  have h1 : σ'⁻¹ * (Pl + 6 * L) ≤ σ'⁻¹ * (Pl + 6 * L) / e := le_div_self hYn he he1
  have h2 : Tp * Z ≤ Tp * (1 / e) := mul_le_mul_of_nonneg_left hZ hT
  have h3 : (3 + 2) * μ * lg / (σ' * e ^ 2) = σ'⁻¹ * (5 * lg) * (μ / e ^ 2) := by ring
  have h4 : σ'⁻¹ * (Pl + 5 * L) * (1 / e) + σ'⁻¹ * (Pl + 6 * L) / e + Tp * (1 / e) =
      (Tp + σ'⁻¹ * (Pl + 5 * L) + σ'⁻¹ * (Pl + 6 * L)) / e := by ring
  have h5 : (Tp + σ'⁻¹ * (Pl + 5 * L) + σ'⁻¹ * (Pl + 6 * L)) / e ≤
      (3 * (Tp + 1 + σ'⁻¹ * Pl) + (2 * 3 + 5) * σ'⁻¹ * L) / e := by
    apply div_le_div_of_nonneg_right _ he.le
    nlinarith [mul_nonneg ha.le hP, mul_nonneg ha.le hL]
  rw [h3]
  linarith

/-- The real algebra of the bound `τ̄♯_j ≤ C_τ[T_z + L + (μ-1)⁻¹]/(μ-1)`
(`09_relay.tex:1549-1553`), with `e = μ - 1`, `lg = log(2μ)`. -/
theorem bound_alg {e σ' Tz L lg μ C : ℝ} (he : 0 < e) (hσ' : 0 < σ') (hTz : 0 ≤ Tz)
    (hL : 0 ≤ L) (hμlg : μ * lg ≤ 3) (hC3 : 3 ≤ C) (hC11 : (2 * 3 + 5) / σ' ≤ C)
    (hC15 : 3 * (3 + 2) / σ' ≤ C) :
    (3 * Tz + (2 * 3 + 5) * σ'⁻¹ * L) / e + (3 + 2) * μ * lg / (σ' * e ^ 2) ≤
      C * (Tz + L + 1 / e) / e := by
  have h1 : 3 * Tz ≤ C * Tz := mul_le_mul_of_nonneg_right hC3 hTz
  have h2 : (2 * 3 + 5) * σ'⁻¹ * L ≤ C * L := by
    apply mul_le_mul_of_nonneg_right _ hL
    rwa [← div_eq_mul_inv]
  have h3 : (3 + 2) * μ * lg / σ' ≤ C := by
    calc (3 + 2) * μ * lg / σ' = 5 * (μ * lg) / σ' := by ring
      _ ≤ 5 * 3 / σ' := by gcongr
      _ = 3 * (3 + 2) / σ' := by ring
      _ ≤ C := hC15
  have eq1 : (3 + 2) * μ * lg / (σ' * e ^ 2) = ((3 + 2) * μ * lg / σ') / e ^ 2 := by
    rw [div_div]
  have eq2 : C * (Tz + L + 1 / e) / e = (C * Tz + C * L) / e + C / e ^ 2 := by
    field_simp
  rw [eq1, eq2]
  gcongr

/-! ### The clock -/

/-- Unrolling the clock: `t♯_{n-d} = Σ_{i ∈ (n-d, n]} (T̂_i + T_pin)/A_i` (`def:clock`,
`06_datum.tex:404-409`; no clock condition is needed for the formulas). -/
theorem tsh_eq_sum (P : Approx) : ∀ d, d ≤ P.n →
    P.tsh (P.n - d) = ∑ i ∈ Finset.Ioc (P.n - d) P.n, (P.That i + P.Tpin) / P.A i
  | 0, _ => by simp [Approx.tsh_n]
  | d + 1, hd => by
    have hk : P.n - (d + 1) < P.n := by omega
    have h1 : P.n - (d + 1) + 1 = P.n - d := by omega
    rw [P.tsh_eq_T_add hk, h1, P.T_of_ne (by omega : P.n - d ≠ P.n + 1),
      tsh_eq_sum P d (by omega),
      ← Finset.sum_Ioc_consecutive _ (show P.n - (d + 1) ≤ P.n - d by omega)
        (show P.n - d ≤ P.n by omega)]
    rw [show Finset.Ioc (P.n - (d + 1)) (P.n - d) = {P.n - d} by
      rw [← h1]
      exact Nat.Ioc_succ_singleton _]
    rw [Finset.sum_singleton]
    ring

/-- `t♯_k = Σ_{i ∈ (k, n]} (T̂_i + T_pin)/A_i` for `k ≤ n`. -/
theorem tsh_eq_sum' (P : Approx) {k : ℕ} (hk : k ≤ P.n) :
    P.tsh k = ∑ i ∈ Finset.Ioc k P.n, (P.That i + P.Tpin) / P.A i := by
  have h := tsh_eq_sum P (P.n - k) (Nat.sub_le _ _)
  rwa [Nat.sub_sub_self hk] at h

/-- `A_j/A_i = μ^{-(i-j)}` for `1 ≤ j ≤ i`. -/
theorem A_div_A (P : Approx) (hA : 0 < P.A₁) (hμ : 0 < P.μ) {j i : ℕ} (hj : 1 ≤ j)
    (hji : j ≤ i) : P.A j / P.A i = P.μ⁻¹ ^ (i - j) := by
  have hA' := hA.ne'
  have hμ' := hμ.ne'
  simp only [Approx.A, amp]
  have e : i - 1 = (j - 1) + (i - j) := by omega
  rw [e, pow_add, inv_pow]
  field_simp

/-- `log(1/s_i) = log(1/s_j) + (i-j) log(2μ)` for `j ≤ i`. -/
theorem log_inv_s (P : Approx) (hs : 0 < P.sbar) (hμ : 0 < P.μ) {j i : ℕ} (hji : j ≤ i) :
    Real.log (1 / P.s i) = Real.log (1 / P.s j) + ((i - j : ℕ) : ℝ) * Real.log (2 * P.μ) := by
  have h2 : 0 < 2 * P.μ := by linarith
  have key : ∀ k : ℕ, Real.log (1 / P.s k) = k * Real.log (2 * P.μ) - Real.log P.sbar := by
    intro k
    simp only [Approx.s, ratio, one_div_div]
    rw [Real.log_div (pow_pos h2 k).ne' hs.ne', Real.log_pow]
  rw [key, key, Nat.cast_sub hji]
  ring

/-! ### Constants -/

/-- `|z| > 0` (`|z| ≥ Re z = σ ≥ σ_b > 0`, `standing_levels`). -/
theorem norm_z_pos (S : Standing) (hS : S.Holds) : 0 < ‖S.z‖ := by
  obtain ⟨hb, hbσ, -⟩ := standing_levels S hS
  have h : S.sigma0 ≤ ‖S.z‖ := Complex.re_le_norm _
  rw [Standing.sigb_def] at hb
  rw [Standing.sigb_def] at hbσ
  linarith

/-- `0 < c_N ≤ C_N` (`lem:uniform`). -/
theorem cN_pos_le_CN (S : Standing) (hS : S.Holds) :
    0 < Eig.cN S.P.χ ∧ Eig.cN S.P.χ ≤ Eig.CN S.P.χ := by
  obtain ⟨-, -, -, -, -, -, hc, -, hG⟩ := Eig.uniform_constants S.P.χ hS.admissible hS.hN
  have h0 : (0 : ℝ) ∈ Icc 0 Gbar := ⟨le_rfl, by unfold Gbar; positivity⟩
  obtain ⟨h1, h2, -⟩ := hG 0 h0
  exact ⟨hc, h1.trans h2⟩

/-- `K_lo > 0`. -/
theorem Klo_pos (S : Standing) (hS : S.Holds) : 0 < S.Klo := by
  have h1 := (cN_pos_le_CN S hS).1
  have h2 := norm_z_pos S hS
  have h3 := hS.δ₀_pos
  have h4 := hS.one_lt_μ
  rw [Standing.Klo_def]
  apply div_pos (mul_pos h1 h3)
  exact mul_pos (mul_pos (by norm_num) h2) (by linarith)

/-- `K_lo ≤ K_up` (`c_N ≤ C_N` and `1/22 ≤ 5μ e^{17σT_pin/16}`, `09_relay.tex:1537-1538`). -/
theorem Klo_le_Kup (S : Standing) (hS : S.Holds) : S.Klo ≤ S.Kup := by
  obtain ⟨hc, hcC⟩ := cN_pos_le_CN S hS
  have hz := norm_z_pos S hS
  have hδ := hS.δ₀_pos
  have hμ := hS.one_lt_μ
  have hT := hS.Tpin_pos
  obtain ⟨hb, hbσ, -⟩ := standing_levels S hS
  have hσ : 0 ≤ S.sigma0 := by linarith
  have hE : 1 ≤ Real.exp (17 * S.sigma0 * S.P.Tpin / 16) := Real.one_le_exp (by positivity)
  have hD : 0 < ‖S.z‖ * (S.P.μ - 1) := mul_pos hz (by linarith)
  have hCN : 0 ≤ Eig.CN S.P.χ * S.P.δ₀ := mul_nonneg (hc.le.trans hcC) hδ.le
  have hnum : Eig.cN S.P.χ * S.P.δ₀ / 22 ≤
      5 * Eig.CN S.P.χ * S.P.δ₀ * S.P.μ * Real.exp (17 * S.sigma0 * S.P.Tpin / 16) := by
    have e1 : Eig.cN S.P.χ * S.P.δ₀ / 22 ≤ Eig.CN S.P.χ * S.P.δ₀ := by
      have := mul_le_mul_of_nonneg_right hcC hδ.le
      have := mul_pos hc hδ
      linarith
    have e2 : 1 ≤ 5 * S.P.μ * Real.exp (17 * S.sigma0 * S.P.Tpin / 16) := by nlinarith
    calc Eig.cN S.P.χ * S.P.δ₀ / 22 ≤ Eig.CN S.P.χ * S.P.δ₀ := e1
      _ ≤ Eig.CN S.P.χ * S.P.δ₀ * (5 * S.P.μ * Real.exp (17 * S.sigma0 * S.P.Tpin / 16)) :=
          le_mul_of_one_le_right hCN e2
      _ = _ := by ring
  calc S.Klo = Eig.cN S.P.χ * S.P.δ₀ / 22 / (‖S.z‖ * (S.P.μ - 1)) := by
        rw [Standing.Klo_def, div_div, mul_assoc]
    _ ≤ 5 * Eig.CN S.P.χ * S.P.δ₀ * S.P.μ * Real.exp (17 * S.sigma0 * S.P.Tpin / 16) /
          (‖S.z‖ * (S.P.μ - 1)) := div_le_div_of_nonneg_right hnum hD.le
    _ = S.Kup := by rw [Standing.Kup_def]; ring

end QuietTimeAux

open QuietTimeAux

/-! ### The core estimate -/

/-- **The core of `lem:quiet-time`** (`09_relay.tex:1524-1547`): if `j ≤ k < n`, the clock is
defined up to level `k + 1`, `κ♯_i ≥ K_lo s_i⁵` for `k < i < n` and `κ♯_n ≥ ½κ_seed`, then
`A_j t♯_k ≤ τ̄♯_j`. -/
theorem QuietTimeAux.core (S : Standing) (hS : S.Holds) (hDet : S.Det)
    (hK : S.Kup * S.P.sbar ^ (3 + 2) ≤ S.P.κs) {j k : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k)
    (hkn : k < S.P.n) (hc : S.P.ClockUpTo (k + 1))
    (hκ : ∀ i ∈ Finset.Ioo k S.P.n, S.Klo * S.P.s i ^ (3 + 2) ≤ S.P.ksh i)
    (hκn : 1 / 2 * S.P.κs ≤ S.P.ksh S.P.n) :
    S.P.A j * S.P.tsh k ≤ S.tauBarSh j := by
  -- basic facts
  have hμ1 : 1 < S.P.μ := hS.one_lt_μ
  have hμle : S.P.μ ≤ 17 / 16 := hS.μ_le
  have hμ0 : 0 < S.P.μ := by linarith
  have hA₁ : 0 < S.P.A₁ := hS.valid.datumParams.A₁_pos
  have hsb : 0 < S.P.sbar := hS.sbar_pos
  have hδ : 0 < S.P.δ₀ := hS.δ₀_pos
  have hTp : 0 < S.P.Tpin := hS.Tpin_pos
  have hσ' : 0 < S.σ' := by linarith [hS.σ'_gt]
  have hKlo : 0 < S.Klo := Klo_pos S hS
  have hKK : S.Klo ≤ S.Kup := Klo_le_Kup S hS
  obtain ⟨-, -, hlev⟩ := detuning S hS hDet
  have hσi : ∀ i, 1 ≤ i → i ≤ S.P.n → S.σ' ≤ S.P.sigma i := fun i h1 h2 => by
    obtain ⟨-, h15, hlt, -⟩ := hlev i (Finset.mem_Icc.2 ⟨h1, h2⟩)
    linarith
  -- the ratio `s_j` and `L = log(1/s_j)`
  have hsj : 0 < S.P.s j := ratio_pos hsb hμ0 j
  have hsj_le : S.P.s j ≤ S.P.sbar := by
    simp only [Approx.s, ratio]
    exact div_le_self hsb.le (one_le_pow₀ (by linarith))
  have hsb_le : S.P.sbar ≤ a / 16 := hS.sbar_le
  have ha1 := a_lt_one
  have hL2 : Real.log 2 ≤ Real.log (1 / S.P.s j) :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hsj]; linarith)
  have hLsb : Real.log (1 / S.P.sbar) ≤ Real.log (1 / S.P.s j) :=
    Real.log_le_log (by positivity) (one_div_le_one_div_of_le hsj hsj_le)
  have hL0 : 0 ≤ Real.log (1 / S.P.s j) :=
    le_trans (Real.log_nonneg (by norm_num)) hL2
  have hPl : 0 ≤ Real.posLog (S.P.δ₀ / S.Klo) := Real.posLog_nonneg
  have hlg : 0 ≤ Real.log (2 * S.P.μ) := Real.log_nonneg (by linarith)
  -- unrolling the clock
  have hsum : S.P.A j * S.P.tsh k =
      ∑ i ∈ Finset.Ioc k S.P.n, (S.P.That i + S.P.Tpin) * S.P.μ⁻¹ ^ (i - j) := by
    rw [tsh_eq_sum' S.P hkn.le, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_Ioc.1 hi
    rw [← A_div_A S.P hA₁ hμ0 hj (by omega)]
    ring
  have hsplit : ∑ i ∈ Finset.Ioc k S.P.n, (S.P.That i + S.P.Tpin) * S.P.μ⁻¹ ^ (i - j) =
      ∑ i ∈ Finset.Ioo k S.P.n, S.P.That i * S.P.μ⁻¹ ^ (i - j) +
        S.P.That S.P.n * S.P.μ⁻¹ ^ (S.P.n - j) +
        S.P.Tpin * ∑ i ∈ Finset.Ioc k S.P.n, S.P.μ⁻¹ ^ (i - j) := by
    have e1 : ∑ i ∈ Finset.Ioc k S.P.n, (S.P.That i + S.P.Tpin) * S.P.μ⁻¹ ^ (i - j) =
        ∑ i ∈ Finset.Ioc k S.P.n, S.P.That i * S.P.μ⁻¹ ^ (i - j) +
          S.P.Tpin * ∑ i ∈ Finset.Ioc k S.P.n, S.P.μ⁻¹ ^ (i - j) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have e2 : ∑ i ∈ Finset.Ioc k S.P.n, S.P.That i * S.P.μ⁻¹ ^ (i - j) =
        ∑ i ∈ Finset.Ioo k S.P.n, S.P.That i * S.P.μ⁻¹ ^ (i - j) +
          S.P.That S.P.n * S.P.μ⁻¹ ^ (S.P.n - j) := by
      rw [← Finset.Ioo_insert_right hkn, Finset.sum_insert (by simp), add_comm]
    rw [e1, e2]
  -- the pinning terms
  have hpin : ∑ i ∈ Finset.Ioc k S.P.n, S.P.μ⁻¹ ^ (i - j) ≤ 1 / (S.P.μ - 1) :=
    sum_geom_le hμ1 _ j fun i hi => by
      have := Finset.mem_Ioc.1 hi
      omega
  -- the active phases `k < i < n`
  have hact : ∑ i ∈ Finset.Ioo k S.P.n, S.P.That i * S.P.μ⁻¹ ^ (i - j) ≤
      S.σ'⁻¹ * (Real.posLog (S.P.δ₀ / S.Klo) + 5 * Real.log (1 / S.P.s j)) *
          (1 / (S.P.μ - 1)) +
        S.σ'⁻¹ * (5 * Real.log (2 * S.P.μ)) * (S.P.μ / (S.P.μ - 1) ^ 2) := by
    have hF : ∀ i ∈ Finset.Ioo k S.P.n, j < i := fun i hi => by
      have := Finset.mem_Ioo.1 hi
      omega
    calc ∑ i ∈ Finset.Ioo k S.P.n, S.P.That i * S.P.μ⁻¹ ^ (i - j)
        ≤ ∑ i ∈ Finset.Ioo k S.P.n,
            (S.σ'⁻¹ * (Real.posLog (S.P.δ₀ / S.Klo) + 5 * Real.log (1 / S.P.s j)) *
                S.P.μ⁻¹ ^ (i - j) +
              S.σ'⁻¹ * (5 * Real.log (2 * S.P.μ)) *
                (((i - j : ℕ) : ℝ) * S.P.μ⁻¹ ^ (i - j))) := by
          apply Finset.sum_le_sum
          intro i hi
          have hi' := Finset.mem_Ioo.1 hi
          have hmem := hc.ksh_mem (by omega : k + 1 ≤ i) hi'.2.le
          have hsi : 0 < S.P.s i := ratio_pos hsb hμ0 i
          have hT1 : S.P.That i ≤ S.σ'⁻¹ * Real.log (S.P.δ₀ / S.P.ksh i) :=
            inv_mul_log_le hσ' (hσi i (by omega) hi'.2.le) hmem.1 hmem.2
          have hT2 := log_div_le hδ hmem.1 hKlo hsi one_pos
            (by rw [one_mul]; exact hκ i hi)
          rw [Real.log_one, log_inv_s S.P hsb hμ0 (by omega : j ≤ i)] at hT2
          have hT3 : S.P.That i ≤ S.σ'⁻¹ * (Real.posLog (S.P.δ₀ / S.Klo) +
              5 * Real.log (1 / S.P.s j)) +
              S.σ'⁻¹ * (5 * Real.log (2 * S.P.μ)) * ((i - j : ℕ) : ℝ) := by
            have hinv : 0 ≤ S.σ'⁻¹ := (inv_pos.2 hσ').le
            have := mul_le_mul_of_nonneg_left hT2 hinv
            nlinarith
          have hq : 0 ≤ S.P.μ⁻¹ ^ (i - j) := by positivity
          calc S.P.That i * S.P.μ⁻¹ ^ (i - j)
              ≤ (S.σ'⁻¹ * (Real.posLog (S.P.δ₀ / S.Klo) + 5 * Real.log (1 / S.P.s j)) +
                  S.σ'⁻¹ * (5 * Real.log (2 * S.P.μ)) * ((i - j : ℕ) : ℝ)) *
                  S.P.μ⁻¹ ^ (i - j) := mul_le_mul_of_nonneg_right hT3 hq
            _ = _ := by ring
      _ = S.σ'⁻¹ * (Real.posLog (S.P.δ₀ / S.Klo) + 5 * Real.log (1 / S.P.s j)) *
              ∑ i ∈ Finset.Ioo k S.P.n, S.P.μ⁻¹ ^ (i - j) +
            S.σ'⁻¹ * (5 * Real.log (2 * S.P.μ)) *
              ∑ i ∈ Finset.Ioo k S.P.n, ((i - j : ℕ) : ℝ) * S.P.μ⁻¹ ^ (i - j) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ _ := by
          have hB : 0 ≤ S.σ'⁻¹ * (Real.posLog (S.P.δ₀ / S.Klo) + 5 * Real.log (1 / S.P.s j)) := by
            positivity
          have hD : 0 ≤ S.σ'⁻¹ * (5 * Real.log (2 * S.P.μ)) := by positivity
          exact add_le_add (mul_le_mul_of_nonneg_left (sum_geom_le hμ1 _ j hF) hB)
            (mul_le_mul_of_nonneg_left (sum_lin_geom_le hμ1 _ j hF) hD)
  -- the seeded phase `i = n`
  have hseed : S.P.That S.P.n * S.P.μ⁻¹ ^ (S.P.n - j) ≤
      S.σ'⁻¹ * (Real.posLog (S.P.δ₀ / S.Klo) + 6 * Real.log (1 / S.P.s j)) := by
    have hmem := hc.ksh_mem (by omega : k + 1 ≤ S.P.n) le_rfl
    have hσn : S.σ' ≤ S.P.sigma S.P.n := hσi S.P.n (by omega) le_rfl
    have hκ2 : S.Klo * S.P.sbar ^ (3 + 2) ≤ 2 * S.P.ksh S.P.n := by
      have := mul_le_mul_of_nonneg_right hKK (by positivity : (0 : ℝ) ≤ S.P.sbar ^ (3 + 2))
      linarith
    have hT1 : S.P.That S.P.n ≤ S.σ'⁻¹ * Real.log (S.P.δ₀ / S.P.ksh S.P.n) :=
      inv_mul_log_le hσ' hσn hmem.1 hmem.2
    have hT0 : 0 ≤ S.P.That S.P.n := inv_mul_log_nonneg (hσ'.trans_le hσn) hmem.1 hmem.2
    have hT2 := log_div_le hδ hmem.1 hKlo hsb two_pos hκ2
    have hT3 : Real.log (S.P.δ₀ / S.P.ksh S.P.n) ≤
        Real.posLog (S.P.δ₀ / S.Klo) + 6 * Real.log (1 / S.P.s j) := by
      linarith
    have hq : S.P.μ⁻¹ ^ (S.P.n - j) ≤ 1 :=
      pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hμ1.le)
    calc S.P.That S.P.n * S.P.μ⁻¹ ^ (S.P.n - j) ≤ S.P.That S.P.n :=
          mul_le_of_le_one_right hT0 hq
      _ ≤ S.σ'⁻¹ * Real.log (S.P.δ₀ / S.P.ksh S.P.n) := hT1
      _ ≤ _ := mul_le_mul_of_nonneg_left hT3 (inv_pos.2 hσ').le
  -- assembling
  rw [hsum, hsplit, Standing.tauBarSh_def, Standing.Tz_def]
  exact final_alg (by linarith) (by linarith) hσ' hTp.le hPl hL0 hact hseed hpin

/-! ### `lem:quiet-time` -/

/-- **`lem:quiet-time`, main part** (`09_relay.tex:1496-1507`). Assume (SA), (Det),
`K_up s̄⁵ ≤ κ_seed`, `1 ≤ j < n`, `t ≥ 0`; for every `i ∈ (j, n]` with `t♯_i` defined and
`t♯_i ≤ t`, the clock is defined up to level `i` and `κ♯_i ≥ K_lo s_i⁵` if `i < n`; `t ≤ t♯_j` if
`t♯_j` is defined; and `κ♯_n ≥ ½κ_seed`. Then `A_jt ≤ τ̄♯_j`. -/
theorem quiet_time (S : Standing) (hS : S.Holds) (hDet : S.Det)
    (hK : S.Kup * S.P.sbar ^ (3 + 2) ≤ S.P.κs) {j : ℕ} (hj : 1 ≤ j) (hjn : j < S.P.n) {t : ℝ}
    (ht : 0 ≤ t)
    (hcl : ∀ i ∈ Finset.Ioc j S.P.n, S.P.ClockUpTo (i + 1) → S.P.tsh i ≤ t →
      S.P.ClockUpTo i ∧ (i < S.P.n → S.Klo * S.P.s i ^ (3 + 2) ≤ S.P.ksh i))
    (htj : S.P.ClockUpTo (j + 1) → t ≤ S.P.tsh j) (hκn : 1 / 2 * S.P.κs ≤ S.P.ksh S.P.n) :
    S.P.A j * t ≤ S.tauBarSh j := by
  classical
  -- `Q i`: for every `i' ∈ [i, n]`, `t♯_{i'}` is defined and `t♯_{i'} ≤ t`
  have hQn : ∀ i' ∈ Finset.Icc S.P.n S.P.n, S.P.ClockUpTo (i' + 1) ∧ S.P.tsh i' ≤ t := by
    intro i' hi'
    have e : i' = S.P.n := by
      have := Finset.mem_Icc.1 hi'
      omega
    rw [e, S.P.tsh_n]
    exact ⟨S.P.clockUpTo_succ_n, ht⟩
  have hex : ∃ i, j < i ∧
      ∀ i' ∈ Finset.Icc i S.P.n, S.P.ClockUpTo (i' + 1) ∧ S.P.tsh i' ≤ t :=
    ⟨S.P.n, hjn, hQn⟩
  obtain ⟨hjs, hQs⟩ := Nat.find_spec hex
  have hsn : Nat.find hex ≤ S.P.n := Nat.find_min' hex ⟨hjn, hQn⟩
  have hfacts : ∀ i ∈ Finset.Icc (Nat.find hex) S.P.n,
      S.P.ClockUpTo i ∧ (i < S.P.n → S.Klo * S.P.s i ^ (3 + 2) ≤ S.P.ksh i) := fun i hi =>
    hcl i (by
      have := Finset.mem_Icc.1 hi
      exact Finset.mem_Ioc.2 ⟨by omega, this.2⟩) (hQs i hi).1 (hQs i hi).2
  have hclock : S.P.ClockUpTo (Nat.find hex) :=
    (hfacts _ (Finset.mem_Icc.2 ⟨le_rfl, hsn⟩)).1
  obtain ⟨k, hk1⟩ : ∃ k, k + 1 = Nat.find hex := ⟨Nat.find hex - 1, by omega⟩
  have hclock' : S.P.ClockUpTo (k + 1) := by rw [hk1]; exact hclock
  -- `t ≤ t♯_k`
  have htk : t ≤ S.P.tsh k := by
    rcases Nat.lt_or_ge j k with hjk | hjk
    · have hmin := Nat.find_min hex (show k < Nat.find hex by omega)
      by_contra hlt
      replace hlt := not_le.1 hlt
      apply hmin
      refine ⟨hjk, fun i' hi' => ?_⟩
      have hi'' := Finset.mem_Icc.1 hi'
      rcases eq_or_lt_of_le hi''.1 with h | h
      · rw [← h]
        exact ⟨hclock', hlt.le⟩
      · exact hQs i' (Finset.mem_Icc.2 ⟨by omega, hi''.2⟩)
    · have e : k = j := by omega
      rw [e] at hclock' ⊢
      exact htj hclock'
  have hAj : 0 < S.P.A j := amp_pos hS.valid.datumParams.A₁_pos (by linarith [hS.one_lt_μ]) j
  calc S.P.A j * t ≤ S.P.A j * S.P.tsh k := mul_le_mul_of_nonneg_left htk hAj.le
    _ ≤ S.tauBarSh j :=
      QuietTimeAux.core S hS hDet hK hj (by omega) (by omega) hclock' (fun i hi => by
        have hi' := Finset.mem_Ioo.1 hi
        exact (hfacts i (Finset.mem_Icc.2 ⟨by omega, hi'.2.le⟩)).2 hi'.2) hκn

/-- **`lem:quiet-time`, the bound on `τ̄♯_j`** (`09_relay.tex:1507-1509`, proof `:1549-1553`):
under (SA), for `1 ≤ j < n`, `τ̄♯_j ≤ C_τ[T_z + log(1/s_j) + (μ-1)⁻¹]/(μ-1)`. -/
theorem quiet_time_bound (S : Standing) (hS : S.Holds) {j : ℕ} (hj : 1 ≤ j) (hjn : j < S.P.n) :
    S.tauBarSh j ≤
      S.Ctau * (S.Tz + Real.log (1 / S.P.s j) + 1 / (S.P.μ - 1)) / (S.P.μ - 1) := by
  have hμ1 : 1 < S.P.μ := hS.one_lt_μ
  have hμle : S.P.μ ≤ 17 / 16 := hS.μ_le
  have hμ0 : 0 < S.P.μ := by linarith
  have hsb : 0 < S.P.sbar := hS.sbar_pos
  have hσ' : 0 < S.σ' := by linarith [hS.σ'_gt]
  have hsj : 0 < S.P.s j := ratio_pos hsb hμ0 j
  have hsj_le : S.P.s j ≤ S.P.sbar := by
    simp only [Approx.s, ratio]
    exact div_le_self hsb.le (one_le_pow₀ (by linarith))
  have hsb_le : S.P.sbar ≤ a / 16 := hS.sbar_le
  have ha1 := a_lt_one
  have hL0 : 0 ≤ Real.log (1 / S.P.s j) :=
    Real.log_nonneg (by rw [le_div_iff₀ hsj]; linarith)
  have hTz : 0 ≤ S.Tz := by
    rw [Standing.Tz_def]
    have := hS.Tpin_pos
    have : 0 ≤ S.σ'⁻¹ * Real.posLog (S.P.δ₀ / S.Klo) :=
      mul_nonneg (inv_pos.2 hσ').le Real.posLog_nonneg
    linarith
  have hμlg : S.P.μ * Real.log (2 * S.P.μ) ≤ 3 := by
    have h1 : Real.log (2 * S.P.μ) ≤ 2 * S.P.μ - 1 := Real.log_le_sub_one_of_pos (by linarith)
    have h0 : 0 ≤ Real.log (2 * S.P.μ) := Real.log_nonneg (by linarith)
    nlinarith
  have hC11 : (2 * 3 + 5) / S.σ' ≤ S.Ctau := le_max_of_le_right (le_max_left _ _)
  have hC15 : 3 * (3 + 2) / S.σ' ≤ S.Ctau := le_max_of_le_right (le_max_right _ _)
  rw [Standing.tauBarSh_def]
  exact bound_alg (by linarith) hσ' hTz hL0 hμlg S.three_le_Ctau hC11 hC15

end Relay

end NonUniqueEuler
