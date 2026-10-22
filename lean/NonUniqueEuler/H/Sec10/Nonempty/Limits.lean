import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt
import NonUniqueEuler.Defs.Sec2.Conventions

/-!
# Helper for `lem:nonempty`: elementary limits at `0⁺` and at `+∞`

Helper of `P/Sec10/Nonempty.lean` (`10_parameters.tex:292-375`). The proof of `lem:nonempty` uses
only that finitely many explicit functions tend to `0`:
* `x^γ ⟨log(1/x)⟩^N → 0`, `x^γ (α + β log(1/x))^N → 0` as `x → 0⁺` (`γ > 0`, `N ∈ ℕ`);
* `(1 + T)^3 e^{-bT} → 0` as `T → ∞` (`b > 0`; `r_T(T) → 0` in (P3));
* the passage from `∀ᶠ x in 𝓝[>] 0` to "for every `x ∈ (0, x₀]`".

All lemmas are fully proved. Namespace `NonUniqueEuler.Relay.NonemptyH`.
-/

noncomputable section

open Set Filter Topology

namespace NonUniqueEuler

namespace Relay

namespace NonemptyH

/-- `(1 + y)^N e^{-γ y} → 0` as `y → ∞` (`γ > 0`). -/
theorem tendsto_one_add_pow_mul_exp_neg {γ : ℝ} (hγ : 0 < γ) (N : ℕ) :
    Tendsto (fun y : ℝ => (1 + y) ^ N * Real.exp (-γ * y)) atTop (𝓝 0) := by
  have h0 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (N : ℝ) γ hγ
  have h1 : Tendsto (fun y : ℝ => 1 + y) atTop atTop :=
    tendsto_atTop_add_const_left atTop 1 tendsto_id
  have h2 := (h0.comp h1).const_mul (Real.exp γ)
  rw [mul_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
  simp only [Function.comp_apply, Real.rpow_natCast]
  have : Real.exp (-γ * y) = Real.exp γ * Real.exp (-γ * (1 + y)) := by
    rw [← Real.exp_add]; ring_nf
  rw [this]; ring

/-- **`x^γ (1 + |log x|)^N → 0` as `x → 0⁺`** (`γ > 0`). -/
theorem tendsto_rpow_mul_one_add_abs_log_pow {γ : ℝ} (hγ : 0 < γ) (N : ℕ) :
    Tendsto (fun x : ℝ => x ^ γ * (1 + |Real.log x|) ^ N) (𝓝[>] 0) (𝓝 0) := by
  have h3 : Tendsto (fun x : ℝ => -Real.log x) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  refine ((tendsto_one_add_pow_mul_exp_neg hγ N).comp h3).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
  have hl : Real.log x < 0 := Real.log_neg hx.1 hx.2
  simp only [Function.comp_apply, abs_of_neg hl, Real.rpow_def_of_pos hx.1]
  rw [mul_comm]
  congr 2
  ring

/-- Domination: a function bounded near `0⁺` by `C x^γ (1 + |log x|)^N` tends to `0`. -/
theorem tendsto_of_le_rpow_log {f : ℝ → ℝ} {γ C : ℝ} (hγ : 0 < γ) (N : ℕ)
    (hf : ∀ᶠ x in 𝓝[>] (0 : ℝ), |f x| ≤ C * (x ^ γ * (1 + |Real.log x|) ^ N)) :
    Tendsto f (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_rpow_mul_one_add_abs_log_pow hγ N).const_mul C
  rw [mul_zero] at h
  exact squeeze_zero_norm' (by simpa only [Real.norm_eq_abs] using hf) h

/-- `|α + β log(1/x)| ≤ (|α| + |β|)(1 + |log x|)`. -/
theorem abs_affine_log_le (α β x : ℝ) :
    |α + β * Real.log (1 / x)| ≤ (|α| + |β|) * (1 + |Real.log x|) := by
  rw [one_div, Real.log_inv]
  calc |α + β * -Real.log x| ≤ |α| + |β| * |Real.log x| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_neg]
    _ ≤ (|α| + |β|) * (1 + |Real.log x|) := by
        nlinarith [abs_nonneg α, abs_nonneg β, abs_nonneg (Real.log x)]

/-- **`x^γ (α + β log(1/x))^N → 0` as `x → 0⁺`** (`γ > 0`). -/
theorem tendsto_rpow_mul_affine_log_pow {γ : ℝ} (hγ : 0 < γ) (N : ℕ) (α β : ℝ) :
    Tendsto (fun x : ℝ => x ^ γ * (α + β * Real.log (1 / x)) ^ N) (𝓝[>] 0) (𝓝 0) := by
  refine tendsto_of_le_rpow_log (C := (|α| + |β|) ^ N) hγ N ?_
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
  rw [abs_mul, abs_pow, abs_of_pos (Real.rpow_pos_of_pos hx γ)]
  have h1 := abs_affine_log_le α β x
  have h2 : |α + β * Real.log (1 / x)| ^ N ≤ ((|α| + |β|) * (1 + |Real.log x|)) ^ N :=
    pow_le_pow_left₀ (abs_nonneg _) h1 N
  rw [mul_pow] at h2
  have hp : 0 ≤ x ^ γ := (Real.rpow_pos_of_pos hx γ).le
  calc x ^ γ * |α + β * Real.log (1 / x)| ^ N
      ≤ x ^ γ * ((|α| + |β|) ^ N * (1 + |Real.log x|) ^ N) := mul_le_mul_of_nonneg_left h2 hp
    _ = (|α| + |β|) ^ N * (x ^ γ * (1 + |Real.log x|) ^ N) := by ring

/-- **`x^γ ⟨log(1/x)⟩^N → 0` as `x → 0⁺`** (`γ > 0`). -/
theorem tendsto_rpow_mul_jap_log_pow {γ : ℝ} (hγ : 0 < γ) (N : ℕ) :
    Tendsto (fun x : ℝ => x ^ γ * Prelim.jap (Real.log (1 / x)) ^ N) (𝓝[>] 0) (𝓝 0) := by
  refine tendsto_of_le_rpow_log (C := 1) hγ N ?_
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
  have hp : 0 < x ^ γ := Real.rpow_pos_of_pos hx γ
  rw [abs_of_nonneg (mul_nonneg hp.le (pow_nonneg (Prelim.jap_nonneg _) _)), one_mul]
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Prelim.jap_nonneg _) ?_ N) hp.le
  rw [one_div, Real.log_inv]
  have h1 : Prelim.jap (-Real.log x) ^ 2 ≤ (1 + |Real.log x|) ^ 2 := by
    rw [Prelim.jap_sq]
    nlinarith [abs_nonneg (Real.log x), sq_abs (Real.log x), neg_sq (Real.log x)]
  exact (pow_le_pow_iff_left₀ (Prelim.jap_nonneg _) (by positivity) two_ne_zero).1 h1

/-- `κ ↦ κ/δ` maps `𝓝[>] 0` to `𝓝[>] 0` (`δ > 0`). -/
theorem tendsto_div_const_nhdsGT {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun κ : ℝ => κ / δ) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h : Tendsto (fun κ : ℝ => κ / δ) (𝓝 0) (𝓝 (0 / δ)) :=
      (continuous_id.div_const δ).tendsto 0
    rw [zero_div] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with κ (hκ : 0 < κ)
    exact div_pos hκ hδ

/-- **`(κ/δ)^γ log(δ/κ)^N → 0` as `κ → 0⁺`** (`δ, γ > 0`). -/
theorem tendsto_ratio_rpow_mul_log_pow {δ γ : ℝ} (hδ : 0 < δ) (hγ : 0 < γ) (N : ℕ) :
    Tendsto (fun κ : ℝ => (κ / δ) ^ γ * Real.log (δ / κ) ^ N) (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_rpow_mul_affine_log_pow hγ N 0 1).comp (tendsto_div_const_nhdsGT hδ)
  refine h.congr' (Eventually.of_forall fun κ => ?_)
  simp only [Function.comp_apply, zero_add, one_mul, one_div_div]

/-- **`(κ/δ)^γ ⟨log(δ/κ)⟩^N → 0` as `κ → 0⁺`** (`δ, γ > 0`). -/
theorem tendsto_ratio_rpow_mul_jap_log_pow {δ γ : ℝ} (hδ : 0 < δ) (hγ : 0 < γ) (N : ℕ) :
    Tendsto (fun κ : ℝ => (κ / δ) ^ γ * Prelim.jap (Real.log (δ / κ)) ^ N) (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_rpow_mul_jap_log_pow hγ N).comp (tendsto_div_const_nhdsGT hδ)
  refine h.congr' (Eventually.of_forall fun κ => ?_)
  simp only [Function.comp_apply, one_div_div]

/-- `√κ → 0` as `κ → 0⁺`. -/
theorem tendsto_sqrt_nhdsGT : Tendsto (fun κ : ℝ => Real.sqrt κ) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto Real.sqrt (𝓝 0) (𝓝 (Real.sqrt 0)) := Real.continuous_sqrt.tendsto 0
  rw [Real.sqrt_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- `x^n → 0` as `x → 0⁺` (`n ≥ 1`). -/
theorem tendsto_pow_nhdsGT {n : ℕ} (hn : n ≠ 0) :
    Tendsto (fun x : ℝ => x ^ n) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => x ^ n) (𝓝 0) (𝓝 ((0 : ℝ) ^ n)) := (continuous_pow n).tendsto 0
  rw [zero_pow hn] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- A function tending to `0` is eventually `≤ c` for `c > 0`. -/
theorem eventually_le_of_tendsto_zero {l : Filter ℝ} {f : ℝ → ℝ} (hf : Tendsto f l (𝓝 0))
    {c : ℝ} (hc : 0 < c) : ∀ᶠ x in l, f x ≤ c :=
  hf.eventually (eventually_le_nhds hc)

/-- From "eventually near `0⁺`" to "on an interval `(0, x₀]`". -/
theorem exists_Ioc_of_eventually {P : ℝ → Prop} (h : ∀ᶠ x in 𝓝[>] (0 : ℝ), P x) :
    ∃ x₀ : ℝ, 0 < x₀ ∧ ∀ x ∈ Ioc (0 : ℝ) x₀, P x := by
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 h
  exact ⟨u, hu, fun x hx => hsub hx⟩

/-- From "on an interval `(0, x₀]`" to "eventually near `0⁺`". -/
theorem eventually_of_Ioc {P : ℝ → Prop} {x₀ : ℝ} (hx₀ : 0 < x₀)
    (h : ∀ x ∈ Ioc (0 : ℝ) x₀, P x) : ∀ᶠ x in 𝓝[>] (0 : ℝ), P x :=
  mem_nhdsGT_iff_exists_Ioc_subset.2 ⟨x₀, hx₀, fun x hx => h x hx⟩

/-- **`(1 + T)^3 e^{-bT} → 0` as `T → ∞`** (`b > 0`): `r_T(T) → 0` in (P3). -/
theorem tendsto_rT {b : ℝ} (hb : 0 < b) :
    Tendsto (fun T : ℝ => (1 + T) ^ 3 * Real.exp (-(b * T))) atTop (𝓝 0) := by
  refine (tendsto_one_add_pow_mul_exp_neg hb 3).congr' (Eventually.of_forall fun T => ?_)
  simp only [neg_mul]

end NonemptyH

end Relay

end NonUniqueEuler
