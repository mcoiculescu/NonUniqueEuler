import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Basic

/-!
# Helper for `lem:transfer`: the numerical series

Helper of `P/Sec7/Transfer.lean` (`07_several_rings.tex:157-164`, `:186-189`, `:212-221`).
The constants of `lem:transfer` are existential (D11), so we use the simple majorants
* `Uq q = Σ_{l≥0} (l+q)^q 2^{-l}` (items (1), (2): the exterior series, `tsum_ext_le`), and
* `Vq q = Σ_{l≥0} l^q (3/16)^l` (item (4): the interior series)
in place of the manuscript's `S_{m,q}`; both converge (`summable_Uq`, `summable_Vq`).

`tsum_ext_le` is the estimate of `07_several_rings.tex:157-164`: if `c_l = 0` for `l < 3`
(the monopole and the non-multiples of `m = 3`), `|c_l| ≤ K τ^l` and `|x| ≥ τ/σ` with
`0 < σ ≤ 1/2`, then `Σ_l |c_l| (l+q)^q |x|^{-(l+1+q)} ≤ K τ^{-1-q} σ^{4+q} · 8 U_q`.
-/

noncomputable section

namespace NonUniqueEuler.Rings.TransferAux

/-- `Σ_n (n+k)^k r^n` converges for `0 ≤ r < 1` (binomial expansion of `(n+k)^k`). -/
theorem summable_poly_geom (k : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + k) ^ k * r ^ n) := by
  have : (fun n : ℕ => ((n : ℝ) + k) ^ k * r ^ n) = fun n : ℕ =>
      ∑ m ∈ Finset.range (k + 1), ((n : ℝ) ^ m * r ^ n) * ((k : ℝ) ^ (k - m) * (k.choose m)) := by
    funext n; rw [add_pow, Finset.sum_mul]; exact Finset.sum_congr rfl fun m _ => by ring
  have hr' : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  rw [this]
  exact summable_sum fun m _ =>
    (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) m hr').mul_right _

/-- `U_q = Σ_{l≥0} (l+q)^q 2^{-l}`. -/
def Uq (q : ℕ) : ℝ := ∑' l : ℕ, ((l : ℝ) + q) ^ q * (1 / 2 : ℝ) ^ l

theorem summable_Uq (q : ℕ) : Summable (fun l : ℕ => ((l : ℝ) + q) ^ q * (1 / 2 : ℝ) ^ l) :=
  summable_poly_geom q (by norm_num) (by norm_num)

theorem Uq_nonneg (q : ℕ) : 0 ≤ Uq q :=
  tsum_nonneg fun l => by positivity

/-- `V_q = Σ_{l≥0} l^q (3/16)^l`. -/
def Vq (q : ℕ) : ℝ := ∑' l : ℕ, (l : ℝ) ^ q * (3 / 16 : ℝ) ^ l

theorem summable_Vq (q : ℕ) : Summable (fun l : ℕ => (l : ℝ) ^ q * (3 / 16 : ℝ) ^ l) :=
  summable_pow_mul_geometric_of_norm_lt_one q (by norm_num [abs_of_pos])

theorem Vq_nonneg (q : ℕ) : 0 ≤ Vq q :=
  tsum_nonneg fun l => by positivity

/-- **The exterior series bound** (`07_several_rings.tex:157-164`, `:186-189`). -/
theorem tsum_ext_le {c : ℕ → ℂ} {K τ σ : ℝ} (hK : 0 ≤ K) (hτ : 0 < τ) (hσ0 : 0 < σ)
    (hσ : σ ≤ 1 / 2) (hc : ∀ l, ‖c l‖ ≤ K * τ ^ l) (hvan : ∀ l, l < 3 → c l = 0) (q : ℕ)
    {x : ℂ} (hx : τ / σ ≤ ‖x‖) :
    ∑' l : ℕ, ‖c l‖ * ((l : ℝ) + q) ^ q * (‖x‖ ^ (l + 1 + q))⁻¹ ≤
      K * (τ ^ (1 + q))⁻¹ * σ ^ (4 + q) * (8 * Uq q) := by
  have hτσ : 0 < τ / σ := div_pos hτ hσ0
  set g : ℕ → ℝ := fun l =>
    K * (τ ^ (1 + q))⁻¹ * σ ^ (4 + q) * 8 * (((l : ℝ) + q) ^ q * (1 / 2 : ℝ) ^ l) with hg
  have hg0 : ∀ l, 0 ≤ g l := fun l => by simp only [hg]; positivity
  have hgs : Summable g := (summable_Uq q).mul_left _
  have hterm : ∀ l, ‖c l‖ * ((l : ℝ) + q) ^ q * (‖x‖ ^ (l + 1 + q))⁻¹ ≤ g l := by
    intro l
    rcases lt_or_ge l 3 with hl | hl
    · rw [hvan l hl, norm_zero, zero_mul, zero_mul]
      exact hg0 l
    · obtain ⟨n, rfl⟩ : ∃ n, l = n + 3 := ⟨l - 3, by omega⟩
      have h1 : (‖x‖ ^ (n + 3 + 1 + q))⁻¹ ≤ ((τ / σ) ^ (n + 3 + 1 + q))⁻¹ :=
        inv_anti₀ (pow_pos hτσ _) (pow_le_pow_left₀ hτσ.le hx _)
      have h2 : σ ^ n ≤ (1 / 2 : ℝ) ^ n := pow_le_pow_left₀ hσ0.le hσ n
      have hX : 0 ≤ ((((n + 3 : ℕ) : ℝ)) + q) ^ q := by positivity
      calc ‖c (n + 3)‖ * ((((n + 3 : ℕ) : ℝ)) + q) ^ q * (‖x‖ ^ (n + 3 + 1 + q))⁻¹
          ≤ K * τ ^ (n + 3) * ((((n + 3 : ℕ) : ℝ)) + q) ^ q *
              ((τ / σ) ^ (n + 3 + 1 + q))⁻¹ := by
            gcongr
            exact hc _
        _ = K * (τ ^ (1 + q))⁻¹ * σ ^ (4 + q) * (((((n + 3 : ℕ) : ℝ)) + q) ^ q * σ ^ n) := by
            rw [div_pow]
            field_simp
            ring
        _ ≤ K * (τ ^ (1 + q))⁻¹ * σ ^ (4 + q) *
              (((((n + 3 : ℕ) : ℝ)) + q) ^ q * (1 / 2 : ℝ) ^ n) := by
            gcongr
        _ = g (n + 3) := by
            simp only [hg]
            ring
  have hls : Summable (fun l : ℕ => ‖c l‖ * ((l : ℝ) + q) ^ q * (‖x‖ ^ (l + 1 + q))⁻¹) :=
    Summable.of_nonneg_of_le (fun l => by positivity) hterm hgs
  calc ∑' l : ℕ, ‖c l‖ * ((l : ℝ) + q) ^ q * (‖x‖ ^ (l + 1 + q))⁻¹ ≤ ∑' l, g l :=
        Summable.tsum_le_tsum hterm hls hgs
    _ = K * (τ ^ (1 + q))⁻¹ * σ ^ (4 + q) * (8 * Uq q) := by
        simp only [hg, Uq]
        rw [tsum_mul_left]
        ring

end NonUniqueEuler.Rings.TransferAux
