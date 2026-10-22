import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-!
# Helper for `lem:transfer`(4): termwise derivatives of a power series

Helper of `P/Sec7/Transfer.lean` (`07_several_rings.tex:212-228`). The interior expansion of the
field of an outer ring is a power series `F(z) = Σ_{l≥0} d_l z^l` on `B_{a/2}`
(`hasSum_cauchyTransform_interior`), and item (4) differentiates it termwise. With
`‖d_l‖ ≤ B R^{-l}` (`R > 0`):
* `differentiableOn_powSer`: `F` is holomorphic on `B_R`;
* `iteratedDeriv_powSer`: `F^{(k)}(z) = Σ_l d_l (∏_{i<k}(l-i)) z^{l-k}` for `|z| < R`;
* `norm_iteratedDeriv_powSer_le`: `|F^{(k)}(z)| ≤ Σ_l |d_l| |∏_{i<k}(l-i)| |z|^{l-k}`;
* `norm_prod_sub_le`, `prod_sub_eq_zero_of_lt`: `|∏_{i<k}(l-i)| ≤ l^k`, and it is `0` for `l < k`.

This follows the proof of `Multipole.iteratedDeriv_laurentTail`
(`P/Infra/Multipole/Holomorphic.lean`) with `z^l` in place of `z^{-(l+1)}`
(`iterateDerivWithin_tsum`, `Complex.differentiableOn_tsum_of_summable_norm`).
-/

noncomputable section

open Set Metric

namespace NonUniqueEuler.Rings.TransferAux

/-- The power series `Σ_{l ≥ 0} d_l z^l`. -/
def powSer (d : ℕ → ℂ) (z : ℂ) : ℂ := ∑' l : ℕ, d l * z ^ l

/-- The `k`-th derivative of a single term `c z^n`. -/
theorem iteratedDeriv_powTerm (c : ℂ) (n k : ℕ) (z : ℂ) :
    iteratedDeriv k (fun y => c * y ^ n) z =
      c * ((∏ i ∈ Finset.range k, ((n : ℂ) - i)) * z ^ (n - k)) := by
  rw [iteratedDeriv_const_mul_field c (fun y : ℂ => y ^ n), iteratedDeriv_eq_iterate,
    iter_deriv_pow]

theorem iteratedDerivWithin_powTerm (c : ℂ) (n k : ℕ) {s : Set ℂ} (hs : IsOpen s) {z : ℂ}
    (hz : z ∈ s) :
    iteratedDerivWithin k (fun y => c * y ^ n) s z =
      c * ((∏ i ∈ Finset.range k, ((n : ℂ) - i)) * z ^ (n - k)) := by
  rw [iteratedDerivWithin_of_isOpen hs hz, iteratedDeriv_powTerm]

/-- `∏_{i<k}(n - i) = 0` for `n < k`. -/
theorem prod_sub_eq_zero_of_lt {n k : ℕ} (h : n < k) :
    (∏ i ∈ Finset.range k, ((n : ℂ) - i)) = 0 :=
  Finset.prod_eq_zero (Finset.mem_range.2 h) (sub_self _)

/-- `|∏_{i<k}(n - i)| ≤ n^k`. -/
theorem norm_prod_sub_le (n k : ℕ) :
    ‖∏ i ∈ Finset.range k, ((n : ℂ) - i)‖ ≤ (n : ℝ) ^ k := by
  rcases lt_or_ge n k with h | h
  · rw [prod_sub_eq_zero_of_lt h, norm_zero]
    positivity
  · rw [norm_prod]
    calc ∏ i ∈ Finset.range k, ‖(n : ℂ) - i‖ ≤ ∏ _i ∈ Finset.range k, (n : ℝ) := by
          apply Finset.prod_le_prod (fun i _ => norm_nonneg _)
          intro i hi
          have hik : i < k := Finset.mem_range.mp hi
          have hin : i ≤ n := by omega
          rw [show (n : ℂ) - i = ((n - i : ℕ) : ℂ) by push_cast [Nat.cast_sub hin]; ring,
            Complex.norm_natCast]
          exact_mod_cast Nat.sub_le n i
      _ = (n : ℝ) ^ k := by rw [Finset.prod_const, Finset.card_range]

/-- The bound `|c ∏_{i<k}(n-i) z^{n-k}| ≤ |c| n^k R'^n R'^{-k}` for `|z| ≤ R'`. -/
theorem norm_powTermDeriv_le (c : ℂ) (n k : ℕ) {z : ℂ} {R' : ℝ} (hR' : 0 < R')
    (hz : ‖z‖ ≤ R') :
    ‖c * ((∏ i ∈ Finset.range k, ((n : ℂ) - i)) * z ^ (n - k))‖ ≤
      ‖c‖ * (n : ℝ) ^ k * R' ^ n * (R' ^ k)⁻¹ := by
  rcases lt_or_ge n k with h | h
  · rw [prod_sub_eq_zero_of_lt h, zero_mul, mul_zero, norm_zero]
    positivity
  · rw [norm_mul, norm_mul, norm_pow]
    have h1 := norm_prod_sub_le n k
    have h2 : ‖z‖ ^ (n - k) ≤ R' ^ (n - k) := pow_le_pow_left₀ (norm_nonneg _) hz _
    have h3 : R' ^ (n - k) = R' ^ n * (R' ^ k)⁻¹ := by
      rw [pow_sub₀ _ hR'.ne' h]
    calc ‖c‖ * (‖∏ i ∈ Finset.range k, ((n : ℂ) - i)‖ * ‖z‖ ^ (n - k))
        ≤ ‖c‖ * ((n : ℝ) ^ k * R' ^ (n - k)) := by gcongr
      _ = _ := by rw [h3]; ring

/-- The summable majorant `B R'^{-k} n^k (R'/R)^n`. -/
theorem summable_powMajorant (B : ℝ) {R R' : ℝ} (hR : 0 < R) (hR' : 0 < R') (hRR : R' < R)
    (k : ℕ) :
    Summable (fun n : ℕ => B * (R ^ n)⁻¹ * (n : ℝ) ^ k * R' ^ n * (R' ^ k)⁻¹) := by
  have hr : ‖R' / R‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (div_pos hR' hR)]
    exact (div_lt_one hR).mpr hRR
  have h := (summable_pow_mul_geometric_of_norm_lt_one k hr).mul_left (B * (R' ^ k)⁻¹)
  refine h.congr fun n => ?_
  rw [div_pow]
  field_simp

theorem powTermDeriv_bound {d : ℕ → ℂ} {B R : ℝ} (hd : ∀ l, ‖d l‖ ≤ B * (R ^ l)⁻¹) {R' : ℝ}
    (hR' : 0 < R') (n k : ℕ) {z : ℂ} (hz : ‖z‖ ≤ R') :
    ‖d n * ((∏ i ∈ Finset.range k, ((n : ℂ) - i)) * z ^ (n - k))‖ ≤
      B * (R ^ n)⁻¹ * (n : ℝ) ^ k * R' ^ n * (R' ^ k)⁻¹ := by
  refine (norm_powTermDeriv_le (d n) n k hR' hz).trans ?_
  gcongr
  exact hd n

/-- Termwise differentiation on `B_{R'}`, `R' < R`. -/
theorem powSer_iteratedDerivWithin {d : ℕ → ℂ} {B R : ℝ} (hR : 0 < R)
    (hd : ∀ l, ‖d l‖ ≤ B * (R ^ l)⁻¹) {R' : ℝ} (hR' : 0 < R') (hRR : R' < R) (k : ℕ) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) R') :
    iteratedDerivWithin k (powSer d) (ball (0 : ℂ) R') z =
      ∑' l : ℕ, d l * ((∏ i ∈ Finset.range k, ((l : ℂ) - i)) * z ^ (l - k)) := by
  have hs : IsOpen (ball (0 : ℂ) R') := isOpen_ball
  have hmem : ∀ {y : ℂ}, y ∈ ball (0 : ℂ) R' → ‖y‖ ≤ R' := fun hy =>
    (mem_ball_zero_iff.mp hy).le
  have hP : powSer d = fun y => ∑' n : ℕ, d n * y ^ n := rfl
  rw [hP, iteratedDerivWithin_tsum k hs hz]
  · exact tsum_congr fun n => iteratedDerivWithin_powTerm _ _ _ hs hz
  · intro t ht
    refine Summable.of_norm_bounded (summable_powMajorant B hR hR' hRR 0) fun n => ?_
    have := powTermDeriv_bound hd hR' n 0 (hmem ht)
    simpa using this
  · intro j _ _
    exact SummableLocallyUniformlyOn_of_locally_bounded hs fun K hK _ =>
      ⟨_, summable_powMajorant B hR hR' hRR j, fun n y hy => by
        rw [iteratedDerivWithin_powTerm _ _ _ hs (hK hy)]
        exact powTermDeriv_bound hd hR' n j (hmem (hK hy))⟩
  · intro n j r _ hr
    have heq : iteratedDerivWithin j (fun y => d n * y ^ n) (ball (0 : ℂ) R')
        =ᶠ[nhds r] fun y => d n * ((∏ i ∈ Finset.range j, ((n : ℂ) - i)) * y ^ (n - j)) :=
      Filter.eventually_of_mem (hs.mem_nhds hr) fun y hy => iteratedDerivWithin_powTerm _ _ _ hs hy
    refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
    exact ((differentiableAt_id.pow _).const_mul _).const_mul _

/-- The power series is holomorphic on `B_R`. -/
theorem differentiableOn_powSer {d : ℕ → ℂ} {B R : ℝ} (hR : 0 < R)
    (hd : ∀ l, ‖d l‖ ≤ B * (R ^ l)⁻¹) : DifferentiableOn ℂ (powSer d) (ball (0 : ℂ) R) := by
  intro z hz
  have hz' : ‖z‖ < R := mem_ball_zero_iff.mp hz
  obtain ⟨R', h1, h2⟩ := exists_between hz'
  have hR' : 0 < R' := (norm_nonneg z).trans_lt h1
  have hs : IsOpen (ball (0 : ℂ) R') := isOpen_ball
  have hD : DifferentiableOn ℂ (powSer d) (ball (0 : ℂ) R') := by
    show DifferentiableOn ℂ (fun w => ∑' l : ℕ, d l * w ^ l) _
    refine Complex.differentiableOn_tsum_of_summable_norm (summable_powMajorant B hR hR' h2 0)
      (fun n => ?_) hs (fun n y hy => ?_)
    · exact ((differentiable_id.pow _).const_mul _).differentiableOn
    · have := powTermDeriv_bound hd hR' n 0 (mem_ball_zero_iff.mp hy).le
      simpa using this
  exact (hD.differentiableAt (hs.mem_nhds (mem_ball_zero_iff.mpr h1))).differentiableWithinAt

/-- Termwise derivatives of the power series on `B_R`. -/
theorem iteratedDeriv_powSer {d : ℕ → ℂ} {B R : ℝ} (hR : 0 < R)
    (hd : ∀ l, ‖d l‖ ≤ B * (R ^ l)⁻¹) (k : ℕ) {z : ℂ} (hz : ‖z‖ < R) :
    iteratedDeriv k (powSer d) z =
      ∑' l : ℕ, d l * ((∏ i ∈ Finset.range k, ((l : ℂ) - i)) * z ^ (l - k)) := by
  obtain ⟨R', h1, h2⟩ := exists_between hz
  have hR' : 0 < R' := (norm_nonneg z).trans_lt h1
  have hzb : z ∈ ball (0 : ℂ) R' := mem_ball_zero_iff.mpr h1
  rw [← iteratedDerivWithin_of_isOpen isOpen_ball hzb]
  exact powSer_iteratedDerivWithin hR hd hR' h2 k hzb

/-- `|F^{(k)}(z)| ≤ Σ_l |d_l| |∏_{i<k}(l-i)| |z|^{l-k}` on `B_R`. -/
theorem norm_iteratedDeriv_powSer_le {d : ℕ → ℂ} {B R : ℝ} (hR : 0 < R)
    (hd : ∀ l, ‖d l‖ ≤ B * (R ^ l)⁻¹) (k : ℕ) {z : ℂ} (hz : ‖z‖ < R) :
    ‖iteratedDeriv k (powSer d) z‖ ≤
      ∑' l : ℕ, ‖d l‖ * ‖∏ i ∈ Finset.range k, ((l : ℂ) - i)‖ * ‖z‖ ^ (l - k) := by
  rw [iteratedDeriv_powSer hR hd k hz]
  obtain ⟨R', h1, h2⟩ := exists_between hz
  have hR' : 0 < R' := (norm_nonneg z).trans_lt h1
  have heq : ∀ l : ℕ, ‖d l * ((∏ i ∈ Finset.range k, ((l : ℂ) - i)) * z ^ (l - k))‖ =
      ‖d l‖ * ‖∏ i ∈ Finset.range k, ((l : ℂ) - i)‖ * ‖z‖ ^ (l - k) := by
    intro l
    rw [norm_mul, norm_mul, norm_pow, mul_assoc]
  have hsumN : Summable (fun l : ℕ =>
      ‖d l * ((∏ i ∈ Finset.range k, ((l : ℂ) - i)) * z ^ (l - k))‖) :=
    Summable.of_nonneg_of_le (fun l => norm_nonneg _)
      (fun l => powTermDeriv_bound hd hR' l k h1.le) (summable_powMajorant B hR hR' h2 k)
  refine (norm_tsum_le_tsum_norm hsumN).trans (le_of_eq ?_)
  exact tsum_congr heq

end NonUniqueEuler.Rings.TransferAux
