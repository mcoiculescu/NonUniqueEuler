import NonUniqueEuler.Defs.Infra.Multipole
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-!
# Proof: real derivatives of holomorphic functions; the exterior Laurent series (I-MULT)

Proves the declarations of `NonUniqueEuler/I/Infra/Multipole/Holomorphic.lean`
(eq:derivative-norm of `07_several_rings.tex`; derivative count in the proof of
`lem:ext-multipole`, `02_prelim.tex:493-505`).

* Real vs complex derivatives: `ContDiffAt.restrictScalars_iteratedFDeriv` and
  `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod`; conjugation via `Complex.conjCLE`
  (`ContinuousLinearEquiv.iteratedFDeriv_comp_left`) and `Complex.conjLIE`
  (`LinearIsometryEquiv.norm_iteratedFDeriv_comp_left`).
* Laurent series: on `{ϱ' < |y|}` with `ϱ < ϱ'` the `k`-th derivatives of the terms
  `a_l y^{-(l+1)}` are bounded by `A ϱ^l (l+k)^k ϱ'^{-(l+1+k)}`, which is summable
  (binomial expansion of `(l+k)^k` and `summable_pow_mul_geometric_of_norm_lt_one`);
  then `iteratedDerivWithin_tsum` and `Complex.differentiableOn_tsum_of_summable_norm`.
-/

noncomputable section

open Set Metric Real ComplexConjugate
open scoped ContDiff

namespace NonUniqueEuler.Multipole

private lemma contDiffAt_complex {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {z : ℂ} (hz : z ∈ U) (n : WithTop ℕ∞) :
    ContDiffAt ℂ n F z :=
  (hF.contDiffOn (n := n) hU).contDiffAt (hU.mem_nhds hz)

private lemma iteratedFDeriv_real_eq_restrict {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {z : ℂ} (hz : z ∈ U) (q : ℕ) :
    iteratedFDeriv ℝ q F z = (iteratedFDeriv ℂ q F z).restrictScalars ℝ :=
  ((contDiffAt_complex hU hF hz q).restrictScalars_iteratedFDeriv (𝕜 := ℝ)).symm

/-- Real iterated derivatives of a holomorphic function: `D^q F(z) v = F^{(q)}(z) ∏ vᵢ`. -/
theorem iteratedFDeriv_real_apply_eq {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {z : ℂ} (hz : z ∈ U) (q : ℕ) (v : Fin q → ℂ) :
    iteratedFDeriv ℝ q F z v = iteratedDeriv q F z * ∏ i, v i := by
  rw [iteratedFDeriv_real_eq_restrict hU hF hz q, ContinuousMultilinearMap.coe_restrictScalars,
    iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul, mul_comm]

theorem norm_iteratedFDeriv_real_eq {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {z : ℂ} (hz : z ∈ U) (q : ℕ) :
    ‖iteratedFDeriv ℝ q F z‖ = ‖iteratedDeriv q F z‖ := by
  rw [iteratedFDeriv_real_eq_restrict hU hF hz q, ContinuousMultilinearMap.norm_restrictScalars,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv]

private lemma conj_comp_eq (F : ℂ → ℂ) :
    (fun x => conj (F x)) = (Complex.conjCLE : ℂ ≃L[ℝ] ℂ) ∘ F := by
  funext x; simp

/-- The conjugate of a holomorphic function (e.g. a velocity field off the vorticity support). -/
theorem iteratedFDeriv_real_conj_apply_eq {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {z : ℂ} (hz : z ∈ U) (q : ℕ) (v : Fin q → ℂ) :
    iteratedFDeriv ℝ q (fun x => conj (F x)) z v = conj (iteratedDeriv q F z * ∏ i, v i) := by
  rw [conj_comp_eq, ContinuousLinearEquiv.iteratedFDeriv_comp_left,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    iteratedFDeriv_real_apply_eq hU hF hz q v]
  simp

theorem norm_iteratedFDeriv_real_conj_eq {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {z : ℂ} (hz : z ∈ U) (q : ℕ) :
    ‖iteratedFDeriv ℝ q (fun x => conj (F x)) z‖ = ‖iteratedDeriv q F z‖ := by
  have : (fun x => conj (F x)) = (Complex.conjLIE : ℂ ≃ₗᵢ[ℝ] ℂ) ∘ F := by
    funext x; simp
  rw [this, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left,
    norm_iteratedFDeriv_real_eq hU hF hz q]

theorem contDiffOn_real_of_differentiableOn {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) :
    ContDiffOn ℝ ∞ F U ∧ ContDiffOn ℝ ∞ (fun x => conj (F x)) U := by
  have h1 : ContDiffOn ℝ ∞ F U := (hF.contDiffOn hU).restrict_scalars ℝ
  refine ⟨h1, ?_⟩
  rw [conj_comp_eq]
  exact (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn h1

/-! ### The exterior Laurent series -/

/-- The `k`-th derivative of a single Laurent term `c z^{-(n+1)}`. -/
private lemma iteratedDeriv_term (c : ℂ) (n k : ℕ) (z : ℂ) :
    iteratedDeriv k (fun y => c * (y ^ (n + 1))⁻¹) z =
      c * ((-1) ^ k * (∏ j ∈ Finset.range k, ((n : ℂ) + 1 + j)) * (z ^ (n + 1 + k))⁻¹) := by
  have hfun : (fun y : ℂ => (y ^ (n + 1))⁻¹) = fun y => y ^ (-((n + 1 : ℕ) : ℤ)) := by
    funext y; rw [zpow_neg, zpow_natCast]
  rw [iteratedDeriv_const_mul_field c (fun y : ℂ => (y ^ (n + 1))⁻¹), hfun,
    iteratedDeriv_eq_iterate, iter_deriv_zpow]
  congr 1
  have hprod : (∏ i ∈ Finset.range k, (((-((n + 1 : ℕ) : ℤ) : ℤ) : ℂ) - i)) =
      (-1) ^ k * ∏ j ∈ Finset.range k, ((n : ℂ) + 1 + j) := by
    rw [show (∏ i ∈ Finset.range k, (((-((n + 1 : ℕ) : ℤ) : ℤ) : ℂ) - i)) =
        ∏ i ∈ Finset.range k, -((n : ℂ) + 1 + i) from
        Finset.prod_congr rfl (fun i _ => by push_cast; ring), Finset.prod_neg, Finset.card_range]
  have hpow : z ^ (-((n + 1 : ℕ) : ℤ) - (k : ℤ)) = (z ^ (n + 1 + k))⁻¹ := by
    rw [show (-((n + 1 : ℕ) : ℤ) - (k : ℤ)) = -((n + 1 + k : ℕ) : ℤ) by push_cast; ring,
      zpow_neg, zpow_natCast]
  rw [hprod, hpow]

private lemma iteratedDerivWithin_term (c : ℂ) (n k : ℕ) {s : Set ℂ} (hs : IsOpen s) {z : ℂ}
    (hz : z ∈ s) :
    iteratedDerivWithin k (fun y => c * (y ^ (n + 1))⁻¹) s z =
      c * ((-1) ^ k * (∏ j ∈ Finset.range k, ((n : ℂ) + 1 + j)) * (z ^ (n + 1 + k))⁻¹) := by
  rw [iteratedDerivWithin_of_isOpen hs hz, iteratedDeriv_term]

/-- `|∂^k (c z^{-(n+1)})| ≤ |c| (n+k)^k |z|^{-(n+1+k)}`. -/
private lemma norm_term_le (c : ℂ) (n k : ℕ) (z : ℂ) :
    ‖c * ((-1) ^ k * (∏ j ∈ Finset.range k, ((n : ℂ) + 1 + j)) * (z ^ (n + 1 + k))⁻¹)‖ ≤
      ‖c‖ * ((n : ℝ) + k) ^ k * (‖z‖ ^ (n + 1 + k))⁻¹ := by
  have hP : ‖∏ j ∈ Finset.range k, ((n : ℂ) + 1 + j)‖ ≤ ((n : ℝ) + k) ^ k := by
    rw [norm_prod]
    calc ∏ j ∈ Finset.range k, ‖(n : ℂ) + 1 + j‖ ≤ ∏ _j ∈ Finset.range k, ((n : ℝ) + k) := by
          apply Finset.prod_le_prod (fun j _ => norm_nonneg _)
          intro j hj
          have hj' : (j : ℝ) + 1 ≤ k := by exact_mod_cast Finset.mem_range.mp hj
          rw [show (n : ℂ) + 1 + j = ((n + 1 + j : ℕ) : ℂ) by push_cast; ring,
            Complex.norm_natCast]
          push_cast; linarith
      _ = ((n : ℝ) + k) ^ k := by rw [Finset.prod_const, Finset.card_range]
  calc _ = ‖c‖ * ‖∏ j ∈ Finset.range k, ((n : ℂ) + 1 + j)‖ * (‖z‖ ^ (n + 1 + k))⁻¹ := by
        rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
          norm_inv, norm_pow, mul_assoc]
    _ ≤ _ := by gcongr

private lemma bound_le {a : ℕ → ℂ} {A ϱ : ℝ} (ha : ∀ l, ‖a l‖ ≤ A * ϱ ^ l) {ϱ' : ℝ}
    (hϱ' : 0 < ϱ') {y : ℂ} (hy : ϱ' ≤ ‖y‖) (n k : ℕ) :
    ‖a n‖ * ((n : ℝ) + k) ^ k * (‖y‖ ^ (n + 1 + k))⁻¹ ≤
      A * ϱ ^ n * ((n : ℝ) + k) ^ k * (ϱ' ^ (n + 1 + k))⁻¹ := by
  have h0 : 0 ≤ A * ϱ ^ n := (norm_nonneg _).trans (ha n)
  have h1 : (‖y‖ ^ (n + 1 + k))⁻¹ ≤ (ϱ' ^ (n + 1 + k))⁻¹ :=
    inv_anti₀ (pow_pos hϱ' _) (pow_le_pow_left₀ hϱ'.le hy _)
  have h2 : ‖a n‖ * ((n : ℝ) + k) ^ k ≤ A * ϱ ^ n * ((n : ℝ) + k) ^ k :=
    mul_le_mul_of_nonneg_right (ha n) (by positivity)
  exact mul_le_mul h2 h1 (by positivity) (mul_nonneg h0 (by positivity))

private lemma summable_poly_geom (k : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + k) ^ k * r ^ n) := by
  have : (fun n : ℕ => ((n : ℝ) + k) ^ k * r ^ n) = fun n : ℕ =>
      ∑ m ∈ Finset.range (k + 1), ((n : ℝ) ^ m * r ^ n) * ((k : ℝ) ^ (k - m) * (k.choose m)) := by
    funext n; rw [add_pow, Finset.sum_mul]; exact Finset.sum_congr rfl fun m _ => by ring
  have hr' : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  rw [this]
  exact summable_sum fun m _ =>
    (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) m hr').mul_right _

private lemma summable_bound (A : ℝ) {ϱ ϱ' : ℝ} (hϱ : 0 ≤ ϱ) (hϱϱ' : ϱ < ϱ') (k : ℕ) :
    Summable (fun n : ℕ => A * ϱ ^ n * ((n : ℝ) + k) ^ k * (ϱ' ^ (n + 1 + k))⁻¹) := by
  have hϱ'0 : 0 < ϱ' := hϱ.trans_lt hϱϱ'
  have h := (summable_poly_geom k (r := ϱ / ϱ') (div_nonneg hϱ hϱ'0.le)
    ((div_lt_one hϱ'0).mpr hϱϱ')).mul_left (A * (ϱ' ^ (1 + k))⁻¹)
  refine h.congr fun n => ?_
  have hne : ϱ' ≠ 0 := hϱ'0.ne'
  rw [div_pow]
  field_simp
  ring

/-- The `k`-th derivatives of the Laurent terms are uniformly bounded on `{ϱ' < |y|}`. -/
private lemma term_deriv_bound {a : ℕ → ℂ} {A ϱ : ℝ} (ha : ∀ l, ‖a l‖ ≤ A * ϱ ^ l) {ϱ' : ℝ}
    (hϱ' : 0 < ϱ') (k n : ℕ) {y : ℂ} (hy : y ∈ {y : ℂ | ϱ' < ‖y‖}) :
    ‖iteratedDerivWithin k (fun y => a n * (y ^ (n + 1))⁻¹) {y : ℂ | ϱ' < ‖y‖} y‖ ≤
      A * ϱ ^ n * ((n : ℝ) + k) ^ k * (ϱ' ^ (n + 1 + k))⁻¹ := by
  rw [iteratedDerivWithin_term _ _ _ (isOpen_lt continuous_const continuous_norm) hy]
  exact (norm_term_le _ _ _ _).trans (bound_le ha hϱ' (le_of_lt hy) n k)

/-- Termwise differentiation of the Laurent series on `{ϱ' < |y|}`, `ϱ < ϱ'`. -/
private lemma laurent_iteratedDerivWithin {a : ℕ → ℂ} {A ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (ha : ∀ l, ‖a l‖ ≤ A * ϱ ^ l) {ϱ' : ℝ} (hϱϱ' : ϱ < ϱ') (q : ℕ) {z : ℂ} (hz : ϱ' < ‖z‖) :
    iteratedDerivWithin q (laurentTail a) {y : ℂ | ϱ' < ‖y‖} z =
      ∑' l : ℕ, a l * ((-1) ^ q * (∏ j ∈ Finset.range q, ((l : ℂ) + 1 + j)) *
        (z ^ (l + 1 + q))⁻¹) := by
  have hs : IsOpen {y : ℂ | ϱ' < ‖y‖} := isOpen_lt continuous_const continuous_norm
  have hϱ'0 : 0 < ϱ' := hϱ.trans_lt hϱϱ'
  have hL : laurentTail a = fun y => ∑' n : ℕ, a n * (y ^ (n + 1))⁻¹ := rfl
  rw [hL, iteratedDerivWithin_tsum q hs (show z ∈ {y : ℂ | ϱ' < ‖y‖} from hz)]
  · exact tsum_congr fun n => iteratedDerivWithin_term _ _ _ hs hz
  · intro t ht
    refine Summable.of_norm_bounded (summable_bound A hϱ hϱϱ' 0) fun n => ?_
    simpa using term_deriv_bound ha hϱ'0 0 n ht
  · intro k _ _
    exact SummableLocallyUniformlyOn_of_locally_bounded hs fun K hK _ =>
      ⟨_, summable_bound A hϱ hϱϱ' k, fun n y hy => term_deriv_bound ha hϱ'0 k n (hK hy)⟩
  · intro n k r _ hr
    have heq : iteratedDerivWithin k (fun y => a n * (y ^ (n + 1))⁻¹) {y : ℂ | ϱ' < ‖y‖}
        =ᶠ[nhds r] fun y => a n * ((-1) ^ k * (∏ j ∈ Finset.range k, ((n : ℂ) + 1 + j)) *
          (y ^ (n + 1 + k))⁻¹) :=
      Filter.eventually_of_mem (hs.mem_nhds hr) fun y hy => iteratedDerivWithin_term _ _ _ hs hy
    have hr0 : r ≠ 0 := by
      rintro rfl
      have : ϱ' < 0 := by simpa using hr
      linarith
    refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
    exact (((differentiableAt_id.pow _).inv (pow_ne_zero _ hr0)).const_mul _).const_mul _

/-- The exterior Laurent series is holomorphic outside `closedBall 0 ϱ`. -/
theorem differentiableOn_laurentTail {a : ℕ → ℂ} {A ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (ha : ∀ l, ‖a l‖ ≤ A * ϱ ^ l) :
    DifferentiableOn ℂ (laurentTail a) {z | ϱ < ‖z‖} := by
  intro z hz
  obtain ⟨ϱ', h1, h2⟩ := exists_between (show ϱ < ‖z‖ from hz)
  have hs : IsOpen {y : ℂ | ϱ' < ‖y‖} := isOpen_lt continuous_const continuous_norm
  have hϱ'0 : 0 < ϱ' := hϱ.trans_lt h1
  have hD : DifferentiableOn ℂ (laurentTail a) {y : ℂ | ϱ' < ‖y‖} := by
    show DifferentiableOn ℂ (fun w => ∑' l : ℕ, a l * (w ^ (l + 1))⁻¹) _
    refine Complex.differentiableOn_tsum_of_summable_norm (summable_bound A hϱ h1 0) (fun n => ?_) hs
      (fun n y hy => ?_)
    · intro y hy
      have hy0 : y ≠ 0 := by
        rintro rfl
        have : ϱ' < 0 := by simpa using hy
        linarith
      exact (((differentiableAt_id.pow _).inv (pow_ne_zero _ hy0)).const_mul _).differentiableWithinAt
    · simpa using term_deriv_bound ha hϱ'0 0 n hy
  exact (hD.differentiableAt (hs.mem_nhds h2)).differentiableWithinAt

/-- Termwise derivatives of the exterior Laurent series. -/
theorem iteratedDeriv_laurentTail {a : ℕ → ℂ} {A ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (ha : ∀ l, ‖a l‖ ≤ A * ϱ ^ l) (q : ℕ) {z : ℂ} (hz : ϱ < ‖z‖) :
    iteratedDeriv q (laurentTail a) z =
      ∑' l : ℕ, a l * ((-1) ^ q * (∏ j ∈ Finset.range q, ((l : ℂ) + 1 + j)) *
        (z ^ (l + 1 + q))⁻¹) := by
  obtain ⟨ϱ', h1, h2⟩ := exists_between hz
  rw [← iteratedDerivWithin_of_isOpen (isOpen_lt continuous_const continuous_norm)
    (show z ∈ {y : ℂ | ϱ' < ‖y‖} from h2)]
  exact laurent_iteratedDerivWithin hϱ ha h1 q h2

/-- `|F^{(q)}(z)| ≤ ∑ |a_l| (l+q)^q |z|^{-(l+1+q)}` (proof of `lem:ext-multipole`). -/
theorem norm_iteratedDeriv_laurentTail_le {a : ℕ → ℂ} {A ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (ha : ∀ l, ‖a l‖ ≤ A * ϱ ^ l) (q : ℕ) {z : ℂ} (hz : ϱ < ‖z‖) :
    ‖iteratedDeriv q (laurentTail a) z‖ ≤
      ∑' l : ℕ, ‖a l‖ * ((l : ℝ) + q) ^ q * (‖z‖ ^ (l + 1 + q))⁻¹ := by
  rw [iteratedDeriv_laurentTail hϱ ha q hz]
  have hz0 : 0 < ‖z‖ := hϱ.trans_lt hz
  have hle : ∀ l : ℕ, ‖a l * ((-1) ^ q * (∏ j ∈ Finset.range q, ((l : ℂ) + 1 + j)) *
      (z ^ (l + 1 + q))⁻¹)‖ ≤ ‖a l‖ * ((l : ℝ) + q) ^ q * (‖z‖ ^ (l + 1 + q))⁻¹ :=
    fun l => norm_term_le _ _ _ _
  have hsumB : Summable (fun l : ℕ => ‖a l‖ * ((l : ℝ) + q) ^ q * (‖z‖ ^ (l + 1 + q))⁻¹) :=
    Summable.of_nonneg_of_le (fun l => by positivity) (fun l => bound_le ha hz0 le_rfl l q)
      (summable_bound A hϱ hz q)
  have hsumN : Summable (fun l : ℕ => ‖a l * ((-1) ^ q *
      (∏ j ∈ Finset.range q, ((l : ℂ) + 1 + j)) * (z ^ (l + 1 + q))⁻¹)‖) :=
    Summable.of_nonneg_of_le (fun l => norm_nonneg _) hle hsumB
  exact (norm_tsum_le_tsum_norm hsumN).trans (Summable.tsum_le_tsum hle hsumN hsumB)

end NonUniqueEuler.Multipole
