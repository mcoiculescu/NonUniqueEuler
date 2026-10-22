import NonUniqueEuler.H.Sec6.Integrability.Radii
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Helpers for `prop:integrability`: the terms of the series

Helper of `P/Sec6/Integrability.lean` (`06_datum.tex:42-47`). The `k`-th term `A_k Φ(·/r_k)` of
the datum is radial, nonnegative and supported in the `k`-th annulus (`lem:ring-facts`, here the
hypothesis `RingFacts χ`); the annuli are disjoint, so at every point at most one term is nonzero
and the series is summable.

* `IntegrabilityH.mem_annulus_of_ne_zero`: `Φ(x/r) ≠ 0 → a r ≤ |x| ≤ r`;
* `IntegrabilityH.phi_eq_zero_of_ne`: at most one term is nonzero at each point;
* `IntegrabilityH.summable_terms`, `datum_eq_single`, `term_le_datum`, `datum_nonneg`,
  `datum_radial`, `measurable_datum`.
-/

noncomputable section

open Filter Topology

namespace NonUniqueEuler.Datum.IntegrabilityH

open RingData

variable {χ : ℝ → ℝ} {A₁ μ sbar : ℝ}

/-- `Φ(x/r) ≠ 0` forces `a r ≤ |x| ≤ r` (`supp Φ ⊆ {a ≤ |y| ≤ 1}`, `lem:ring-facts`). -/
theorem mem_annulus_of_ne_zero (hR : RingFacts χ) {r : ℝ} (hr : 0 < r) {x : ℂ}
    (hx : ringPhi χ (x / (r : ℂ)) ≠ 0) : a * r ≤ ‖x‖ ∧ ‖x‖ ≤ r := by
  unfold RingFacts at hR
  have h : a ≤ ‖x / (r : ℂ)‖ ∧ ‖x / (r : ℂ)‖ ≤ 1 := hR.2.2.2.2.2.1 (subset_tsupport _ hx)
  have hn : ‖x / (r : ℂ)‖ = ‖x‖ / r := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le]
  rw [hn, le_div_iff₀ hr, div_le_one hr] at h
  exact h

/-- At every point at most one term of the series is nonzero (`06_datum.tex:44-46`). -/
theorem phi_eq_zero_of_ne (hR : RingFacts χ) (hp : DatumParams A₁ μ sbar) (x : ℂ) (j l : ℕ)
    (hjl : j ≠ l) (hj : ringPhi χ (x / ((radius sbar μ (j + 1) : ℝ) : ℂ)) ≠ 0) :
    ringPhi χ (x / ((radius sbar μ (l + 1) : ℝ) : ℂ)) = 0 := by
  by_contra hl
  have hμ0 : 0 < μ := by linarith [hp.one_lt_μ]
  have h1 := mem_annulus_of_ne_zero hR (radius_pos hp.sbar_pos hμ0 (j + 1)) hj
  have h2 := mem_annulus_of_ne_zero hR (radius_pos hp.sbar_pos hμ0 (l + 1)) hl
  exact Set.disjoint_left.1
    (annuli_disjoint hp (j + 1) (l + 1) (by omega) (by omega) (by omega)) h1 h2

/-- Each term is nonnegative. -/
theorem term_nonneg (hR : RingFacts χ) (hp : DatumParams A₁ μ sbar) (x : ℂ) (j : ℕ) :
    0 ≤ amp A₁ μ (j + 1) * ringPhi χ (x / ((radius sbar μ (j + 1) : ℝ) : ℂ)) := by
  unfold RingFacts at hR
  exact mul_nonneg (amp_pos hp.A₁_pos (by linarith [hp.one_lt_μ]) _).le (hR.2.2.2.1 _).1

/-- The series defining `f` is summable at every point: at most one term is nonzero. -/
theorem summable_terms (hR : RingFacts χ) (hp : DatumParams A₁ μ sbar) (x : ℂ) :
    Summable fun j : ℕ => amp A₁ μ (j + 1) * ringPhi χ (x / ((radius sbar μ (j + 1) : ℝ) : ℂ)) := by
  apply summable_of_hasFiniteSupport
  show (Function.support _).Finite
  apply Set.Subsingleton.finite
  intro j hj l hl
  by_contra hjl
  have hj' : ringPhi χ (x / ((radius sbar μ (j + 1) : ℝ) : ℂ)) ≠ 0 :=
    right_ne_zero_of_mul (Function.mem_support.1 hj)
  exact Function.mem_support.1 hl (by rw [phi_eq_zero_of_ne hR hp x j l hjl hj', mul_zero])

/-- Where the `j`-th term is nonzero, `f` equals it. -/
theorem datum_eq_single (hR : RingFacts χ) (hp : DatumParams A₁ μ sbar) {x : ℂ} {j : ℕ}
    (hj : ringPhi χ (x / ((radius sbar μ (j + 1) : ℝ) : ℂ)) ≠ 0) :
    datum χ A₁ μ sbar x = amp A₁ μ (j + 1) * ringPhi χ (x / ((radius sbar μ (j + 1) : ℝ) : ℂ)) := by
  unfold datum
  exact tsum_eq_single j fun l hl => by
    rw [phi_eq_zero_of_ne hR hp x j l (Ne.symm hl) hj, mul_zero]

/-- Where every term vanishes, `f = 0`. -/
theorem datum_eq_zero {x : ℂ}
    (h : ∀ j : ℕ, ringPhi χ (x / ((radius sbar μ (j + 1) : ℝ) : ℂ)) = 0) :
    datum χ A₁ μ sbar x = 0 := by
  simp [datum, h]

/-- Each term is at most `f`. -/
theorem term_le_datum (hR : RingFacts χ) (hp : DatumParams A₁ μ sbar) (x : ℂ) (j : ℕ) :
    amp A₁ μ (j + 1) * ringPhi χ (x / ((radius sbar μ (j + 1) : ℝ) : ℂ)) ≤
      datum χ A₁ μ sbar x :=
  (summable_terms hR hp x).le_tsum j fun l _ => term_nonneg hR hp x l

/-- `f ≥ 0`. -/
theorem datum_nonneg (hR : RingFacts χ) (hp : DatumParams A₁ μ sbar) (x : ℂ) :
    0 ≤ datum χ A₁ μ sbar x :=
  tsum_nonneg fun j => term_nonneg hR hp x j

/-- `f` is radial (pointwise): each term is. -/
theorem datum_radial (hR : RingFacts χ) : IsRadialPointwise (datum χ A₁ μ sbar) := by
  unfold RingFacts at hR
  intro θ x
  unfold datum
  congr 1
  funext j
  have h : rot θ x / ((radius sbar μ (j + 1) : ℝ) : ℂ) =
      rot θ (x / ((radius sbar μ (j + 1) : ℝ) : ℂ)) := by
    simp only [rot, mul_div_assoc]
  rw [h, hR.2.2.1 θ]

/-- Each term is continuous. -/
theorem continuous_term (hR : RingFacts χ) (c r : ℝ) :
    Continuous fun x : ℂ => c * ringPhi χ (x / (r : ℂ)) := by
  unfold RingFacts at hR
  exact continuous_const.mul (hR.1.continuous.comp (continuous_id.div_const _))

/-- `f` is measurable: the pointwise limit of the (continuous) partial sums. -/
theorem measurable_datum (hR : RingFacts χ) (hp : DatumParams A₁ μ sbar) :
    Measurable (datum χ A₁ μ sbar) := by
  refine measurable_of_tendsto_metrizable (f := fun n x => ∑ j ∈ Finset.range n,
    amp A₁ μ (j + 1) * ringPhi χ (x / ((radius sbar μ (j + 1) : ℝ) : ℂ))) (fun n => ?_) ?_
  · exact (continuous_finsetSum _ fun j _ => continuous_term hR _ _).measurable
  · rw [tendsto_pi_nhds]
    intro x
    exact (summable_terms hR hp x).hasSum.tendsto_sum_nat

end NonUniqueEuler.Datum.IntegrabilityH
