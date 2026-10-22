import NonUniqueEuler.Defs.Sec6.All
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.H.Sec6.Integrability.Radii
import NonUniqueEuler.H.Sec6.Integrability.Terms
import NonUniqueEuler.H.Sec6.Integrability.Lq

/-!
# Proof: `prop:integrability` (the datum `f`)

Proof of `I/Sec6/Integrability.lean` (`06_datum.tex:27-66`); the statement is copied verbatim.

Uses `ringFacts_of_admissible` (`I/Sec4/RingFacts.lean`, `lem:ring-facts`) and the helpers
`H/Sec6/Integrability/{Radii,Terms,Lq}.lean`:
* disjoint annuli and the formula for `log(1/r_k)`: `IntegrabilityH.annuli_disjoint`,
  `IntegrabilityH.log_inv_radius`;
* at most one nonzero term, summability, radial, `f ≥ 0`: `IntegrabilityH.phi_eq_zero_of_ne`,
  `summable_terms`, `datum_radial`, `datum_nonneg`;
* `Σ A_k^q r_k² < ∞` (ratio test): `IntegrabilityH.summable_amp_rpow_mul_radius_sq`;
* `f ∈ L^q`, `f ∉ L^∞`: `IntegrabilityH.memLp_datum`, `IntegrabilityH.not_memLp_top`.

Deviation (minor): `f ∈ L^q` is proved from the pointwise bound `|f|^q ≤ Σ_k A_k^q 1_{B̄_{r_k}}`
(so `∫|f|^q ≤ π Σ_k A_k^q r_k²`) rather than from the identity
`∫ f^q = Σ_k A_k^q r_k² ‖Φ‖_q^q`; only finiteness is claimed.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Datum

open RingData

/-- **`prop:integrability`** (`06_datum.tex:27-34`). For an admissible cutoff and parameters as in
`def:datum`: `DatumProperties` (disjoint annuli, `f` radial, `f ≥ 0`, `f ∈ L¹ ∩ L^q` for
`q ∈ [1,∞)`, `f ∉ L^∞`); at every point at most one term of the series is nonzero and the series
is summable (`06_datum.tex:44-46`); `log(1/r_k) = (k-1)log(1/s̄) + k(k-1)/2 · log(2μ)` for `k ≥ 1`;
and `Σ_{k ≥ 1} A_k^q r_k² < ∞` for every real `q ≥ 1`. -/
theorem integrability (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) {A₁ μ sbar : ℝ}
    (hp : DatumParams A₁ μ sbar) :
    DatumProperties χ A₁ μ sbar ∧
    (∀ (x : ℂ) (j l : ℕ), j ≠ l → ringPhi χ (x / ((radius sbar μ (j + 1) : ℝ) : ℂ)) ≠ 0 →
      ringPhi χ (x / ((radius sbar μ (l + 1) : ℝ) : ℂ)) = 0) ∧
    (∀ x : ℂ, Summable fun j : ℕ =>
      amp A₁ μ (j + 1) * ringPhi χ (x / ((radius sbar μ (j + 1) : ℝ) : ℂ))) ∧
    (∀ k : ℕ, 1 ≤ k → Real.log (1 / radius sbar μ k) =
      ((k : ℝ) - 1) * Real.log (1 / sbar) + (k : ℝ) * ((k : ℝ) - 1) / 2 * Real.log (2 * μ)) ∧
    ∀ q : ℝ, 1 ≤ q → Summable fun j : ℕ => amp A₁ μ (j + 1) ^ q * radius sbar μ (j + 1) ^ 2 := by
  have hR : RingFacts χ := ringFacts_of_admissible hχ
  have hμ0 : 0 < μ := by linarith [hp.one_lt_μ]
  refine ⟨⟨IntegrabilityH.annuli_disjoint hp, IntegrabilityH.datum_radial hR,
    IntegrabilityH.datum_nonneg hR hp, fun q hq => IntegrabilityH.memLp_datum hR hp hq,
    IntegrabilityH.not_memLp_top hR hp⟩,
    fun x j l hjl hj => IntegrabilityH.phi_eq_zero_of_ne hR hp x j l hjl hj,
    IntegrabilityH.summable_terms hR hp,
    IntegrabilityH.log_inv_radius hp.sbar_pos hμ0,
    fun q _ => IntegrabilityH.summable_amp_rpow_mul_radius_sq hp q⟩

end Datum

end NonUniqueEuler
