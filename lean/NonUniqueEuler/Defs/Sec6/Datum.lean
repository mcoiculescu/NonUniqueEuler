import NonUniqueEuler.Statement.Datum
import NonUniqueEuler.Defs.Sec5.All

/-!
# Section 6.1: the datum and the approximate data (definitions)

Manuscript `06_datum.tex:15-136`
(`def:datum`, `prop:integrability`, `def:approx`, `lem:adm`) and `06_datum.tex:504-527`
(`lem:Lq-growth`).

The datum `f = Σ_{k ≥ 1} A_k Φ(·/r_k)` and its parameters `A_k = amp`, `s_k = ratio`,
`r_k = radius` are in the statement layer (`Statement/Datum.lean`); this file adds their
basic API and the approximate data of `def:approx`:
* `approxTerm χ A₁ μ sbar κs n k` is the `k`-th term `f^{(n)}_k` of `f^{(n)}` (`def:regions`,
  first item): `A_k Φ(·/r_k)` for `1 ≤ k < n`, `A_n Φ^{κ_seed}(·/r_n)` for `k = n`, `0` otherwise;
* `approxDatum χ A₁ μ sbar κs n = f^{(n)} = Σ_{k=1}^{n} f^{(n)}_k` (`def:approx`);
* `alphaMu μ`, `psiTheta p₀ θ y` (`lem:Lq-growth`, off the path to the main theorem).

Indices are natural numbers with the manuscript's meaning (`k ≥ 1`; the value at `k = 0` is
never used). The seeded ring `Φ^κ` is `OneRing.PhiSeed χ κ` (`Defs/Sec5/Seed.lean`), meaningful
for `κ ∈ (0, κ_L]`, `κ_L = OneRing.kL χ`, under (N1)–(N3).

All lemmas here are fully proved.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Datum

open RingData

/-! ### `def:datum`: basic API of `A_k`, `s_k`, `r_k` -/

@[simp] theorem amp_one (A₁ μ : ℝ) : amp A₁ μ 1 = A₁ := by
  simp [amp]

/-- `A_{k+1} = μ A_k` for `k ≥ 1` (`06_datum.tex:19`). -/
theorem amp_succ (A₁ μ : ℝ) {k : ℕ} (hk : 1 ≤ k) : amp A₁ μ (k + 1) = μ * amp A₁ μ k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp [amp, pow_succ]
  ring

theorem amp_pos {A₁ μ : ℝ} (hA : 0 < A₁) (hμ : 0 < μ) (k : ℕ) : 0 < amp A₁ μ k :=
  mul_pos hA (pow_pos hμ _)

theorem ratio_pos {sbar μ : ℝ} (hs : 0 < sbar) (hμ : 0 < μ) (k : ℕ) : 0 < ratio sbar μ k :=
  div_pos hs (pow_pos (by linarith) _)

@[simp] theorem radius_one (sbar μ : ℝ) : radius sbar μ 1 = 1 := by
  simp [radius]

/-- `r_{k+1} = s_k r_k` for `k ≥ 1` (`06_datum.tex:19`). -/
theorem radius_succ (sbar μ : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    radius sbar μ (k + 1) = ratio sbar μ k * radius sbar μ k := by
  rw [radius, Finset.prod_Ico_succ_top hk, radius, mul_comm]

theorem radius_pos {sbar μ : ℝ} (hs : 0 < sbar) (hμ : 0 < μ) (k : ℕ) : 0 < radius sbar μ k :=
  Finset.prod_pos fun j _ => ratio_pos hs hμ j

/-! ### `def:approx`: the approximate data `f^{(n)}` -/

/-- The `k`-th term `f^{(n)}_k` of the approximate datum (`def:regions`, `06_datum.tex:162-164`;
`def:approx`, `06_datum.tex:76`): `A_k Φ(·/r_k)` for `1 ≤ k < n`, `A_n Φ^{κ_seed}(·/r_n)` for
`k = n`, and `0` for the indices `k = 0` and `k > n`, which do not occur. -/
def approxTerm (χ : ℝ → ℝ) (A₁ μ sbar κs : ℝ) (n k : ℕ) (x : ℂ) : ℝ :=
  if 1 ≤ k ∧ k < n then amp A₁ μ k * ringPhi χ (x / ((radius sbar μ k : ℝ) : ℂ))
  else if k = n then amp A₁ μ k * OneRing.PhiSeed χ κs (x / ((radius sbar μ k : ℝ) : ℂ))
  else 0

/-- **The approximate datum** `f^{(n)} = Σ_{k<n} A_k Φ(·/r_k) + A_n Φ^{κ_seed}(·/r_n)`
(`def:approx`, `06_datum.tex:71-81`), written as `Σ_{k=1}^{n} f^{(n)}_k`. The manuscript takes
`n ≥ 2` and `κ_seed ∈ (0, κ_L]`, under (N1)–(N3) (`Datum.Approx.Valid`). -/
def approxDatum (χ : ℝ → ℝ) (A₁ μ sbar κs : ℝ) (n : ℕ) (x : ℂ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, approxTerm χ A₁ μ sbar κs n k x

theorem approxTerm_of_lt {χ : ℝ → ℝ} {A₁ μ sbar κs : ℝ} {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n)
    (x : ℂ) :
    approxTerm χ A₁ μ sbar κs n k x = amp A₁ μ k * ringPhi χ (x / ((radius sbar μ k : ℝ) : ℂ)) := by
  simp [approxTerm, hk, hkn]

theorem approxTerm_self {χ : ℝ → ℝ} {A₁ μ sbar κs : ℝ} {n : ℕ} (x : ℂ) :
    approxTerm χ A₁ μ sbar κs n n x =
      amp A₁ μ n * OneRing.PhiSeed χ κs (x / ((radius sbar μ n : ℝ) : ℂ)) := by
  simp [approxTerm]

theorem approxTerm_of_gt {χ : ℝ → ℝ} {A₁ μ sbar κs : ℝ} {n k : ℕ} (hk : n < k) (x : ℂ) :
    approxTerm χ A₁ μ sbar κs n k x = 0 := by
  have h1 : ¬ (1 ≤ k ∧ k < n) := fun h => by omega
  have h2 : k ≠ n := by omega
  simp [approxTerm, h1, h2]

theorem approxTerm_zero {χ : ℝ → ℝ} {A₁ μ sbar κs : ℝ} {n : ℕ} (hn : 1 ≤ n) (x : ℂ) :
    approxTerm χ A₁ μ sbar κs n 0 x = 0 := by
  have h2 : (0 : ℕ) ≠ n := by omega
  simp [approxTerm, h2]

/-- The splitting `f^{(n)} = Σ_{i<k} f^{(n)}_i + f^{(n)}_k + Σ_{i>k} f^{(n)}_i` for `1 ≤ k ≤ n`
(the three parts of the datum in ring-`k` units, `06_datum.tex:323-330`). -/
theorem approxDatum_split (χ : ℝ → ℝ) (A₁ μ sbar κs : ℝ) {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (x : ℂ) :
    approxDatum χ A₁ μ sbar κs n x =
      (∑ i ∈ Finset.Ico 1 k, approxTerm χ A₁ μ sbar κs n i x) +
        approxTerm χ A₁ μ sbar κs n k x +
        ∑ i ∈ Finset.Ioc k n, approxTerm χ A₁ μ sbar κs n i x := by
  rw [approxDatum, ← Finset.Ico_add_one_right_eq_Icc, ← Finset.Ico_add_one_add_one_eq_Ioc,
    ← Finset.sum_Ico_consecutive _ hk (by omega : k ≤ n + 1),
    Finset.sum_eq_sum_Ico_succ_bot (by omega : k < n + 1)]
  ring

/-! ### `lem:Lq-growth` (`06_datum.tex:504-527`; not used for the main theorem, R13) -/

/-- `α_μ = (log μ)² / (4 log(2μ))` (`lem:Lq-growth`, `06_datum.tex:507`). -/
def alphaMu (μ : ℝ) : ℝ := Real.log μ ^ 2 / (4 * Real.log (2 * μ))

/-- `ψ_θ(y) = inf{ y^ε ε⁻¹ θ(1/ε) : 0 < ε ≤ 1/p₀ }` (`lem:Lq-growth`(2), `06_datum.tex:514-515`),
as a real infimum (the set is bounded below by `0` when `θ > 0` and `y ≥ 1`). -/
def psiTheta (p₀ : ℝ) (θ : ℝ → ℝ) (y : ℝ) : ℝ :=
  sInf ((fun ε : ℝ => y ^ ε * ε⁻¹ * θ (1 / ε)) '' Ioc 0 (1 / p₀))

end Datum

end NonUniqueEuler
