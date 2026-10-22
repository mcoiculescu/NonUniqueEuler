import NonUniqueEuler.Vendor.Flow.BoundedLipschitzFlow
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Helper for `lem:ode`: cutting a `C^k` field off to a bounded, globally Lipschitz field

For `F ∈ C^k(U)` (`k ≥ 1`, `U ⊆ ℝ × E` open, `E` finite-dimensional) and a closed ball
`closedBall c (2ρ) ⊆ U` (sup norm on `ℝ × E`), `exists_cutoff_data` produces a vendored bounded
Lipschitz flow datum `V` (`Vendor/Flow/BoundedLipschitzFlow.lean`) whose field
`V.velocity = χ • F` (`χ` a smooth bump, `= 1` on `closedBall c ρ`, supported in
`closedBall c (2ρ)`) is `C^k` on `ℝ × E`, agrees with `F` on `closedBall c ρ` and satisfies
`‖V.velocity t x‖ ≤ ‖F t x‖`.

`local_flow_package` then gives, around each point `p ∈ U`, a box `I × 𝒰` on which the global
flow of `V` solves the original equation and stays in `ball p ρ ⊆ U`.
-/

noncomputable section

open Set Function Metric Filter
open scoped Topology NNReal

namespace NonUniqueEuler.Smooth.ODEH

open NonUniqueEuler.Vendor.BoundedLipschitzFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : ℝ → E → E} {U : Set (ℝ × E)}

/-- Cut-off of a `C^k` field on `U` to a bounded, globally Lipschitz `C^k` field on `ℝ × E`. -/
theorem exists_cutoff_data {k : ℕ} (hk : 1 ≤ k) (hU : IsOpen U)
    (hF : ContDiffOn ℝ k (uncurry F) U) {c : ℝ × E} {ρ : ℝ} (hρ : 0 < ρ)
    (hc : closedBall c (2 * ρ) ⊆ U) :
    ∃ V : Data E, ContDiff ℝ k (uncurry V.velocity) ∧
      (∀ q ∈ closedBall c ρ, uncurry V.velocity q = uncurry F q) ∧
      (∀ t x, ‖V.velocity t x‖ ≤ ‖F t x‖) := by
  let χ : ContDiffBump c := ⟨ρ, 2 * ρ, hρ, by linarith⟩
  let f : ℝ → E → E := fun t x => χ (t, x) • F t x
  have hfu : uncurry f = fun q => χ q • uncurry F q := rfl
  have hts : tsupport χ = closedBall c (2 * ρ) := χ.tsupport_eq
  have hcont : ContDiff ℝ k (uncurry f) := by
    rw [hfu, contDiff_iff_contDiffAt]
    intro q
    by_cases hq : q ∈ U
    · exact χ.contDiffAt.smul (hF.contDiffAt (hU.mem_nhds hq))
    · have hq' : q ∉ tsupport χ := by rw [hts]; exact fun h => hq (hc h)
      rw [notMem_tsupport_iff_eventuallyEq] at hq'
      have hev : (fun q => χ q • uncurry F q) =ᶠ[𝓝 q] fun _ => (0 : E) :=
        hq'.mono fun r hr => by simp [hr]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hcs : HasCompactSupport (uncurry f) := by
    rw [hfu]; exact χ.hasCompactSupport.smul_right
  obtain ⟨K, hK⟩ := hcont.lipschitzWith_of_hasCompactSupport hcs (by norm_cast; omega)
  obtain ⟨M, hM⟩ := (isCompact_closedBall c (2 * ρ)).exists_bound_of_continuousOn
    ((hF.continuousOn).mono hc)
  have hnorm : ∀ t x, ‖f t x‖ ≤ ‖F t x‖ := by
    intro t x
    simp only [f, norm_smul, Real.norm_eq_abs, abs_of_nonneg χ.nonneg]
    exact mul_le_of_le_one_left (norm_nonneg _) χ.le_one
  have hbound : ∀ t x, ‖f t x‖ ≤ max M 0 := by
    intro t x
    by_cases hq : (t, x) ∈ closedBall c (2 * ρ)
    · exact (hnorm t x).trans ((hM _ hq).trans (le_max_left _ _))
    · have h0 : χ (t, x) = 0 := by
        have : (t, x) ∉ support χ := fun h => hq (hts ▸ subset_tsupport _ h)
        simpa using this
      simp [f, h0]
  refine ⟨⟨f, hcont.continuous, K, fun t => ?_, ⟨max M 0, le_max_right _ _⟩,
    fun t x => hbound t x⟩, hcont, ?_, hnorm⟩
  · have h := hK.comp (LipschitzWith.prodMk_left t)
    rw [mul_one] at h
    exact h
  · intro q hq
    change χ q • uncurry F q = uncurry F q
    rw [χ.one_of_mem_closedBall hq, one_smul]

/-- Around each point `p ∈ U`: a cut-off datum `V`, a ball `ball p ρ ⊆ U` on which `V.velocity`
agrees with `F`, and a time `a ≤ ρ` such that the flow of `V` from `(s, y)`,
`s ∈ (p.1 - a, p.1 + a)`, `y ∈ ball p.2 (ρ/2)`, stays in `ball p ρ` for times in
`(p.1 - a, p.1 + a)`. -/
theorem local_flow_package {k : ℕ} (hk : 1 ≤ k) (hU : IsOpen U)
    (hF : ContDiffOn ℝ k (uncurry F) U) {p : ℝ × E} (hp : p ∈ U) :
    ∃ (V : Data E) (ρ a : ℝ), 0 < ρ ∧ 0 < a ∧ a ≤ ρ ∧ ContDiff ℝ k (uncurry V.velocity) ∧
      ball p ρ ⊆ U ∧ (∀ q ∈ ball p ρ, uncurry V.velocity q = uncurry F q) ∧
      ∀ s ∈ Ioo (p.1 - a) (p.1 + a), ∀ t ∈ Ioo (p.1 - a) (p.1 + a), ∀ y ∈ ball p.2 (ρ / 2),
        (t, V.flow s t y) ∈ ball p ρ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU p hp
  set ρ := ε / 3 with hρdef
  have hρ : 0 < ρ := by positivity
  have hc : closedBall p (2 * ρ) ⊆ U := (closedBall_subset_ball (by linarith)).trans hball
  obtain ⟨V, hVc, hVeq, -⟩ := exists_cutoff_data hk hU hF hρ hc
  set M : ℝ := (V.speedBound : ℝ) with hMdef
  have hM : 0 ≤ M := V.speedBound.2
  set a := min ρ (ρ / (4 * (M + 1))) with hadef
  have ha : 0 < a := lt_min hρ (by positivity)
  have haρ : a ≤ ρ := min_le_left _ _
  have ha' : a ≤ ρ / (4 * (M + 1)) := min_le_right _ _
  refine ⟨V, ρ, a, hρ, ha, haρ, hVc, (ball_subset_ball (by linarith)).trans hball,
    fun q hq => hVeq q (ball_subset_closedBall hq), ?_⟩
  intro s hs t ht y hy
  have hts : |t - s| ≤ 2 * a := by
    rw [abs_le]; constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  have hd : dist (V.flow s t y) y ≤ M * |t - s| := by
    have := (V.flow_lipschitz_time s y).dist_le_mul t s
    simpa [V.flow_initial, Real.dist_eq] using this
  have hMa : M * |t - s| < ρ / 2 := by
    have h1 : M * |t - s| ≤ M * (2 * a) := mul_le_mul_of_nonneg_left hts hM
    have h2 : M * (2 * a) ≤ M * (2 * (ρ / (4 * (M + 1)))) :=
      mul_le_mul_of_nonneg_left (by linarith) hM
    have h3 : M * (2 * (ρ / (4 * (M + 1)))) < ρ / 2 := by
      rw [show M * (2 * (ρ / (4 * (M + 1)))) = ρ / 2 * (M / (M + 1)) by field_simp; ring]
      have : M / (M + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
      nlinarith
    linarith
  rw [mem_ball, Prod.dist_eq]
  refine max_lt ?_ ?_
  · rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2]
  · have hy' : dist y p.2 < ρ / 2 := hy
    calc dist (V.flow s t y) p.2 ≤ dist (V.flow s t y) y + dist y p.2 := dist_triangle _ _ _
      _ < ρ / 2 + ρ / 2 := by linarith
      _ = ρ := by ring

end NonUniqueEuler.Smooth.ODEH
