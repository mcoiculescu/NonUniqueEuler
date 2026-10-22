import NonUniqueEuler.Defs.Sec11.All
import NonUniqueEuler.I.Sec6.Adm
import NonUniqueEuler.I.SmoothB.Smooth
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Proof: the approximate solutions are weakly continuous in `L²` (used in `thm:main-explicit`)

Proof of `I/Sec11/ApproxWeakCont.lean` (`approx_weakCont`).

**Argument.** A deviation in route, not in content, from the sketch of the interface file: the
sketch goes through the flow representation `ω(t) = f ∘ Φ_t⁻¹`; here only thm:smooth(1)–(2) are
used (`Smooth.sol_isSmoothSol`): `(t, x) ↦ ω(t, x)` is continuous (`C^∞`) and
`supp ω(t) ⊂ B_{R(t)}` with `R(t) = R₀ + U_* |t|`. Then
1. `ω(t)` is continuous with compact support, so in `L²`;
2. for `ψ ∈ L²` and `t₀ ∈ ℝ`, on `t ∈ [t₀ - 1, t₀ + 1]` the integrand `ω(t, x) ψ(x)` is dominated
   by `M |ψ| 1_{B̄_R}` (`M` = the maximum of `|ω|` on the compact set `[t₀-1, t₀+1] × B̄_R`), which
   is integrable since `ψ ∈ L² ⊂ L¹_loc`; dominated convergence gives continuity at `t₀`.

The general fact is `isWeakContL2On_of_continuous_uncurry`.
-/

noncomputable section

open MeasureTheory Set Metric Filter

namespace NonUniqueEuler

namespace Datum

open RingData

/-- A jointly continuous space–time function whose slices are supported in a common closed disk
on every time interval `[-T, T]` is weakly continuous into `L²` on every time set `s`. -/
theorem isWeakContL2On_of_continuous_uncurry {ω : ℝ → ℂ → ℝ}
    (hc : Continuous (Function.uncurry ω))
    (hsupp : ∀ T : ℝ, ∃ R : ℝ, ∀ t ∈ Icc (-T) T, tsupport (ω t) ⊆ closedBall 0 R)
    (s : Set ℝ) : Weak.IsWeakContL2On s ω := by
  have hcx : ∀ t, Continuous (ω t) := fun t =>
    hc.comp (continuous_const.prodMk continuous_id)
  have hct : ∀ x, Continuous (fun t => ω t x) := fun x =>
    hc.comp (continuous_id.prodMk continuous_const)
  refine ⟨fun t _ => ?_, fun ψ hψ => ?_⟩
  · obtain ⟨R, hR⟩ := hsupp |t|
    have ht : t ∈ Icc (-|t|) |t| := ⟨neg_abs_le t, le_abs_self t⟩
    have hcs : HasCompactSupport (ω t) :=
      (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset (isClosed_tsupport _) (hR t ht)
    exact (hcx t).memLp_of_hasCompactSupport hcs
  · refine Continuous.continuousOn (continuous_iff_continuousAt.2 fun t₀ => ?_)
    obtain ⟨R, hR⟩ := hsupp (|t₀| + 1)
    have hK : Icc (t₀ - 1) (t₀ + 1) ⊆ Icc (-(|t₀| + 1)) (|t₀| + 1) := by
      intro t ht
      have h1 := neg_abs_le t₀
      have h2 := le_abs_self t₀
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    obtain ⟨M, hM⟩ := (isCompact_Icc.prod (isCompact_closedBall (0 : ℂ) R)).exists_bound_of_continuousOn
      (hc.continuousOn (s := Icc (t₀ - 1) (t₀ + 1) ×ˢ closedBall (0 : ℂ) R))
    have hψi : IntegrableOn ψ (closedBall (0 : ℂ) R) volume :=
      (hψ.locallyIntegrable one_le_two).integrableOn_isCompact (isCompact_closedBall 0 R)
    refine continuousAt_of_dominated
      (bound := (closedBall (0 : ℂ) R).indicator fun x => M * ‖ψ x‖)
      (Eventually.of_forall fun t => ((hcx t).aestronglyMeasurable.mul hψ.1)) ?_ ?_ ?_
    · filter_upwards [Icc_mem_nhds (by linarith : t₀ - 1 < t₀) (by linarith : t₀ < t₀ + 1)]
        with t ht
      refine Eventually.of_forall fun x => ?_
      by_cases hx : x ∈ closedBall (0 : ℂ) R
      · rw [indicator_of_mem hx, norm_mul]
        have hb : ‖ω t x‖ ≤ M := hM (t, x) ⟨ht, hx⟩
        gcongr
      · have h0 : ω t x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hR t (hK ht) h)
        rw [indicator_of_notMem hx, h0, zero_mul, norm_zero]
    · exact IntegrableOn.integrable_indicator (hψi.norm.const_mul M) measurableSet_closedBall
    · exact Eventually.of_forall fun x => ((hct x).mul continuous_const).continuousAt

/-- **`ω^{(n)}` is weakly continuous into `L²` on `[0, ∞)`** (used in `thm:main-explicit`,
`11_bootstrap.tex:694-708`, through `prop:defect`): under (N1)–(N3), for an admissible `χ`,
parameters as in `def:datum` and `κ_seed ∈ (0, κ_L]`, for every `n ≥ 2`. -/
theorem approx_weakCont (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {A₁ μ sbar κs : ℝ} (hp : DatumParams A₁ μ sbar) (hκ : κs ∈ Ioc 0 (OneRing.kL χ)) {n : ℕ}
    (hn : 2 ≤ n) :
    Weak.IsWeakContL2On (Ici 0) (Smooth.sol (approxDatum χ A₁ μ sbar κs n)) := by
  obtain ⟨hadm, -, -⟩ := adm χ hχ hN hp hκ
  obtain ⟨hsm, hcs, -⟩ := hadm n hn
  obtain ⟨R₀, hR₀⟩ := (isBounded_iff_subset_ball (0 : ℂ)).1 hcs.isCompact.isBounded
  have hsol := Smooth.sol_isSmoothSol (R₀ := R₀) ⟨hsm, hR₀⟩
  refine isWeakContL2On_of_continuous_uncurry hsol.contDiff.continuous (fun T => ?_) _
  refine ⟨Smooth.suppRadius (approxDatum χ A₁ μ sbar κs n) R₀ T, fun t ht =>
    (hsol.tsupport_subset t).trans (ball_subset_closedBall.trans
      (closedBall_subset_closedBall ?_))⟩
  exact Smooth.suppRadius_mono_abs _ R₀ ((abs_le.2 ⟨ht.1, ht.2⟩).trans (le_abs_self T))

end Datum

end NonUniqueEuler
