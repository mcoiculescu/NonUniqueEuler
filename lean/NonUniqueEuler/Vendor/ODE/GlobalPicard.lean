import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Vendored: global Picard existence for globally Lipschitz vector fields

**Attribution.** Copied verbatim (only the namespace and the imports were changed) from the
OpenAI baseline repository `NavierStokesAndEuler` (Apache-2.0),
file `Euler/EulerProof.lean`, lines 18141-18310 (namespace `EulerPacketExistence`,
section `GlobalPicard`, and the theorem `exists_global_solution`).

Content: for a jointly continuous time-dependent vector field `f : ℝ → E → E` on a real Banach
space with a uniform global Lipschitz constant `K` in the state variable, there is a global
solution `u : ℝ → E` with `u 0 = x` and `HasDerivAt u (f t (u t)) t` for every `t`
(`NonUniqueEuler.Vendor.GlobalPicard.exists_global_solution`).
Used by `NonUniqueEuler/H/Evans/ODE/*` (the Evans ODE, `04_ring.tex` `def:evans`).
-/

open Function intervalIntegral MeasureTheory Metric Set
open scoped Nat NNReal Topology

namespace NonUniqueEuler.Vendor.GlobalPicard

section GlobalPicard

variable {E : Type*} [NormedAddCommGroup E]
  {a b : ℝ} (t₀ : Icc a b)

/-- Extend a continuous curve from a compact interval by endpoint values. -/
noncomputable def extendCurve (α : C(Icc a b, E)) (t : ℝ) : E :=
  α (projIcc a b (t₀.2.1.trans t₀.2.2) t)

theorem continuous_extendCurve (α : C(Icc a b, E)) : Continuous (extendCurve t₀ α) :=
  α.continuous.comp continuous_projIcc

theorem extendCurve_of_mem (α : C(Icc a b, E)) {t : ℝ} (ht : t ∈ Icc a b) :
    extendCurve t₀ α t = α ⟨t, ht⟩ := by
  simp only [extendCurve, projIcc_of_mem _ ht]

variable {f : ℝ → E → E} (hf : Continuous (uncurry f))

include hf

theorem continuous_comp_extendCurve (α : C(Icc a b, E)) :
    Continuous (fun t => f t (extendCurve t₀ α t)) :=
  hf.comp (continuous_id.prodMk (continuous_extendCurve t₀ α))

variable [NormedSpace ℝ E] [CompleteSpace E]

/-- The Volterra map on all continuous curves, without a spatial-radius
restriction.  Global Lipschitz continuity makes an iterate contractive. -/
noncomputable def picardStep (x : E) (α : C(Icc a b, E)) : C(Icc a b, E) :=
  ⟨fun t => x + ∫ s in t₀.1..t.1, f s (extendCurve t₀ α s),
    (continuous_const.add (intervalIntegral.differentiable_integral_of_continuous
      (continuous_comp_extendCurve t₀ hf α)).continuous).comp continuous_subtype_val⟩

theorem picardStep_apply (x : E) (α : C(Icc a b, E)) (t : Icc a b) :
    picardStep t₀ hf x α t = x + ∫ s in t₀.1..t.1, f s (extendCurve t₀ α s) := rfl

variable {K : ℝ≥0} (hLip : ∀ t, LipschitzWith K (f t))

include hLip

theorem picard_iterate_point_bound (x : E) (α β : C(Icc a b, E)) (n : ℕ) (t : Icc a b) :
    dist (((picardStep t₀ hf x)^[n]) α t) (((picardStep t₀ hf x)^[n]) β t) ≤
      (K * |t.1 - t₀.1|) ^ n / n ! * dist α β := by
  induction n generalizing t with
  | zero => simpa using ContinuousMap.dist_apply_le_dist (f := α) (g := β) t
  | succ n hn =>
    rw [iterate_succ_apply', iterate_succ_apply', dist_eq_norm, picardStep_apply,
      picardStep_apply, add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub
        ((continuous_comp_extendCurve t₀ hf _).intervalIntegrable _ _)
        ((continuous_comp_extendCurve t₀ hf _).intervalIntegrable _ _)]
    calc
      _ ≤ ∫ s in uIoc t₀.1 t.1, K ^ (n + 1) * |s - t₀.1| ^ n / n ! * dist α β := by
        rw [intervalIntegral.norm_intervalIntegral_eq]
        apply MeasureTheory.norm_integral_le_of_norm_le (Continuous.integrableOn_uIoc (by fun_prop))
        apply ae_restrict_mem measurableSet_Ioc |>.mono
        intro s hs
        have hsi : s ∈ Icc a b := (uIcc_subset_Icc t₀.2 t.2) (uIoc_subset_uIcc hs)
        rw [← dist_eq_norm, extendCurve_of_mem t₀ _ hsi, extendCurve_of_mem t₀ _ hsi]
        calc
          _ ≤ K * dist (((picardStep t₀ hf x)^[n]) α ⟨s, hsi⟩)
              (((picardStep t₀ hf x)^[n]) β ⟨s, hsi⟩) := (hLip s).dist_le_mul _ _
          _ ≤ K ^ (n + 1) * |s - t₀.1| ^ n / n ! * dist α β := by
            rw [pow_succ', mul_assoc, mul_div_assoc, mul_assoc]
            gcongr
            simpa only [mul_pow] using hn ⟨s, hsi⟩
      _ ≤ (K * |t.1 - t₀.1|) ^ (n + 1) / (n + 1) ! * dist α β := by
        apply le_of_abs_le
        rw [← intervalIntegral.abs_intervalIntegral_eq, intervalIntegral.integral_mul_const,
          intervalIntegral.integral_div, intervalIntegral.integral_const_mul, abs_mul, abs_div,
          abs_mul, intervalIntegral.abs_intervalIntegral_eq, integral_pow_abs_sub_uIoc, abs_div,
          abs_pow, abs_pow, abs_dist, NNReal.abs_eq, abs_abs, mul_div, div_div, ← abs_mul,
          ← Nat.cast_succ, ← Nat.cast_mul, ← Nat.factorial_succ, Nat.abs_cast, ← mul_pow]

theorem picard_iterate_bound (x : E) (α β : C(Icc a b, E)) (n : ℕ) :
    dist (((picardStep t₀ hf x)^[n]) α) (((picardStep t₀ hf x)^[n]) β) ≤
      (K * max (b - t₀.1) (t₀.1 - a)) ^ n / n ! * dist α β := by
  rw [ContinuousMap.dist_le]
  · intro t
    apply le_trans (picard_iterate_point_bound t₀ hf hLip x α β n t)
    gcongr
    exact abs_sub_le_max_sub t.2.1 t.2.2 _
  · have hmax : 0 ≤ max (b - t₀.1) (t₀.1 - a) := le_max_of_le_left (sub_nonneg.mpr t₀.2.2)
    positivity

theorem exists_picard_fixed_point (x : E) :
    ∃ α : C(Icc a b, E), IsFixedPt (picardStep t₀ hf x) α := by
  obtain ⟨n, hn⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop (K * max (b - t₀.1) (t₀.1 - a))
    |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
  have hnonneg : (0 : ℝ) ≤ (K * max (b - t₀.1) (t₀.1 - a)) ^ n / n ! := by
    have hmax : 0 ≤ max (b - t₀.1) (t₀.1 - a) := le_max_of_le_left (sub_nonneg.mpr t₀.2.2)
    positivity
  let C : ℝ≥0 := ⟨(K * max (b - t₀.1) (t₀.1 - a)) ^ n / n !, hnonneg⟩
  have hcontract : ContractingWith C ((picardStep t₀ hf x)^[n]) :=
    ⟨hn, LipschitzWith.of_dist_le_mul fun α β => picard_iterate_bound t₀ hf hLip x α β n⟩
  exact ⟨_, hcontract.isFixedPt_fixedPoint_iterate⟩

/-- A globally Lipschitz time-dependent vector field has a solution on
every finite interval.  Full derivatives also hold at the endpoints. -/
theorem exists_solution_on_compact_interval (x : E) :
    ∃ α : ℝ → E, α t₀.1 = x ∧
      ∀ t ∈ Icc a b, HasDerivAt α (f t (α t)) t := by
  obtain ⟨α, hfixed⟩ := exists_picard_fixed_point t₀ hf hLip x
  let u : ℝ → E := fun t => x + ∫ s in t₀.1..t, f s (extendCurve t₀ α s)
  have heq : ∀ t ∈ Icc a b, u t = extendCurve t₀ α t := by
    intro t ht
    have hh := congrArg (fun v : C(Icc a b, E) => v ⟨t, ht⟩) hfixed
    rw [extendCurve_of_mem t₀ α ht]
    exact hh
  have hc := continuous_comp_extendCurve t₀ hf α
  refine ⟨u, by simp [u], ?_⟩
  intro t ht
  have hd := (intervalIntegral.integral_hasDerivAt_right (a := t₀.1) (b := t) (hc.intervalIntegrable t₀.1 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add x
  change HasDerivAt u (f t (u t)) t
  rw [heq t ht]
  exact hd

end GlobalPicard

/-- Global existence for a jointly continuous vector field with a uniform
global Lipschitz constant in the state variable.  Finite-interval solutions
are glued using the proved ODE uniqueness theorem. -/
theorem exists_global_solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E → E} {K : ℝ≥0}
    (hf : Continuous (uncurry f)) (hLip : ∀ t, LipschitzWith K (f t)) (x : E) :
    ∃ u : ℝ → E, u 0 = x ∧ ∀ t, HasDerivAt u (f t (u t)) t := by
  classical
  have hlocal : ∀ R : ℝ, 0 < R → ∃ u : ℝ → E, u 0 = x ∧
      ∀ t ∈ Icc (-R) R, HasDerivAt u (f t (u t)) t := by
    intro R hR
    let t₀ : Icc (-R) R := ⟨0, by constructor <;> linarith⟩
    exact exists_solution_on_compact_interval t₀ hf hLip x
  choose v hv0 hvd using hlocal
  let u : ℝ → E := fun t => v (|t| + 1) (by positivity) t
  have hagree : ∀ R (hR : 0 < R), EqOn u (v R hR) (Ioo (-R) R) := by
    intro R hR s hs
    let R' := |s| + 1
    have hR' : 0 < R' := by dsimp [R']; positivity
    let B := min R R'
    have hB : 0 < B := lt_min hR hR'
    have hBR : B ≤ R := min_le_left _ _
    have hBR' : B ≤ R' := min_le_right _ _
    have hzero : (0 : ℝ) ∈ Ioo (-B) B := by constructor <;> linarith
    have hsB : s ∈ Ioo (-B) B := by
      apply abs_lt.mp
      apply lt_min (abs_lt.mpr hs)
      dsimp [R']
      linarith
    have heq := ODE_solution_unique_of_mem_Ioo (v := f) (s := fun _ => (univ : Set E))
      (fun t _ => (hLip t).lipschitzOnWith) hzero
      (fun t ht => ⟨hvd R hR t (by constructor <;> linarith [ht.1, ht.2]), mem_univ _⟩)
      (fun t ht => ⟨hvd R' hR' t (by constructor <;> linarith [ht.1, ht.2]), mem_univ _⟩)
      (by rw [hv0 R hR, hv0 R' hR'])
    exact (heq hsB).symm
  refine ⟨u, ?_, ?_⟩
  · exact hv0 (|0| + 1) (by positivity)
  · intro t
    let R := |t| + 1
    have hR : 0 < R := by dsimp [R]; positivity
    have ht : t ∈ Ioo (-R) R := by
      apply abs_lt.mp
      dsimp [R]
      linarith
    have heq : u =ᶠ[𝓝 t] v R hR := Filter.eventually_of_mem
      (Ioo_mem_nhds ht.1 ht.2) (fun s hs => hagree R hR hs)
    have hd := hvd R hR t (Ioo_subset_Icc_self ht)
    rw [hagree R hR ht]
    exact hd.congr_of_eventuallyEq heq

end NonUniqueEuler.Vendor.GlobalPicard
