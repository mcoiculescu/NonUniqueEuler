import NonUniqueEuler.H.Sec3.Compact.Basic
import NonUniqueEuler.I.Sec2.Velocity

/-!
# Helpers for `prop:compact`: convergence of the velocities, property (iii)

Helper file of `P/Sec3/Compact.lean`. Manuscript: proof of `prop:compact`(iii)
(`03_compactness.tex:316-320`).

* `velocity_slice_tendsto`: for every `t ∈ [0,T]`, `vₙ(t) → v(t)` in `L²(B_R)`, by
  `lem:velocity`(b) (`BS.velocity_weak_tendsto_two`) and (i) at the time `t`.
* `velocity_tendsto_bochner`: (iii), `vₙ - v → 0` in `L^s(0,T; L²(B_R))`, `s ∈ [1,∞)`, by
  dominated convergence in `t` with the bound `‖vₙ(t) - v(t)‖_{L²(B_R)} ≤ 2 C(2,R) M`
  (`tendsto_eLpNorm_zero_of_dominated`, which needs no measurability in `t`).
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace NonUniqueEuler.Compact.PropCompact

open Weak

variable {T M : ℝ} {gs : ℕ → ℂ → ℝ} {g : ℂ → ℝ} {ωs : ℕ → ℝ → ℂ → ℝ}

/-- `L¹` membership from `L²` membership and a finite `L¹ ∩ L²` bound. -/
theorem memLp_one_of_normL1LpE_le {f : ℂ → ℝ} (h2 : MemLp f 2 volume)
    (hb : normL1LpE 2 f ≤ ENNReal.ofReal M) : MemLp f 1 volume :=
  ⟨h2.aestronglyMeasurable,
    ((eLpNorm_one_le_normL1LpE 2 _).trans hb).trans_lt ENNReal.ofReal_lt_top⟩

theorem normL1Lp_le_of_normL1LpE_le {f : ℂ → ℝ} (hM : 0 ≤ M) (h2 : MemLp f 2 volume)
    (hb : normL1LpE 2 f ≤ ENNReal.ofReal M) : Prelim.normL1Lp 2 f ≤ M := by
  rw [normL1Lp_eq_toReal (memLp_one_of_normL1LpE_le h2 hb) h2]
  exact ENNReal.toReal_le_of_le_ofReal hM hb

/-- `lem:velocity`(a) with `‖f‖_{L¹∩L²} ≤ M`: `v = K ∗ f ∈ L²(B_R)` with `‖v‖_{L²(B_R)} ≤ C M`. -/
theorem velocity_memLp_le {R C : ℝ} (hC0 : 0 < C)
    (hC : ∀ ω : ℂ → ℝ, MemLp ω 1 volume → MemLp ω 2 volume →
      (∀ᵐ x, Integrable (fun y => biotSavartKernel (x - y) * (ω y : ℂ)) volume) ∧
      Prelim.MemL1AddLinf (velocity ω) ∧
      MemLp (velocity ω) 2 (volume.restrict (ball (0 : ℂ) R)) ∧
      eLpNorm (velocity ω) 2 (volume.restrict (ball (0 : ℂ) R)) ≤
        ENNReal.ofReal (C * Prelim.normL1Lp 2 ω) ∧
      ∫⁻ x, ‖ω x‖ₑ * Conv.convAbs biotSavartKernel ω x ≤
        ENNReal.ofReal (C * Prelim.normL1Lp 2 ω ^ 2))
    (hM : 0 ≤ M) {f : ℂ → ℝ} (h2 : MemLp f 2 volume) (hb : normL1LpE 2 f ≤ ENNReal.ofReal M) :
    MemLp (velocity f) 2 (volume.restrict (ball (0 : ℂ) R)) ∧
      eLpNorm (velocity f) 2 (volume.restrict (ball (0 : ℂ) R)) ≤ ENNReal.ofReal (C * M) := by
  have h1 := memLp_one_of_normL1LpE_le h2 hb
  obtain ⟨-, -, hm, hle, -⟩ := hC f h1 h2
  exact ⟨hm, hle.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (normL1Lp_le_of_normL1LpE_le hM h2 hb) hC0.le))⟩

/-- For every `t ∈ [0,T]`, `vₙ(t) → v(t)` in `L²(B_R)` (`lem:velocity`(b) and (i)). -/
theorem velocity_slice_tendsto (h : IsCompactSeq T M gs g ωs) {ω : ℝ → ℂ → ℝ}
    (hi : WeakTendstoUnifL2On ωs ω (Icc 0 T)) (hω2 : ∀ t ∈ Icc 0 T, MemLp (ω t) 2 volume)
    {R : ℝ} (hR : 0 < R) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun n => eLpNorm (velocity (ωs n t) - velocity (ω t)) 2
      (volume.restrict (ball (0 : ℂ) R))) atTop (𝓝 0) := by
  have hconv : Prelim.WeakTendstoLp 2 (fun n => ωs n t) (ω t) :=
    weakTendstoLp_two_iff.2 ⟨fun n => seq_memLp_two h n ht, hω2 t ht,
      fun ψ hψ => (hi ψ hψ).tendsto_at ht⟩
  exact (BS.velocity_weak_tendsto_two hR hconv (fun n => seq_eLpNorm_one_le h n ht)).2

/-- **(iii) of `prop:compact`**: `K ∗ ωₙ → K ∗ ω` in `L^s(0,T;L²(B_R))`, `s ∈ [1,∞)`, `R > 0`. -/
theorem velocity_tendsto_bochner (h : IsCompactSeq T M gs g ωs) (hM : 0 ≤ M)
    {ω : ℝ → ℂ → ℝ} (hi : WeakTendstoUnifL2On ωs ω (Icc 0 T))
    (hω2 : ∀ t ∈ Icc 0 T, MemLp (ω t) 2 volume)
    (hωb : ∀ t ∈ Icc 0 T, normL1LpE 2 (ω t) ≤ ENNReal.ofReal M)
    (s : ℝ) (hs : 1 ≤ s) (R : ℝ) (hR : 0 < R) :
    Tendsto (fun n => bochnerNorm (ENNReal.ofReal s) 2 (Ioo 0 T) (ball (0 : ℂ) R)
      (fun t x => velocityField (ωs n) t x - velocityField ω t x)) atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := BS.velocity_bounds_two hR
  have hs0 : ENNReal.ofReal s ≠ 0 := (ENNReal.ofReal_pos.2 (by linarith)).ne'
  refine tendsto_eLpNorm_zero_of_dominated (c := ENNReal.ofReal (C * M) + ENNReal.ofReal (C * M))
    (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩) hs0
    ENNReal.ofReal_ne_top ?_ ?_
  · intro n
    refine ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => ?_
    have ht' := Ioo_subset_Icc_self ht
    have hn := velocity_memLp_le hC0 hC hM (seq_memLp_two h n ht') (h.bound n t ht')
    have hl := velocity_memLp_le hC0 hC hM (hω2 t ht') (hωb t ht')
    show eLpNorm (velocity (ωs n t) - velocity (ω t)) 2 (volume.restrict (ball (0 : ℂ) R)) ≤ _
    exact (eLpNorm_sub_le hn.1.aestronglyMeasurable hl.1.aestronglyMeasurable one_le_two).trans
      (add_le_add hn.2 hl.2)
  · refine ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => ?_
    exact velocity_slice_tendsto h hi hω2 hR (Ioo_subset_Icc_self ht)

end NonUniqueEuler.Compact.PropCompact
