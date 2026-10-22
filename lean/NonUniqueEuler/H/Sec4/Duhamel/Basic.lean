import NonUniqueEuler.Defs.Sec4.Linear
import NonUniqueEuler.Defs.Sec4.Bridge
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.Module.Star

/-!
# Helper for `lem:duhamel`: generic facts (joint continuity, `X^s`, real elements)

Helper of `P/Sec4/Duhamel.lean`.

* `DuhamelAux.continuousOn_apply_of_bound`: a family of continuous linear maps that is bounded and
  strongly continuous on a set `J` of times is jointly continuous on `J × E`;
* `DuhamelAux.exists_memX_iff`, `DuhamelAux.exists_isReal_iff`: `X^s` is the kernel of a
  continuous linear map, and "real" is the equalizer of a continuous antilinear and a continuous
  linear map;
* `DuhamelAux.intervalIntegral_memX`, `DuhamelAux.intervalIntegral_isReal`: an integrable path
  with values in `X^s` (in the real elements) on `[a, b]` has its integral in `X^s` (real);
* `DuhamelAux.memX_add`, `DuhamelAux.isReal_add`: sums.

The `X^s` / real-element lemmas are copies (renamed namespace) of the proved lemmas of
`H/Sec5/Running/Bridge.lean` (that helper file cannot be imported here (import rules, `README.md`)).
-/

noncomputable section

open MeasureTheory Set Filter Topology ComplexConjugate

namespace NonUniqueEuler.Lin.DuhamelAux

open Sect Sob RingData

/-! ### Joint continuity of bounded, strongly continuous families -/

/-- A family `t ↦ A t` of continuous linear maps that is bounded by `B` and strongly continuous
on `J` is jointly continuous on `J × E`. -/
theorem continuousOn_apply_of_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {A : ℝ → E →L[ℂ] F} {J : Set ℝ} {B : ℝ}
    (hB : ∀ t ∈ J, ‖A t‖ ≤ B) (hc : ∀ x, ContinuousOn (fun t => A t x) J) :
    ContinuousOn (fun p : ℝ × E => A p.1 p.2) (J ×ˢ univ) := by
  rintro ⟨t₀, x₀⟩ ⟨ht₀, -⟩
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.continuousWithinAt_iff.1 (hc x₀ t₀ ht₀) (ε / 2) (half_pos hε)
  set B' : ℝ := max B 0 + 1 with hB'
  have hB'pos : 0 < B' := by positivity
  refine ⟨min δ₁ (ε / (2 * B')), lt_min hδ₁ (by positivity), ?_⟩
  rintro ⟨t, x⟩ ⟨ht, -⟩ hd
  rw [Prod.dist_eq, max_lt_iff] at hd
  obtain ⟨hdt, hdx⟩ := hd
  have hdt' : dist t t₀ < δ₁ := lt_of_lt_of_le hdt (min_le_left _ _)
  have hdx' : dist x x₀ < ε / (2 * B') := lt_of_lt_of_le hdx (min_le_right _ _)
  have hA : ‖A t‖ ≤ B' := le_trans (hB t ht) (le_trans (le_max_left _ _) (by linarith))
  have e1 : dist (A t x) (A t x₀) ≤ ε / 2 := by
    rw [dist_eq_norm, ← map_sub]
    calc ‖A t (x - x₀)‖ ≤ ‖A t‖ * ‖x - x₀‖ := (A t).le_opNorm _
      _ ≤ B' * ‖x - x₀‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg _)
      _ ≤ B' * (ε / (2 * B')) := by
          rw [← dist_eq_norm]
          exact mul_le_mul_of_nonneg_left hdx'.le hB'pos.le
      _ = ε / 2 := by field_simp
  have e2 : dist (A t x₀) (A t₀ x₀) < ε / 2 := h₁ ht hdt'
  calc dist (A t x) (A t₀ x₀) ≤ dist (A t x) (A t x₀) + dist (A t x₀) (A t₀ x₀) :=
        dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt e1 e2
    _ = ε := add_halves ε

/-! ### `X^s` and real elements (copied from `H/Sec5/Running/Bridge.lean`) -/

/-- `X^s` is the kernel of a continuous linear map on `Y^s(N)`. -/
theorem exists_memX_iff (s : ℕ) :
    ∃ T : Y s annN →L[ℂ] Lp ℂ 2 (volume : Measure ℂ), ∀ w : Y s annN, Lin.MemX w ↔ T w = 0 := by
  refine ⟨((Ang.rotLp (2 * Real.pi / (3 : ℕ)) - ContinuousLinearMap.id ℂ _).comp (proj0 s)).comp
    (YSub s annN).subtypeL, fun w => ?_⟩
  rw [Lin.memX_iff, YsymSub, Submodule.mem_inf, LinearMap.mem_ker]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    exact ⟨w.2, h⟩

/-- "Real" is the equalizer of a continuous antilinear map and a continuous linear map. -/
theorem exists_isReal_iff (s : ℕ) (K : Set ℂ) :
    ∃ (C : Y s K →SL[starRingEnd ℂ] Lp ℂ 2 (volume : Measure ℂ))
      (P : Y s K →L[ℂ] Lp ℂ 2 (volume : Measure ℂ)), ∀ w : Y s K, w.IsReal ↔ C w = P w := by
  set P : Y s K →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) := (proj0 s).comp (YSub s K).subtypeL
  set Cst : ℂ →SL[starRingEnd ℂ] ℂ := (starL ℂ : ℂ ≃L⋆[ℂ] ℂ).toContinuousLinearMap
  set C : Y s K →SL[starRingEnd ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
    (Cst.compLpL 2 (volume : Measure ℂ)).comp P
  refine ⟨C, P, fun w => ?_⟩
  have hP : ((P w : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) = w.fn := rfl
  have hC : ((C w : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) =ᵐ[volume] fun x => conj (w.fn x) := by
    have := Cst.coeFn_compLpL (p := 2) (μ := (volume : Measure ℂ)) (P w)
    filter_upwards [this] with x hx
    show ((Cst.compLpL 2 (volume : Measure ℂ) (P w) : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) x = _
    rw [hx, hP]
    rfl
  constructor
  · intro hw
    refine Lp.ext ?_
    rw [hP]
    filter_upwards [hC, hw] with x h1 h2
    rw [h1]
    exact Complex.conj_eq_iff_im.2 h2
  · intro h
    have h' : ((C w : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) =ᵐ[volume]
        ((P w : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) := by rw [h]
    rw [hP] at h'
    filter_upwards [hC, h'] with x h1 h2
    rw [h1] at h2
    exact Complex.conj_eq_iff_im.1 h2

/-- The kernel of a continuous linear map is closed under interval integrals of integrable paths
with values in it on `[a, b]`. -/
theorem intervalIntegral_mem_ker {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (T : E →L[ℂ] F) {f : ℝ → E} {a b : ℝ} (hab : a ≤ b) (hf : IntervalIntegrable f volume a b)
    (h0 : ∀ v ∈ Icc a b, T (f v) = 0) : T (∫ v in a..b, f v) = 0 := by
  rw [← T.intervalIntegral_comp_comm hf]
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : F))]
  · simp
  · intro v hv
    rw [uIcc_of_le hab] at hv
    exact h0 v hv

/-- The equalizer of a continuous antilinear and a continuous linear map is closed under interval
integrals of integrable paths with values in it on `[a, b]`. -/
theorem intervalIntegral_eq_of_eq {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (C : E →SL[starRingEnd ℂ] F) (P : E →L[ℂ] F) {f : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) (h0 : ∀ v ∈ Icc a b, C (f v) = P (f v)) :
    C (∫ v in a..b, f v) = P (∫ v in a..b, f v) := by
  have hfi : IntegrableOn f (Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hf
  rw [intervalIntegral.integral_of_le hab]
  rw [← ContinuousLinearMap.integral_comp_commSL (fun r x => by simp) C hfi,
    ← P.integral_comp_comm hfi]
  refine setIntegral_congr_fun measurableSet_Ioc fun v hv => h0 v (Ioc_subset_Icc_self hv)

/-- An integrable path in `X^s` on `[a, b]` has its integral in `X^s`. -/
theorem intervalIntegral_memX {s : ℕ} {f : ℝ → Y s annN} {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) (hX : ∀ v ∈ Icc a b, Lin.MemX (f v)) :
    Lin.MemX (∫ v in a..b, f v) := by
  obtain ⟨T, hT⟩ := exists_memX_iff s
  rw [hT]
  exact intervalIntegral_mem_ker T hab hf fun v hv => (hT _).1 (hX v hv)

/-- An integrable path of real elements of `Y^s(K)` on `[a, b]` has a real integral. -/
theorem intervalIntegral_isReal {s : ℕ} {K : Set ℂ} {f : ℝ → Y s K} {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) (hR : ∀ v ∈ Icc a b, (f v).IsReal) :
    (∫ v in a..b, f v).IsReal := by
  obtain ⟨C, P, hCP⟩ := exists_isReal_iff s K
  rw [hCP]
  exact intervalIntegral_eq_of_eq C P hab hf fun v hv => (hCP _).1 (hR v hv)

/-- Sums of real elements are real. -/
theorem isReal_add {s : ℕ} {K : Set ℂ} {w w' : Y s K} (hw : w.IsReal) (hw' : w'.IsReal) :
    (w + w').IsReal := by
  obtain ⟨C, P, hCP⟩ := exists_isReal_iff s K
  rw [hCP] at hw hw' ⊢
  rw [map_add, map_add, hw, hw']

/-- Sums of elements of `X^s` lie in `X^s`. -/
theorem memX_add {s : ℕ} {w w' : Y s annN} (hw : Lin.MemX w) (hw' : Lin.MemX w') :
    Lin.MemX (w + w') := by
  obtain ⟨T, hT⟩ := exists_memX_iff s
  rw [hT] at hw hw' ⊢
  rw [map_add, hw, hw', add_zero]

end NonUniqueEuler.Lin.DuhamelAux
