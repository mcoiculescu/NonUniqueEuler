import NonUniqueEuler.Defs.Sec4.Eigendata
import NonUniqueEuler.I.Infra.Polar.Fubini
import NonUniqueEuler.I.Infra.Sobolev.Space
import NonUniqueEuler.I.Infra.Sobolev.Norm
import NonUniqueEuler.I.Infra.Sobolev.NormDeriv

/-!
# Helpers for `lem:seed`: `ℓ_*` only sees the a.e. class; functions of `Y^s(K)`

Helper of `P/Sec5/Seed.lean`.

* `SeedH.ae_circle_of_ae`, `SeedH.angularSector_congr_ae`, `SeedH.ellFn_congr_ae`: if `f = g`
  a.e. on the plane, then `ℓ_*(G)(f) = ℓ_*(G)(g)` (Tonelli in polar coordinates).
* `SeedH.Y_memH_fn`, `SeedH.Y_fn_zero_outside`, `SeedH.Y_fn_sub`, `SeedH.Y_fn_add`,
  `SeedH.Y_fn_smul`, `SeedH.exists_Y_of_memH`: the function of `w ∈ Y^s(K)` lies in `H^s` with
  `‖w.fn‖_{H^s} = ‖w‖`, vanishes a.e. outside `K`, is linear a.e.; conversely an `H^s` function
  vanishing a.e. outside `K` is the function of an element of `Y^s(K)`.

The first group and `Y_memH_fn` … `exists_Y_of_memH` are copied (namespace renamed) from
`H/Sec5/QuietHandoff/Basic.lean` (proof `Sec5/QuietHandoff`), which this proof may
not import (import rules, `README.md`).
-/

noncomputable section

open MeasureTheory Set Real Filter
open scoped ENNReal

namespace NonUniqueEuler.OneRing.SeedH

open Sect Sob

/-! ### `ℓ_*` only sees the a.e. class -/

/-- The polar parametrization `(r, θ) ↦ r e^{iθ}` is continuous. -/
theorem continuous_circleMap_prod :
    Continuous fun p : ℝ × ℝ => circleMap 0 p.1 p.2 := by
  simp only [circleMap, zero_add]
  exact (Complex.continuous_ofReal.comp continuous_fst).mul
    (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))

/-- If `f = g` a.e. on the plane, then for a.e. `r > 0`, `f = g` a.e. on the circle of
radius `r` (parametrized by `θ ∈ (0, 2π]`). -/
theorem ae_circle_of_ae {f g : ℂ → ℂ} (h : f =ᵐ[volume] g) :
    ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), ∀ᵐ θ ∂(volume.restrict (Ioc (0 : ℝ) (2 * π))),
      f (circleMap 0 r θ) = g (circleMap 0 r θ) := by
  set N : Set ℂ := toMeasurable volume {x | ¬ f x = g x} with hNdef
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : volume N = 0 := by
    rw [hNdef, measure_toMeasurable]
    exact h
  have hsub : {x | ¬ f x = g x} ⊆ N := subset_toMeasurable _ _
  set F : ℂ → ℝ≥0∞ := N.indicator 1 with hFdef
  have hFm : Measurable F := measurable_one.indicator hNm
  have hFc : Measurable fun p : ℝ × ℝ => F (circleMap 0 p.1 p.2) :=
    hFm.comp continuous_circleMap_prod.measurable
  have hI : ∫⁻ x, F x = 0 := by
    rw [hFdef, lintegral_indicator_one hNm]
    exact hN0
  rw [Polar.lintegral_eq_lintegral_Ioi_circle hFm] at hI
  have hmeas : Measurable fun r : ℝ =>
      ENNReal.ofReal r * ∫⁻ θ in Ioc (0 : ℝ) (2 * π), F (circleMap 0 r θ) :=
    ENNReal.measurable_ofReal.mul (hFc.lintegral_prod_right' (ν := volume.restrict _))
  have h0 := (lintegral_eq_zero_iff hmeas).1 hI
  have hpos : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), r ∈ Ioi (0 : ℝ) :=
    ae_restrict_mem measurableSet_Ioi
  filter_upwards [h0, hpos] with r hr hrpos
  have hr' : ENNReal.ofReal r * ∫⁻ θ in Ioc (0 : ℝ) (2 * π), F (circleMap 0 r θ) = 0 := hr
  rcases mul_eq_zero.1 hr' with h1 | h1
  · exact absurd h1 (ENNReal.ofReal_pos.2 hrpos).ne'
  · have h2 := (lintegral_eq_zero_iff (hFm.comp (continuous_circleMap 0 r).measurable)).1 h1
    filter_upwards [h2] with θ hθ
    by_contra hne
    have hmem : circleMap 0 r θ ∈ N := hsub hne
    have h3 : F (circleMap 0 r θ) = 1 := by
      rw [hFdef, Set.indicator_of_mem hmem]
      rfl
    have h4 : F (circleMap 0 r θ) = 0 := hθ
    rw [h3] at h4
    exact one_ne_zero h4

/-- The angular sectors of a.e. equal functions agree a.e. on `(0, ∞)`. -/
theorem angularSector_congr_ae {f g : ℂ → ℂ} (h : f =ᵐ[volume] g) (ℓ : ℤ) :
    Polar.angularSector f ℓ =ᵐ[volume.restrict (Ioi (0 : ℝ))] Polar.angularSector g ℓ := by
  filter_upwards [ae_circle_of_ae h] with r hr
  unfold Polar.angularSector
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  rw [uIoc_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
  rw [ae_restrict_iff' measurableSet_Ioc] at hr
  filter_upwards [hr] with θ hθ hmem
  have hc : ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = circleMap 0 r θ := by
    simp [circleMap]
  rw [hc, hθ hmem]

/-- `ℓ_*(G)` on functions (`Eig.ellFn`) only depends on the a.e. class. -/
theorem ellFn_congr_ae (χ : ℝ → ℝ) (G : ℝ) {f g : ℂ → ℂ} (h : f =ᵐ[volume] g) :
    Eig.ellFn χ G f = Eig.ellFn χ G g := by
  unfold Eig.ellFn SectorSetting.ellStar
  congr 2
  refine integral_congr_ae ?_
  filter_upwards [angularSector_congr_ae h 3] with r hr
  rw [hr]

/-! ### Functions of elements of `Y^s(K)` -/

variable {s : ℕ} {K : Set ℂ}

theorem stronglyMeasurable_tupleFn (F : SobTuple s) : StronglyMeasurable (tupleFn F) :=
  Lp.stronglyMeasurable _

theorem suppCLM_eq_zero_iff (F : SobTuple s) :
    suppCLM s K F = 0 ↔ ∀ᵐ x ∂volume, x ∉ K → tupleFn F x = 0 := by
  have hc := LpToLpRestrictCLM_coeFn ℂ (μ := (volume : Measure ℂ)) (p := 2) Kᶜ (proj0 s F)
  have hmeas : MeasurableSet {x | tupleFn F x = 0} :=
    (stronglyMeasurable_tupleFn F).measurable (measurableSet_singleton 0)
  rw [suppCLM, ContinuousLinearMap.comp_apply, Lp.eq_zero_iff_ae_eq_zero]
  constructor
  · intro h
    have h2 : tupleFn F =ᵐ[volume.restrict Kᶜ] 0 := hc.symm.trans h
    exact (ae_restrict_iff hmeas).1 h2
  · intro h
    have h2 : ∀ᵐ x ∂volume.restrict Kᶜ, tupleFn F x = 0 := (ae_restrict_iff hmeas).2 h
    filter_upwards [hc, h2] with x hx h2x
    rw [hx]
    exact h2x

theorem mem_YSub_iff (F : SobTuple s) :
    F ∈ YSub s K ↔ F ∈ HkSub s ∧ ∀ᵐ x ∂volume, x ∉ K → tupleFn F x = 0 := by
  rw [YSub, Submodule.mem_inf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    suppCLM_eq_zero_iff]

/-- The function of `w ∈ Y^s(K)` lies in `H^s`, with `‖w.fn‖_{H^s} = ‖w‖`. -/
theorem Y_memH_fn (w : Y s K) : MemH s w.fn ∧ normH s w.fn = ‖w‖ :=
  Hk.memH_fn (Y.toHk w)

/-- The function of `w ∈ Y^s(K)` vanishes a.e. outside `K`. -/
theorem Y_fn_zero_outside (w : Y s K) : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ K → w.fn x = 0 :=
  ((mem_YSub_iff (K := K) (w : SobTuple s)).1 w.2).2

/-- The function of a difference is the difference of the functions, a.e. -/
theorem Y_fn_sub (v w : Y s K) : (v - w).fn =ᵐ[volume] fun x => v.fn x - w.fn x := by
  have h : ((v - w : Y s K) : SobTuple s).ofLp (idx0 s) =
      (v : SobTuple s).ofLp (idx0 s) - (w : SobTuple s).ofLp (idx0 s) := rfl
  have h2 := Lp.coeFn_sub ((v : SobTuple s).ofLp (idx0 s)) ((w : SobTuple s).ofLp (idx0 s))
  unfold Y.fn tupleFn
  rw [h]
  exact h2

/-- An `H^s` function vanishing a.e. outside `K` is (a.e.) the function of an element of
`Y^s(K)`. -/
theorem exists_Y_of_memH {f : ℂ → ℂ} (hf : MemH s f)
    (hK : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ K → f x = 0) : ∃ w : Y s K, w.fn =ᵐ[volume] f := by
  obtain ⟨F, hF⟩ := memH_iff_exists_Hk.1 hf
  have hmem : (F : SobTuple s) ∈ YSub s K := by
    refine (mem_YSub_iff (F : SobTuple s)).2 ⟨F.2, ?_⟩
    have hF' : tupleFn (F : SobTuple s) =ᵐ[volume] f := hF
    filter_upwards [hF', hK] with x hx hKx hxK
    rw [hx]
    exact hKx hxK
  exact ⟨⟨(F : SobTuple s), hmem⟩, hF⟩

/-- The function of a sum is the sum of the functions, a.e. -/
theorem Y_fn_add (v w : Y s K) : (v + w).fn =ᵐ[volume] fun x => v.fn x + w.fn x := by
  have h : ((v + w : Y s K) : SobTuple s).ofLp (idx0 s) =
      (v : SobTuple s).ofLp (idx0 s) + (w : SobTuple s).ofLp (idx0 s) := rfl
  have h2 := Lp.coeFn_add ((v : SobTuple s).ofLp (idx0 s)) ((w : SobTuple s).ofLp (idx0 s))
  unfold Y.fn tupleFn
  rw [h]
  exact h2

/-- The function of a scalar multiple is the scalar multiple of the function, a.e. -/
theorem Y_fn_smul (c : ℂ) (w : Y s K) : (c • w).fn =ᵐ[volume] fun x => c * w.fn x := by
  have h : ((c • w : Y s K) : SobTuple s).ofLp (idx0 s) =
      c • (w : SobTuple s).ofLp (idx0 s) := rfl
  have h2 := Lp.coeFn_smul c ((w : SobTuple s).ofLp (idx0 s))
  unfold Y.fn tupleFn
  rw [h]
  filter_upwards [h2] with x hx
  rw [hx]
  rfl

end NonUniqueEuler.OneRing.SeedH
