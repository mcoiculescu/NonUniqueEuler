import NonUniqueEuler.Defs.Infra.SectorSpace
import NonUniqueEuler.I.Infra.Sobolev.Space
import NonUniqueEuler.I.Infra.Polar.Radial

/-!
# Helpers for `P/Infra/SectorSpace/Decomposition`: membership, functions and norms

Function-level characterisations of the closed submodules `YSub`, `YsecSub` of `SobTuple s`
(`Defs/Infra/SectorSpace.lean`), the functions and norms of their elements
(`Sob.Hk.memH_fn`, `Sob.Hk.ext_fn`, `Sob.norm_toHk`), and the transfer of null sets of
`(0, ∞)` to the plane through `x ↦ |x|` (`Polar.lintegral_comp_norm`).

(The membership criteria duplicate the private helpers of `P/Infra/SectorSpace/Projection`, which
this proof may not import (import rules, `README.md`).)
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace NonUniqueEuler.Sect.DecompH

open Sob Ang

variable {s : ℕ} {K : Set ℂ}

theorem memLp_tupleFn (F : SobTuple s) : MemLp (tupleFn F) 2 volume :=
  Lp.memLp _

theorem stronglyMeasurable_tupleFn (F : SobTuple s) : StronglyMeasurable (tupleFn F) :=
  Lp.stronglyMeasurable _

/-! ### The support condition -/

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

/-! ### The sector condition -/

theorem sectorDefect_eq_zero_iff (ℓ : ℤ) (θ : ℝ) (F : SobTuple s) :
    sectorDefect s ℓ θ F = 0 ↔
      (fun x => tupleFn F (rot θ x)) =ᵐ[volume]
        fun x => Complex.exp ((ℓ : ℂ) * θ * Complex.I) * tupleFn F x := by
  have hr : (rotLp θ (proj0 s F) : ℂ → ℂ) =ᵐ[volume] fun x => tupleFn F (rot θ x) :=
    rotLp_coeFn θ (proj0 s F)
  have hs : ((Complex.exp ((ℓ : ℂ) * θ * Complex.I) • proj0 s F : Lp ℂ 2 volume) : ℂ → ℂ)
      =ᵐ[volume] Complex.exp ((ℓ : ℂ) * θ * Complex.I) • tupleFn F :=
    Lp.coeFn_smul (Complex.exp ((ℓ : ℂ) * θ * Complex.I)) (proj0 s F)
  rw [sectorDefect, ContinuousLinearMap.comp_apply, sub_apply,
    smul_apply, ContinuousLinearMap.id_apply, sub_eq_zero, Lp.ext_iff]
  constructor
  · intro h
    filter_upwards [hr, hs, h] with x hrx hsx hx
    rw [← hrx, hx, hsx]
    rfl
  · intro h
    filter_upwards [hr, hs, h] with x hrx hsx hx
    rw [hrx, hsx]
    exact hx

theorem mem_YsecSub_iff' (ℓ : ℤ) (F : SobTuple s) :
    F ∈ YsecSub s K ℓ ↔ F ∈ YSub s K ∧ IsSectorFn ℓ (tupleFn F) := by
  rw [YsecSub, Submodule.mem_inf, Submodule.mem_iInf]
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, sectorDefect_eq_zero_iff]
  rfl

/-! ### Functions and norms -/

/-- The norm of `F : Hk s` is the `H^s` norm of any function a.e. equal to its function. -/
theorem Hk.norm_eq_normH_of_ae {F : Hk s} {f : ℂ → ℂ} (hf : MemH s f)
    (h : F.fn =ᵐ[volume] f) : ‖F‖ = normH s f := by
  have hF : toHk s f = F := Hk.ext_fn ((toHk_fn hf).trans h.symm)
  rw [← hF, norm_toHk hf]

theorem Y.memH_fn (w : Y s K) : MemH s w.fn := (Hk.memH_fn w.toHk).1

theorem Y.normH_fn (w : Y s K) : normH s w.fn = ‖w‖ := (Hk.memH_fn w.toHk).2

theorem Y.supp (w : Y s K) : ∀ᵐ x ∂volume, x ∉ K → w.fn x = 0 :=
  ((mem_YSub_iff (w : SobTuple s)).1 w.2).2

/-- The norm of `w ∈ Y^s(K)` is the `H^s` norm of any function a.e. equal to its function. -/
theorem Y.norm_eq_normH_of_ae {w : Y s K} {f : ℂ → ℂ} (hf : MemH s f)
    (h : w.fn =ᵐ[volume] f) : ‖w‖ = normH s f :=
  Hk.norm_eq_normH_of_ae (F := w.toHk) hf h

theorem Ysec.isSectorFn {ℓ : ℤ} (g : Ysec s K ℓ) : IsSectorFn ℓ g.fn :=
  ((mem_YsecSub_iff' ℓ (g : SobTuple s)).1 g.2).2

theorem norm_inclSec {ℓ : ℤ} (g : Ysec s K ℓ) : ‖inclSec s K ℓ g‖ = ‖g‖ := rfl

theorem Ysec.memH_fn {ℓ : ℤ} (g : Ysec s K ℓ) : MemH s g.fn := Y.memH_fn (inclSec s K ℓ g)

theorem Ysec.supp {ℓ : ℤ} (g : Ysec s K ℓ) : ∀ᵐ x ∂volume, x ∉ K → g.fn x = 0 :=
  Y.supp (inclSec s K ℓ g)

theorem Ysec.norm_eq_normH_of_ae {ℓ : ℤ} {g : Ysec s K ℓ} {f : ℂ → ℂ} (hf : MemH s f)
    (h : g.fn =ᵐ[volume] f) : ‖g‖ = normH s f :=
  Y.norm_eq_normH_of_ae (w := inclSec s K ℓ g) hf h

/-! ### Null sets of `(0, ∞)` and the plane -/

/-- A property holding for a.e. `r > 0` holds at `|x|` for a.e. `x ∈ ℂ`. -/
theorem ae_comp_norm {P : ℝ → Prop} (hP : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), P r) :
    ∀ᵐ x : ℂ, P ‖x‖ := by
  set μ := (volume : Measure ℝ).restrict (Ioi (0 : ℝ))
  set N := toMeasurable μ {r | ¬ P r}
  have hNm : MeasurableSet N := measurableSet_toMeasurable μ _
  have hμN : μ N = 0 := by
    rw [measure_toMeasurable]
    exact hP
  have hNae : ∀ᵐ r ∂μ, r ∉ N := measure_eq_zero_iff_ae_notMem.1 hμN
  have hpre : MeasurableSet ((fun x : ℂ => ‖x‖) ⁻¹' N) := measurable_norm hNm
  have hvol : volume ((fun x : ℂ => ‖x‖) ⁻¹' N) = 0 := by
    rw [← lintegral_indicator_one hpre]
    have h1 : (fun x : ℂ => ((fun x : ℂ => ‖x‖) ⁻¹' N).indicator (1 : ℂ → ℝ≥0∞) x) =
        fun x : ℂ => N.indicator (1 : ℝ → ℝ≥0∞) ‖x‖ := by
      funext x
      by_cases hx : ‖x‖ ∈ N
      · rw [indicator_of_mem (show x ∈ (fun x : ℂ => ‖x‖) ⁻¹' N from hx),
          indicator_of_mem hx]
        rfl
      · rw [indicator_of_notMem (show x ∉ (fun x : ℂ => ‖x‖) ⁻¹' N from hx),
          indicator_of_notMem hx]
    rw [h1, Polar.lintegral_comp_norm (f := N.indicator (1 : ℝ → ℝ≥0∞))
      (measurable_one.indicator hNm)]
    have h2 : ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * N.indicator (1 : ℝ → ℝ≥0∞) r = 0 := by
      rw [← lintegral_zero (μ := μ)]
      refine lintegral_congr_ae ?_
      filter_upwards [hNae] with r hr
      rw [indicator_of_notMem hr, mul_zero]
    rw [h2, mul_zero]
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hvol] with x hx
  by_contra hPx
  exact hx (subset_toMeasurable μ {r | ¬ P r} hPx)

end NonUniqueEuler.Sect.DecompH
