import Mathlib.Analysis.Normed.Algebra.Exponential
import NonUniqueEuler.Defs.Infra.SectorSpace
import NonUniqueEuler.I.Infra.Sobolev.Space
import NonUniqueEuler.I.Infra.Polar.Radial
import NonUniqueEuler.I.Infra.SectorSpace.Decomposition

/-!
# Helpers for `P/Sec4/SemigroupLaw`: elements of the sector spaces, exponentials

* Function-level characterisations of `YSub`, `YsecSub` (`Defs/Infra/SectorSpace.lean`), and
  extensionality: an element of `Y s K` or `Ysec s K ℓ` is determined by its function
  (`Sob.Hk.ext_fn`); its norm is the `H^s` norm of its function. (These duplicate private
  helpers of `H/Infra/SectorSpace/Projection/Basic.lean` and
  `H/Infra/SectorSpace/Decomposition/Basic.lean`, which this proof may not import
  (import rules, `README.md`).)
* Null sets of `(0, ∞)` transfer to the plane through `x ↦ |x|` (`ae_comp_norm`).
* An element of `Y^s` on an annulus is determined by its sector projections (`hasSum_secProj`).
* Intertwining of exponentials: if a continuous additive, real-homogeneous `J` satisfies
  `J A = B J`, then `J exp(tA) = exp(tB) J` for real `t` (exponential series).
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal Nat

namespace NonUniqueEuler.Sect.SgLawH

open Sob Ang

variable {s : ℕ} {K : Set ℂ}

/-! ### Tuples and their functions -/

theorem stronglyMeasurable_tupleFn (F : SobTuple s) : StronglyMeasurable (tupleFn F) :=
  Lp.stronglyMeasurable _

theorem tupleFn_add (F G : SobTuple s) :
    tupleFn (F + G) =ᵐ[volume] tupleFn F + tupleFn G :=
  Lp.coeFn_add (F.ofLp (idx0 s)) (G.ofLp (idx0 s))

theorem tupleFn_smul (c : ℂ) (F : SobTuple s) :
    tupleFn (c • F) =ᵐ[volume] c • tupleFn F :=
  Lp.coeFn_smul c (F.ofLp (idx0 s))

/-- Two elements of `H^s` with a.e. equal functions are equal (as tuples). -/
theorem tuple_ext {F G : SobTuple s} (hF : F ∈ HkSub s) (hG : G ∈ HkSub s)
    (h : tupleFn F =ᵐ[volume] tupleFn G) : F = G := by
  have := Hk.ext_fn (F := (⟨F, hF⟩ : Hk s)) (G := ⟨G, hG⟩) h
  exact congrArg Subtype.val this

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

/-! ### Elements of `Y s K` and `Ysec s K ℓ` -/

theorem Y.ext_fn {w v : Y s K} (h : w.fn =ᵐ[volume] v.fn) : w = v :=
  Subtype.ext (tuple_ext (YSub_le_HkSub s K w.2) (YSub_le_HkSub s K v.2) h)

theorem Ysec.ext_fn {ℓ : ℤ} {g h : Ysec s K ℓ} (hgh : g.fn =ᵐ[volume] h.fn) : g = h :=
  Subtype.ext (tuple_ext (YSub_le_HkSub s K (YsecSub_le_YSub s K ℓ g.2))
    (YSub_le_HkSub s K (YsecSub_le_YSub s K ℓ h.2)) hgh)

theorem Y.memH_fn (w : Y s K) : MemH s w.fn := (Hk.memH_fn w.toHk).1

theorem Y.supp (w : Y s K) : ∀ᵐ x ∂volume, x ∉ K → w.fn x = 0 :=
  ((mem_YSub_iff (w : SobTuple s)).1 w.2).2

theorem Ysec.isSectorFn {ℓ : ℤ} (g : Ysec s K ℓ) : IsSectorFn ℓ g.fn :=
  ((mem_YsecSub_iff' ℓ (g : SobTuple s)).1 g.2).2

theorem Ysec.memH_fn {ℓ : ℤ} (g : Ysec s K ℓ) : MemH s g.fn := Y.memH_fn (inclSec s K ℓ g)

theorem Ysec.supp {ℓ : ℤ} (g : Ysec s K ℓ) : ∀ᵐ x ∂volume, x ∉ K → g.fn x = 0 :=
  Y.supp (inclSec s K ℓ g)

theorem Ysec.fn_add {ℓ : ℤ} (g h : Ysec s K ℓ) : (g + h).fn =ᵐ[volume] g.fn + h.fn :=
  tupleFn_add (g : SobTuple s) h

theorem Ysec.fn_smul {ℓ : ℤ} (c : ℂ) (g : Ysec s K ℓ) : (c • g).fn =ᵐ[volume] c • g.fn :=
  tupleFn_smul c (g : SobTuple s)

/-- The norm of `F : Hk s` is the `H^s` norm of any function a.e. equal to its function. -/
theorem Hk.norm_eq_normH_of_ae {F : Hk s} {f : ℂ → ℂ} (hf : MemH s f)
    (h : F.fn =ᵐ[volume] f) : ‖F‖ = normH s f := by
  have hF : toHk s f = F := Hk.ext_fn ((toHk_fn hf).trans h.symm)
  rw [← hF, norm_toHk hf]

/-- The norm of `g ∈ Y^s_ℓ(K)` is the `H^s` norm of any function a.e. equal to its function. -/
theorem Ysec.norm_eq_normH_of_ae {ℓ : ℤ} {g : Ysec s K ℓ} {f : ℂ → ℂ} (hf : MemH s f)
    (h : g.fn =ᵐ[volume] f) : ‖g‖ = normH s f :=
  Hk.norm_eq_normH_of_ae (F := (inclSec s K ℓ g).toHk) hf h

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

/-! ### Sector projections -/

/-- An element of `Y^s` on the annulus is determined by its sector projections. -/
theorem Y_ext_of_secProj {ρm ρp : ℝ} (hρm : 0 < ρm) (hρ : ρm < ρp)
    {a b : Y s (closedAnnulus ρm ρp)}
    (h : ∀ ℓ, secProj s _ ℓ a = secProj s _ ℓ b) : a = b := by
  have ha := hasSum_secProj hρm hρ a
  have hb := hasSum_secProj hρm hρ b
  simp only [h] at ha
  exact ha.unique hb

/-! ### Intertwining of exponentials -/

/-- If `J` is continuous, additive and real-homogeneous with `J ∘ A = B ∘ J`, then
`J ∘ exp(tA) = exp(tB) ∘ J` for every real `t`. -/
theorem exp_smul_apply_intertwine {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (A : E →L[ℂ] E) (B : F →L[ℂ] F) (J : E →+ F) (hJ : Continuous J)
    (hJr : ∀ (r : ℝ) (x : E), J ((r : ℂ) • x) = (r : ℂ) • J x)
    (hAB : ∀ x, J (A x) = B (J x)) (t : ℝ) (x : E) :
    J (NormedSpace.exp ((t : ℂ) • A) x) = NormedSpace.exp ((t : ℂ) • B) (J x) := by
  have hpow : ∀ (n : ℕ) (y : E), J ((((t : ℂ) • A) ^ n) y) = (((t : ℂ) • B) ^ n) (J y) := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [pow_succ', pow_succ', mul_apply_eq_comp, mul_apply_eq_comp,
        smul_apply, smul_apply, hJr, hAB, ih]
  have h1 : HasSum (fun n : ℕ => ((n !⁻¹ : ℂ) • ((t : ℂ) • A) ^ n) x)
      (NormedSpace.exp ((t : ℂ) • A) x) :=
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) ((t : ℂ) • A)).map
      (ContinuousLinearMap.apply ℂ E x) (ContinuousLinearMap.apply ℂ E x).continuous
  have h2 : HasSum (fun n : ℕ => ((n !⁻¹ : ℂ) • ((t : ℂ) • B) ^ n) (J x))
      (NormedSpace.exp ((t : ℂ) • B) (J x)) :=
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) ((t : ℂ) • B)).map
      (ContinuousLinearMap.apply ℂ F (J x)) (ContinuousLinearMap.apply ℂ F (J x)).continuous
  have h3 := h1.map J hJ
  refine h3.unique ?_
  convert h2 using 1
  funext n
  simp only [Function.comp_apply, smul_apply]
  have hc : (n !⁻¹ : ℂ) = ((n !⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [hc, hJr, hpow]

end NonUniqueEuler.Sect.SgLawH
