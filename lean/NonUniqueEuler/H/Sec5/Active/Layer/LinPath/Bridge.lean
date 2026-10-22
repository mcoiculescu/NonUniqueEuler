import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Infra.Sobolev.Space
import NonUniqueEuler.I.Infra.Sobolev.Norm
import NonUniqueEuler.I.Infra.SectorSpace.Lower
import NonUniqueEuler.I.Sec4.SemigroupConstruct
import NonUniqueEuler.I.Sec4.RingFacts

/-!
# Helpers for `wlin0_path`: bridges between plane functions and `Y^s(N)`

Helper of `P/Sec5/Active/Layer/LinPath.lean` (fully proved modulo the interface files it
imports). Namespace `NonUniqueEuler.OneRing.LinPathH`. These are copies of proved helpers of
other proofs (`H/Sec5/Quiet/Approx/Bridge.lean`, `H/Sec5/Quiet/Approx/DuhamelFn.lean`,
`H/Sec5/Quiet/Approx/Calculus.lean`, `H/Sec5/Running/Bridge.lean`), which a proof file may not
import (import rules, `README.md`).

* `Y_ext_fn`, `Y_memH_fn`, `Y_fn_add`, `Y_fn_sub`, `norm_sub_eq_normH`: functions of elements
  of `Y^s(K)`;
* `toY_congr_ae`, `toY_fn_self`, `exists_Y_of_memH`, `toY_fn_ae`: the chosen elements
  `Sect.toY s K f`;
* `MemXFn.mono`, `MemXFn.congr_ae`, `MemXFn.toY_fn`, `MemXFn.memX_toY`, `memXFn_of_memX`: the
  space `X^s` on functions and in `Y^s(N)`;
* `lowerY_toY`: `lowerY s s' N (toY s' N f) = toY s N f` for `f ∈ X^{s'}`;
* `memX_of_hasDerivWithinAt`: a derivative of a path in `X^s` lies in `X^s`;
* `L_fn_ae`: `(L(G)w).fn = L(G)(w.fn)` a.e. (`semigroupConstruct_LinY`).
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace NonUniqueEuler.OneRing.LinPathH

open Sect Sob RingData

/-! ### `Y^s(K)` and `Sect.toY` -/

theorem measurableSet_annN : MeasurableSet annN :=
  (isClosed_closedAnnulus _ _).measurableSet

/-- An element of `Y^s(K)` is determined by its function. -/
theorem Y_ext_fn {s : ℕ} {K : Set ℂ} {w₁ w₂ : Y s K} (h : w₁.fn =ᵐ[volume] w₂.fn) : w₁ = w₂ := by
  have : Y.toHk w₁ = Y.toHk w₂ := Hk.ext_fn h
  exact Subtype.ext (show (w₁ : SobTuple s) = w₂ from
    congrArg (fun F : Hk s => (F : SobTuple s)) this)

/-- The function of `w ∈ Y^s(K)` lies in `H^s`, with norm `‖w‖`. -/
theorem Y_memH_fn {s : ℕ} {K : Set ℂ} (w : Y s K) : MemH s w.fn ∧ normH s w.fn = ‖w‖ :=
  Hk.memH_fn (Y.toHk w)

/-- `Sect.toY` only depends on the a.e. class of the function. -/
theorem toY_congr_ae {s : ℕ} {K : Set ℂ} {f g : ℂ → ℂ} (h : f =ᵐ[volume] g) :
    toY s K f = toY s K g := by
  classical
  by_cases hf : ∃ w : Y s K, w.fn =ᵐ[volume] f
  · have hg : ∃ w : Y s K, w.fn =ᵐ[volume] g := let ⟨w, hw⟩ := hf; ⟨w, hw.trans h⟩
    exact Y_ext_fn ((toY_spec hf).trans (h.trans (toY_spec hg).symm))
  · have hg : ¬ ∃ w : Y s K, w.fn =ᵐ[volume] g := fun ⟨w, hw⟩ => hf ⟨w, hw.trans h.symm⟩
    simp [toY, hf, hg]

/-- `toY` of the function of an element is the element. -/
theorem toY_fn_self {s : ℕ} {K : Set ℂ} (w : Y s K) : toY s K w.fn = w :=
  Y_ext_fn (toY_spec ⟨w, EventuallyEq.rfl⟩)

/-- A function of `H^s` vanishing a.e. outside the measurable set `K` is the function of an
element of `Y^s(K)`. -/
theorem exists_Y_of_memH {s : ℕ} {K : Set ℂ} (hKm : MeasurableSet K) {f : ℂ → ℂ}
    (hf : MemH s f) (hK : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ K → f x = 0) :
    ∃ w : Y s K, w.fn =ᵐ[volume] f := by
  set F : Hk s := toHk s f with hFdef
  have hFf : F.fn =ᵐ[volume] f := toHk_fn hf
  have hmem : (F : SobTuple s) ∈ YSub s K := by
    refine Submodule.mem_inf.2 ⟨F.2, LinearMap.mem_ker.2 ?_⟩
    rw [ContinuousLinearMap.coe_coe]
    rw [Lp.eq_zero_iff_ae_eq_zero]
    have h1 := LpToLpRestrictCLM_coeFn ℂ Kᶜ (proj0 s (F : SobTuple s))
    have h2 : ((proj0 s (F : SobTuple s) : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) =
        F.fn := rfl
    have h3 : F.fn =ᵐ[(volume : Measure ℂ).restrict Kᶜ] 0 := by
      have hFf' : F.fn =ᵐ[(volume : Measure ℂ).restrict Kᶜ] f := ae_restrict_of_ae hFf
      refine hFf'.trans ?_
      rw [EventuallyEq, ae_restrict_iff' hKm.compl]
      filter_upwards [hK] with x hx hxK
      exact hx hxK
    show ((LpToLpRestrictCLM ℂ ℂ ℂ (volume : Measure ℂ) 2 Kᶜ) (proj0 s (F : SobTuple s)) :
        ℂ → ℂ) =ᵐ[(volume : Measure ℂ).restrict Kᶜ] 0
    refine h1.trans ?_
    rw [h2]
    exact h3
  exact ⟨⟨(F : SobTuple s), hmem⟩, hFf⟩

/-- `toY s K f` has the function `f` (a.e.) for `f ∈ H^s` vanishing a.e. outside `K`. -/
theorem toY_fn_ae {s : ℕ} {K : Set ℂ} (hKm : MeasurableSet K) {f : ℂ → ℂ}
    (hf : MemH s f) (hK : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ K → f x = 0) :
    (toY s K f).fn =ᵐ[volume] f :=
  toY_spec (exists_Y_of_memH hKm hf hK)

/-- The function of a sum of elements. -/
theorem Y_fn_add {s : ℕ} {K : Set ℂ} (w w' : Y s K) :
    (w + w').fn =ᵐ[volume] fun x => w.fn x + w'.fn x := by
  have h : (((w + w' : Y s K) : SobTuple s).ofLp (idx0 s) : Lp ℂ 2 (volume : Measure ℂ)) =
      ((w : SobTuple s).ofLp (idx0 s) : Lp ℂ 2 (volume : Measure ℂ)) +
        ((w' : SobTuple s).ofLp (idx0 s)) := rfl
  have h2 : (w + w').fn = (((w + w' : Y s K) : SobTuple s).ofLp (idx0 s) : ℂ → ℂ) := rfl
  rw [h2, h]
  exact Lp.coeFn_add _ _

/-- The function of a difference of elements. -/
theorem Y_fn_sub {s : ℕ} {K : Set ℂ} (w w' : Y s K) :
    (w - w').fn =ᵐ[volume] fun x => w.fn x - w'.fn x := by
  have h : (((w - w' : Y s K) : SobTuple s).ofLp (idx0 s) : Lp ℂ 2 (volume : Measure ℂ)) =
      ((w : SobTuple s).ofLp (idx0 s) : Lp ℂ 2 (volume : Measure ℂ)) -
        ((w' : SobTuple s).ofLp (idx0 s)) := rfl
  have h2 : (w - w').fn = (((w - w' : Y s K) : SobTuple s).ofLp (idx0 s) : ℂ → ℂ) := rfl
  rw [h2, h]
  exact Lp.coeFn_sub _ _

/-- `‖w - w'‖ = ‖f - f'‖_{H^s}` when `w, w'` have the functions `f, f'`. -/
theorem norm_sub_eq_normH {s : ℕ} {K : Set ℂ} {w w' : Y s K} {f f' : ℂ → ℂ}
    (hw : w.fn =ᵐ[volume] f) (hw' : w'.fn =ᵐ[volume] f') :
    ‖w - w'‖ = normH s (fun x => f x - f' x) := by
  have hae : (w - w').fn =ᵐ[volume] fun x => f x - f' x := by
    filter_upwards [Y_fn_sub w w', hw, hw'] with x h1 h2 h3
    rw [h1, h2, h3]
  rw [← (Y_memH_fn (w - w')).2, ((Y_memH_fn (w - w')).1.congr_ae hae).2]

/-! ### The space `X^s` -/

theorem MemXFn.mono {s s' : ℕ} {f : ℂ → ℂ} (hf : Lin.MemXFn s' f) (hs : s ≤ s') :
    Lin.MemXFn s f :=
  ⟨hf.1.mono_order hs, hf.2.1, hf.2.2⟩

/-- `X^s` only sees the a.e. class. -/
theorem MemXFn.congr_ae {s : ℕ} {f g : ℂ → ℂ} (hf : Lin.MemXFn s f) (hfg : f =ᵐ[volume] g) :
    Lin.MemXFn s g := by
  refine ⟨(hf.1.congr_ae hfg).1, ?_, ?_⟩
  · filter_upwards [hf.2.1, hfg] with x h1 h2 hx
    rw [← h2, h1 hx]
  · have hcomp : (fun x => g (rot (2 * Real.pi / (3 : ℕ)) x)) =ᵐ[volume]
        fun x => f (rot (2 * Real.pi / (3 : ℕ)) x) :=
      (Polar.measurePreserving_rot (2 * Real.pi / (3 : ℕ))).quasiMeasurePreserving.ae_eq_comp
        hfg.symm
    exact hcomp.trans (hf.2.2.trans hfg)

/-- The function of `toY s N f` for `f ∈ X^s`. -/
theorem MemXFn.toY_fn {s : ℕ} {f : ℂ → ℂ} (hf : Lin.MemXFn s f) :
    (toY s annN f).fn =ᵐ[volume] f :=
  toY_fn_ae measurableSet_annN hf.1 hf.2.1

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

/-- For `f ∈ X^s` (`Lin.MemXFn s f`), `toY s annN f ∈ X^s`. -/
theorem MemXFn.memX_toY {s : ℕ} {f : ℂ → ℂ} (hf : Lin.MemXFn s f) :
    Lin.MemX (toY s annN f) := by
  have hfn : (toY s annN f).fn =ᵐ[volume] f := MemXFn.toY_fn hf
  rw [Lin.memX_iff, YsymSub, Submodule.mem_inf, LinearMap.mem_ker]
  refine ⟨(toY s annN f).2, ?_⟩
  rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
    sub_apply, ContinuousLinearMap.id_apply, sub_eq_zero]
  refine Lp.ext ?_
  have hrot := Lp.coeFn_compMeasurePreserving (proj0 s ((toY s annN f : Y s annN) : SobTuple s))
    (Polar.measurePreserving_rot (2 * Real.pi / (3 : ℕ)))
  have hcomp : (fun x => (toY s annN f).fn (rot (2 * Real.pi / (3 : ℕ)) x)) =ᵐ[volume]
      fun x => f (rot (2 * Real.pi / (3 : ℕ)) x) :=
    (Polar.measurePreserving_rot (2 * Real.pi / (3 : ℕ))).quasiMeasurePreserving.ae_eq_comp hfn
  have hsym : (fun x => f (rot (2 * Real.pi / (3 : ℕ)) x)) =ᵐ[volume] f := hf.2.2
  show ((Ang.rotLp (2 * Real.pi / (3 : ℕ)) (proj0 s ((toY s annN f : Y s annN) : SobTuple s)) :
      Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) =ᵐ[volume] (toY s annN f).fn
  refine hrot.trans ?_
  exact hcomp.trans (hsym.trans hfn.symm)

/-- An element of `X^s` (`Lin.MemX`) has its function in `X^s` (`Lin.MemXFn`). -/
theorem memXFn_of_memX {s : ℕ} {w : Y s annN} (hw : Lin.MemX w) : Lin.MemXFn s w.fn := by
  refine ⟨(Y_memH_fn w).1, ?_, ?_⟩
  · have h2 : suppCLM s annN (w : SobTuple s) = 0 := by
      have := (Submodule.mem_inf.1 w.2).2
      rwa [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at this
    rw [Lp.eq_zero_iff_ae_eq_zero] at h2
    have h1 := LpToLpRestrictCLM_coeFn ℂ annNᶜ (proj0 s (w : SobTuple s))
    have h4 : w.fn =ᵐ[(volume : Measure ℂ).restrict annNᶜ] 0 := h1.symm.trans h2
    rw [EventuallyEq, ae_restrict_iff' measurableSet_annN.compl] at h4
    filter_upwards [h4] with x hx hxN
    exact hx hxN
  · have h := hw
    rw [Lin.memX_iff, YsymSub, Submodule.mem_inf, LinearMap.mem_ker] at h
    have h2 := h.2
    rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
      sub_apply, ContinuousLinearMap.id_apply, sub_eq_zero] at h2
    have hrot := Lp.coeFn_compMeasurePreserving (proj0 s (w : SobTuple s))
      (Polar.measurePreserving_rot (2 * Real.pi / (3 : ℕ)))
    have h5 : ((Ang.rotLp (2 * Real.pi / (3 : ℕ)) (proj0 s (w : SobTuple s)) :
        Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) =ᵐ[volume] w.fn := by
      rw [h2]
      rfl
    exact hrot.symm.trans h5

/-- `lowerY` of `toY`: for `f ∈ X^{s'}` and `s ≤ s'`, `lowerY s s' N (toY s' N f) = toY s N f`. -/
theorem lowerY_toY {s s' : ℕ} (hss : s ≤ s') {f : ℂ → ℂ} (hf : Lin.MemXFn s' f) :
    lowerY s s' annN (toY s' annN f) = toY s annN f := by
  refine Y_ext_fn ?_
  exact ((lowerY_spec hss annN).1 _).trans ((MemXFn.toY_fn hf).trans
    (MemXFn.toY_fn (MemXFn.mono hf hss)).symm)

/-- A derivative within `[0,T]` (`T > 0`) of a path with values in `X^s` lies in `X^s`. -/
theorem memX_of_hasDerivWithinAt {s : ℕ} {T t : ℝ} (hT : 0 < T) (ht : t ∈ Icc 0 T)
    {p : ℝ → Y s annN} {p' : Y s annN} (hp : ∀ τ ∈ Icc (0 : ℝ) T, Lin.MemX (p τ))
    (hd : HasDerivWithinAt p p' (Icc 0 T) t) : Lin.MemX p' := by
  obtain ⟨L, hL⟩ := exists_memX_iff s
  rw [hL]
  have h1 := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt (f := p) t hd
  simp only [ContinuousLinearMap.coe_restrictScalars'] at h1
  have h2 : HasDerivWithinAt (fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure ℂ))) (L p')
      (Icc 0 T) t :=
    h1.congr_of_mem (fun τ hτ => ((hL _).1 (hp τ hτ)).symm) ht
  have h3 : HasDerivWithinAt (fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure ℂ))) 0 (Icc 0 T) t :=
    hasDerivWithinAt_const _ _ _
  exact (uniqueDiffOn_Icc hT t ht).eq_deriv _ h2 h3

/-- `(L(G)w).fn = L(G)(w.fn)` a.e. for `w ∈ Y^{k+1}(N)` (`lem:semigroup-construct`(2)). -/
theorem L_fn_ae (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (k : ℕ) (G : ℝ) (w : Y (k + 1) annN) :
    (Lin.L χ k G w).fn =ᵐ[volume] Lin.Lfn χ G w.fn :=
  (ringPhiSetting χ).LinY_spec_of_exists k G
    ((ringPhiSetting χ).semigroupConstruct_LinY (ringPhiSetting_valid hχ) k G) w

end NonUniqueEuler.OneRing.LinPathH
