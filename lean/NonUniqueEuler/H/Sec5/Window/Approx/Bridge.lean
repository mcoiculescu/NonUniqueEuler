import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Infra.Sobolev.Space
import NonUniqueEuler.I.Infra.Sobolev.Norm
import NonUniqueEuler.I.Infra.Sobolev.NormDeriv
import NonUniqueEuler.I.Infra.SectorSpace.Lower
import NonUniqueEuler.I.Infra.CkNorm.Basic

/-!
# Helpers for `window_approx`: the bridge between plane functions and `Y^s(N)`, and paths

Helper of `P/Sec5/Window/Approx.lean` (fully proved). Namespace
`NonUniqueEuler.OneRing.WAppH`. This file is a copy (namespace renamed) of the proved
helper `H/Sec5/Quiet/Approx/Bridge.lean` of the proof `Sec5/Quiet/Approx` (import rule: helpers of
another proof may not be imported), which itself copies lemmas of `H/Sec5/Energy/ToY.lean` and
`H/Sec5/Running/Bridge.lean`.

* `Sect.toY` on functions of `H^s` vanishing outside `K`: function, norm, additivity, a.e.
  invariance; `toY` of the function of an element; `lowerY` of `toY`;
* the space `X^s` (`Lin.MemXFn`): linear operations, finite sums, a.e. invariance, `toY` lands
  in `Lin.MemX`, and conversely `memXFn_of_memX`;
* paths: `PathC`, `PathC1` are stable under sums, a.e. changes and lowering of the level.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace NonUniqueEuler.OneRing.WAppH

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

theorem toY_zero (s : ℕ) (K : Set ℂ) : toY s K (0 : ℂ → ℂ) = 0 := by
  have h : (0 : Y s K).fn =ᵐ[volume] (0 : ℂ → ℂ) := by
    show ((((0 : Y s K) : SobTuple s).ofLp (idx0 s) : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ)
      =ᵐ[volume] 0
    simpa using (Lp.coeFn_zero ℂ 2 (volume : Measure ℂ))
  rw [← toY_congr_ae h, toY_fn_self]

/-- For `f ∈ H^s` vanishing a.e. outside the measurable set `K`, the tuple of `toY s K f` is the
tuple of `toHk s f`. -/
theorem coe_toY_eq_coe_toHk {s : ℕ} {K : Set ℂ} (hKm : MeasurableSet K) {f : ℂ → ℂ}
    (hf : MemH s f) (hK : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ K → f x = 0) :
    ((toY s K f : Y s K) : SobTuple s) = ((toHk s f : Hk s) : SobTuple s) := by
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
  set w : Y s K := ⟨(F : SobTuple s), hmem⟩
  have hw : w.fn =ᵐ[volume] f := hFf
  have hY : toY s K f = w := Y_ext_fn ((toY_spec ⟨w, hw⟩).trans hw.symm)
  rw [hY]

/-- The function of `toY s K f` is `f` a.e. -/
theorem toY_fn_ae {s : ℕ} {K : Set ℂ} (hKm : MeasurableSet K) {f : ℂ → ℂ} (hf : MemH s f)
    (hK : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ K → f x = 0) : (toY s K f).fn =ᵐ[volume] f := by
  have h : (toY s K f).fn = (toHk s f).fn := by
    simp only [Y.fn, Hk.fn, coe_toY_eq_coe_toHk hKm hf hK]
  rw [h]
  exact toHk_fn hf

/-- `‖toY s K f‖ = ‖f‖_{H^s}`. -/
theorem norm_toY {s : ℕ} {K : Set ℂ} (hKm : MeasurableSet K) {f : ℂ → ℂ} (hf : MemH s f)
    (hK : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ K → f x = 0) : ‖toY s K f‖ = normH s f := by
  rw [Submodule.coe_norm, coe_toY_eq_coe_toHk hKm hf hK, ← Submodule.coe_norm, norm_toHk hf]

theorem toY_add {s : ℕ} {K : Set ℂ} (hKm : MeasurableSet K) {f g : ℂ → ℂ} (hf : MemH s f)
    (hfK : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ K → f x = 0) (hg : MemH s g)
    (hgK : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ K → g x = 0) :
    toY s K (f + g) = toY s K f + toY s K g := by
  have hfgK : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ K → (f + g) x = 0 := by
    filter_upwards [hfK, hgK] with x h1 h2 hx
    simp [h1 hx, h2 hx]
  apply Subtype.ext
  rw [Submodule.coe_add, coe_toY_eq_coe_toHk hKm (hf.add hg).1 hfgK,
    coe_toY_eq_coe_toHk hKm hf hfK, coe_toY_eq_coe_toHk hKm hg hgK, toHk_add hf hg,
    Submodule.coe_add]

theorem toY_neg {s : ℕ} {K : Set ℂ} (hKm : MeasurableSet K) {f : ℂ → ℂ} (hf : MemH s f)
    (hfK : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ K → f x = 0) :
    toY s K (-f) = -toY s K f := by
  have hneg : -f = (-1 : ℂ) • f := by funext x; simp
  have hm : MemH s ((-1 : ℂ) • f) := (hf.const_smul (-1)).1
  have hK' : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ K → ((-1 : ℂ) • f) x = 0 := by
    filter_upwards [hfK] with x h hx
    simp [h hx]
  apply Subtype.ext
  rw [hneg, Submodule.coe_neg, coe_toY_eq_coe_toHk hKm hm hK', coe_toY_eq_coe_toHk hKm hf hfK,
    toHk_smul hf, Submodule.coe_smul, neg_one_smul]

/-- The function of a difference of elements. -/
theorem Y_fn_sub {s : ℕ} {K : Set ℂ} (w w' : Y s K) :
    (w - w').fn =ᵐ[volume] fun x => w.fn x - w'.fn x := by
  have h : (((w - w' : Y s K) : SobTuple s).ofLp (idx0 s) : Lp ℂ 2 (volume : Measure ℂ)) =
      ((w : SobTuple s).ofLp (idx0 s) : Lp ℂ 2 (volume : Measure ℂ)) -
        ((w' : SobTuple s).ofLp (idx0 s)) := rfl
  have h2 : (w - w').fn = (((w - w' : Y s K) : SobTuple s).ofLp (idx0 s) : ℂ → ℂ) := rfl
  rw [h2, h]
  exact Lp.coeFn_sub _ _

/-- The function of a sum of elements. -/
theorem Y_fn_add {s : ℕ} {K : Set ℂ} (w w' : Y s K) :
    (w + w').fn =ᵐ[volume] fun x => w.fn x + w'.fn x := by
  have h : (((w + w' : Y s K) : SobTuple s).ofLp (idx0 s) : Lp ℂ 2 (volume : Measure ℂ)) =
      ((w : SobTuple s).ofLp (idx0 s) : Lp ℂ 2 (volume : Measure ℂ)) +
        ((w' : SobTuple s).ofLp (idx0 s)) := rfl
  have h2 : (w + w').fn = (((w + w' : Y s K) : SobTuple s).ofLp (idx0 s) : ℂ → ℂ) := rfl
  rw [h2, h]
  exact Lp.coeFn_add _ _

/-- `‖w - w'‖ = ‖f - f'‖_{H^s}` when `w, w'` have the functions `f, f'`. -/
theorem norm_sub_eq_normH {s : ℕ} {K : Set ℂ} {w w' : Y s K} {f f' : ℂ → ℂ}
    (hw : w.fn =ᵐ[volume] f) (hw' : w'.fn =ᵐ[volume] f') :
    ‖w - w'‖ = normH s (fun x => f x - f' x) := by
  have hae : (w - w').fn =ᵐ[volume] fun x => f x - f' x := by
    filter_upwards [Y_fn_sub w w', hw, hw'] with x h1 h2 h3
    rw [h1, h2, h3]
  rw [← (Y_memH_fn (w - w')).2, ((Y_memH_fn (w - w')).1.congr_ae hae).2]

/-! ### The space `X^s` on functions -/

theorem MemXFn.add {s : ℕ} {f g : ℂ → ℂ} (hf : Lin.MemXFn s f) (hg : Lin.MemXFn s g) :
    Lin.MemXFn s (f + g) := by
  refine ⟨(hf.1.add hg.1).1, ?_, ?_⟩
  · filter_upwards [hf.2.1, hg.2.1] with x h1 h2 hx
    simp [h1 hx, h2 hx]
  · exact hf.2.2.add hg.2.2

theorem MemXFn.neg {s : ℕ} {f : ℂ → ℂ} (hf : Lin.MemXFn s f) : Lin.MemXFn s (-f) := by
  have hneg : (-1 : ℂ) • f = -f := by funext x; simp
  refine ⟨?_, ?_, ?_⟩
  · have h := (hf.1.const_smul (-1)).1
    rwa [hneg] at h
  · filter_upwards [hf.2.1] with x h1 hx
    simp [h1 hx]
  · exact hf.2.2.neg

theorem MemXFn.sub {s : ℕ} {f g : ℂ → ℂ} (hf : Lin.MemXFn s f) (hg : Lin.MemXFn s g) :
    Lin.MemXFn s (f - g) := by
  rw [sub_eq_add_neg]
  exact MemXFn.add hf (MemXFn.neg hg)

theorem MemXFn.mono {s s' : ℕ} {f : ℂ → ℂ} (hf : Lin.MemXFn s' f) (hs : s ≤ s') :
    Lin.MemXFn s f :=
  ⟨hf.1.mono_order hs, hf.2.1, hf.2.2⟩

theorem memXFn_zero (s : ℕ) : Lin.MemXFn s (0 : ℂ → ℂ) := by
  have h0 := Hk.memH_fn (0 : Hk s)
  have hz : (0 : Hk s).fn =ᵐ[volume] (0 : ℂ → ℂ) := by
    show ((((0 : Hk s) : SobTuple s).ofLp (idx0 s) : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ)
      =ᵐ[volume] 0
    simpa using (Lp.coeFn_zero ℂ 2 (volume : Measure ℂ))
  refine ⟨(h0.1.congr_ae hz).1, Eventually.of_forall fun _ _ => rfl, ?_⟩
  exact Eventually.of_forall fun _ => rfl

theorem MemXFn.sum {s : ℕ} {ι : Type*} (S : Finset ι) {f : ι → ℂ → ℂ}
    (hf : ∀ i ∈ S, Lin.MemXFn s (f i)) : Lin.MemXFn s (∑ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using memXFn_zero s
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    exact MemXFn.add (hf a (Finset.mem_insert_self a S))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

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

/-- `‖toY s N f‖ = ‖f‖_{H^s}` for `f ∈ X^s`. -/
theorem MemXFn.norm_toY {s : ℕ} {f : ℂ → ℂ} (hf : Lin.MemXFn s f) :
    ‖toY s annN f‖ = normH s f :=
  WAppH.norm_toY measurableSet_annN hf.1 hf.2.1

theorem toY_add' {s : ℕ} {f g : ℂ → ℂ} (hf : Lin.MemXFn s f) (hg : Lin.MemXFn s g) :
    toY s annN (f + g) = toY s annN f + toY s annN g :=
  toY_add measurableSet_annN hf.1 hf.2.1 hg.1 hg.2.1

theorem toY_neg' {s : ℕ} {f : ℂ → ℂ} (hf : Lin.MemXFn s f) :
    toY s annN (-f) = -toY s annN f :=
  toY_neg measurableSet_annN hf.1 hf.2.1

theorem toY_sub' {s : ℕ} {f g : ℂ → ℂ} (hf : Lin.MemXFn s f) (hg : Lin.MemXFn s g) :
    toY s annN (f - g) = toY s annN f - toY s annN g := by
  rw [sub_eq_add_neg, toY_add' hf (MemXFn.neg hg), toY_neg' hg, ← sub_eq_add_neg]

theorem toY_sum {s : ℕ} {ι : Type*} (S : Finset ι) {f : ι → ℂ → ℂ}
    (hf : ∀ i ∈ S, Lin.MemXFn s (f i)) :
    toY s annN (∑ i ∈ S, f i) = ∑ i ∈ S, toY s annN (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using toY_zero s annN
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      toY_add' (hf a (Finset.mem_insert_self a S))
        (MemXFn.sum S fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

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

/-! ### Paths -/

theorem PathC.add {s : ℕ} {T : ℝ} {u v : ℝ → ℂ → ℂ} (hu : PathC s T u) (hv : PathC s T v) :
    PathC s T (fun t => u t + v t) := by
  refine ⟨fun t ht => MemXFn.add (hu.1 t ht) (hv.1 t ht), ?_⟩
  refine (hu.2.add hv.2).congr fun t ht => ?_
  exact toY_add' (hu.1 t ht) (hv.1 t ht)

theorem PathC.neg {s : ℕ} {T : ℝ} {u : ℝ → ℂ → ℂ} (hu : PathC s T u) :
    PathC s T (fun t => -u t) := by
  refine ⟨fun t ht => MemXFn.neg (hu.1 t ht), ?_⟩
  refine hu.2.neg.congr fun t ht => ?_
  exact toY_neg' (hu.1 t ht)

theorem PathC.sub {s : ℕ} {T : ℝ} {u v : ℝ → ℂ → ℂ} (hu : PathC s T u) (hv : PathC s T v) :
    PathC s T (fun t => u t - v t) := by
  have := PathC.add hu (PathC.neg hv)
  simpa [sub_eq_add_neg] using this

theorem PathC.zero (s : ℕ) (T : ℝ) : PathC s T (fun _ => (0 : ℂ → ℂ)) :=
  ⟨fun _ _ => memXFn_zero s, continuousOn_const⟩

theorem PathC.sum {s : ℕ} {T : ℝ} {ι : Type*} (S : Finset ι) {u : ι → ℝ → ℂ → ℂ}
    (hu : ∀ i ∈ S, PathC s T (u i)) : PathC s T (fun t => ∑ i ∈ S, u i t) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using PathC.zero s T
  | insert a S ha ih =>
    have h := PathC.add (hu a (Finset.mem_insert_self a S))
      (ih fun i hi => hu i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert ha] using h

/-- Lowering the level of a path. -/
theorem PathC.mono_level {s s' : ℕ} {T : ℝ} {u : ℝ → ℂ → ℂ} (hu : PathC s' T u)
    (hss : s ≤ s') : PathC s T u := by
  refine ⟨fun t ht => MemXFn.mono (hu.1 t ht) hss, ?_⟩
  refine ((lowerY s s' annN).continuous.comp_continuousOn hu.2).congr fun t ht => ?_
  exact (lowerY_toY hss (hu.1 t ht)).symm

/-- `t ↦ ‖u(t)‖_{H^s}` is continuous on `[0,T]` for `u ∈ C([0,T];X^s)`. -/
theorem PathC.continuousOn_normH {s : ℕ} {T : ℝ} {u : ℝ → ℂ → ℂ} (hu : PathC s T u) :
    ContinuousOn (fun t => normH s (u t)) (Icc 0 T) := by
  refine hu.2.norm.congr fun t ht => ?_
  exact (MemXFn.norm_toY (hu.1 t ht)).symm

theorem PathC1.add {s : ℕ} {T : ℝ} {u u' v v' : ℝ → ℂ → ℂ} (hu : PathC1 s T u u')
    (hv : PathC1 s T v v') : PathC1 s T (fun t => u t + v t) (fun t => u' t + v' t) := by
  refine ⟨PathC.add hu.1 hv.1, PathC.add hu.2.1 hv.2.1, fun t ht => ?_⟩
  have h := (hu.2.2 t ht).add (hv.2.2 t ht)
  rw [← toY_add' (hu.2.1.1 t ht) (hv.2.1.1 t ht)] at h
  exact h.congr_of_mem (fun t' ht' => toY_add' (hu.1.1 t' ht') (hv.1.1 t' ht')) ht

theorem PathC1.zero (s : ℕ) (T : ℝ) :
    PathC1 s T (fun _ => (0 : ℂ → ℂ)) (fun _ => (0 : ℂ → ℂ)) := by
  refine ⟨PathC.zero s T, PathC.zero s T, fun t _ => ?_⟩
  rw [toY_zero]
  exact hasDerivWithinAt_const _ _ _

theorem PathC1.sum {s : ℕ} {T : ℝ} {ι : Type*} (S : Finset ι) {u u' : ι → ℝ → ℂ → ℂ}
    (hu : ∀ i ∈ S, PathC1 s T (u i) (u' i)) :
    PathC1 s T (fun t => ∑ i ∈ S, u i t) (fun t => ∑ i ∈ S, u' i t) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using PathC1.zero s T
  | insert a S ha ih =>
    have h := PathC1.add (hu a (Finset.mem_insert_self a S))
      (ih fun i hi => hu i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert ha] using h

/-- Lowering the level of a `C¹` path. -/
theorem PathC1.mono_level {s s' : ℕ} {T : ℝ} {u u' : ℝ → ℂ → ℂ} (hu : PathC1 s' T u u')
    (hss : s ≤ s') : PathC1 s T u u' := by
  refine ⟨PathC.mono_level hu.1 hss, PathC.mono_level hu.2.1 hss, fun t ht => ?_⟩
  have h := ((lowerY s s' annN).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt
    (f := fun t => toY s' annN (u t)) t (hu.2.2 t ht)
  simp only [ContinuousLinearMap.coe_restrictScalars'] at h
  rw [lowerY_toY hss (hu.2.1.1 t ht)] at h
  exact h.congr_of_mem (fun t' ht' => (lowerY_toY hss (hu.1.1 t' ht')).symm) ht

/-- Paths only see the a.e. class at each time. -/
theorem PathC.congr_ae {s : ℕ} {T : ℝ} {u v : ℝ → ℂ → ℂ} (hu : PathC s T u)
    (huv : ∀ t ∈ Icc (0 : ℝ) T, u t =ᵐ[volume] v t) : PathC s T v := by
  refine ⟨fun t ht => MemXFn.congr_ae (hu.1 t ht) (huv t ht), ?_⟩
  exact hu.2.congr fun t ht => (toY_congr_ae (huv t ht)).symm

theorem PathC1.congr_ae {s : ℕ} {T : ℝ} {u u' v v' : ℝ → ℂ → ℂ} (hu : PathC1 s T u u')
    (huv : ∀ t ∈ Icc (0 : ℝ) T, u t =ᵐ[volume] v t)
    (huv' : ∀ t ∈ Icc (0 : ℝ) T, u' t =ᵐ[volume] v' t) : PathC1 s T v v' := by
  refine ⟨PathC.congr_ae hu.1 huv, PathC.congr_ae hu.2.1 huv', fun t ht => ?_⟩
  have h := hu.2.2 t ht
  rw [toY_congr_ae (huv' t ht)] at h
  exact h.congr_of_mem (fun t' ht' => (toY_congr_ae (huv t' ht')).symm) ht


/-! ### Additions for `window_approx` -/

/-- `toY` of the function of an element of a higher level is its inclusion. -/
theorem toY_fn_lower {s s' : ℕ} (hss : s ≤ s') (w : Y s' annN) :
    toY s annN w.fn = lowerY s s' annN w := by
  have hl := (lowerY_spec hss annN).1 w
  exact Y_ext_fn ((toY_spec ⟨_, hl⟩).trans hl.symm)

theorem isReal_zero (s : ℕ) (K : Set ℂ) : (0 : Y s K).IsReal := by
  have hz : (0 : Y s K).fn =ᵐ[volume] (0 : ℂ → ℂ) := by
    show ((((0 : Y s K) : SobTuple s).ofLp (idx0 s) : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ)
      =ᵐ[volume] 0
    simpa using (Lp.coeFn_zero ℂ 2 (volume : Measure ℂ))
  show ∀ᵐ x ∂(volume : Measure ℂ), ((0 : Y s K).fn x).im = 0
  filter_upwards [hz] with x hx
  rw [hx]
  rfl

/-- `toY` of a real function of `X^s` is real. -/
theorem toY_isReal {s : ℕ} {f : ℂ → ℂ} (hf : Lin.MemXFn s f)
    (hr : ∀ᵐ x ∂(volume : Measure ℂ), (f x).im = 0) : (toY s annN f).IsReal := by
  show ∀ᵐ x ∂(volume : Measure ℂ), ((toY s annN f).fn x).im = 0
  filter_upwards [MemXFn.toY_fn hf, hr] with x h1 h2
  rw [h1, h2]

/-- `‖f‖_{H^k} ≤ ‖f‖_{H^{k'}}` for `k ≤ k'`, with no membership hypothesis (copy of
`ActiveH.normH_mono_order'`). -/
theorem normH_mono_order' {k k' : ℕ} (hk : k ≤ k') (f : ℂ → ℂ) :
    normH k f ≤ normH k' f := by
  unfold normH normHOn
  apply Real.sqrt_le_sqrt
  exact Finset.sum_le_sum_of_subset_of_nonneg (multiIdx_mono hk)
    (fun _ _ _ => sq_nonneg _)

/-- Lowering the order of a `C^k`-continuous field path. -/
theorem CkPathOn.mono_order {k k' : ℕ} {U : Set ℂ} {I : Set ℝ} {h : ℝ → ℂ → ℂ}
    (hh : CkPathOn k' U I h) (hk : k ≤ k') : CkPathOn k U I h := by
  refine ⟨fun t ht => (hh.1 t ht).mono_order hk, fun t ht => ?_⟩
  refine squeeze_zero' (Eventually.of_forall fun _ => normCk_nonneg _ _ _) ?_ (hh.2 t ht)
  filter_upwards [self_mem_nhdsWithin] with t' ht'
  exact normCk_mono_order (MemCk.sub (hh.1 t' ht') (hh.1 t ht)).1 hk

/-- Along a path in `C([0,T];X^k)`, `‖u(τ') - u(τ)‖_{H^k} → 0` as `τ' → τ` in `[0,T]`. -/
theorem PathC.tendsto_normH_sub {k : ℕ} {T : ℝ} {u : ℝ → ℂ → ℂ} (hu : PathC k T u) {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) T) :
    Tendsto (fun τ' => normH k (u τ' - u τ)) (𝓝[Icc (0 : ℝ) T] τ) (𝓝 0) := by
  have hc : Tendsto (fun τ' => ‖toY k annN (u τ') - toY k annN (u τ)‖)
      (𝓝[Icc (0 : ℝ) T] τ) (𝓝 0) := by
    have := (hu.2 τ hτ)
    rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero] at this
    exact this
  refine hc.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with τ' hτ'
  rw [← toY_sub' (hu.1 τ' hτ') (hu.1 τ hτ), MemXFn.norm_toY (MemXFn.sub (hu.1 τ' hτ') (hu.1 τ hτ))]

/-- Along a path in `C([0,T];X^k)`, `‖u(τ')‖_{H^k} → ‖u(τ)‖_{H^k}`. -/
theorem PathC.tendsto_normH {k : ℕ} {T : ℝ} {u : ℝ → ℂ → ℂ} (hu : PathC k T u) {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) T) :
    Tendsto (fun τ' => normH k (u τ')) (𝓝[Icc (0 : ℝ) T] τ) (𝓝 (normH k (u τ))) := by
  have hc : Tendsto (fun τ' => ‖toY k annN (u τ')‖) (𝓝[Icc (0 : ℝ) T] τ)
      (𝓝 ‖toY k annN (u τ)‖) := ((hu.2 τ hτ).norm).tendsto
  rw [MemXFn.norm_toY (hu.1 τ hτ)] at hc
  refine hc.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with τ' hτ'
  exact MemXFn.norm_toY (hu.1 τ' hτ')

/-- An `X^k`-valued family continuous in the `H^k` norm is a path in `C([0,T];X^k)`. -/
theorem pathC_of_tendsto {k : ℕ} {T : ℝ} {u : ℝ → ℂ → ℂ}
    (hX : ∀ τ ∈ Icc (0 : ℝ) T, Lin.MemXFn k (u τ))
    (hlim : ∀ τ ∈ Icc (0 : ℝ) T,
      Tendsto (fun τ' => normH k (u τ' - u τ)) (𝓝[Icc (0 : ℝ) T] τ) (𝓝 0)) :
    PathC k T u := by
  refine ⟨hX, fun τ hτ => ?_⟩
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  refine (hlim τ hτ).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with τ' hτ'
  rw [← toY_sub' (hX τ' hτ') (hX τ hτ), MemXFn.norm_toY (MemXFn.sub (hX τ' hτ') (hX τ hτ))]

/-- A family with `‖u(τ') - u(τ)‖_{H^k} ≤ b(τ') → 0` is continuous in the `H^k` norm. -/
theorem tendsto_normH_sub_of_le {k : ℕ} {I : Set ℝ} {u : ℝ → ℂ → ℂ} {τ : ℝ} {b : ℝ → ℝ}
    (hle : ∀ᶠ τ' in 𝓝[I] τ, normH k (u τ' - u τ) ≤ b τ')
    (hb : Tendsto b (𝓝[I] τ) (𝓝 0)) :
    Tendsto (fun τ' => normH k (u τ' - u τ)) (𝓝[I] τ) (𝓝 0) :=
  squeeze_zero' (Eventually.of_forall fun _ => normH_nonneg _ _) hle hb

/-- `‖w(τ') - w(τ)‖_{H^s} → 0` along a path in `C([0,T];X^{s+1})`. -/
theorem PathC.tendsto_normH_sub_lower {s : ℕ} {T : ℝ} {u : ℝ → ℂ → ℂ} (hu : PathC (s + 1) T u)
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) :
    Tendsto (fun τ' => normH s (u τ' - u τ)) (𝓝[Icc (0 : ℝ) T] τ) (𝓝 0) := by
  refine tendsto_normH_sub_of_le ?_ (PathC.tendsto_normH_sub hu hτ)
  filter_upwards [self_mem_nhdsWithin] with τ' hτ'
  exact normH_mono_order' (Nat.le_succ s) _

/-- The `H^k` norm of a function a.e. equal to a sum of two `H^k` functions. -/
theorem normH_le_of_ae_eq_add {k : ℕ} {f g₁ g₂ : ℂ → ℂ} (h₁ : MemH k g₁) (h₂ : MemH k g₂)
    (hf : f =ᵐ[volume] g₁ + g₂) : normH k f ≤ normH k g₁ + normH k g₂ := by
  have hs := h₁.add h₂
  rw [(hs.1.congr_ae hf.symm).2]
  exact hs.2

end NonUniqueEuler.OneRing.WAppH
