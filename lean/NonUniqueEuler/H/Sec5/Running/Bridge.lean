import NonUniqueEuler.Defs.Sec4.Linear
import NonUniqueEuler.Defs.Sec4.Bridge
import NonUniqueEuler.I.Infra.Sobolev.Space
import NonUniqueEuler.I.Infra.Sobolev.Norm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.Module.Star

/-!
# Helper for `lem:running`: bridges between plane functions and `Y^s(K)`

Helper of `P/Sec5/Running.lean`. Generic facts on the chosen elements `Sect.toY s K f`:

* `RunningAux.Y_ext_fn`: an element of `Y^s(K)` is determined by its function (the first two
  lemmas are the ones of `H/Sec5/ReductionEq/Paths.lean`, whose file cannot be imported here);
* `RunningAux.exists_Y_of_memH`, `RunningAux.toY_fn`: a function of `H^s` vanishing a.e. off a
  measurable `K` is (a.e.) the function of `toY s K f`;
* `RunningAux.Y_memH_fn`, `RunningAux.Y_norm_eq`: `w.fn ∈ H^s` and `‖w‖ = ‖w.fn‖_{H^s}`;
* `RunningAux.Y_fn_sub`, `RunningAux.norm_sub_eq_normH`: differences;
* `RunningAux.memX_toY`: `toY s annN f ∈ X^s` for `f ∈ X^s` (`Lin.MemXFn s f`);
* `RunningAux.exists_memX_iff`, `RunningAux.exists_isReal_iff`: `X^s` is the kernel of a
  continuous linear map, and "real" is the equalizer of a continuous antilinear and a continuous
  linear map;
* `RunningAux.intervalIntegral_memX`, `RunningAux.intervalIntegral_isReal`: an integrable path
  with values in `X^s` (in the real elements) on `[a, b]` has its integral in `X^s` (real).
-/

noncomputable section

open MeasureTheory Set Filter Topology ComplexConjugate

namespace NonUniqueEuler.OneRing.RunningAux

open Sect Sob RingData

/-- An element of `Y^s(K)` is determined by its function. -/
theorem Y_ext_fn {s : ℕ} {K : Set ℂ} {w₁ w₂ : Y s K} (h : w₁.fn =ᵐ[volume] w₂.fn) : w₁ = w₂ := by
  have : Y.toHk w₁ = Y.toHk w₂ := Hk.ext_fn h
  exact Subtype.ext (show (w₁ : SobTuple s) = w₂ from
    congrArg (fun F : Hk s => (F : SobTuple s)) this)

/-- `Sect.toY` only depends on the a.e. class of the function. -/
theorem toY_congr_ae {s : ℕ} {K : Set ℂ} {f g : ℂ → ℂ} (h : f =ᵐ[volume] g) :
    toY s K f = toY s K g := by
  classical
  by_cases hf : ∃ w : Y s K, w.fn =ᵐ[volume] f
  · have hg : ∃ w : Y s K, w.fn =ᵐ[volume] g := let ⟨w, hw⟩ := hf; ⟨w, hw.trans h⟩
    exact Y_ext_fn ((toY_spec hf).trans (h.trans (toY_spec hg).symm))
  · have hg : ¬ ∃ w : Y s K, w.fn =ᵐ[volume] g := fun ⟨w, hw⟩ => hf ⟨w, hw.trans h.symm⟩
    simp [toY, hf, hg]

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
theorem toY_fn {s : ℕ} {K : Set ℂ} (hKm : MeasurableSet K) {f : ℂ → ℂ}
    (hf : MemH s f) (hK : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ K → f x = 0) :
    (toY s K f).fn =ᵐ[volume] f :=
  toY_spec (exists_Y_of_memH hKm hf hK)

/-- The function of `w ∈ Y^s(K)` lies in `H^s`. -/
theorem Y_memH_fn {s : ℕ} {K : Set ℂ} (w : Y s K) : MemH s w.fn :=
  (Hk.memH_fn (Y.toHk w)).1

/-- The norm of `Y^s(K)` is the `H^s` norm of the function. -/
theorem Y_norm_eq {s : ℕ} {K : Set ℂ} (w : Y s K) : ‖w‖ = normH s w.fn := by
  have h := (Hk.memH_fn (Y.toHk w)).2
  have h' : ‖Y.toHk w‖ = ‖w‖ := rfl
  rw [← h', ← h]
  rfl

/-- The function of a difference. -/
theorem Y_fn_sub {s : ℕ} {K : Set ℂ} (w w' : Y s K) :
    (w - w').fn =ᵐ[volume] fun x => w.fn x - w'.fn x := by
  have h : (((w - w' : Y s K) : SobTuple s)).ofLp (idx0 s) =
      (w : SobTuple s).ofLp (idx0 s) - (w' : SobTuple s).ofLp (idx0 s) := rfl
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
  rw [Y_norm_eq, (MemH.congr_ae (Y_memH_fn (w - w')) hae).2]

/-- The underlying `L²` function of `w ∈ Y^s(K)`. -/
theorem coeFn_proj0 {s : ℕ} {K : Set ℂ} (w : Y s K) :
    ((proj0 s (w : SobTuple s) : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) = w.fn := rfl

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

/-- For `f ∈ X^s` (`Lin.MemXFn s f`), `toY s annN f ∈ X^s`, with function `f` a.e. -/
theorem memX_toY {s : ℕ} {f : ℂ → ℂ} (hf : Lin.MemXFn s f) :
    (toY s annN f).fn =ᵐ[volume] f ∧ Lin.MemX (toY s annN f) := by
  have hKm : MeasurableSet annN := (isClosed_closedAnnulus _ _).measurableSet
  have hfn : (toY s annN f).fn =ᵐ[volume] f := toY_fn hKm hf.1 hf.2.1
  refine ⟨hfn, ?_⟩
  rw [Lin.memX_iff, YsymSub, Submodule.mem_inf, LinearMap.mem_ker]
  refine ⟨(toY s annN f).2, ?_⟩
  rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, sub_apply,
    ContinuousLinearMap.id_apply, sub_eq_zero]
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
  have hfi : IntegrableOn f (Ioc a b) volume := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hf
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

end NonUniqueEuler.OneRing.RunningAux
