import NonUniqueEuler.Defs.Sec4.Bridge
import NonUniqueEuler.I.Infra.Sobolev.Space
import NonUniqueEuler.I.Infra.Sobolev.Paths
import NonUniqueEuler.I.Infra.Sobolev.Smooth

/-!
# Helpers for `lem:reduction`(3): smooth paths in `Y^k(K)`

Helper of `P/Sec5/ReductionEq.lean`. Generic bridges between the chosen elements
`Sect.toY k K f` of `Y^k(K)` and `Sob.toHk k f` of `H^k`, and the regularity of smooth families:

* `RedEqH.Y_ext_fn`: an element of `Y^k(K)` is determined by its function;
* `RedEqH.toY_congr_ae`: `Sect.toY` only sees the a.e. class of the function;
* `RedEqH.coe_toY_eq_coe_toHk`: for `f ∈ H^k` vanishing a.e. off `K`, `toY k K f` and `toHk k f`
  are the same tuple;
* `RedEqH.hasDerivWithinAt_toY_of_contDiff`, `RedEqH.continuousOn_toY_of_contDiff`: a jointly
  smooth family `u(t,x)` with spatial supports in a fixed compact set for `t` in an open set `I`,
  and supported in `K` for `t ∈ J ⊆ I`, is differentiable within `J` (and continuous on `J`) as a
  path in `Y^k(K)`, with derivative `∂_t u` (`I/Infra/Sobolev/Paths.lean`).
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace NonUniqueEuler.OneRing.RedEqH

open Sect Sob

/-- An element of `Y^k(K)` is determined by its function. -/
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

/-- For `f ∈ H^k` vanishing a.e. outside the measurable set `K`, the tuple of `toY k K f` is the
tuple of `toHk k f`. -/
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

/-- A path in a submodule is differentiable within a set if its coercion is. -/
theorem hasDerivWithinAt_of_coe {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {p : Submodule ℂ E} {f : ℝ → p} {f' : p} {J : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt (fun s => (f s : E)) (f' : E) J t) : HasDerivWithinAt f f' J t := by
  rw [hasDerivWithinAt_iff_tendsto] at h ⊢
  refine h.congr fun s => ?_
  congr 1

/-- The `t`-derivative of a jointly smooth family is jointly smooth. -/
theorem contDiff_deriv_fst {u : ℝ → ℂ → ℂ} (hu : ContDiff ℝ ∞ (fun p : ℝ × ℂ => u p.1 p.2)) :
    ContDiff ℝ ∞ (fun p : ℝ × ℂ => deriv (fun s => u s p.2) p.1) := by
  have heq : (fun p : ℝ × ℂ => deriv (fun s => u s p.2) p.1) =
      fun p => fderiv ℝ (fun q : ℝ × ℂ => u q.1 q.2) p ((1 : ℝ), (0 : ℂ)) := by
    funext p
    have hd : HasFDerivAt (fun q : ℝ × ℂ => u q.1 q.2)
        (fderiv ℝ (fun q : ℝ × ℂ => u q.1 q.2) p) p :=
      (hu.differentiable (by simp)).differentiableAt.hasFDerivAt
    have hl : HasDerivAt (fun s : ℝ => ((s, p.2) : ℝ × ℂ)) ((1 : ℝ), (0 : ℂ)) p.1 :=
      (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
    have := hd.comp_hasDerivAt (x := p.1) (by simpa using hl)
    exact this.deriv
  rw [heq]
  exact (hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- The slices of a jointly smooth family are smooth. -/
theorem contDiff_slice {u : ℝ → ℂ → ℂ} (hu : ContDiff ℝ ∞ (fun p : ℝ × ℂ => u p.1 p.2))
    (t : ℝ) : ContDiff ℝ ∞ (u t) :=
  hu.comp (contDiff_const.prodMk contDiff_id)

/-- Supports of the `t`-derivative: if `u(s, x) = 0` for `s` in the open set `I` and `x ∉ K'`,
then `∂_t u(t, x) = 0` for `t ∈ I` and `x ∉ K'`. -/
theorem deriv_eq_zero_of_supp {u : ℝ → ℂ → ℂ} {K' : Set ℂ} {I : Set ℝ} (hI : IsOpen I)
    (hsupp : ∀ t ∈ I, ∀ x ∉ K', u t x = 0) {t : ℝ} (ht : t ∈ I) {x : ℂ} (hx : x ∉ K') :
    deriv (fun s => u s x) t = 0 := by
  have : (fun s => u s x) =ᶠ[𝓝 t] fun _ => (0 : ℂ) := by
    filter_upwards [hI.mem_nhds ht] with s hs
    exact hsupp s hs x hx
  rw [this.deriv_eq, deriv_const]

/-- A jointly smooth family with spatial supports in the fixed compact `K'` for `t` in the open
set `I`, whose slices vanish outside `K` for `t ∈ J ⊆ I`, is continuous on `J` as a path in
`Y^k(K)`. -/
theorem continuousOn_toY_of_contDiff {k : ℕ} {u : ℝ → ℂ → ℂ}
    (hu : ContDiff ℝ ∞ (fun p : ℝ × ℂ => u p.1 p.2)) {K' : Set ℂ} (hK' : IsCompact K')
    {I : Set ℝ} (hI : IsOpen I) (hsupp : ∀ t ∈ I, ∀ x ∉ K', u t x = 0) {J : Set ℝ}
    (hJI : J ⊆ I) {K : Set ℂ} (hKm : MeasurableSet K) (hJ : ∀ t ∈ J, ∀ x ∉ K, u t x = 0) :
    ContinuousOn (fun s => toY k K (u s)) J := by
  have hc : ContinuousOn (fun s => ((toHk k (u s) : Hk k) : SobTuple k)) J :=
    ((HkSub k).subtypeL.continuous.comp_continuousOn
      (continuousOn_toHk_of_contDiff hu hK' hI hsupp)).mono hJI
  have heq : ∀ s ∈ J, ((toY k K (u s) : Y k K) : SobTuple k) = ((toHk k (u s) : Hk k) : SobTuple k) :=
    fun s hs => coe_toY_eq_coe_toHk hKm
      (memH_of_contDiff_hasCompactSupport (contDiff_slice hu s)
        (HasCompactSupport.intro hK' (hsupp s (hJI hs))) k).1
      (Eventually.of_forall fun x hx => hJ s hs x hx)
  rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
  exact hc.congr fun s hs => heq s hs

/-- A jointly smooth family with spatial supports in the fixed compact `K'` for `t` in the open
set `I`, whose slices and `t`-derivatives vanish outside `K` for `t ∈ J ⊆ I`, is differentiable
within `J` as a path in `Y^k(K)`, with derivative `∂_t u`. -/
theorem hasDerivWithinAt_toY_of_contDiff {k : ℕ} {u : ℝ → ℂ → ℂ}
    (hu : ContDiff ℝ ∞ (fun p : ℝ × ℂ => u p.1 p.2)) {K' : Set ℂ} (hK' : IsCompact K')
    {I : Set ℝ} (hI : IsOpen I) (hsupp : ∀ t ∈ I, ∀ x ∉ K', u t x = 0) {J : Set ℝ}
    (hJI : J ⊆ I) {K : Set ℂ} (hKm : MeasurableSet K) (hJ : ∀ t ∈ J, ∀ x ∉ K, u t x = 0)
    (hJ' : ∀ t ∈ J, ∀ x ∉ K, deriv (fun s => u s x) t = 0) {t : ℝ} (ht : t ∈ J) :
    HasDerivWithinAt (fun s => toY k K (u s))
      (toY k K (fun x => deriv (fun s => u s x) t)) J t := by
  have hmem : ∀ s ∈ I, MemH k (u s) := fun s hs =>
    (memH_of_contDiff_hasCompactSupport (contDiff_slice hu s)
      (HasCompactSupport.intro hK' (hsupp s hs)) k).1
  have hdu := contDiff_deriv_fst hu
  have hmem' : MemH k (fun x => deriv (fun s => u s x) t) :=
    (memH_of_contDiff_hasCompactSupport
      (contDiff_slice (u := fun t x => deriv (fun s => u s x) t) hdu t)
      (HasCompactSupport.intro hK'
        fun x hx => deriv_eq_zero_of_supp hI hsupp (hJI ht) hx) k).1
  have hd : HasDerivAt (fun s => ((toHk k (u s) : Hk k) : SobTuple k))
      ((toHk k (fun x => deriv (fun s => u s x) t) : Hk k) : SobTuple k) t :=
    ((HkSub k).subtypeL.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_toHk_of_contDiff hu hK' hI hsupp (hJI ht))
  have heq : ∀ s ∈ J,
      ((toY k K (u s) : Y k K) : SobTuple k) = ((toHk k (u s) : Hk k) : SobTuple k) :=
    fun s hs => coe_toY_eq_coe_toHk hKm (hmem s (hJI hs))
      (Eventually.of_forall fun x hx => hJ s hs x hx)
  have heq' : ((toY k K (fun x => deriv (fun s => u s x) t) : Y k K) : SobTuple k) =
      ((toHk k (fun x => deriv (fun s => u s x) t) : Hk k) : SobTuple k) :=
    coe_toY_eq_coe_toHk hKm hmem' (Eventually.of_forall fun x hx => hJ' t ht x hx)
  apply hasDerivWithinAt_of_coe
  rw [heq']
  exact hd.hasDerivWithinAt.congr_of_mem heq ht

end NonUniqueEuler.OneRing.RedEqH
