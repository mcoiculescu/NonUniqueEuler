import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Infra.Sobolev.Space
import NonUniqueEuler.I.Infra.Sobolev.Norm
import NonUniqueEuler.I.Infra.Sobolev.NormDeriv
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv

/-!
# Helpers for `lem:energy`: the elements `Sect.toY s K f` of `Y^s(K)` and the space `X^s`

Helper of `P/Sec5/Energy.lean`. For `f ∈ H^s` vanishing a.e. outside a measurable `K`:
* `EnergyH.coe_toY_eq_coe_toHk`: `toY s K f` and `toHk s f` are the same tuple;
* `EnergyH.toY_fn_ae`, `EnergyH.norm_toY`: its function is `f` a.e. and its norm is `‖f‖_{H^s}`;
* `EnergyH.toY_add`, `EnergyH.toY_neg`, `EnergyH.toY_sub`, `EnergyH.toY_congr_ae`: `Sect.toY` is
  additive on such functions and only sees the a.e. class;
* `EnergyH.inner_toY`: `⟪toY f, toY g⟫ = ∑_{|γ| ≤ s} ⟨∂^γ g, ∂^γ f⟩_{L²}`
  (`Prelim.innerL2`, linear in its first argument);
* `EnergyH.MemXFn.add`, `.sub`, `.mono`: `X^s` is a linear space, decreasing in `s`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ComplexConjugate

namespace NonUniqueEuler.OneRing.EnergyH

open Sect Sob

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
  rw [Submodule.coe_add, coe_toY_eq_coe_toHk hKm (hf.add hg).1 hfgK, coe_toY_eq_coe_toHk hKm hf hfK,
    coe_toY_eq_coe_toHk hKm hg hgK, toHk_add hf hg, Submodule.coe_add]

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

theorem toY_sub {s : ℕ} {K : Set ℂ} (hKm : MeasurableSet K) {f g : ℂ → ℂ} (hf : MemH s f)
    (hfK : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ K → f x = 0) (hg : MemH s g)
    (hgK : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ K → g x = 0) :
    toY s K (f - g) = toY s K f - toY s K g := by
  have hng : MemH s (-g) := by
    have h := (hg.const_smul (-1)).1
    have hneg : (-1 : ℂ) • g = -g := by funext x; simp
    rwa [hneg] at h
  have hngK : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ K → (-g) x = 0 := by
    filter_upwards [hgK] with x h hx
    simp [h hx]
  rw [sub_eq_add_neg, toY_add hKm hf hfK hng hngK, toY_neg hKm hg hgK, ← sub_eq_add_neg]

/-- The stored derivatives of `toHk s f` are the weak derivatives of `f`. -/
theorem der_toHk_ae {s : ℕ} {f : ℂ → ℂ} (hf : MemH s f) (γ : SobIdx s) :
    (toHk s f).der γ =ᵐ[volume] weakPartial γ.1 f := by
  have hw := Hk.hasWeakDeriv (toHk s f) γ
  have hff : (toHk s f).fn =ᵐ[volume] f := toHk_fn hf
  have hw' : HasWeakDerivOn univ (pdList γ.1) f ((toHk s f).der γ) :=
    hw.congr_ae (by filter_upwards [hff] with x hx _ using hx)
      (Eventually.of_forall fun _ _ => rfl)
  have hL : MemLp ((toHk s f).der γ) 2 volume := Lp.memLp _
  exact (hf.weakPartial_ae_eq γ.2 hL hw').symm

/-- **The inner product of `Y^s(K)`** for elements given by functions:
`⟪toY f, toY g⟫ = ∑_{|γ| ≤ s} ∫ ∂^γ g · conj(∂^γ f)`. -/
theorem inner_toY {s : ℕ} {K : Set ℂ} (hKm : MeasurableSet K) {f g : ℂ → ℂ} (hf : MemH s f)
    (hfK : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ K → f x = 0) (hg : MemH s g)
    (hgK : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ K → g x = 0) :
    inner ℂ (toY s K f) (toY s K g) =
      ∑ γ : SobIdx s, Prelim.innerL2 (weakPartial γ.1 g) (weakPartial γ.1 f) := by
  rw [Submodule.coe_inner, coe_toY_eq_coe_toHk hKm hf hfK, coe_toY_eq_coe_toHk hKm hg hgK,
    ← Submodule.coe_inner, Hk.inner_eq]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [L2.inner_def, Prelim.innerL2]
  refine integral_congr_ae ?_
  filter_upwards [der_toHk_ae hf γ, der_toHk_ae hg γ] with x h1 h2
  have e1 : (((toHk s f : Hk s) : SobTuple s).ofLp γ : ℂ → ℂ) x = weakPartial γ.1 f x := h1
  have e2 : (((toHk s g : Hk s) : SobTuple s).ofLp γ : ℂ → ℂ) x = weakPartial γ.1 g x := h2
  rw [RCLike.inner_apply, e1, e2]

/-! ### The space `X^s` -/

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

/-- `‖toY s N f‖ = ‖f‖_{H^s}` for `f ∈ X^s`. -/
theorem MemXFn.norm_toY {s : ℕ} {f : ℂ → ℂ} (hf : Lin.MemXFn s f) :
    ‖toY s RingData.annN f‖ = normH s f :=
  EnergyH.norm_toY (isClosed_closedAnnulus _ _).measurableSet hf.1 hf.2.1

end NonUniqueEuler.OneRing.EnergyH
