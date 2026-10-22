import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Infra.Sobolev.Norm
import NonUniqueEuler.I.Infra.Sobolev.Space

/-!
# Helpers for `lem:linear-part`: bridges between plane functions and `Y^s(N)`

Helper of `P/Sec5/LinearPart.lean` (fully proved). Namespace
`NonUniqueEuler.OneRing.LinearPartH`.

* `Y_ext_fn`: an element of `Y^s(K)` is determined by its function (a.e.);
* `Y.memH_fn`: the function of `w ∈ Y^s(K)` is in `H^s`, with norm `‖w‖`;
* `Y.fn_sub`, `Y.fn_neg`: the function of a difference / negative (a.e.);
* `toY_fn_and_norm`: for `f ∈ H^s` vanishing a.e. off a measurable `K`, `toY s K f` has
  function `f` and norm `‖f‖_{H^s}` (the same argument as the helper of `thm:quiet`,
  `H/Sec5/Quiet/Basic.lean`, which a proof file may not import);
* `memX_toY`, `norm_toY`: for `f ∈ X^s`, `toY s N f ∈ X^s` and `‖toY s N f‖ = ‖f‖_{H^s}`;
* `toY_neg`: `toY s N (-f) = -toY s N f` for `f ∈ X^s`.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace NonUniqueEuler.OneRing.LinearPartH

open RingData Sect Sob

/-- An element of `Y^s(K)` is determined by its function. -/
theorem Y_ext_fn {s : ℕ} {K : Set ℂ} {w₁ w₂ : Y s K} (h : w₁.fn =ᵐ[volume] w₂.fn) :
    w₁ = w₂ := by
  have : Y.toHk w₁ = Y.toHk w₂ := Hk.ext_fn h
  exact Subtype.ext (show (w₁ : SobTuple s) = w₂ from
    congrArg (fun F : Hk s => (F : SobTuple s)) this)

/-- The function of an element of `Y^s(K)` lies in `H^s`, with norm the norm of the element. -/
theorem Y.memH_fn {s : ℕ} {K : Set ℂ} (w : Y s K) : MemH s w.fn ∧ normH s w.fn = ‖w‖ := by
  have h := Hk.memH_fn (Y.toHk w)
  exact ⟨h.1, h.2⟩

/-- The function of a difference. -/
theorem Y.fn_sub {s : ℕ} {K : Set ℂ} (w₁ w₂ : Y s K) :
    (w₁ - w₂).fn =ᵐ[volume] w₁.fn - w₂.fn := by
  have h : ((w₁ - w₂ : Y s K) : SobTuple s).ofLp (idx0 s) =
      (w₁ : SobTuple s).ofLp (idx0 s) - (w₂ : SobTuple s).ofLp (idx0 s) := rfl
  show (((w₁ - w₂ : Y s K) : SobTuple s).ofLp (idx0 s) : ℂ → ℂ) =ᵐ[volume] _
  rw [h]
  exact Lp.coeFn_sub _ _

/-- The function of a negative. -/
theorem Y.fn_neg {s : ℕ} {K : Set ℂ} (w : Y s K) :
    (-w).fn =ᵐ[volume] -w.fn := by
  have h : ((-w : Y s K) : SobTuple s).ofLp (idx0 s) = -(w : SobTuple s).ofLp (idx0 s) := rfl
  show (((-w : Y s K) : SobTuple s).ofLp (idx0 s) : ℂ → ℂ) =ᵐ[volume] _
  rw [h]
  exact Lp.coeFn_neg _

/-- For `f ∈ H^s` vanishing a.e. outside the measurable set `K`, `toY s K f` has function `f`
(a.e.) and norm `‖f‖_{H^s}`; the witness `∃ w, w.fn = f` is part of the conclusion. -/
theorem toY_fn_and_norm {s : ℕ} {K : Set ℂ} (hKm : MeasurableSet K) {f : ℂ → ℂ}
    (hf : MemH s f) (hK : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ K → f x = 0) :
    (∃ w : Y s K, w.fn =ᵐ[volume] f) ∧
      (toY s K f).fn =ᵐ[volume] f ∧ ‖toY s K f‖ = normH s f := by
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
  have hspec : (toY s K f).fn =ᵐ[volume] f := toY_spec ⟨w, hw⟩
  refine ⟨⟨w, hw⟩, hspec, ?_⟩
  have hY := Y.memH_fn (toY s K f)
  rw [← hY.2, (hY.1.congr_ae hspec).2]

/-- `annN` is measurable. -/
theorem measurableSet_annN : MeasurableSet annN :=
  isCompact_annN.isClosed.measurableSet

/-- For `f ∈ X^s`, `‖toY s N f‖ = ‖f‖_{H^s}`. -/
theorem norm_toY {s : ℕ} {f : ℂ → ℂ} (hf : Lin.MemXFn s f) :
    ‖toY s annN f‖ = normH s f :=
  (toY_fn_and_norm measurableSet_annN hf.1 hf.2.1).2.2

/-- For `f ∈ X^s`, the function of `toY s N f` is `f` (a.e.). -/
theorem toY_fn {s : ℕ} {f : ℂ → ℂ} (hf : Lin.MemXFn s f) :
    (toY s annN f).fn =ᵐ[volume] f :=
  (toY_fn_and_norm measurableSet_annN hf.1 hf.2.1).2.1

/-- For `f ∈ X^s`, `toY s N f ∈ X^s`. -/
theorem memX_toY {s : ℕ} {f : ℂ → ℂ} (hf : Lin.MemXFn s f) :
    Lin.MemX (toY s annN f) := by
  set w := toY s annN f with hwdef
  have hwf : w.fn =ᵐ[volume] f := toY_fn hf
  refine Submodule.mem_inf.2 ⟨w.2, LinearMap.mem_ker.2 ?_⟩
  rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
    sub_apply, ContinuousLinearMap.id_apply, sub_eq_zero]
  set F : Lp ℂ 2 (volume : Measure ℂ) := proj0 s (w : SobTuple s) with hFdef
  have hF : (F : ℂ → ℂ) = w.fn := rfl
  refine Lp.ext ?_
  have h1 := Ang.rotLp_coeFn (2 * Real.pi / ((3 : ℕ) : ℝ)) F
  refine h1.trans ?_
  have h2 : (fun x => (F : ℂ → ℂ) (rot (2 * Real.pi / ((3 : ℕ) : ℝ)) x)) =ᵐ[volume]
      fun x => f (rot (2 * Real.pi / ((3 : ℕ) : ℝ)) x) := by
    rw [hF]
    exact (Polar.measurePreserving_rot _).quasiMeasurePreserving.ae_eq_comp hwf
  refine h2.trans ?_
  refine (hf.2.2 : (fun x => f (rot (2 * Real.pi / ((3 : ℕ) : ℝ)) x)) =ᵐ[volume] f).trans ?_
  rw [hF]
  exact hwf.symm

/-- `toY s N (-f) = -toY s N f` for `f ∈ X^s`. -/
theorem toY_neg {s : ℕ} {f : ℂ → ℂ} (hf : Lin.MemXFn s f) :
    toY s annN (fun x => -f x) = -toY s annN f := by
  have h1 : (-toY s annN f).fn =ᵐ[volume] fun x => -f x := by
    filter_upwards [Y.fn_neg (toY s annN f), toY_fn hf] with x hx1 hx2
    rw [hx1, Pi.neg_apply, hx2]
  have h2 : (toY s annN (fun x => -f x)).fn =ᵐ[volume] fun x => -f x :=
    toY_spec ⟨_, h1⟩
  exact Y_ext_fn (h2.trans h1.symm)

end NonUniqueEuler.OneRing.LinearPartH
