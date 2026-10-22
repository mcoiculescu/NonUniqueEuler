import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Infra.Sobolev.Space
import NonUniqueEuler.I.Infra.Sobolev.Norm
import NonUniqueEuler.I.Infra.Polar.Fubini
import NonUniqueEuler.I.Sec4.SemigroupLaw
import NonUniqueEuler.I.Sec4.RingFacts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Helper for `lem:coupling`: bridges between plane functions and `Y^s(N)`

Helper of `P/Sec8/Coupling.lean` (fully proved, modulo the interface files it imports).

The first group of lemmas is copied from the helpers `H/Sec5/Running/Bridge.lean`,
`H/Sec5/Running/EllCongr.lean` and `H/Sec5/Running/Integrand.lean` of `lem:running` (a helper of
another proof cannot be imported), in the namespace `CouplingAux` to avoid clashes in the full
library:
* `Y_ext_fn`, `toY_congr_ae`, `exists_Y_of_memH`, `toY_fn`, `Y_memH_fn`, `Y_norm_eq`, `Y_fn_sub`,
  `norm_sub_eq_normH`, `memX_toY`: the chosen elements `Sect.toY s K f`;
* `angularSector_congr_ae`, `ellFn_congr_ae`: `ℓ_*(G)` on functions only sees the a.e. class;
* `continuousOn_S_comp`, `intervalIntegrable_S_comp`: the Duhamel integrand is continuous.

New here:
* `memH_zero`, `memXFn_zero`, `toY_zero`, `Y_fn_add`, `toY_add`: the zero function and sums;
* `wlin_add`: the linear response is additive in the field (`lem:coupling`(3)).
-/

noncomputable section

open MeasureTheory Set Real Filter Topology
open scoped ENNReal

namespace NonUniqueEuler.CouplingAux

open Sect Sob RingData OneRing

/-! ### Elements of `Y^s(K)` and their functions (copied from `H/Sec5/Running/Bridge.lean`) -/

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

/-- The function of a sum. -/
theorem Y_fn_add {s : ℕ} {K : Set ℂ} (w w' : Y s K) :
    (w + w').fn =ᵐ[volume] fun x => w.fn x + w'.fn x := by
  have h : (((w + w' : Y s K) : SobTuple s)).ofLp (idx0 s) =
      (w : SobTuple s).ofLp (idx0 s) + (w' : SobTuple s).ofLp (idx0 s) := rfl
  have h2 : (w + w').fn = (((w + w' : Y s K) : SobTuple s).ofLp (idx0 s) : ℂ → ℂ) := rfl
  rw [h2, h]
  exact Lp.coeFn_add _ _

/-- The function of `0`. -/
theorem Y_fn_zero {s : ℕ} {K : Set ℂ} : (0 : Y s K).fn =ᵐ[volume] (0 : ℂ → ℂ) := by
  have h : (((0 : Y s K) : SobTuple s)).ofLp (idx0 s) = 0 := rfl
  have h2 : (0 : Y s K).fn = ((((0 : Y s K) : SobTuple s)).ofLp (idx0 s) : ℂ → ℂ) := rfl
  rw [h2, h]
  exact Lp.coeFn_zero _ _ _

/-- `‖w - w'‖ = ‖f - f'‖_{H^s}` when `w, w'` have the functions `f, f'`. -/
theorem norm_sub_eq_normH {s : ℕ} {K : Set ℂ} {w w' : Y s K} {f f' : ℂ → ℂ}
    (hw : w.fn =ᵐ[volume] f) (hw' : w'.fn =ᵐ[volume] f') :
    ‖w - w'‖ = normH s (fun x => f x - f' x) := by
  have hae : (w - w').fn =ᵐ[volume] fun x => f x - f' x := by
    filter_upwards [Y_fn_sub w w', hw, hw'] with x h1 h2 h3
    rw [h1, h2, h3]
  rw [Y_norm_eq, (MemH.congr_ae (Y_memH_fn (w - w')) hae).2]

/-- `annN` is measurable. -/
theorem measurableSet_annN : MeasurableSet annN := (isClosed_closedAnnulus _ _).measurableSet

/-- For `f ∈ X^s` (`Lin.MemXFn s f`), `toY s annN f ∈ X^s`, with function `f` a.e. -/
theorem memX_toY {s : ℕ} {f : ℂ → ℂ} (hf : Lin.MemXFn s f) :
    (toY s annN f).fn =ᵐ[volume] f ∧ Lin.MemX (toY s annN f) := by
  have hfn : (toY s annN f).fn =ᵐ[volume] f := toY_fn measurableSet_annN hf.1 hf.2.1
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

/-! ### The zero function and sums (new) -/

/-- The zero function lies in every `H^s`. -/
theorem memH_zero (s : ℕ) : MemH s (0 : ℂ → ℂ) := by
  refine ⟨MemLp.zero, fun γ _ => ⟨0, MemLp.zero, fun φ _ => ?_⟩⟩
  simp

/-- The zero function lies in every `X^s`. -/
theorem memXFn_zero (s : ℕ) : Lin.MemXFn s (0 : ℂ → ℂ) :=
  ⟨memH_zero s, Eventually.of_forall fun _ _ => rfl, Eventually.of_forall fun _ => rfl⟩

/-- `toY s annN 0 = 0`. -/
theorem toY_zero (s : ℕ) : toY s annN (0 : ℂ → ℂ) = 0 :=
  Y_ext_fn ((memX_toY (memXFn_zero s)).1.trans Y_fn_zero.symm)

/-- `toY` is additive on `X^s`. -/
theorem toY_add {s : ℕ} {f g : ℂ → ℂ} (hf : Lin.MemXFn s f) (hg : Lin.MemXFn s g) :
    toY s annN (fun x => f x + g x) = toY s annN f + toY s annN g := by
  have hfg : MemH s (fun x => f x + g x) := (MemH.add hf.1 hg.1).1
  have hsupp : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → f x + g x = 0 := by
    filter_upwards [hf.2.1, hg.2.1] with x h1 h2 hx
    rw [h1 hx, h2 hx, add_zero]
  refine Y_ext_fn ?_
  filter_upwards [toY_fn measurableSet_annN hfg hsupp, Y_fn_add (toY s annN f) (toY s annN g),
    (memX_toY hf).1, (memX_toY hg).1] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]

/-! ### `ℓ_*` only sees the a.e. class (copied from `H/Sec5/Running/EllCongr.lean`) -/

/-- The polar parametrisation `(r, θ) ↦ r e^{iθ}` is continuous. -/
theorem continuous_polarParam :
    Continuous fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I) := by
  fun_prop

/-- a.e. equal functions on `ℂ` have a.e. equal angular sectors on `(0, ∞)`. -/
theorem angularSector_congr_ae {g g' : ℂ → ℂ} (h : g =ᵐ[volume] g') (ℓ : ℤ) :
    Polar.angularSector g ℓ =ᵐ[volume.restrict (Ioi 0)] Polar.angularSector g' ℓ := by
  have h0 : volume {x | ¬ g x = g' x} = 0 := ae_iff.1 h
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null h0
  have hmeasN : Measurable (N.indicator (1 : ℂ → ℝ≥0∞)) := measurable_one.indicator hNm
  have hT := Polar.lintegral_eq_lintegral_Ioi_circle hmeasN
  rw [lintegral_indicator_one hNm, hN0] at hT
  have hFm : Measurable fun p : ℝ × ℝ => N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 p.1 p.2) := by
    refine hmeasN.comp ?_
    have : (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) =
        fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I) := by
      funext p; simp [circleMap]
    rw [this]
    exact continuous_polarParam.measurable
  have hGm : Measurable fun r : ℝ => ENNReal.ofReal r *
      ∫⁻ θ in Ioc (0 : ℝ) (2 * π), N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 r θ) :=
    ENNReal.measurable_ofReal.mul (hFm.lintegral_prod_right' (ν := volume.restrict (Ioc 0 (2 * π))))
  have hae := (lintegral_eq_zero_iff hGm).1 hT.symm
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioi] with r hr hrpos
  have hrpos' : (0 : ℝ) < r := hrpos
  have hr' : ∫⁻ θ in Ioc (0 : ℝ) (2 * π), N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 r θ) = 0 := by
    have hr2 : ENNReal.ofReal r *
        ∫⁻ θ in Ioc (0 : ℝ) (2 * π), N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 r θ) = 0 := hr
    rcases mul_eq_zero.1 hr2 with h1 | h1
    · exact absurd h1 (ENNReal.ofReal_pos.2 hrpos').ne'
    · exact h1
  have hθm : Measurable fun θ : ℝ => N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 r θ) :=
    hFm.comp (measurable_const.prodMk measurable_id)
  have hθ := (lintegral_eq_zero_iff hθm).1 hr'
  unfold Polar.angularSector
  congr 1
  rw [intervalIntegral.integral_of_le (by positivity), intervalIntegral.integral_of_le (by positivity)]
  refine integral_congr_ae ?_
  filter_upwards [hθ] with θ hθ'
  have hnot : circleMap 0 r θ ∉ N := by
    intro hmem
    have : N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 r θ) = 1 := indicator_of_mem hmem _
    simp [this] at hθ'
  have hcm : circleMap 0 r θ = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    simp [circleMap]
  rw [hcm] at hnot
  have heq : g ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
      g' ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
    by_contra hne
    exact hnot (hNsub hne)
  simp only [heq]

/-- `ℓ_*(G)` on functions (`Eig.ellFn`) only depends on the a.e. class of the function. -/
theorem ellFn_congr_ae (χ : ℝ → ℝ) (G : ℝ) {f g : ℂ → ℂ} (hfg : f =ᵐ[volume] g) :
    Eig.ellFn χ G f = Eig.ellFn χ G g := by
  have hs := angularSector_congr_ae hfg 3
  unfold Eig.ellFn SectorSetting.ellStar
  congr 2
  refine integral_congr_ae ?_
  filter_upwards [hs] with r hr
  rw [hr]

/-! ### The Duhamel integrand (copied from `H/Sec5/Running/Integrand.lean`) -/

/-- `v ↦ e^{(u-v)L(G)} g(v)` is continuous on `[0,u]` for `g` continuous on `[0,u]`. -/
theorem continuousOn_S_comp (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (s : ℕ) (G : ℝ) {u : ℝ}
    {g : ℝ → Y s annN} (hg : ContinuousOn g (Icc 0 u)) :
    ContinuousOn (fun v => Lin.S χ s G (u - v) (g v)) (Icc 0 u) := by
  obtain ⟨B, hB⟩ :=
    (ringPhiSetting χ).semigroup_bound (ringPhiSetting_valid hχ) s (abs_nonneg G) u
  intro v₀ hv₀
  have hmaps : MapsTo (fun v => u - v) (Icc 0 u) (Icc 0 u) := fun v hv =>
    ⟨by linarith [hv.2], by linarith [hv.1]⟩
  have h2 : ContinuousWithinAt (fun v => Lin.S χ s G (u - v) (g v₀)) (Icc 0 u) v₀ := by
    have hc := (ringPhiSetting χ).semigroup_continuousOn (ringPhiSetting_valid hχ) s G (g v₀)
    have h3 : ContinuousWithinAt (fun t => Lin.S χ s G t (g v₀)) (Icc 0 u) (u - v₀) :=
      (hc (u - v₀) (show (0 : ℝ) ≤ u - v₀ by linarith [hv₀.2])).mono Icc_subset_Ici_self
    exact h3.comp (continuousWithinAt_const.sub continuousWithinAt_id) hmaps
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero] at h2 ⊢
  have h1 : Tendsto (fun v => ‖g v - g v₀‖) (𝓝[Icc 0 u] v₀) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 (hg v₀ hv₀)
  have hlim : Tendsto (fun v => B * ‖g v - g v₀‖ +
      ‖Lin.S χ s G (u - v) (g v₀) - Lin.S χ s G (u - v₀) (g v₀)‖) (𝓝[Icc 0 u] v₀) (𝓝 0) := by
    simpa using (h1.const_mul B).add h2
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (eventually_nhdsWithin_of_forall fun v hv => ?_) hlim
  have hsplit : Lin.S χ s G (u - v) (g v) - Lin.S χ s G (u - v₀) (g v₀) =
      Lin.S χ s G (u - v) (g v - g v₀) +
        (Lin.S χ s G (u - v) (g v₀) - Lin.S χ s G (u - v₀) (g v₀)) := by
    rw [map_sub]; abel
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
  have hop : ‖Lin.S χ s G (u - v)‖ ≤ B := hB G le_rfl (u - v) (hmaps hv)
  calc ‖Lin.S χ s G (u - v) (g v - g v₀)‖ ≤ ‖Lin.S χ s G (u - v)‖ * ‖g v - g v₀‖ :=
        (Lin.S χ s G (u - v)).le_opNorm _
    _ ≤ B * ‖g v - g v₀‖ := mul_le_mul_of_nonneg_right hop (norm_nonneg _)

/-- The Duhamel integrand is interval integrable on `[0,u]`. -/
theorem intervalIntegrable_S_comp (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (s : ℕ) (G : ℝ)
    {u : ℝ} (hu : 0 ≤ u) {g : ℝ → Y s annN} (hg : ContinuousOn g (Icc 0 u)) :
    IntervalIntegrable (fun v => Lin.S χ s G (u - v) (g v)) volume 0 u :=
  (continuousOn_S_comp χ hχ s G hg).intervalIntegrable_of_Icc hu

/-! ### Additivity of the linear response (new) -/

/-- The forcing `-h·∇Φ` is additive in the field `h` (pointwise). -/
theorem forcing_add (χ : ℝ → ℝ) (h₁ h₂ : ℝ → ℂ → ℂ) (v : ℝ) :
    forcing χ (fun τ y => h₁ τ y + h₂ τ y) v = fun x => forcing χ h₁ v x + forcing χ h₂ v x := by
  funext x
  simp only [forcing, hGrad, Sob.dotGrad, Complex.add_re, Complex.add_im]
  push_cast
  ring

/-- **Additivity of the linear response in the field** (`lem:coupling`(3), `08_kick.tex:150-153`):
if `-h₁·∇Φ` and `-h₂·∇Φ` lie in `C([0,T];X^s)`, then for `τ ∈ [0,T]`,
`wlin[h₁](τ) + wlin[h₂](τ) = wlin[h₁ + h₂](τ)` in `Y^s(N)`. -/
theorem wlin_add (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) {s : ℕ} {G T : ℝ}
    {h₁ h₂ : ℝ → ℂ → ℂ} (hp₁ : PathC s T (forcing χ h₁)) (hp₂ : PathC s T (forcing χ h₂))
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) :
    wlin χ s G h₁ τ + wlin χ s G h₂ τ = wlin χ s G (fun v y => h₁ v y + h₂ v y) τ := by
  have hsub : Icc (0 : ℝ) τ ⊆ Icc 0 T := Icc_subset_Icc le_rfl hτ.2
  have hc₁ : ContinuousOn (fun v => toY s annN (forcing χ h₁ v)) (Icc 0 τ) := hp₁.2.mono hsub
  have hc₂ : ContinuousOn (fun v => toY s annN (forcing χ h₂ v)) (Icc 0 τ) := hp₂.2.mono hsub
  have hi₁ := intervalIntegrable_S_comp χ hχ s G hτ.1 hc₁
  have hi₂ := intervalIntegrable_S_comp χ hχ s G hτ.1 hc₂
  simp only [wlin_def, wlin0_def, toY_zero, map_zero, zero_add]
  rw [← intervalIntegral.integral_add hi₁ hi₂]
  refine intervalIntegral.integral_congr fun v hv => ?_
  rw [uIcc_of_le hτ.1] at hv
  simp only [forcing_add]
  rw [toY_add (hp₁.1 v (hsub hv)) (hp₂.1 v (hsub hv)), map_add]

end NonUniqueEuler.CouplingAux
