import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Infra.Sobolev.Space
import NonUniqueEuler.I.Infra.Sobolev.Norm
import NonUniqueEuler.I.Infra.Sobolev.NormDeriv
import NonUniqueEuler.I.Infra.Polar.Fubini
import NonUniqueEuler.I.Sec4.SemigroupLaw
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.I.Sec4.Eigendata
import NonUniqueEuler.I.Sec4.PropSemigroup
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Helper for `lem:handoff`: `ℓ_*(G)` on linear responses and on differences

Helper of `P/Sec9/Handoff.lean` (`09_relay.tex:887-924`). Generic facts on `Y^s(N)` and on the
functional `ℓ_*(G)` on functions (`Eig.ellFn`).

The first group is copied, in the namespace `Relay.HandoffAux` (to avoid clashes), from the helpers
of other proofs, which cannot be imported here (import rules, `README.md`):
`H/Sec8/Coupling/Bridge.lean` (itself copied from `H/Sec5/Running/*`) and
`H/Sec5/QuietHandoff/Basic.lean`:
* `Y_ext_fn`, `exists_Y_of_memH`, `toY_fn`, `Y_memH_fn`, `Y_fn_sub`, `Y_fn_add`, `Y_fn_zero`,
  `Y_fn_zero_outside`, `memX_toY`, `memH_zero`, `memXFn_zero`, `toY_zero`: elements of `Y^s(K)`
  and their functions;
* `angularSector_congr_ae`, `ellFn_congr_ae`: `ℓ_*(G)` on functions only sees the a.e. class;
* `continuousOn_S_comp`, `intervalIntegrable_S_comp`: the Duhamel integrand is continuous;
* `norm_ellFn_sub_le` (from `P/Sec5/QuietHandoff.lean`): `|ℓ_*(f) - ℓ_*(g)| ≤ ‖ℓ_*(G)‖ ‖f - g‖_{H^s}`.

New here:
* `ellFn_wlin_eq`: for a forcing `F = -h·∇Φ ∈ C([0,T];X^s)` (`OneRing.PathC`), at every level `s`,
  `ℓ_*(G)(wlin(u)) = ∫₀ᵘ e^{λ_*(u-v)} ℓ_*(G)(F(v)) dv` (`ℓ_*(G)` is bounded, so it commutes with the
  Duhamel integral, and `prop:semigroup` gives `ℓ_*(e^{τL}f) = e^{λ_*τ}ℓ_*(f)`;
  `09_relay.tex:905-908`). In particular the value does not depend on the level `s`.
-/

noncomputable section

open MeasureTheory Set Real Filter Topology
open scoped ENNReal

namespace NonUniqueEuler.Relay.HandoffAux

open Sect Sob RingData OneRing

/-! ### Elements of `Y^s(K)` and their functions (copied) -/

/-- An element of `Y^s(K)` is determined by its function. -/
theorem Y_ext_fn {s : ℕ} {K : Set ℂ} {w₁ w₂ : Y s K} (h : w₁.fn =ᵐ[volume] w₂.fn) : w₁ = w₂ := by
  have : Y.toHk w₁ = Y.toHk w₂ := Hk.ext_fn h
  exact Subtype.ext (show (w₁ : SobTuple s) = w₂ from
    congrArg (fun F : Hk s => (F : SobTuple s)) this)

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

/-- The function of `w ∈ Y^s(K)` lies in `H^s`, with `‖w.fn‖_{H^s} = ‖w‖`. -/
theorem Y_memH_fn {s : ℕ} {K : Set ℂ} (w : Y s K) : MemH s w.fn ∧ normH s w.fn = ‖w‖ :=
  Hk.memH_fn (Y.toHk w)

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

theorem stronglyMeasurable_tupleFn {s : ℕ} (F : SobTuple s) : StronglyMeasurable (tupleFn F) :=
  Lp.stronglyMeasurable _

theorem suppCLM_eq_zero_iff {s : ℕ} {K : Set ℂ} (F : SobTuple s) :
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

theorem mem_YSub_iff {s : ℕ} {K : Set ℂ} (F : SobTuple s) :
    F ∈ YSub s K ↔ F ∈ HkSub s ∧ ∀ᵐ x ∂volume, x ∉ K → tupleFn F x = 0 := by
  rw [YSub, Submodule.mem_inf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    suppCLM_eq_zero_iff]

/-- The function of `w ∈ Y^s(K)` vanishes a.e. outside `K`. -/
theorem Y_fn_zero_outside {s : ℕ} {K : Set ℂ} (w : Y s K) :
    ∀ᵐ x ∂(volume : Measure ℂ), x ∉ K → w.fn x = 0 :=
  ((mem_YSub_iff (K := K) (w : SobTuple s)).1 w.2).2

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

/-! ### `ℓ_*` only sees the a.e. class (copied) -/

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
    ENNReal.measurable_ofReal.mul
      (hFm.lintegral_prod_right' (ν := volume.restrict (Ioc 0 (2 * π))))
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
  rw [intervalIntegral.integral_of_le (by positivity),
    intervalIntegral.integral_of_le (by positivity)]
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

/-! ### The Duhamel integrand (copied) -/

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

/-! ### `ℓ_*(G)` on differences (copied from `P/Sec5/QuietHandoff.lean`) -/

/-- `|ℓ_*(G)(f) - ℓ_*(G)(g)| ≤ ‖ℓ_*(G)‖_{(Y^0)^*} ‖f - g‖_{H^s}` for `f, g ∈ H^s` vanishing a.e.
outside `N`. -/
theorem norm_ellFn_sub_le (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ)
    (hN : NumericalHypothesis χ) {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) {s : ℕ} {f g : ℂ → ℂ}
    (hf : MemH s f) (hg : MemH s g)
    (hfs : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → f x = 0)
    (hgs : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → g x = 0) :
    ‖Eig.ellFn χ G f - Eig.ellFn χ G g‖ ≤ ‖Eig.ell χ 0 G‖ * normH s (f - g) := by
  have hspec := Eig.ell_spec_of_exists (Eig.exists_ell χ hχ hN hG 0)
  have hf0 : MemH 0 f := hf.mono_order (Nat.zero_le s)
  have hg0 : MemH 0 g := hg.mono_order (Nat.zero_le s)
  obtain ⟨f', hf'⟩ := exists_Y_of_memH measurableSet_annN hf0 hfs
  obtain ⟨g', hg'⟩ := exists_Y_of_memH measurableSet_annN hg0 hgs
  have e1 : Eig.ellFn χ G f = Eig.ell χ 0 G f' := by
    rw [hspec, ellFn_congr_ae χ G hf']
  have e2 : Eig.ellFn χ G g = Eig.ell χ 0 G g' := by
    rw [hspec, ellFn_congr_ae χ G hg']
  rw [e1, e2, ← map_sub]
  refine ((Eig.ell χ 0 G).le_opNorm _).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (ContinuousLinearMap.opNorm_nonneg _)
  obtain ⟨hm, hn⟩ := Y_memH_fn (f' - g')
  have hae : (f' - g').fn =ᵐ[volume] f - g := by
    filter_upwards [Y_fn_sub f' g', hf', hg'] with x hx h1 h2
    rw [hx, h1, h2]
    rfl
  rw [← hn, ← (hm.congr_ae hae).2]
  exact (hf.sub hg).1.normH_mono (Nat.zero_le s)

/-! ### `ℓ_*(G)` of a linear response (new) -/

/-- **`ℓ_*(G)` of the linear response** (`09_relay.tex:905-908`, `lem:running` with `w₀ = 0`):
if the forcing `F = -h·∇Φ` lies in `C([0,T];X^s)` (`PathC s T (forcing χ h)`) and `G ∈ [0,G₁]`,
then for `u ∈ [0,T]`, `ℓ_*(G)(wlin(u)) = ∫₀ᵘ e^{λ_*(u-v)} ℓ_*(G)(F(v)) dv`, at every level `s`.
`ℓ_*(G)` is bounded on `Y^s(N)` (`exists_ell`), so it commutes with the (integrable) Duhamel
integral, and `ℓ_*(e^{τL}f) = e^{λ_*τ}ℓ_*(f)` (`prop:semigroup`). -/
theorem ellFn_wlin_eq (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) {s : ℕ} {T : ℝ} {h : ℝ → ℂ → ℂ}
    (hp : PathC s T (forcing χ h)) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) T) :
    Eig.ellFn χ G (wlin χ s G h u).fn =
      ∫ v in (0 : ℝ)..u, Complex.exp (Eig.lam χ G * ((u - v : ℝ) : ℂ)) *
        Eig.ellFn χ G (forcing χ h v) := by
  have hsub : Icc (0 : ℝ) u ⊆ Icc 0 T := Icc_subset_Icc le_rfl hu.2
  have hc : ContinuousOn (fun v => toY s annN (forcing χ h v)) (Icc 0 u) := hp.2.mono hsub
  have hint := intervalIntegrable_S_comp χ hχ s G hu.1 hc
  have hellw : ∀ w : Y s annN, Eig.ell χ s G w = Eig.ellFn χ G w.fn :=
    Eig.ell_spec_of_exists (Eig.exists_ell χ hχ hN hG s)
  have hW : wlin χ s G h u =
      ∫ v in (0 : ℝ)..u, Lin.S χ s G (u - v) (toY s annN (forcing χ h v)) := by
    simp only [wlin_def, wlin0_def, toY_zero, map_zero, zero_add]
  rw [← hellw, hW, ← ContinuousLinearMap.intervalIntegral_comp_comm _ hint]
  refine intervalIntegral.integral_congr fun v hv => ?_
  rw [uIcc_of_le hu.1] at hv
  obtain ⟨hfn, hX⟩ := memX_toY (hp.1 v (hsub hv))
  have huv : (0 : ℝ) ≤ u - v := by linarith [hv.2]
  show Eig.ell χ s G (Lin.S χ s G (u - v) (toY s annN (forcing χ h v))) = _
  rw [(Eig.propSemigroup_formulas χ hχ hN s hG huv).2 _ hX, hellw, ellFn_congr_ae χ G hfn]

/-- The level independence of `ℓ_*(G)(wlin(u))`: the same value at two levels `s, s'` when the
forcing is continuous into both `X^s` and `X^{s'}`. -/
theorem ellFn_wlin_level (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) {s s' : ℕ} {T : ℝ} {h : ℝ → ℂ → ℂ}
    (hp : PathC s T (forcing χ h)) (hp' : PathC s' T (forcing χ h)) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) T) :
    Eig.ellFn χ G (wlin χ s G h u).fn = Eig.ellFn χ G (wlin χ s' G h u).fn := by
  rw [ellFn_wlin_eq χ hχ hN hG hp hu, ellFn_wlin_eq χ hχ hN hG hp' hu]

end NonUniqueEuler.Relay.HandoffAux
