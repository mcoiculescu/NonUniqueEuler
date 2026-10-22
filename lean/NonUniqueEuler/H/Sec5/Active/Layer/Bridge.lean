import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Sec4.Eigendata
import NonUniqueEuler.I.Sec4.Uniform
import NonUniqueEuler.I.Sec5.Bilinear
import NonUniqueEuler.I.Infra.Polar.Fubini
import NonUniqueEuler.I.Infra.Sobolev.Space
import NonUniqueEuler.I.Infra.Sobolev.Norm
import NonUniqueEuler.I.Infra.Sobolev.NormDeriv

/-!
# Helpers for the initial layer of `thm:active`: bridges between plane functions and `Y^s(N)`

Helper of `P/Sec5/Active/Layer.lean` (fully proved modulo the interface files it imports).
Namespace `NonUniqueEuler.OneRing.LayerH`. These are copies of proved helpers of other proofs
(`H/Sec5/LinearPart/Bridge.lean`, `H/Sec5/LinearPart/Bound.lean`,
`H/Sec5/QuietHandoff/Basic.lean`, `P/Sec5/QuietHandoff.lean`), which a proof file may not import
(import rules, `README.md`).

* `Y_ext_fn`, `Y_memH_fn`, `Y_fn_zero_outside`, `Y_fn_sub`, `Y_fn_neg`: functions of elements of
  `Y^s(K)`;
* `toY_fn_and_norm`, `norm_toY`, `toY_fn`, `memX_toY`, `toY_neg`: `toY s N f` for `f ∈ X^s`;
* `forcing_memX_norm`: `F = -h·∇Φ ∈ X^k` with `‖F‖_{H^k} ≤ C_∇(k)‖h‖_{C^k(N')}`;
* `ellFn_congr_ae`, `norm_ellFn_sub_le`: `ℓ_*(G)` only sees the a.e. class, and
  `|ℓ_*(f) - ℓ_*(g)| ≤ ‖ℓ_*(G)‖_{(Y^0)^*}‖f - g‖_{H^s}`.
-/

noncomputable section

open MeasureTheory Set Real Filter Topology
open scoped ENNReal

namespace NonUniqueEuler.OneRing.LayerH

open RingData Sect Sob

/-! ### Functions of elements of `Y^s(K)` -/

/-- An element of `Y^s(K)` is determined by its function. -/
theorem Y_ext_fn {s : ℕ} {K : Set ℂ} {w₁ w₂ : Y s K} (h : w₁.fn =ᵐ[volume] w₂.fn) :
    w₁ = w₂ := by
  have : Y.toHk w₁ = Y.toHk w₂ := Hk.ext_fn h
  exact Subtype.ext (show (w₁ : SobTuple s) = w₂ from
    congrArg (fun F : Hk s => (F : SobTuple s)) this)

/-- The function of an element of `Y^s(K)` lies in `H^s`, with norm the norm of the element. -/
theorem Y_memH_fn {s : ℕ} {K : Set ℂ} (w : Y s K) : MemH s w.fn ∧ normH s w.fn = ‖w‖ := by
  have h := Hk.memH_fn (Y.toHk w)
  exact ⟨h.1, h.2⟩

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

/-- The function of a difference. -/
theorem Y_fn_sub {s : ℕ} {K : Set ℂ} (w₁ w₂ : Y s K) :
    (w₁ - w₂).fn =ᵐ[volume] fun x => w₁.fn x - w₂.fn x := by
  have h : ((w₁ - w₂ : Y s K) : SobTuple s).ofLp (idx0 s) =
      (w₁ : SobTuple s).ofLp (idx0 s) - (w₂ : SobTuple s).ofLp (idx0 s) := rfl
  show (((w₁ - w₂ : Y s K) : SobTuple s).ofLp (idx0 s) : ℂ → ℂ) =ᵐ[volume] _
  rw [h]
  exact Lp.coeFn_sub _ _

/-- The function of a negative. -/
theorem Y_fn_neg {s : ℕ} {K : Set ℂ} (w : Y s K) :
    (-w).fn =ᵐ[volume] -w.fn := by
  have h : ((-w : Y s K) : SobTuple s).ofLp (idx0 s) = -(w : SobTuple s).ofLp (idx0 s) := rfl
  show (((-w : Y s K) : SobTuple s).ofLp (idx0 s) : ℂ → ℂ) =ᵐ[volume] _
  rw [h]
  exact Lp.coeFn_neg _

/-- An `H^s` function vanishing a.e. outside `K` is (a.e.) the function of an element of
`Y^s(K)`. -/
theorem exists_Y_of_memH {s : ℕ} {K : Set ℂ} {f : ℂ → ℂ} (hf : MemH s f)
    (hK : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ K → f x = 0) : ∃ w : Y s K, w.fn =ᵐ[volume] f := by
  obtain ⟨F, hF⟩ := memH_iff_exists_Hk.1 hf
  have hmem : (F : SobTuple s) ∈ YSub s K := by
    refine (mem_YSub_iff (F : SobTuple s)).2 ⟨F.2, ?_⟩
    have hF' : tupleFn (F : SobTuple s) =ᵐ[volume] f := hF
    filter_upwards [hF', hK] with x hx hKx hxK
    rw [hx]
    exact hKx hxK
  exact ⟨⟨(F : SobTuple s), hmem⟩, hF⟩

/-- For `f ∈ H^s` vanishing a.e. outside `K`, `toY s K f` has function `f` (a.e.) and norm
`‖f‖_{H^s}`. -/
theorem toY_fn_and_norm {s : ℕ} {K : Set ℂ} {f : ℂ → ℂ}
    (hf : MemH s f) (hK : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ K → f x = 0) :
    (toY s K f).fn =ᵐ[volume] f ∧ ‖toY s K f‖ = normH s f := by
  have hspec : (toY s K f).fn =ᵐ[volume] f := toY_spec (exists_Y_of_memH hf hK)
  refine ⟨hspec, ?_⟩
  have hY := Y_memH_fn (toY s K f)
  rw [← hY.2, (hY.1.congr_ae hspec).2]

/-- For `f ∈ X^s`, `‖toY s N f‖ = ‖f‖_{H^s}`. -/
theorem norm_toY {s : ℕ} {f : ℂ → ℂ} (hf : Lin.MemXFn s f) :
    ‖toY s annN f‖ = normH s f :=
  (toY_fn_and_norm hf.1 hf.2.1).2

/-- For `f ∈ X^s`, the function of `toY s N f` is `f` (a.e.). -/
theorem toY_fn {s : ℕ} {f : ℂ → ℂ} (hf : Lin.MemXFn s f) :
    (toY s annN f).fn =ᵐ[volume] f :=
  (toY_fn_and_norm hf.1 hf.2.1).1

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
    filter_upwards [Y_fn_neg (toY s annN f), toY_fn hf] with x hx1 hx2
    rw [hx1, Pi.neg_apply, hx2]
  have h2 : (toY s annN (fun x => -f x)).fn =ᵐ[volume] fun x => -f x :=
    toY_spec ⟨_, h1⟩
  exact Y_ext_fn (h2.trans h1.symm)

/-- `C_∇(k) ≥ 0`. -/
theorem Cnab_nonneg (χ : ℝ → ℝ) (k : ℕ) : 0 ≤ Eig.Cnab χ k := by
  unfold Eig.Cnab
  have := Sob.normH_nonneg (k + 1) fun y => ((ringPhi χ y : ℝ) : ℂ)
  positivity

/-- The forcing `F(v) = -h(v)·∇Φ` lies in `X^k`, with `‖F(v)‖_{H^k} ≤ C_∇(k)‖h(v)‖_{C^k(N')}`
(`lem:bilinear`(3)). -/
theorem forcing_memX_norm (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {k : ℕ} (hk : 2 ≤ k) {hf : ℂ → ℂ} (hhf : MemCk k annN' hf) (hsym : IsSymFieldOn annN' hf) :
    Lin.MemX (Sect.toY k annN (fun x => -hGrad hf (PhiC χ) x)) ∧
      ‖Sect.toY k annN (fun x => -hGrad hf (PhiC χ) x)‖ ≤ Eig.Cnab χ k * normCk k annN' hf := by
  obtain ⟨-, -, hnorm, hX⟩ := bilinear_Phi χ hχ hN hk hhf
  have hXf := hX hsym
  rw [toY_neg hXf]
  refine ⟨?_, ?_⟩
  · show -((Sect.toY k annN (hGrad hf (PhiC χ)) : Sob.SobTuple k)) ∈ Lin.Xsub k
    exact neg_mem (memX_toY hXf)
  · rw [norm_neg, norm_toY hXf]
    exact hnorm

/-! ### `ℓ_*` only sees the a.e. class -/

/-- The polar parametrization `(r, θ) ↦ r e^{iθ}` is continuous. -/
theorem continuous_circleMap_prod :
    Continuous fun p : ℝ × ℝ => circleMap 0 p.1 p.2 := by
  simp only [circleMap, zero_add]
  exact (Complex.continuous_ofReal.comp continuous_fst).mul
    (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))

/-- If `f = g` a.e. on the plane, then for a.e. `r > 0`, `f = g` a.e. on the circle of
radius `r`. -/
theorem ae_circle_of_ae {f g : ℂ → ℂ} (h : f =ᵐ[volume] g) :
    ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), ∀ᵐ θ ∂(volume.restrict (Ioc (0 : ℝ) (2 * π))),
      f (circleMap 0 r θ) = g (circleMap 0 r θ) := by
  set N : Set ℂ := toMeasurable volume {x | ¬ f x = g x} with hNdef
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : volume N = 0 := by
    rw [hNdef, measure_toMeasurable]
    exact h
  have hsub : {x | ¬ f x = g x} ⊆ N := subset_toMeasurable _ _
  set F : ℂ → ℝ≥0∞ := N.indicator 1 with hFdef
  have hFm : Measurable F := measurable_one.indicator hNm
  have hFc : Measurable fun p : ℝ × ℝ => F (circleMap 0 p.1 p.2) :=
    hFm.comp continuous_circleMap_prod.measurable
  have hI : ∫⁻ x, F x = 0 := by
    rw [hFdef, lintegral_indicator_one hNm]
    exact hN0
  rw [Polar.lintegral_eq_lintegral_Ioi_circle hFm] at hI
  have hmeas : Measurable fun r : ℝ =>
      ENNReal.ofReal r * ∫⁻ θ in Ioc (0 : ℝ) (2 * π), F (circleMap 0 r θ) :=
    ENNReal.measurable_ofReal.mul (hFc.lintegral_prod_right' (ν := volume.restrict _))
  have h0 := (lintegral_eq_zero_iff hmeas).1 hI
  have hpos : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), r ∈ Ioi (0 : ℝ) :=
    ae_restrict_mem measurableSet_Ioi
  filter_upwards [h0, hpos] with r hr hrpos
  have hr' : ENNReal.ofReal r * ∫⁻ θ in Ioc (0 : ℝ) (2 * π), F (circleMap 0 r θ) = 0 := hr
  rcases mul_eq_zero.1 hr' with h1 | h1
  · exact absurd h1 (ENNReal.ofReal_pos.2 hrpos).ne'
  · have h2 := (lintegral_eq_zero_iff (hFm.comp (continuous_circleMap 0 r).measurable)).1 h1
    filter_upwards [h2] with θ hθ
    by_contra hne
    have hmem : circleMap 0 r θ ∈ N := hsub hne
    have h3 : F (circleMap 0 r θ) = 1 := by
      rw [hFdef, Set.indicator_of_mem hmem]
      rfl
    have h4 : F (circleMap 0 r θ) = 0 := hθ
    rw [h3] at h4
    exact one_ne_zero h4

/-- The angular sectors of a.e. equal functions agree a.e. on `(0, ∞)`. -/
theorem angularSector_congr_ae {f g : ℂ → ℂ} (h : f =ᵐ[volume] g) (ℓ : ℤ) :
    Polar.angularSector f ℓ =ᵐ[volume.restrict (Ioi (0 : ℝ))] Polar.angularSector g ℓ := by
  filter_upwards [ae_circle_of_ae h] with r hr
  unfold Polar.angularSector
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  rw [uIoc_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
  rw [ae_restrict_iff' measurableSet_Ioc] at hr
  filter_upwards [hr] with θ hθ hmem
  have hc : ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = circleMap 0 r θ := by
    simp [circleMap]
  rw [hc, hθ hmem]

/-- `ℓ_*(G)` on functions (`Eig.ellFn`) only depends on the a.e. class. -/
theorem ellFn_congr_ae (χ : ℝ → ℝ) (G : ℝ) {f g : ℂ → ℂ} (h : f =ᵐ[volume] g) :
    Eig.ellFn χ G f = Eig.ellFn χ G g := by
  unfold Eig.ellFn SectorSetting.ellStar
  congr 2
  refine integral_congr_ae ?_
  filter_upwards [angularSector_congr_ae h 3] with r hr
  rw [hr]

/-- `|ℓ_*(G)(f) - ℓ_*(G)(g)| ≤ ‖ℓ_*(G)‖_{(Y^0)^*} ‖f - g‖_{H^s}` for `f, g ∈ H^s` vanishing a.e.
outside `N`. -/
theorem norm_ellFn_sub_le (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ)
    (hN : NumericalHypothesis χ) {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) {s : ℕ} {f g : ℂ → ℂ}
    (hf : Sob.MemH s f) (hg : Sob.MemH s g)
    (hfs : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → f x = 0)
    (hgs : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → g x = 0) :
    ‖Eig.ellFn χ G f - Eig.ellFn χ G g‖ ≤ ‖Eig.ell χ 0 G‖ * Sob.normH s (f - g) := by
  have hspec := Eig.ell_spec_of_exists (Eig.exists_ell χ hχ hN hG 0)
  have hf0 : Sob.MemH 0 f := hf.mono_order (Nat.zero_le s)
  have hg0 : Sob.MemH 0 g := hg.mono_order (Nat.zero_le s)
  obtain ⟨f', hf'⟩ := exists_Y_of_memH (K := annN) hf0 hfs
  obtain ⟨g', hg'⟩ := exists_Y_of_memH (K := annN) hg0 hgs
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

end NonUniqueEuler.OneRing.LayerH
