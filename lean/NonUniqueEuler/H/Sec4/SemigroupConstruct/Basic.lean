import NonUniqueEuler.Defs.Sec4.Operators
import NonUniqueEuler.I.Infra.Sobolev.Space
import NonUniqueEuler.I.Infra.Polar.Fubini
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv

/-!
# Helpers for `lem:semigroup-construct`: basic facts on the sector spaces and angular sectors

Helper file of `P/Sec4/SemigroupConstruct.lean` (fully proved).

* Elements of `Y^s(K)` and `Y^s_ℓ(K)`: their functions are linear a.e., determine the element
  (`Sob.Hk.ext_fn`), lie in `H^s` and vanish a.e. outside `K`. (The first lemmas follow
  `P/Infra/SectorSpace/RadialMul.lean`, namespace `Sect.RadMulP`, which no file may import.)
* Angular sectors: `angularSector` respects a.e. equality (polar Fubini,
  `Polar.lintegral_eq_lintegral_Ioi_circle`), is additive a.e. for locally integrable functions,
  homogeneous, pulls out radial factors, and inverts `Ang.ofProfile`.
* `secNormSq` respects a.e. equality on `(0, ∞)`.
-/

noncomputable section

open MeasureTheory Set Real Filter
open scoped ENNReal

namespace NonUniqueEuler.SGC

open Sob Sect Ang

variable {s : ℕ} {K : Set ℂ} {ℓ : ℤ}

/-! ### Tuples -/

theorem tupleFn_add (F G : SobTuple s) :
    tupleFn (F + G) =ᵐ[volume] tupleFn F + tupleFn G :=
  Lp.coeFn_add (F.ofLp (idx0 s)) (G.ofLp (idx0 s))

theorem tupleFn_smul (c : ℂ) (F : SobTuple s) :
    tupleFn (c • F) =ᵐ[volume] c • tupleFn F :=
  Lp.coeFn_smul c (F.ofLp (idx0 s))

theorem tupleFn_zero : tupleFn (0 : SobTuple s) =ᵐ[volume] 0 :=
  Lp.coeFn_zero _ _ _

theorem stronglyMeasurable_tupleFn (F : SobTuple s) : StronglyMeasurable (tupleFn F) :=
  Lp.stronglyMeasurable _

theorem memLp_tupleFn (F : SobTuple s) : MemLp (tupleFn F) 2 volume :=
  Lp.memLp _

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

/-! ### Elements of `Y^s(K)` -/

/-- `w ∈ Y^s(K)` as an element of `H^s`. -/
def yHk (w : Y s K) : Hk s := ⟨(w : SobTuple s), YSub_le_HkSub s K w.2⟩

theorem y_memH (w : Y s K) : MemH s w.fn ∧ normH s w.fn = ‖w‖ :=
  Hk.memH_fn (yHk w)

theorem y_ext {v w : Y s K} (h : v.fn =ᵐ[volume] w.fn) : v = w :=
  Subtype.ext (tuple_ext (YSub_le_HkSub s K v.2) (YSub_le_HkSub s K w.2) h)

theorem y_supp (w : Y s K) : ∀ᵐ x ∂volume, x ∉ K → w.fn x = 0 :=
  ((mem_YSub_iff (K := K) (w : SobTuple s)).1 w.2).2

theorem y_fn_add (v w : Y s K) : (v + w).fn =ᵐ[volume] v.fn + w.fn :=
  tupleFn_add (v : SobTuple s) w

theorem y_fn_smul (c : ℂ) (w : Y s K) : (c • w).fn =ᵐ[volume] c • w.fn :=
  tupleFn_smul c (w : SobTuple s)

theorem y_fn_zero : (0 : Y s K).fn =ᵐ[volume] 0 :=
  tupleFn_zero

theorem y_memLp (w : Y s K) : MemLp w.fn 2 volume :=
  memLp_tupleFn _

/-! ### Elements of `Y^s_ℓ(K)` -/

/-- `g ∈ Y^s_ℓ(K)` as an element of `H^s`. -/
def ysecHk (g : Ysec s K ℓ) : Hk s :=
  ⟨(g : SobTuple s), YSub_le_HkSub s K (YsecSub_le_YSub s K ℓ g.2)⟩

theorem ysec_memH (g : Ysec s K ℓ) : MemH s g.fn ∧ normH s g.fn = ‖g‖ :=
  Hk.memH_fn (ysecHk g)

theorem ysec_ext {g h : Ysec s K ℓ} (hgh : g.fn =ᵐ[volume] h.fn) : g = h :=
  Subtype.ext (tuple_ext (YSub_le_HkSub s K (YsecSub_le_YSub s K ℓ g.2))
    (YSub_le_HkSub s K (YsecSub_le_YSub s K ℓ h.2)) hgh)

theorem ysec_supp (g : Ysec s K ℓ) : ∀ᵐ x ∂volume, x ∉ K → g.fn x = 0 :=
  ((mem_YSub_iff (K := K) (g : SobTuple s)).1 (YsecSub_le_YSub s K ℓ g.2)).2

theorem ysec_fn_add (g h : Ysec s K ℓ) : (g + h).fn =ᵐ[volume] g.fn + h.fn :=
  tupleFn_add (g : SobTuple s) h

theorem ysec_fn_smul (c : ℂ) (g : Ysec s K ℓ) : (c • g).fn =ᵐ[volume] c • g.fn :=
  tupleFn_smul c (g : SobTuple s)

theorem ysec_fn_zero : (0 : Ysec s K ℓ).fn =ᵐ[volume] 0 :=
  tupleFn_zero

theorem ysec_memLp (g : Ysec s K ℓ) : MemLp g.fn 2 volume :=
  memLp_tupleFn _

theorem ysec_fn_sub (g h : Ysec s K ℓ) : (g - h).fn =ᵐ[volume] g.fn - h.fn :=
  Lp.coeFn_sub ((g : SobTuple s).ofLp (idx0 s)) ((h : SobTuple s).ofLp (idx0 s))

/-- Two continuous linear maps into `Y^s_ℓ(K)` with a.e. equal functions are equal. -/
theorem ysec_clm_ext {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {T T' : E →L[ℂ] Ysec s K ℓ} (h : ∀ g, (T g).fn =ᵐ[volume] (T' g).fn) : T = T' :=
  ContinuousLinearMap.ext fun g => ysec_ext (h g)

/-- Two continuous linear maps into `Y^s(K)` with a.e. equal functions are equal. -/
theorem y_clm_ext {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {T T' : E →L[ℂ] Y s K} (h : ∀ g, (T g).fn =ᵐ[volume] (T' g).fn) : T = T' :=
  ContinuousLinearMap.ext fun g => y_ext (h g)

/-! ### Angular sectors -/

theorem circleMap_zero_eq (r θ : ℝ) :
    circleMap 0 r θ = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
  simp [circleMap]

theorem continuous_circleMap_zero_prod :
    Continuous fun p : ℝ × ℝ => circleMap 0 p.1 p.2 := by
  simp only [circleMap, zero_add]
  fun_prop

/-- For a null set `N`, almost every circle meets `N` in a null set of angles. -/
theorem ae_circle_of_null {N : Set ℂ} (hN : volume N = 0) :
    ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ᵐ θ ∂(volume.restrict (Ioc (0 : ℝ) (2 * π))), circleMap 0 r θ ∉ N := by
  set M := toMeasurable volume N with hM
  have hMm : MeasurableSet M := measurableSet_toMeasurable _ _
  have hM0 : volume M = 0 := by rw [hM, measure_toMeasurable]; exact hN
  have hF : Measurable (M.indicator (1 : ℂ → ℝ≥0∞)) := measurable_one.indicator hMm
  have h := Polar.lintegral_eq_lintegral_Ioi_circle hF
  rw [lintegral_indicator_one hMm, hM0] at h
  have hmeas : Measurable fun r : ℝ => ENNReal.ofReal r *
      ∫⁻ θ in Ioc (0 : ℝ) (2 * π), M.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 r θ) := by
    refine measurable_id.ennreal_ofReal.mul ?_
    exact (hF.comp continuous_circleMap_zero_prod.measurable).lintegral_prod_right'
  have h2 := (lintegral_eq_zero_iff hmeas).1 h.symm
  have hpos : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), 0 < r :=
    ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => hr
  filter_upwards [h2, hpos] with r hr hr0
  have hr' : ∫⁻ θ in Ioc (0 : ℝ) (2 * π), M.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 r θ) = 0 := by
    have := hr
    simp only [Pi.zero_apply, mul_eq_zero, ENNReal.ofReal_eq_zero, not_le.2 hr0, false_or] at this
    exact this
  have hmθ : Measurable fun θ : ℝ => M.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 r θ) :=
    hF.comp (continuous_circleMap 0 r).measurable
  have h3 := (lintegral_eq_zero_iff hmθ).1 hr'
  filter_upwards [h3] with θ hθ hNθ
  have : circleMap 0 r θ ∈ M := subset_toMeasurable _ _ hNθ
  simp [Set.indicator_of_mem this] at hθ

/-- `angularSector` respects a.e. equality, for a.e. radius. -/
theorem angularSector_congr_ae {f g : ℂ → ℂ} (hfg : f =ᵐ[volume] g) (ℓ : ℤ) :
    Polar.angularSector f ℓ =ᵐ[volume.restrict (Ioi 0)] Polar.angularSector g ℓ := by
  have hN : volume {x | f x ≠ g x} = 0 := hfg
  filter_upwards [ae_circle_of_null hN] with r hr
  simp only [Polar.angularSector]
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  rw [Set.uIoc_of_le (by positivity)]
  rw [ae_restrict_iff' measurableSet_Ioc] at hr
  filter_upwards [hr] with θ hθ hθI
  have := hθ hθI
  simp only [not_not, circleMap_zero_eq] at this
  rw [this]

/-- `angularSector` is additive for a.e. radius. -/
theorem angularSector_add_ae {f g : ℂ → ℂ} (hf : LocallyIntegrable f volume)
    (hg : LocallyIntegrable g volume) (ℓ : ℤ) :
    ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), Polar.angularSector (f + g) ℓ r =
      Polar.angularSector f ℓ r + Polar.angularSector g ℓ r := by
  filter_upwards [Polar.ae_circleIntegrable_of_locallyIntegrable hf,
    Polar.ae_circleIntegrable_of_locallyIntegrable hg] with r hfr hgr
  have hc : ContinuousOn (fun θ : ℝ => Complex.exp (-((ℓ : ℂ) * θ * Complex.I)))
      (uIcc 0 (2 * π)) := by fun_prop
  have hf' := IntervalIntegrable.mul_continuousOn (f := fun θ => f (circleMap 0 r θ)) hfr hc
  have hg' := IntervalIntegrable.mul_continuousOn (f := fun θ => g (circleMap 0 r θ)) hgr hc
  simp only [circleMap_zero_eq] at hf' hg'
  simp only [Polar.angularSector, Pi.add_apply, add_mul]
  rw [intervalIntegral.integral_add hf' hg', mul_add]

/-- `angularSector` is homogeneous. -/
theorem angularSector_smul (c : ℂ) (f : ℂ → ℂ) (ℓ : ℤ) (r : ℝ) :
    Polar.angularSector (c • f) ℓ r = c * Polar.angularSector f ℓ r := by
  simp only [Polar.angularSector, Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  ring

theorem norm_ofReal_mul_exp {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
    ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = r := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr]

/-- A radial factor comes out of `angularSector`. -/
theorem angularSector_radial_mul (a : ℝ → ℂ) (f : ℂ → ℂ) (ℓ : ℤ) {r : ℝ} (hr : 0 ≤ r) :
    Polar.angularSector (fun x => a ‖x‖ * f x) ℓ r = a r * Polar.angularSector f ℓ r := by
  simp only [Polar.angularSector, norm_ofReal_mul_exp hr, mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  ring

theorem angPhase_ofReal_mul_exp (ℓ : ℤ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    angPhase ℓ ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
      Complex.exp ((ℓ : ℂ) * θ * Complex.I) := by
  rw [angPhase, norm_ofReal_mul_exp hr.le]
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [mul_div_cancel_left₀ _ hr', mul_assoc, Complex.exp_int_mul]

/-- `angularSector` inverts `ofProfile`. -/
theorem angularSector_ofProfile (ℓ : ℤ) (h : ℝ → ℂ) {r : ℝ} (hr : 0 < r) :
    Polar.angularSector (ofProfile ℓ h) ℓ r = h r := by
  simp only [Polar.angularSector, ofProfile, norm_ofReal_mul_exp hr.le,
    angPhase_ofReal_mul_exp ℓ hr]
  have : ∀ θ : ℝ, h r * Complex.exp ((ℓ : ℂ) * θ * Complex.I) *
      Complex.exp (-((ℓ : ℂ) * θ * Complex.I)) = h r := by
    intro θ
    rw [mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
  simp only [this, intervalIntegral.integral_const, sub_zero, Complex.real_smul]
  have hπ : (2 * π : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  push_cast
  field_simp

/-! ### Sector norms -/

theorem locallyIntegrableOn_of_memLp_Ioi {h : ℝ → ℂ} (hh : MemLp h 2 (volume.restrict (Ioi 0))) :
    LocallyIntegrableOn h (Ioi 0) volume :=
  locallyIntegrableOn_of_locallyIntegrable_restrict (hh.locallyIntegrable (by norm_num))

/-- The chosen weak derivatives of a.e. equal `H^k` profiles agree a.e. on `(0, ∞)`. -/
theorem weakDeriv1On_congr_ae {k : ℕ} {f g : ℝ → ℂ} (hf : MemH1On k (Ioi 0) f)
    (hfg : f =ᵐ[volume.restrict (Ioi 0)] g) {j : ℕ} (hj : j ≤ k) :
    weakDeriv1On (Ioi 0) j f =ᵐ[volume.restrict (Ioi 0)] weakDeriv1On (Ioi 0) j g := by
  obtain ⟨h, hh, hfh⟩ := hf.deriv j hj
  have hloc := locallyIntegrableOn_of_memLp_Ioi hh
  have hfg' : ∀ᵐ x, x ∈ Ioi (0 : ℝ) → f x = g x := (ae_restrict_iff' measurableSet_Ioi).1 hfg
  have hgh : HasWeakDerivOn (Ioi 0) (derivList j) g h :=
    hfh.congr_ae hfg' (Eventually.of_forall fun _ _ => rfl)
  have h1 := weakDerivOn_ae_eq isOpen_Ioi hloc hfh
  have h2 := weakDerivOn_ae_eq isOpen_Ioi hloc hgh
  rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [h1, h2] with x hx1 hx2 hx
  simp only [weakDeriv1On]
  rw [hx1 hx, hx2 hx]

/-- `secNormSq` respects a.e. equality on `(0, ∞)`, on subsets of `(0, ∞)`. -/
theorem secNormSq_congr_ae {k : ℕ} (ℓ : ℤ) {I : Set ℝ} (hI : I ⊆ Ioi 0) {f g : ℝ → ℂ}
    (hf : MemH1On k (Ioi 0) f) (hfg : f =ᵐ[volume.restrict (Ioi 0)] g) :
    secNormSq k ℓ I f = secNormSq k ℓ I g := by
  refine Finset.sum_congr rfl fun j hj => ?_
  congr 1
  have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have h := weakDeriv1On_congr_ae hf hfg hjk
  refine integral_congr_ae ?_
  have h' := ae_restrict_of_ae_restrict_of_subset hI h
  filter_upwards [h'] with x hx
  rw [hx]

end NonUniqueEuler.SGC
