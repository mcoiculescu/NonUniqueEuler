import NonUniqueEuler.Defs.Sec4.Bridge
import NonUniqueEuler.I.Infra.Sobolev.Space
import NonUniqueEuler.I.Infra.Sobolev.Symmetry
import NonUniqueEuler.I.Infra.Polar.Fubini

/-!
# Helpers for `P/Sec4/PropSemigroup/RieszCont`: elements of `Y^s(K)`, conjugation, sectors

* Function-level characterisation of `YSub` and extensionality: an element of `Y s K` is
  determined by its function (`Sob.Hk.ext_fn`); its norm is the `H^s` norm of its function.
  (These duplicate helpers of `H/Sec4/SemigroupLaw/Basic.lean`, which this proof may not import
  (import rules, `README.md`).)
* `cjY : Y^s(K) → Y^s(K)`, complex conjugation `w ↦ conj ∘ w` (`Sob.MemH.conj`): additive,
  conjugate-homogeneous and isometric (as `H/Sec4/SemigroupLaw/Conj.lean`, on `Y^s` instead of
  the sector spaces).
* `angularSector_congr_ae`: angular sectors of a.e. equal functions agree a.e. on `(0, ∞)`
  (Tonelli in polar coordinates; a copy of `H/Sec4/PropSemigroup/EllSector.lean`).
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal ComplexConjugate

namespace NonUniqueEuler.Sect.RieszContH

open Sob Ang

variable {s : ℕ} {K : Set ℂ}

/-! ### Tuples and their functions -/

theorem stronglyMeasurable_tupleFn (F : SobTuple s) : StronglyMeasurable (tupleFn F) :=
  Lp.stronglyMeasurable _

theorem tupleFn_add (F G : SobTuple s) :
    tupleFn (F + G) =ᵐ[volume] tupleFn F + tupleFn G :=
  Lp.coeFn_add (F.ofLp (idx0 s)) (G.ofLp (idx0 s))

theorem tupleFn_smul (c : ℂ) (F : SobTuple s) :
    tupleFn (c • F) =ᵐ[volume] c • tupleFn F :=
  Lp.coeFn_smul c (F.ofLp (idx0 s))

/-- Two elements of `H^s` with a.e. equal functions are equal (as tuples). -/
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

/-! ### Elements of `Y s K` -/

theorem Y_ext_fn {w v : Y s K} (h : w.fn =ᵐ[volume] v.fn) : w = v :=
  Subtype.ext (tuple_ext (YSub_le_HkSub s K w.2) (YSub_le_HkSub s K v.2) h)

theorem Y_memH_fn (w : Y s K) : MemH s w.fn := (Hk.memH_fn w.toHk).1

theorem Y_supp (w : Y s K) : ∀ᵐ x ∂volume, x ∉ K → w.fn x = 0 :=
  ((mem_YSub_iff (w : SobTuple s)).1 w.2).2

theorem Y_fn_add (w v : Y s K) : (w + v).fn =ᵐ[volume] w.fn + v.fn :=
  tupleFn_add (w : SobTuple s) v

theorem Y_fn_smul (c : ℂ) (w : Y s K) : (c • w).fn =ᵐ[volume] c • w.fn :=
  tupleFn_smul c (w : SobTuple s)

/-- The norm of `F : Hk s` is the `H^s` norm of any function a.e. equal to its function. -/
theorem Hk_norm_eq_normH_of_ae {F : Hk s} {f : ℂ → ℂ} (hf : MemH s f)
    (h : F.fn =ᵐ[volume] f) : ‖F‖ = normH s f := by
  have hF : toHk s f = F := Hk.ext_fn ((toHk_fn hf).trans h.symm)
  rw [← hF, norm_toHk hf]

/-- The norm of `w ∈ Y^s(K)` is the `H^s` norm of any function a.e. equal to its function. -/
theorem Y_norm_eq_normH_of_ae {w : Y s K} {f : ℂ → ℂ} (hf : MemH s f)
    (h : w.fn =ᵐ[volume] f) : ‖w‖ = normH s f :=
  Hk_norm_eq_normH_of_ae (F := w.toHk) hf h

/-! ### Complex conjugation on `Y^s(K)` -/

/-- `conj w ∈ Y^s(K)` for `w ∈ Y^s(K)`. -/
theorem exists_Y_conj (w : Y s K) :
    ∃ w' : Y s K, w'.fn =ᵐ[volume] fun x => conj (w.fn x) := by
  obtain ⟨hmem, -⟩ := (Y_memH_fn w).conj
  obtain ⟨F, hF⟩ := memH_iff_exists_Hk.1 hmem
  have hY : (F : SobTuple s) ∈ YSub s K := by
    rw [mem_YSub_iff]
    refine ⟨F.2, ?_⟩
    filter_upwards [hF, Y_supp w] with x hx hsupp hxK
    change F.fn x = 0
    rw [hx, hsupp hxK, map_zero]
  exact ⟨⟨F, hY⟩, hF⟩

/-- Complex conjugation `Y^s(K) → Y^s(K)`. -/
def cjY (s : ℕ) (K : Set ℂ) (w : Y s K) : Y s K :=
  toY s K fun x => conj (w.fn x)

theorem cjY_fn (w : Y s K) : (cjY s K w).fn =ᵐ[volume] fun x => conj (w.fn x) :=
  toY_spec (exists_Y_conj w)

theorem cjY_add (w v : Y s K) : cjY s K (w + v) = cjY s K w + cjY s K v := by
  refine Y_ext_fn ?_
  filter_upwards [cjY_fn (w + v), Y_fn_add w v, cjY_fn w, cjY_fn v,
    Y_fn_add (cjY s K w) (cjY s K v)] with x h1 h2 h3 h4 h5
  rw [h1, h5, h2, Pi.add_apply, map_add, Pi.add_apply, h3, h4]

theorem cjY_smul (c : ℂ) (w : Y s K) : cjY s K (c • w) = conj c • cjY s K w := by
  refine Y_ext_fn ?_
  filter_upwards [cjY_fn (c • w), Y_fn_smul c w, cjY_fn w,
    Y_fn_smul (conj c) (cjY s K w)] with x h1 h2 h3 h4
  rw [h1, h4, h2, Pi.smul_apply, Pi.smul_apply, h3, smul_eq_mul, smul_eq_mul, map_mul]

theorem norm_cjY (w : Y s K) : ‖cjY s K w‖ = ‖w‖ := by
  obtain ⟨hmem, hnorm⟩ := (Y_memH_fn w).conj
  rw [Y_norm_eq_normH_of_ae hmem (cjY_fn w), hnorm,
    ← Y_norm_eq_normH_of_ae (Y_memH_fn w) (Filter.EventuallyEq.refl _ _)]

/-- `cjY` as an additive map. -/
def cjYHom (s : ℕ) (K : Set ℂ) : Y s K →+ Y s K :=
  AddMonoidHom.mk' (cjY s K) cjY_add

theorem continuous_cjY : Continuous (cjY s K) :=
  AddMonoidHomClass.continuous_of_bound (cjYHom s K) 1 fun w => by
    change ‖cjY s K w‖ ≤ 1 * ‖w‖
    rw [norm_cjY, one_mul]

/-! ### Elements of `Ysec s K ℓ` -/

theorem Ysec_ext_fn {ℓ : ℤ} {g h : Ysec s K ℓ} (hgh : g.fn =ᵐ[volume] h.fn) : g = h :=
  Subtype.ext (tuple_ext (YSub_le_HkSub s K (YsecSub_le_YSub s K ℓ g.2))
    (YSub_le_HkSub s K (YsecSub_le_YSub s K ℓ h.2)) hgh)

theorem Ysec_fn_smul {ℓ : ℤ} (c : ℂ) (g : Ysec s K ℓ) : (c • g).fn =ᵐ[volume] c • g.fn :=
  tupleFn_smul c (g : SobTuple s)

/-! ### Angular sectors of a.e. equal functions -/

/-- The angular sectors of a.e. equal functions agree a.e. on `(0, ∞)`. -/
theorem angularSector_congr_ae {f g : ℂ → ℂ} (h : f =ᵐ[volume] g) (ℓ : ℤ) :
    Polar.angularSector f ℓ =ᵐ[volume.restrict (Ioi (0 : ℝ))] Polar.angularSector g ℓ := by
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 h)
  have hmeas : Measurable (N.indicator (1 : ℂ → ℝ≥0∞)) := measurable_one.indicator hNm
  have htot := Polar.lintegral_eq_lintegral_Ioi_circle hmeas
  rw [lintegral_indicator_one hNm, hN0] at htot
  have hcm : Continuous fun p : ℝ × ℝ => circleMap 0 p.1 p.2 := by
    simp only [circleMap]
    fun_prop
  have hF : Measurable fun p : ℝ × ℝ => N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 p.1 p.2) :=
    hmeas.comp hcm.measurable
  have hinner : Measurable fun r : ℝ =>
      ∫⁻ θ in Ioc (0 : ℝ) (2 * π), N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 r θ) :=
    hF.lintegral_prod_right'
  have hprod : Measurable fun r : ℝ => ENNReal.ofReal r *
      ∫⁻ θ in Ioc (0 : ℝ) (2 * π), N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 r θ) :=
    (ENNReal.measurable_ofReal.comp measurable_id).mul hinner
  have hae := (lintegral_eq_zero_iff hprod).1 htot.symm
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioi] with r hr hr0
  simp only [Pi.zero_apply] at hr
  have hpos : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hr0).ne'
  have hinner0 :
      ∫⁻ θ in Ioc (0 : ℝ) (2 * π), N.indicator (1 : ℂ → ℝ≥0∞) (circleMap 0 r θ) = 0 := by
    rcases mul_eq_zero.1 hr with h' | h'
    · exact absurd h' hpos
    · exact h'
  have hcθ : Continuous fun θ : ℝ => circleMap 0 r θ := continuous_circleMap 0 r
  have hθ := (lintegral_eq_zero_iff (hmeas.comp hcθ.measurable)).1 hinner0
  have hθ' := (ae_restrict_iff' measurableSet_Ioc).1 hθ
  unfold Polar.angularSector
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  rw [uIoc_of_le (by positivity)]
  filter_upwards [hθ'] with θ hθ1 hθmem
  have hnot : circleMap 0 r θ ∉ N := by
    intro hm
    have h1 := hθ1 hθmem
    simp [Set.indicator_of_mem hm] at h1
  have hfg : f (circleMap 0 r θ) = g (circleMap 0 r θ) := by
    by_contra hne
    exact hnot (hsub hne)
  simp only [circleMap, zero_add] at hfg
  rw [hfg]

/-! ### Conjugation of sector functions -/

theorem conj_angPhase (ℓ : ℤ) (x : ℂ) : conj (angPhase ℓ x) = angPhase (-ℓ) x := by
  unfold angPhase
  rw [map_zpow₀, zpow_neg, ← inv_zpow]
  congr 1
  by_cases hx : x = 0
  · simp [hx]
  · have hn : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hx
    have hu : ‖x / (‖x‖ : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 hx)]
    have hu0 : x / (‖x‖ : ℂ) ≠ 0 := div_ne_zero hx hn
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hu]
    simp

theorem conj_ofProfile (ℓ : ℤ) (h : ℝ → ℂ) (x : ℂ) :
    conj (ofProfile ℓ h x) = ofProfile (-ℓ) (fun r => conj (h r)) x := by
  unfold ofProfile
  rw [map_mul, conj_angPhase]

end NonUniqueEuler.Sect.RieszContH
