import NonUniqueEuler.Defs.Sec4.Operators
import NonUniqueEuler.I.Infra.Sobolev.Space
import NonUniqueEuler.I.Infra.SectorSpace.Decomposition
import NonUniqueEuler.I.Infra.AngularFourier.NormEquiv
import NonUniqueEuler.I.Infra.AngularFourier.Derivatives
import NonUniqueEuler.I.Sec4.SemigroupConstruct
import NonUniqueEuler.I.Sec4.KBound

/-!
# Helpers for `P/Sec4/LargeSectors`: operator-norm bounds on `Y^s_ℓ`

* `exists_secNormY_equiv`: the profile norm `‖g_ℓ‖_{s,ℓ}` (`S.secNormY s g`) and the `Y^s_ℓ` norm
  are equivalent uniformly in `ℓ` (`Sect.exists_norm_Ysec_equiv`, square roots taken).
* `exists_norm_exp_transSec_le`: `‖exp(t(-iℓΩ))‖_{Y^s_ℓ → Y^s_ℓ} ≤ C(1+|t|)^s` uniformly in `ℓ`
  and `|G| ≤ G₊` (`lem:semigroup-construct`(1), `semigroupConstruct_transport_sector`, plus the
  norm equivalence).
* `exists_norm_Ksec_le`: `‖k_ℓ𝒢_ℓ‖_{Y^s_ℓ → Y^s_ℓ} ≤ K/|ℓ|` for `ℓ ≠ 0` (`cor:K-bound` with
  `(1+ℓ²)⁻¹ ≤ ℓ⁻²`, the spec `semigroupConstruct_Ksec`, and the norm equivalences
  `Sect.exists_norm_Ysec_equiv`, `Ang.exists_norm_equiv_ofProfile`).

The first lemmas (functions, support and norms of elements of `Y^s_ℓ`) are copies of the helpers
of `H/Infra/SectorSpace/Decomposition/Basic.lean`, which this proof may not import
(import rules, `README.md`).
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler.LargeSectorsH

open Sect Sob

/-! ### Elements of `Y^s_ℓ`: function, support, norm -/

section Basic

variable {s : ℕ} {K : Set ℂ}

theorem stronglyMeasurable_tupleFn (F : SobTuple s) : StronglyMeasurable (tupleFn F) :=
  Lp.stronglyMeasurable _

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

/-- The norm of `F : Hk s` is the `H^s` norm of any function a.e. equal to its function. -/
theorem Hk_norm_eq_normH_of_ae {F : Hk s} {f : ℂ → ℂ} (hf : MemH s f)
    (h : F.fn =ᵐ[volume] f) : ‖F‖ = normH s f := by
  have hF : toHk s f = F := Hk.ext_fn ((toHk_fn hf).trans h.symm)
  rw [← hF, norm_toHk hf]

theorem Ysec_memH_fn {ℓ : ℤ} (g : Ysec s K ℓ) : MemH s g.fn :=
  (Hk.memH_fn (inclSec s K ℓ g).toHk).1

theorem Ysec_supp {ℓ : ℤ} (g : Ysec s K ℓ) : ∀ᵐ x ∂volume, x ∉ K → g.fn x = 0 :=
  ((mem_YSub_iff ((inclSec s K ℓ g : Y s K) : SobTuple s)).1 (inclSec s K ℓ g).2).2

theorem Ysec_norm_eq_normH_of_ae {ℓ : ℤ} {g : Ysec s K ℓ} {f : ℂ → ℂ} (hf : MemH s f)
    (h : g.fn =ᵐ[volume] f) : ‖g‖ = normH s f :=
  Hk_norm_eq_normH_of_ae (F := (inclSec s K ℓ g).toHk) hf h

end Basic

/-! ### Norm equivalence and the two operator bounds -/

variable (S : SectorSetting)

/-- `‖g_ℓ‖_{s,ℓ} ≤ a‖g‖` and `‖g‖ ≤ b‖g_ℓ‖_{s,ℓ}` on `Y^s_ℓ`, uniformly in `ℓ`. -/
theorem exists_secNormY_equiv (hS : S.Valid) (s : ℕ) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ (ℓ : ℤ) (g : Ysec s S.Nstar ℓ),
      S.secNormY s g ≤ a * ‖g‖ ∧ ‖g‖ ≤ b * S.secNormY s g := by
  obtain ⟨c, C, hc, hC, h⟩ := exists_norm_Ysec_equiv s hS.ρm_pos hS.ρm_lt_ρp
  refine ⟨(Real.sqrt c)⁻¹, Real.sqrt C, by positivity, Real.sqrt_pos.2 hC, fun ℓ g => ?_⟩
  obtain ⟨h1, h2⟩ := h ℓ g
  have hq : 0 ≤ Sob.secNormSq s ℓ (Icc S.ρm S.ρp) (Polar.angularSector g.fn ℓ) :=
    secNormSq_nonneg s ℓ measurableSet_Icc (fun r hr => le_trans hS.ρm_pos.le hr.1) _
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hdef : S.secNormY s g =
      Real.sqrt (Sob.secNormSq s ℓ (Icc S.ρm S.ρp) (Polar.angularSector g.fn ℓ)) := rfl
  rw [hdef]
  constructor
  · rw [inv_mul_eq_div, le_div_iff₀ hsc, ← Real.sqrt_mul hq]
    calc Real.sqrt (Sob.secNormSq s ℓ (Icc S.ρm S.ρp) (Polar.angularSector g.fn ℓ) * c)
        ≤ Real.sqrt (‖g‖ ^ 2) := Real.sqrt_le_sqrt (by rw [mul_comm]; exact h1)
      _ = ‖g‖ := Real.sqrt_sq (norm_nonneg _)
  · rw [← Real.sqrt_mul hC.le]
    calc ‖g‖ = Real.sqrt (‖g‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ _ := Real.sqrt_le_sqrt h2

/-- `lem:semigroup-construct`(1) in the operator norm of `Y^s_ℓ`:
`‖exp(t(-iℓΩ))‖ ≤ C(1+|t|)^s` for all `ℓ`, `|G| ≤ G₊`, `t`. -/
theorem exists_norm_exp_transSec_le (hS : S.Valid) (s : ℕ) {Gp : ℝ} (hGp : 0 ≤ Gp) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ℓ : ℤ) (G : ℝ), |G| ≤ Gp → ∀ t : ℝ,
      ‖NormedSpace.exp ((t : ℂ) • S.transSec s ℓ G)‖ ≤ C * (1 + |t|) ^ s := by
  obtain ⟨C₀, hC₀, h₀⟩ := S.semigroupConstruct_transport_sector hS s hGp
  obtain ⟨a, b, ha, hb, hab⟩ := exists_secNormY_equiv S hS s
  refine ⟨b * C₀ * a, by positivity, fun ℓ G hG t => ?_⟩
  have ht : 0 ≤ (1 + |t|) ^ s := pow_nonneg (by positivity) s
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun g => ?_
  calc ‖NormedSpace.exp ((t : ℂ) • S.transSec s ℓ G) g‖
      ≤ b * S.secNormY s (NormedSpace.exp ((t : ℂ) • S.transSec s ℓ G) g) := (hab ℓ _).2
    _ ≤ b * (C₀ * (1 + |t|) ^ s * S.secNormY s g) :=
        mul_le_mul_of_nonneg_left (h₀ ℓ G hG t g) hb.le
    _ ≤ b * (C₀ * (1 + |t|) ^ s * (a * ‖g‖)) := by
        gcongr
        exact (hab ℓ g).1
    _ = b * C₀ * a * (1 + |t|) ^ s * ‖g‖ := by ring

/-- `cor:K-bound` in the operator norm of `Y^s_ℓ`: `‖k_ℓ𝒢_ℓ‖ ≤ K/|ℓ|` for `ℓ ≠ 0`. -/
theorem exists_norm_Ksec_le (hS : S.Valid) (s : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ ℓ : ℤ, ℓ ≠ 0 → ‖S.Ksec s ℓ‖ ≤ K / |(ℓ : ℝ)| := by
  obtain ⟨CK, hCK, hK⟩ := S.K_bound hS s
  obtain ⟨c, C, hc, hC, hequiv⟩ := exists_norm_Ysec_equiv s hS.ρm_pos hS.ρm_lt_ρp
  obtain ⟨c', C', hc', hC', hprof⟩ := Ang.exists_norm_equiv_ofProfile s hS.ρm_pos hS.ρm_lt_ρp
  refine ⟨Real.sqrt (C' * CK / c), Real.sqrt_pos.2 (by positivity), fun ℓ hℓ => ?_⟩
  have hℓR : (ℓ : ℝ) ≠ 0 := by exact_mod_cast hℓ
  have habs : 0 < |(ℓ : ℝ)| := abs_pos.2 hℓR
  have hl2 : 0 < (ℓ : ℝ) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hℓR))
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun g => ?_
  set h := Polar.angularSector g.fn ℓ with hhdef
  have hgH : MemH s g.fn := Ysec_memH_fn g
  have hgK : ∀ᵐ x ∂volume, ¬ (S.ρm ≤ ‖x‖ ∧ ‖x‖ ≤ S.ρp) → g.fn x = 0 := Ysec_supp g
  obtain ⟨hh, hhK⟩ := Ang.memH1On_angularSector hS.ρm_pos hgH hgK ℓ
  obtain ⟨hKH, hKsupp, hKle⟩ := hK ℓ hℓ h hh hhK
  have hKsupp' : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), r ∉ Icc S.ρm S.ρp →
      S.KsecFn ℓ h r = 0 := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun r hr hrI => hKsupp r hr ?_
    intro hr'
    exact hrI ⟨hS.ρm_lt_r₁.le.trans hr'.1, hr'.2.trans hS.r₂_lt_ρp.le⟩
  obtain ⟨hmem, -, hupper⟩ := hprof ℓ (S.KsecFn ℓ h) hKH hKsupp'
  have hfn := S.Ksec_spec_of_exists s ℓ (S.semigroupConstruct_Ksec hS s ℓ) g
  have hnormK : ‖S.Ksec s ℓ g‖ = normH s (Ang.ofProfile ℓ (S.KsecFn ℓ h)) :=
    Ysec_norm_eq_normH_of_ae hmem hfn
  have hg2 : c * Sob.secNormSq s ℓ (Icc S.ρm S.ρp) h ≤ ‖g‖ ^ 2 := (hequiv ℓ g).1
  have hq : 0 ≤ Sob.secNormSq s ℓ (Icc S.ρm S.ρp) h :=
    secNormSq_nonneg s ℓ measurableSet_Icc (fun r hr => le_trans hS.ρm_pos.le hr.1) _
  have hq' : Sob.secNormSq s ℓ (Icc S.ρm S.ρp) h ≤ ‖g‖ ^ 2 / c := by
    rw [le_div_iff₀ hc]; linarith
  have hKle' : Sob.secNormSq s ℓ (Icc S.ρm S.ρp) (S.KsecFn ℓ h) ≤
      CK * (1 + (ℓ : ℝ) ^ 2)⁻¹ * Sob.secNormSq s ℓ (Icc S.ρm S.ρp) h := hKle
  have hinv : (1 + (ℓ : ℝ) ^ 2)⁻¹ ≤ ((ℓ : ℝ) ^ 2)⁻¹ :=
    inv_anti₀ hl2 (by linarith)
  have hsq : ‖S.Ksec s ℓ g‖ ^ 2 ≤ (C' * CK / c) * (‖g‖ / |(ℓ : ℝ)|) ^ 2 := by
    calc ‖S.Ksec s ℓ g‖ ^ 2 = normH s (Ang.ofProfile ℓ (S.KsecFn ℓ h)) ^ 2 := by rw [hnormK]
      _ ≤ C' * Sob.secNormSq s ℓ (Icc S.ρm S.ρp) (S.KsecFn ℓ h) := hupper
      _ ≤ C' * (CK * (1 + (ℓ : ℝ) ^ 2)⁻¹ * Sob.secNormSq s ℓ (Icc S.ρm S.ρp) h) :=
          mul_le_mul_of_nonneg_left hKle' hC'.le
      _ ≤ C' * (CK * ((ℓ : ℝ) ^ 2)⁻¹ * (‖g‖ ^ 2 / c)) := by
          gcongr
      _ = (C' * CK / c) * (‖g‖ / |(ℓ : ℝ)|) ^ 2 := by
          rw [div_pow, sq_abs]
          field_simp
  have hnn : 0 ≤ ‖g‖ / |(ℓ : ℝ)| := by positivity
  calc ‖S.Ksec s ℓ g‖ = Real.sqrt (‖S.Ksec s ℓ g‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((C' * CK / c) * (‖g‖ / |(ℓ : ℝ)|) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (C' * CK / c) * (‖g‖ / |(ℓ : ℝ)|) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hnn]
    _ = Real.sqrt (C' * CK / c) / |(ℓ : ℝ)| * ‖g‖ := by ring

end NonUniqueEuler.LargeSectorsH
