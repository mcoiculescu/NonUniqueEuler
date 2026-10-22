import NonUniqueEuler.H.Sec4.SemigroupConstruct.Basic
import NonUniqueEuler.I.Sec4.SectorSetting
import NonUniqueEuler.I.Sec4.KBound
import NonUniqueEuler.I.Infra.SectorSpace.RadialMul
import NonUniqueEuler.I.Infra.SectorSpace.Decomposition
import NonUniqueEuler.I.Infra.AngularFourier.NormEquiv
import NonUniqueEuler.I.Infra.AngularFourier.Derivatives
import NonUniqueEuler.I.Infra.Sobolev.Norm
import NonUniqueEuler.I.Infra.CkNorm.Basic

/-!
# Helpers for `lem:semigroup-construct`: the sector operators `-iℓΩ`, `k_ℓ𝒢_ℓ`, `L_ℓ(G)`

Helper file of `P/Sec4/SemigroupConstruct.lean` (fully proved). Remark after
`lem:semigroup-construct` (`04_ring.tex:944-947`):

* `transSec_spec`: `S.transSec s ℓ G` is multiplication by `-iℓΩ(|x|;G)` (`Ω` is smooth on
  `(0, ∞)`, `contDiffOn_Omega`, so `exists_radialMul_spec` applies);
* `kElem`: the element of `Y^s_ℓ` with function `ofProfile ℓ (k_ℓ𝒢_ℓ g_ℓ)` (`cor:K-bound`,
  `K_bound`, and `exists_Ysec_ofProfile`); it is linear in `g` (the profile map is linear a.e.,
  `angularSector_add_ae`, and `𝒢_ℓ` is linear on `L²` profiles supported in `[ρ₋, ρ₊]`) and bounded
  uniformly in `ℓ` (`exists_norm_equiv_ofProfile`, `K_bound`, `exists_norm_Ysec_equiv`);
* `exists_Ksec`: the bounded operator of `semigroupConstruct_Ksec`; `Ksec_apply_eq` and
  `exists_norm_Ksec_le`: the chosen `S.Ksec s ℓ` is it, with `‖S.Ksec s ℓ‖ ≤ C` uniformly in `ℓ`;
* `Lsec_spec`: `S.Lsec s ℓ G` acts on profiles by `LsecFn`.
-/

noncomputable section

open MeasureTheory Set Real Filter
open scoped ContDiff

namespace NonUniqueEuler.SGC

open Sob Sect Ang SectorSetting

/-! ### The coefficient `-iℓΩ` -/

/-- The multiplier `-iℓΩ(r;G)` of `transSec`. -/
def transCoef (S : SectorSetting) (ℓ : ℤ) (G : ℝ) (r : ℝ) : ℂ :=
  -(Complex.I * (ℓ : ℂ) * ((S.Omega G r : ℝ) : ℂ))

theorem contDiffOn_transCoef (S : SectorSetting) (hS : S.Valid) (ℓ : ℤ) (G : ℝ) :
    ContDiffOn ℝ ∞ (transCoef S ℓ G) (Ioi 0) := by
  have h1 : ContDiffOn ℝ ∞ (fun r => ((S.Omega G r : ℝ) : ℂ)) (Ioi 0) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_Omega S hS G)
  exact (contDiffOn_const.mul h1).neg

theorem memCk_of_contDiffOn_Ioi {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} (hf : ContDiffOn ℝ ∞ f (Ioi 0)) {a b : ℝ} (ha : 0 < a) (k : ℕ) :
    MemCk k (Icc a b) f :=
  IsCkNear.memCk_of_isCompact
    ⟨Ioi 0, isOpen_Ioi, fun _ hr => lt_of_lt_of_le ha hr.1, hf.of_le (by exact_mod_cast le_top)⟩
    isCompact_Icc

theorem transSec_eq_radialMul (S : SectorSetting) (s : ℕ) (ℓ : ℤ) (G : ℝ) :
    S.transSec s ℓ G = radialMul s (closedAnnulus S.ρm S.ρp) ℓ (transCoef S ℓ G) := rfl

theorem transSec_spec (S : SectorSetting) (hS : S.Valid) (s : ℕ) (ℓ : ℤ) (G : ℝ)
    (g : Ysec s S.Nstar ℓ) :
    (S.transSec s ℓ G g).fn =ᵐ[volume] fun x => transCoef S ℓ G ‖x‖ * g.fn x := by
  obtain ⟨C, -, h⟩ := exists_radialMul_spec s hS.ρm_pos hS.ρm_lt_ρp
  exact (h ℓ _ (memCk_of_contDiffOn_Ioi (contDiffOn_transCoef S hS ℓ G) hS.ρm_pos s)).1 g

/-! ### Profiles -/

theorem prof_spec {S : SectorSetting} (hS : S.Valid) {s : ℕ} {ℓ : ℤ} (g : Ysec s S.Nstar ℓ) :
    MemH1On s (Ioi 0) (Polar.angularSector g.fn ℓ) ∧
      ∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc S.ρm S.ρp → Polar.angularSector g.fn ℓ r = 0 :=
  memH1On_angularSector hS.ρm_pos (ysec_memH g).1 (ysec_supp g) ℓ

/-! ### The Green operator is linear on `L²` profiles supported in a compact interval -/

theorem integrableOn_green_integrand {a b : ℝ} {h : ℝ → ℂ}
    (hh : MemLp h 2 (volume.restrict (Ioi 0)))
    (hsupp : ∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc a b → h r = 0) (n : ℕ) {r : ℝ}
    (hr : 0 ≤ r) :
    IntegrableOn (fun ρ : ℝ => (((min r ρ / max r ρ) ^ n : ℝ) : ℂ) * h ρ * (ρ : ℂ)) (Ioi 0) := by
  set μ : Measure ℝ := volume.restrict (Ioi 0) with hμ
  have hfin : μ (Icc a b) ≠ ⊤ := by
    rw [hμ, Measure.restrict_apply measurableSet_Icc]
    exact ((measure_mono inter_subset_left).trans_lt measure_Icc_lt_top).ne
  have : IsFiniteMeasure (μ.restrict (Icc a b)) := isFiniteMeasure_restrict.2 hfin
  have hint : Integrable h (μ.restrict (Icc a b)) := (hh.restrict (Icc a b)).integrable (by norm_num)
  have hmeas : AEStronglyMeasurable
      (fun ρ : ℝ => (((min r ρ / max r ρ) ^ n : ℝ) : ℂ) * (ρ : ℂ)) (μ.restrict (Icc a b)) :=
    (by fun_prop : Measurable fun ρ : ℝ =>
      (((min r ρ / max r ρ) ^ n : ℝ) : ℂ) * (ρ : ℂ)).aestronglyMeasurable
  have hbd : ∀ᵐ ρ ∂(μ.restrict (Icc a b)),
      ‖(((min r ρ / max r ρ) ^ n : ℝ) : ℂ) * (ρ : ℂ)‖ ≤ |b| := by
    rw [hμ, Measure.restrict_restrict measurableSet_Icc]
    refine ae_restrict_of_forall_mem (measurableSet_Icc.inter measurableSet_Ioi) fun ρ hρ => ?_
    have hρ0 : 0 < ρ := hρ.2
    have hmax : 0 < max r ρ := lt_max_of_lt_right hρ0
    have hq0 : 0 ≤ min r ρ / max r ρ := div_nonneg (le_min hr hρ0.le) hmax.le
    have hq1 : min r ρ / max r ρ ≤ 1 := (div_le_one hmax).2 (min_le_max)
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hq0 n), abs_of_pos hρ0]
    calc (min r ρ / max r ρ) ^ n * ρ ≤ 1 * ρ :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ hq0 hq1) hρ0.le
      _ ≤ |b| := by rw [one_mul]; exact hρ.1.2.trans (le_abs_self b)
  have h1 : Integrable (fun ρ : ℝ => (((min r ρ / max r ρ) ^ n : ℝ) : ℂ) * (ρ : ℂ) * h ρ)
      (μ.restrict (Icc a b)) := hint.bdd_mul hmeas hbd
  have h2 : IntegrableOn (fun ρ : ℝ => (((min r ρ / max r ρ) ^ n : ℝ) : ℂ) * h ρ * (ρ : ℂ))
      (Icc a b) μ := by
    refine h1.congr (Eventually.of_forall fun ρ => ?_)
    simp only
    ring
  have h3 := (integrable_indicator_iff measurableSet_Icc).2 h2
  refine h3.congr ?_
  filter_upwards [hsupp] with ρ hρ
  by_cases hm : ρ ∈ Icc a b
  · rw [indicator_of_mem hm]
  · rw [indicator_of_notMem hm, hρ hm, mul_zero, zero_mul]

theorem green_congr_ae {ℓ : ℤ} {h h' : ℝ → ℂ} (hhh : h =ᵐ[volume.restrict (Ioi 0)] h')
    (r : ℝ) : green ℓ h r = green ℓ h' r := by
  simp only [green]
  congr 1
  refine setIntegral_congr_ae measurableSet_Ioi ?_
  filter_upwards [(ae_restrict_iff' measurableSet_Ioi).1 hhh] with ρ hρ hρI
  rw [hρ hρI]

theorem green_add {ℓ : ℤ} {a b : ℝ} {h₁ h₂ : ℝ → ℂ}
    (hh₁ : MemLp h₁ 2 (volume.restrict (Ioi 0)))
    (hs₁ : ∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc a b → h₁ r = 0)
    (hh₂ : MemLp h₂ 2 (volume.restrict (Ioi 0)))
    (hs₂ : ∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc a b → h₂ r = 0) {r : ℝ} (hr : 0 ≤ r) :
    green ℓ (h₁ + h₂) r = green ℓ h₁ r + green ℓ h₂ r := by
  simp only [green, Pi.add_apply, mul_add, add_mul]
  rw [integral_add (integrableOn_green_integrand hh₁ hs₁ _ hr)
    (integrableOn_green_integrand hh₂ hs₂ _ hr), mul_add]

theorem green_smul {ℓ : ℤ} (c : ℂ) (h : ℝ → ℂ) (r : ℝ) :
    green ℓ (c • h) r = c * green ℓ h r := by
  simp only [green, Pi.smul_apply, smul_eq_mul]
  have : ∀ ρ : ℝ, (((min r ρ / max r ρ) ^ ℓ.natAbs : ℝ) : ℂ) * (c * h ρ) * (ρ : ℂ) =
      c * ((((min r ρ / max r ρ) ^ ℓ.natAbs : ℝ) : ℂ) * h ρ * (ρ : ℂ)) := fun ρ => by ring
  simp only [this]
  rw [integral_const_mul]
  ring

/-! ### The coupling operator `k_ℓ𝒢_ℓ` on a sector -/

/-- The plane function `(k_ℓ𝒢_ℓ g_ℓ)(r) e^{iℓθ}` of a plane function `g`. -/
def kFn (S : SectorSetting) (ℓ : ℤ) (g : ℂ → ℂ) : ℂ → ℂ :=
  ofProfile ℓ (S.KsecFn ℓ (Polar.angularSector g ℓ))

theorem exists_kFn {S : SectorSetting} (hS : S.Valid) {s : ℕ} {ℓ : ℤ} (g : Ysec s S.Nstar ℓ) :
    ∃ g' : Ysec s S.Nstar ℓ, g'.fn =ᵐ[volume] kFn S ℓ g.fn := by
  by_cases hℓ : ℓ = 0
  · subst hℓ
    refine ⟨0, ?_⟩
    have : kFn S 0 g.fn = fun _ => 0 := by
      funext x
      simp [kFn, ofProfile, KsecFn]
    rw [this]
    exact ysec_fn_zero
  · obtain ⟨CK, -, hK⟩ := K_bound S hS s
    obtain ⟨hm, hsupp⟩ := prof_spec hS g
    obtain ⟨hm', hz, -⟩ := hK ℓ hℓ _ hm hsupp
    have hsupp' : ∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc S.ρm S.ρp →
        S.KsecFn ℓ (Polar.angularSector g.fn ℓ) r = 0 := by
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun r hr hrI => hz r hr fun h => hrI ?_
      exact ⟨hS.ρm_lt_r₁.le.trans h.1, h.2.trans hS.r₂_lt_ρp.le⟩
    exact exists_Ysec_ofProfile hS.ρm_pos hS.ρm_lt_ρp ℓ hm' hsupp'

/-- The element of `Y^s_ℓ` with function `kFn S ℓ g.fn`. -/
def kElem (S : SectorSetting) (s : ℕ) (ℓ : ℤ) (g : Ysec s S.Nstar ℓ) : Ysec s S.Nstar ℓ :=
  toYsec s S.Nstar ℓ (kFn S ℓ g.fn)

theorem kElem_spec {S : SectorSetting} (hS : S.Valid) {s : ℕ} {ℓ : ℤ} (g : Ysec s S.Nstar ℓ) :
    (kElem S s ℓ g).fn =ᵐ[volume] kFn S ℓ g.fn :=
  toYsec_spec (exists_kFn hS g)

theorem kFn_add {S : SectorSetting} (hS : S.Valid) {s : ℕ} {ℓ : ℤ} (g g' : Ysec s S.Nstar ℓ) :
    kFn S ℓ (g + g').fn = kFn S ℓ g.fn + kFn S ℓ g'.fn := by
  have hp : Polar.angularSector (g + g').fn ℓ =ᵐ[volume.restrict (Ioi 0)]
      Polar.angularSector g.fn ℓ + Polar.angularSector g'.fn ℓ := by
    filter_upwards [angularSector_congr_ae (ysec_fn_add g g') ℓ,
      angularSector_add_ae ((ysec_memLp g).locallyIntegrable (by norm_num))
        ((ysec_memLp g').locallyIntegrable (by norm_num)) ℓ] with r h1 h2
    rw [h1, h2, Pi.add_apply]
  obtain ⟨hm, hs⟩ := prof_spec hS g
  obtain ⟨hm', hs'⟩ := prof_spec hS g'
  funext x
  simp only [kFn, ofProfile, KsecFn, Pi.add_apply]
  rw [green_congr_ae hp, green_add hm.memLp hs hm'.memLp hs' (norm_nonneg x)]
  ring

theorem kFn_smul {S : SectorSetting} {s : ℕ} {ℓ : ℤ} (c : ℂ) (g : Ysec s S.Nstar ℓ) :
    kFn S ℓ (c • g).fn = c • kFn S ℓ g.fn := by
  have hp : Polar.angularSector (c • g).fn ℓ =ᵐ[volume.restrict (Ioi 0)]
      c • Polar.angularSector g.fn ℓ := by
    filter_upwards [angularSector_congr_ae (ysec_fn_smul c g) ℓ] with r h1
    rw [h1, angularSector_smul, Pi.smul_apply, smul_eq_mul]
  funext x
  simp only [kFn, ofProfile, KsecFn, Pi.smul_apply, smul_eq_mul]
  rw [green_congr_ae hp, green_smul]
  ring

/-- `kElem` as a linear map. -/
def kLin {S : SectorSetting} (hS : S.Valid) (s : ℕ) (ℓ : ℤ) :
    Ysec s S.Nstar ℓ →ₗ[ℂ] Ysec s S.Nstar ℓ where
  toFun := kElem S s ℓ
  map_add' g g' := by
    refine ysec_ext ?_
    filter_upwards [kElem_spec hS (g + g'), ysec_fn_add (kElem S s ℓ g) (kElem S s ℓ g'),
      kElem_spec hS g, kElem_spec hS g'] with x h1 h2 h3 h4
    rw [h1, h2, Pi.add_apply, h3, h4, kFn_add hS g g', Pi.add_apply]
  map_smul' c g := by
    refine ysec_ext ?_
    filter_upwards [kElem_spec hS (c • g), ysec_fn_smul c (kElem S s ℓ g),
      kElem_spec hS g] with x h1 h2 h3
    rw [h1, RingHom.id_apply, h2, Pi.smul_apply, h3, kFn_smul c g, Pi.smul_apply]

/-- The uniform bound `‖k_ℓ𝒢_ℓ g‖_{Y^s} ≤ C ‖g‖_{Y^s}` (`cor:K-bound` and `lem:norm-equiv`). -/
theorem exists_norm_kElem_le {S : SectorSetting} (hS : S.Valid) (s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ℓ : ℤ) (g : Ysec s S.Nstar ℓ), ‖kElem S s ℓ g‖ ≤ C * ‖g‖ := by
  obtain ⟨CK, hCK, hK⟩ := K_bound S hS s
  obtain ⟨c1, C1, hc1, hC1, h1⟩ := exists_norm_equiv_ofProfile s hS.ρm_pos hS.ρm_lt_ρp
  obtain ⟨c2, C2, hc2, hC2, h2⟩ := exists_norm_Ysec_equiv s hS.ρm_pos hS.ρm_lt_ρp
  refine ⟨Real.sqrt (C1 * CK / c2), Real.sqrt_pos.2 (by positivity), fun ℓ g => ?_⟩
  by_cases hℓ : ℓ = 0
  · subst hℓ
    have h0 : kElem S s 0 g = 0 := by
      refine ysec_ext ?_
      filter_upwards [kElem_spec hS g, (ysec_fn_zero : (0 : Ysec s S.Nstar 0).fn =ᵐ[volume] 0)]
        with x hx h0
      rw [hx, h0]
      simp [kFn, ofProfile, KsecFn]
    rw [h0, norm_zero]
    positivity
  · obtain ⟨hm, hsupp⟩ := prof_spec hS g
    obtain ⟨hm', hz, hbound⟩ := hK ℓ hℓ _ hm hsupp
    have hsupp' : ∀ᵐ r ∂(volume.restrict (Ioi 0)), r ∉ Icc S.ρm S.ρp →
        S.KsecFn ℓ (Polar.angularSector g.fn ℓ) r = 0 := by
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun r hr hrI => hz r hr fun h => hrI ?_
      exact ⟨hS.ρm_lt_r₁.le.trans h.1, h.2.trans hS.r₂_lt_ρp.le⟩
    obtain ⟨-, -, hup⟩ := h1 ℓ _ hm' hsupp'
    obtain ⟨hlow, -⟩ := h2 ℓ g
    have hnk : ‖kElem S s ℓ g‖ = normH s (kFn S ℓ g.fn) := by
      rw [← (ysec_memH (kElem S s ℓ g)).2]
      exact ((ysec_memH (kElem S s ℓ g)).1.congr_ae (kElem_spec hS g)).2.symm
    have hsec0 : 0 ≤ Sob.secNormSq s ℓ (Icc S.ρm S.ρp) (Polar.angularSector g.fn ℓ) :=
      secNormSq_nonneg s ℓ measurableSet_Icc (fun r hr => hS.ρm_pos.le.trans hr.1) _
    have hw : (1 + (ℓ : ℝ) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg (ℓ : ℝ)])
    have hsq : ‖kElem S s ℓ g‖ ^ 2 ≤ (C1 * CK / c2) * ‖g‖ ^ 2 := by
      rw [hnk]
      calc normH s (kFn S ℓ g.fn) ^ 2
          ≤ C1 * Sob.secNormSq s ℓ (Icc S.ρm S.ρp)
              (S.KsecFn ℓ (Polar.angularSector g.fn ℓ)) := hup
        _ ≤ C1 * (CK * (1 + (ℓ : ℝ) ^ 2)⁻¹ *
              Sob.secNormSq s ℓ (Icc S.ρm S.ρp) (Polar.angularSector g.fn ℓ)) :=
            mul_le_mul_of_nonneg_left hbound hC1.le
        _ ≤ C1 * (CK * Sob.secNormSq s ℓ (Icc S.ρm S.ρp) (Polar.angularSector g.fn ℓ)) := by
            gcongr
            calc CK * (1 + (ℓ : ℝ) ^ 2)⁻¹ ≤ CK * 1 := mul_le_mul_of_nonneg_left hw hCK.le
              _ = CK := mul_one _
        _ = (C1 * CK / c2) * (c2 *
              Sob.secNormSq s ℓ (Icc S.ρm S.ρp) (Polar.angularSector g.fn ℓ)) := by
            field_simp
        _ ≤ (C1 * CK / c2) * ‖g‖ ^ 2 := mul_le_mul_of_nonneg_left hlow (by positivity)
    have := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (by positivity),
      Real.sqrt_sq (norm_nonneg _)] at this

/-- `semigroupConstruct_Ksec` (the existence). -/
theorem exists_Ksec (S : SectorSetting) (hS : S.Valid) (s : ℕ) (ℓ : ℤ) :
    ∃ T : Ysec s S.Nstar ℓ →L[ℂ] Ysec s S.Nstar ℓ, ∀ g : Ysec s S.Nstar ℓ,
      (T g).fn =ᵐ[volume] Ang.ofProfile ℓ (S.KsecFn ℓ (Polar.angularSector g.fn ℓ)) := by
  obtain ⟨C, -, hC⟩ := exists_norm_kElem_le hS s
  exact ⟨(kLin hS s ℓ).mkContinuous C (hC ℓ), fun g => kElem_spec hS g⟩

theorem Ksec_spec (S : SectorSetting) (hS : S.Valid) (s : ℕ) (ℓ : ℤ) (g : Ysec s S.Nstar ℓ) :
    (S.Ksec s ℓ g).fn =ᵐ[volume] Ang.ofProfile ℓ (S.KsecFn ℓ (Polar.angularSector g.fn ℓ)) :=
  Ksec_spec_of_exists S s ℓ (exists_Ksec S hS s ℓ) g

theorem Ksec_apply_eq (S : SectorSetting) (hS : S.Valid) (s : ℕ) (ℓ : ℤ) (g : Ysec s S.Nstar ℓ) :
    S.Ksec s ℓ g = kElem S s ℓ g :=
  ysec_ext ((Ksec_spec S hS s ℓ g).trans (kElem_spec hS g).symm)

/-- The chosen `S.Ksec s ℓ` is bounded uniformly in `ℓ`. -/
theorem exists_norm_Ksec_le (S : SectorSetting) (hS : S.Valid) (s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ℓ : ℤ, ‖S.Ksec s ℓ‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := exists_norm_kElem_le hS s
  refine ⟨C, hC, fun ℓ => ContinuousLinearMap.opNorm_le_bound _ hC.le fun g => ?_⟩
  rw [Ksec_apply_eq S hS]
  exact h ℓ g

/-! ### The sector operator `L_ℓ(G)` -/

theorem Lsec_spec (S : SectorSetting) (hS : S.Valid) (s : ℕ) (ℓ : ℤ) (G : ℝ)
    (g : Ysec s S.Nstar ℓ) :
    (S.Lsec s ℓ G g).fn =ᵐ[volume]
      Ang.ofProfile ℓ (S.LsecFn ℓ G (Polar.angularSector g.fn ℓ)) := by
  have hL : S.Lsec s ℓ G g = S.transSec s ℓ G g + S.Ksec s ℓ g := rfl
  have hg : g.fn =ᵐ[volume] ofProfile ℓ (Polar.angularSector g.fn ℓ) :=
    Ysec.fn_ae_eq_ofProfile hS.ρm_pos g
  filter_upwards [ysec_fn_add (S.transSec s ℓ G g) (S.Ksec s ℓ g), transSec_spec S hS s ℓ G g,
    Ksec_spec S hS s ℓ g, hg] with x h1 h2 h3 h4
  rw [hL, h1, Pi.add_apply, h2, h3, h4]
  simp only [ofProfile, LsecFn, transCoef]
  ring

end NonUniqueEuler.SGC
