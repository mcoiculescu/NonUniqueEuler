import NonUniqueEuler.H.Sec4.Sector.SecBasic
import NonUniqueEuler.H.Sec4.Sector.GreenGrowth
import NonUniqueEuler.H.Sec4.Sector.Riccati
import NonUniqueEuler.I.Sec4.SectorSetting
import NonUniqueEuler.I.Infra.SectorSpace.RadialMul
import NonUniqueEuler.I.Infra.SectorSpace.Decomposition
import NonUniqueEuler.I.Infra.CkNorm.Basic

/-!
# Helper for `lem:sector`(4): `L_ℓ(G)` is a bounded operator on `Y^0_ℓ`

Helper file of `P/Sec4/Sector.lean` (fully proved). Manuscript `04_ring.tex:282-286`.

* `isProfileL2_KsecFn`: for `g ∈ Y^0_ℓ` (as a profile), `k_ℓ𝒢_ℓ g ∈ Y^0_ℓ`: `k_ℓ` is continuous on
  `(0,∞)` and vanishes off `[r₁, r₂]`, and `𝒢_ℓ g` is continuous (`Prof.continuousOn_Psi`).
* `exists_Ksec0`: the bounded operator `k_ℓ𝒢_ℓ` on `Y^0_ℓ` (linear in the profile, bounded by
  `norm_green_le`, `|𝒢_ℓ g(r)| ≤ (ρ₊/(2|ℓ|)) ‖g‖_{L²(r dr)}`). This follows the construction of
  `H/Sec4/SemigroupConstruct/SectorOps.lean` (for every `s`, from `cor:K-bound`, which depends on
  `lem:sector`), here for `s = 0` from part (1) only.
* `Lsec_zero_spec'`: the chosen `S.Lsec 0 ℓ G` acts on profiles as `L_ℓ(G)`.
-/

noncomputable section

open MeasureTheory Set Real Filter
open scoped ContDiff

namespace NonUniqueEuler.SectorH

open Sob Sect Ang SectorSetting

/-! ### Profiles in `Y^0_ℓ` -/

theorem prof_of_isProfileL2 {S : SectorSetting} (hS : S.Valid) {g : ℝ → ℂ}
    (hg : S.IsProfileL2 g) : Prof S.ρm S.ρp g :=
  ⟨hS.ρm_pos, hS.ρm_lt_ρp.le, hg.1.integrable (by norm_num), hg.2⟩

theorem Prof.add {a b : ℝ} {p q : ℝ → ℂ} (hp : Prof a b p) (hq : Prof a b q) :
    Prof a b (p + q) := by
  refine ⟨hp.pos, hp.le, hp.int.add hq.int, ?_⟩
  filter_upwards [hp.supp, hq.supp] with r h1 h2 hr
  simp [h1 hr, h2 hr]

theorem green_add_of_prof {a b : ℝ} {p q : ℝ → ℂ} (hp : Prof a b p) (hq : Prof a b q) (ℓ : ℤ)
    {r : ℝ} (hr : 0 ≤ r) : green ℓ (p + q) r = green ℓ p r + green ℓ q r := by
  rw [green_eq_Psi (hp.add hq), green_eq_Psi hp, green_eq_Psi hq]
  simp only [Psi, Pi.add_apply, mul_add]
  rw [integral_add (hp.integrable_ker _ hr) (hq.integrable_ker _ hr)]
  ring

theorem green_congr_ae {ℓ : ℤ} {h h' : ℝ → ℂ} (hhh : h =ᵐ[volume.restrict (Ioi 0)] h')
    (r : ℝ) : green ℓ h r = green ℓ h' r := by
  simp only [green]
  congr 1
  refine setIntegral_congr_ae measurableSet_Ioi ?_
  filter_upwards [(ae_restrict_iff' measurableSet_Ioi).1 hhh] with ρ hρ hρI
  rw [hρ hρI]

theorem green_smul {ℓ : ℤ} (c : ℂ) (h : ℝ → ℂ) (r : ℝ) :
    green ℓ (c • h) r = c * green ℓ h r := by
  simp only [green, Pi.smul_apply, smul_eq_mul]
  have : ∀ ρ : ℝ, (((min r ρ / max r ρ) ^ ℓ.natAbs : ℝ) : ℂ) * (c * h ρ) * (ρ : ℂ) =
      c * ((((min r ρ / max r ρ) ^ ℓ.natAbs : ℝ) : ℂ) * h ρ * (ρ : ℂ)) := fun ρ => by ring
  simp only [this]
  rw [integral_const_mul]
  ring

/-! ### The coefficient `k_ℓ` -/

theorem continuousOn_kcoef (S : SectorSetting) (hS : S.Valid) (ℓ : ℤ) :
    ContinuousOn (S.kcoef ℓ) (Ioi 0) := by
  have hd : Continuous S.dom := (contDiff_dom S hS).continuous
  refine ContinuousOn.div (continuousOn_const.mul (Complex.continuous_ofReal.comp hd).continuousOn)
    Complex.continuous_ofReal.continuousOn fun r hr => ?_
  exact_mod_cast ne_of_gt (show (0 : ℝ) < r from hr)

theorem kcoef_eq_zero (S : SectorSetting) (hS : S.Valid) (ℓ : ℤ) {r : ℝ} (hr : 0 < r)
    (hrI : r ∉ Icc S.ρm S.ρp) : S.kcoef ℓ r = 0 := by
  have : r ∉ Icc S.r₁ S.r₂ := fun h =>
    hrI ⟨hS.ρm_lt_r₁.le.trans h.1, h.2.trans hS.r₂_lt_ρp.le⟩
  simp [kcoef, hS.dom_eq_zero r hr this]

theorem continuousOn_green {S : SectorSetting} (hS : S.Valid) {p : ℝ → ℂ} (hp : S.IsProfileL2 p)
    (ℓ : ℤ) : ContinuousOn (green ℓ p) (Ioi 0) := by
  have h := prof_of_isProfileL2 hS hp
  have : green ℓ p = fun t => -(((2 * |(ℓ : ℝ)|)⁻¹ : ℝ) : ℂ) * Psi S.ρm S.ρp ℓ.natAbs p t :=
    funext (green_eq_Psi h ℓ)
  rw [this]
  exact continuousOn_const.mul ((h.continuousOn_Psi _).mono fun t ht => mem_Ici.2 (le_of_lt ht))

theorem continuousOn_KsecFn {S : SectorSetting} (hS : S.Valid) {p : ℝ → ℂ}
    (hp : S.IsProfileL2 p) (ℓ : ℤ) : ContinuousOn (S.KsecFn ℓ p) (Ioi 0) :=
  (continuousOn_kcoef S hS ℓ).mul (continuousOn_green hS hp ℓ)

theorem KsecFn_eq_zero {S : SectorSetting} (hS : S.Valid) (ℓ : ℤ) (p : ℝ → ℂ) {r : ℝ}
    (hr : 0 < r) (hrI : r ∉ Icc S.ρm S.ρp) : S.KsecFn ℓ p r = 0 := by
  simp [KsecFn, kcoef_eq_zero S hS ℓ hr hrI]

theorem isProfileL2_KsecFn {S : SectorSetting} (hS : S.Valid) {p : ℝ → ℂ}
    (hp : S.IsProfileL2 p) (ℓ : ℤ) : S.IsProfileL2 (S.KsecFn ℓ p) := by
  have hsub : Icc S.ρm S.ρp ⊆ Ioi 0 := fun r hr => hS.ρm_pos.trans_le hr.1
  have hc : ContinuousOn (S.KsecFn ℓ p) (Icc S.ρm S.ρp) := (continuousOn_KsecFn hS hp ℓ).mono hsub
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨?_, ?_⟩
  · exact MemLp.of_bound (hc.aestronglyMeasurable measurableSet_Icc) M
      (ae_restrict_of_forall_mem measurableSet_Icc hM)
  · exact ae_restrict_of_forall_mem measurableSet_Ioi fun r hr hrI =>
      KsecFn_eq_zero hS ℓ p hr hrI

/-- `|k_ℓ 𝒢_ℓ g(r)| ≤ M ‖g‖_{L²(r dr)}` for `r > 0`, with `M` depending on `S` and `ℓ` only. -/
theorem exists_norm_KsecFn_le (S : SectorSetting) (hS : S.Valid) (ℓ : ℤ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p : ℝ → ℂ, S.IsProfileL2 p → ∀ r : ℝ, 0 < r →
      ‖S.KsecFn ℓ p r‖ ≤ M * Real.sqrt (∫ ρ in Ioi (0 : ℝ), ‖p ρ‖ ^ 2 * ρ) := by
  by_cases hℓ : ℓ = 0
  · subst hℓ
    exact ⟨0, le_rfl, fun p _ r _ => by simp [KsecFn]⟩
  have hsub : Icc S.ρm S.ρp ⊆ Ioi 0 := fun r hr => hS.ρm_pos.trans_le hr.1
  obtain ⟨Mk, hMk⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((continuousOn_kcoef S hS ℓ).mono hsub)
  have hMk0 : 0 ≤ Mk := (norm_nonneg _).trans (hMk S.ρm ⟨le_rfl, hS.ρm_lt_ρp.le⟩)
  refine ⟨Mk * (S.ρp / (2 * |(ℓ : ℝ)|)), by
    have := hS.ρm_pos.trans hS.ρm_lt_ρp; positivity, fun p hp r hr => ?_⟩
  by_cases hrI : r ∈ Icc S.ρm S.ρp
  · rw [KsecFn, norm_mul, mul_assoc]
    exact mul_le_mul (hMk r hrI) (norm_green_le (prof_of_isProfileL2 hS hp) hp.1 hℓ hr.le)
      (norm_nonneg _) hMk0
  · rw [KsecFn_eq_zero hS ℓ p hr hrI, norm_zero]
    have := hS.ρm_pos.trans hS.ρm_lt_ρp
    positivity

/-! ### The operator `k_ℓ𝒢_ℓ` on `Y^0_ℓ` -/

/-- The plane function `(k_ℓ𝒢_ℓ f_ℓ)(r) e^{iℓθ}` of a plane function `f`. -/
def kFn0 (S : SectorSetting) (ℓ : ℤ) (f : ℂ → ℂ) : ℂ → ℂ :=
  ofProfile ℓ (S.KsecFn ℓ (Polar.angularSector f ℓ))

theorem exists_kFn0 {S : SectorSetting} (hS : S.Valid) {ℓ : ℤ} (g : Ysec 0 S.Nstar ℓ) :
    ∃ g' : Ysec 0 S.Nstar ℓ, g'.fn =ᵐ[volume] kFn0 S ℓ g.fn :=
  let ⟨g', hg', _⟩ := exists_Ysec_zero_of_isProfileL2 S hS ℓ
    (isProfileL2_KsecFn hS (isProfileL2_angularSector S hS ℓ g).1 ℓ)
  ⟨g', hg'⟩

/-- The element of `Y^0_ℓ` with function `kFn0 S ℓ g.fn`. -/
def kElem0 (S : SectorSetting) (ℓ : ℤ) (g : Ysec 0 S.Nstar ℓ) : Ysec 0 S.Nstar ℓ :=
  toYsec 0 S.Nstar ℓ (kFn0 S ℓ g.fn)

theorem kElem0_spec {S : SectorSetting} (hS : S.Valid) {ℓ : ℤ} (g : Ysec 0 S.Nstar ℓ) :
    (kElem0 S ℓ g).fn =ᵐ[volume] kFn0 S ℓ g.fn :=
  toYsec_spec (exists_kFn0 hS g)

theorem kFn0_add {S : SectorSetting} (hS : S.Valid) {ℓ : ℤ} (g g' : Ysec 0 S.Nstar ℓ) :
    kFn0 S ℓ (g + g').fn = kFn0 S ℓ g.fn + kFn0 S ℓ g'.fn := by
  have hp : Polar.angularSector (g + g').fn ℓ =ᵐ[volume.restrict (Ioi 0)]
      Polar.angularSector g.fn ℓ + Polar.angularSector g'.fn ℓ := by
    filter_upwards [angularSector_congr_ae (ysec_fn_add g g') ℓ,
      angularSector_add_ae ((ysec_memLp g).locallyIntegrable (by norm_num))
        ((ysec_memLp g').locallyIntegrable (by norm_num)) ℓ] with r h1 h2
    rw [h1, h2, Pi.add_apply]
  have h1 := prof_of_isProfileL2 hS (isProfileL2_angularSector S hS ℓ g).1
  have h2 := prof_of_isProfileL2 hS (isProfileL2_angularSector S hS ℓ g').1
  funext x
  simp only [kFn0, ofProfile, KsecFn, Pi.add_apply]
  rw [green_congr_ae hp, green_add_of_prof h1 h2 ℓ (norm_nonneg x)]
  ring

theorem kFn0_smul {S : SectorSetting} {ℓ : ℤ} (c : ℂ) (g : Ysec 0 S.Nstar ℓ) :
    kFn0 S ℓ (c • g).fn = c • kFn0 S ℓ g.fn := by
  have hp : Polar.angularSector (c • g).fn ℓ =ᵐ[volume.restrict (Ioi 0)]
      c • Polar.angularSector g.fn ℓ := by
    filter_upwards [angularSector_congr_ae (ysec_fn_smul c g) ℓ] with r h1
    rw [h1, angularSector_smul, Pi.smul_apply, smul_eq_mul]
  funext x
  simp only [kFn0, ofProfile, KsecFn, Pi.smul_apply, smul_eq_mul]
  rw [green_congr_ae hp, green_smul]
  ring

/-- `kElem0` as a linear map. -/
def kLin0 {S : SectorSetting} (hS : S.Valid) (ℓ : ℤ) :
    Ysec 0 S.Nstar ℓ →ₗ[ℂ] Ysec 0 S.Nstar ℓ where
  toFun := kElem0 S ℓ
  map_add' g g' := by
    refine ysec_ext ?_
    filter_upwards [kElem0_spec hS (g + g'), ysec_fn_add (kElem0 S ℓ g) (kElem0 S ℓ g'),
      kElem0_spec hS g, kElem0_spec hS g'] with x h1 h2 h3 h4
    rw [h1, h2, Pi.add_apply, h3, h4, kFn0_add hS g g', Pi.add_apply]
  map_smul' c g := by
    refine ysec_ext ?_
    filter_upwards [kElem0_spec hS (c • g), ysec_fn_smul c (kElem0 S ℓ g),
      kElem0_spec hS g] with x h1 h2 h3
    rw [h1, RingHom.id_apply, h2, Pi.smul_apply, h3, kFn0_smul c g, Pi.smul_apply]

/-- `‖k_ℓ𝒢_ℓ g‖_{Y^0_ℓ} ≤ C ‖g‖_{Y^0_ℓ}`. -/
theorem exists_norm_kElem0_le {S : SectorSetting} (hS : S.Valid) (ℓ : ℤ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : Ysec 0 S.Nstar ℓ, ‖kElem0 S ℓ g‖ ≤ C * ‖g‖ := by
  obtain ⟨M, hM0, hM⟩ := exists_norm_KsecFn_le S hS ℓ
  have hρp : 0 < S.ρp := hS.ρm_pos.trans hS.ρm_lt_ρp
  refine ⟨M * S.ρp, by positivity, fun g => ?_⟩
  set p := Polar.angularSector g.fn ℓ with hpdef
  obtain ⟨hp, hng⟩ := isProfileL2_angularSector S hS ℓ g
  set k := kElem0 S ℓ g
  obtain ⟨-, hnk⟩ := isProfileL2_angularSector S hS ℓ k
  set Q := ∫ ρ in Ioi (0 : ℝ), ‖p ρ‖ ^ 2 * ρ with hQ
  have hQ0 : 0 ≤ Q := setIntegral_nonneg measurableSet_Ioi fun ρ hρ =>
    mul_nonneg (sq_nonneg _) (le_of_lt hρ)
  -- the profile of `k` is `k_ℓ𝒢_ℓ p`
  have hkp : Polar.angularSector k.fn ℓ =ᵐ[volume.restrict (Ioi 0)] S.KsecFn ℓ p := by
    filter_upwards [angularSector_congr_ae (kElem0_spec hS g) ℓ,
      ae_restrict_mem measurableSet_Ioi] with r h1 hr
    rw [h1, kFn0, angularSector_ofProfile ℓ _ hr]
  have hint : ∫ r in Ioi (0 : ℝ), ‖Polar.angularSector k.fn ℓ r‖ ^ 2 * r =
      ∫ r in Ioi (0 : ℝ), ‖S.KsecFn ℓ p r‖ ^ 2 * r := by
    refine integral_congr_ae ?_
    filter_upwards [hkp] with r hr
    rw [hr]
  have hsub : Icc S.ρm S.ρp ⊆ Ioi 0 := fun r hr => hS.ρm_pos.trans_le hr.1
  have hIcc : ∫ r in Ioi (0 : ℝ), ‖S.KsecFn ℓ p r‖ ^ 2 * r =
      ∫ r in Icc S.ρm S.ρp, ‖S.KsecFn ℓ p r‖ ^ 2 * r := by
    refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioi.nullMeasurableSet hsub
      (Eventually.of_forall fun r hr => ?_)
    rw [KsecFn_eq_zero hS ℓ p hr.1 hr.2, norm_zero]
    ring
  have hbound : ∫ r in Icc S.ρm S.ρp, ‖S.KsecFn ℓ p r‖ ^ 2 * r ≤
      (M * Real.sqrt Q) ^ 2 * S.ρp * (S.ρp - S.ρm) := by
    have h1 : ‖∫ r in Icc S.ρm S.ρp, ‖S.KsecFn ℓ p r‖ ^ 2 * r‖ ≤
        (M * Real.sqrt Q) ^ 2 * S.ρp * volume.real (Icc S.ρm S.ρp) := by
      refine norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top fun r hr => ?_
      have hr0 : 0 < r := hsub hr
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hr0.le)]
      have hK := hM p hp r hr0
      have hKsq : ‖S.KsecFn ℓ p r‖ ^ 2 ≤ (M * Real.sqrt Q) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hK 2
      exact mul_le_mul hKsq hr.2 hr0.le (sq_nonneg _)
    rw [Real.volume_real_Icc_of_le hS.ρm_lt_ρp.le] at h1
    exact (le_abs_self _).trans (by rwa [← Real.norm_eq_abs])
  have hsq : ‖k‖ ^ 2 ≤ (M * S.ρp) ^ 2 * ‖g‖ ^ 2 := by
    rw [hnk, hint, hIcc, hng]
    have hpi : 0 ≤ 2 * π := by positivity
    calc 2 * π * ∫ r in Icc S.ρm S.ρp, ‖S.KsecFn ℓ p r‖ ^ 2 * r
        ≤ 2 * π * ((M * Real.sqrt Q) ^ 2 * S.ρp * (S.ρp - S.ρm)) :=
          mul_le_mul_of_nonneg_left hbound hpi
      _ = 2 * π * (M ^ 2 * Q * S.ρp * (S.ρp - S.ρm)) := by
          rw [mul_pow, Real.sq_sqrt hQ0]
      _ ≤ 2 * π * (M ^ 2 * Q * S.ρp * S.ρp) := by
          gcongr
          linarith [hS.ρm_pos]
      _ = (M * S.ρp) ^ 2 * (2 * π * Q) := by ring
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (by positivity), Real.sqrt_sq (norm_nonneg _)] at this

/-- The bounded operator `k_ℓ𝒢_ℓ` on `Y^0_ℓ`. -/
theorem exists_Ksec0 (S : SectorSetting) (hS : S.Valid) (ℓ : ℤ) :
    ∃ T : Ysec 0 S.Nstar ℓ →L[ℂ] Ysec 0 S.Nstar ℓ, ∀ g : Ysec 0 S.Nstar ℓ,
      (T g).fn =ᵐ[volume] Ang.ofProfile ℓ (S.KsecFn ℓ (Polar.angularSector g.fn ℓ)) := by
  obtain ⟨C, -, hC⟩ := exists_norm_kElem0_le hS ℓ
  exact ⟨(kLin0 hS ℓ).mkContinuous C hC, fun g => kElem0_spec hS g⟩

/-! ### The transport part and `L_ℓ(G)` -/

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

theorem transSec_spec (S : SectorSetting) (hS : S.Valid) (s : ℕ) (ℓ : ℤ) (G : ℝ)
    (g : Ysec s S.Nstar ℓ) :
    (S.transSec s ℓ G g).fn =ᵐ[volume] fun x => transCoef S ℓ G ‖x‖ * g.fn x := by
  obtain ⟨C, -, h⟩ := exists_radialMul_spec s hS.ρm_pos hS.ρm_lt_ρp
  exact (h ℓ _ (memCk_of_contDiffOn_Ioi (contDiffOn_transCoef S hS ℓ G) hS.ρm_pos s)).1 g

theorem Lsec_zero_spec' (S : SectorSetting) (hS : S.Valid) (ℓ : ℤ) (G : ℝ)
    (g : Ysec 0 S.Nstar ℓ) :
    (S.Lsec 0 ℓ G g).fn =ᵐ[volume]
      Ang.ofProfile ℓ (S.LsecFn ℓ G (Polar.angularSector g.fn ℓ)) := by
  have hL : S.Lsec 0 ℓ G g = S.transSec 0 ℓ G g + S.Ksec 0 ℓ g := rfl
  have hg : g.fn =ᵐ[volume] ofProfile ℓ (Polar.angularSector g.fn ℓ) :=
    Ysec.fn_ae_eq_ofProfile hS.ρm_pos g
  filter_upwards [ysec_fn_add (S.transSec 0 ℓ G g) (S.Ksec 0 ℓ g), transSec_spec S hS 0 ℓ G g,
    Ksec_spec_of_exists S 0 ℓ (exists_Ksec0 S hS ℓ) g, hg] with x h1 h2 h3 h4
  rw [hL, h1, Pi.add_apply, h2, h3, h4]
  simp only [ofProfile, LsecFn, transCoef]
  ring

end NonUniqueEuler.SectorH
