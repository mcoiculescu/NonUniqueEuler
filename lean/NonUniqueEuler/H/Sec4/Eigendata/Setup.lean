import NonUniqueEuler.H.Sec4.Eigendata.Basic
import NonUniqueEuler.I.Sec4.HypN
import NonUniqueEuler.I.Sec4.EvansUnits
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.I.Sec4.Resolvent
import NonUniqueEuler.I.Sec4.EvansSimple
import NonUniqueEuler.I.Infra.AngularFourier.SectorL2
import NonUniqueEuler.I.Infra.AngularFourier.Symmetry
import NonUniqueEuler.I.Infra.Sobolev.Smooth

/-!
# Helpers for `def:eigendata`: the eigenvalue, `g_*`, `n_* > 0`, `φ_* ∈ X^s`

Helper of `P/Sec4/Eigendata.lean` (fully proved). Namespace `NonUniqueEuler.Eig.EigendataH`.

* `rc_sq_mul_mem`: `R_c² G ∈ [0, 1/50]` for `G ∈ [0, G₁]`;
* `LamFacts`, `lamFacts`: under (N), `λ_*(G)` is a simple zero of `E^Φ_3(·;G)` with
  `Re λ_*(G) > 211/2500` (`hypN_lamC`, `eq:evans-units`), the ring setting is valid, and `J ≠ 0`;
* `gstar_facts`: `g_*` is smooth on `(0,∞)`, vanishes off `[a, 1]`, is not zero
  (`lem:resolvent`(2));
* `nstar_pos`: `n_*(G) > 0`;
* `memXFn_const_mul_ofProfile`, `memXFn_phi`: `c g(r) e^{3iθ} ∈ X^s` for every `s`;
* `angularSector_phi`, `ellFn_phi`, `ellFn_conj_phi`: `ℓ_*(G)(φ_*) = 1`, `ℓ_*(G)(conj φ_*) = 0`.
-/

noncomputable section

open MeasureTheory Set Real Filter Topology ComplexConjugate
open scoped ENNReal ContDiff

namespace NonUniqueEuler.Eig.EigendataH

open RingData Sect Sob Ang

/-- `R_c² G ∈ [0, 1/50]` for `G ∈ [0, G₁]`. -/
theorem rc_sq_mul_mem {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) : Rc ^ 2 * G ∈ Icc (0 : ℝ) (1 / 50) := by
  have hRc : 0 < Rc ^ 2 := by unfold Rc; positivity
  refine ⟨mul_nonneg hRc.le hG.1, ?_⟩
  calc Rc ^ 2 * G ≤ Rc ^ 2 * Gbar := mul_le_mul_of_nonneg_left hG.2 hRc.le
    _ = 1 / 50 := by
      have : Rc ≠ 0 := by unfold Rc; positivity
      unfold Gbar; field_simp

/-- The facts about `λ_*(G)` used throughout (`hypN_lamC` at `R_c² G`, `eq:evans-units`,
`lem:ring-facts`, `thm:evans-simple`(2)). -/
structure LamFacts (χ : ℝ → ℝ) (G : ℝ) : Prop where
  valid : (ringPhiSetting χ).Valid
  re_gt : 211 / 2500 < (lam χ G).re
  re_pos : 0 < (lam χ G).re
  evans : (ringPhiSetting χ).evans 3 (lam χ G) G = 0
  deriv : deriv (fun w => (ringPhiSetting χ).evans 3 w G) (lam χ G) ≠ 0
  J_ne : J χ G ≠ 0

theorem lamFacts {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) : LamFacts χ G := by
  obtain ⟨h1, h2, h3, -⟩ := hypN_lamC χ hN.n1 hN.n2 (rc_sq_mul_mem hG)
  have hval := ringPhiSetting_valid hχ
  have hre : 0 < (lam χ G).re := lt_trans (by norm_num) h1
  have hE : (ringPhiSetting χ).evans 3 (lam χ G) G = 0 := by
    rw [evans_units hχ 3 (by norm_num) _ hre G]
    exact h2
  have hE' : deriv (fun w => (ringPhiSetting χ).evans 3 w G) (lam χ G) ≠ 0 := by
    rw [evans_units_deriv hχ 3 (by norm_num) _ hre G]
    exact h3
  exact ⟨hval, h1, hre, hE, hE',
    (SectorSetting.evansSimple_riesz _ hval 3 (by norm_num) _ hre G hE hE').1⟩

/-- `a > 0`, `a < 1`. -/
theorem a_pos : 0 < a := ringData_order.2.2.2.2.2.2.2.1

theorem a_lt_one : a < 1 := ringData_order.2.2.2.2.2.2.2.2

/-- `lem:resolvent`(2) for `g_*(G)`: smooth on `(0,∞)`, zero off `[a, 1]`, not zero. -/
theorem gstar_facts {χ : ℝ → ℝ} {G : ℝ} (hL : LamFacts χ G) :
    ContDiffOn ℝ ∞ (gstar χ G) (Ioi 0) ∧
      (∀ r : ℝ, 0 < r → r ∉ Icc a 1 → gstar χ G r = 0) ∧
      ∃ r : ℝ, 0 < r ∧ gstar χ G r ≠ 0 := by
  obtain ⟨h1, h2, h3, -⟩ :=
    SectorSetting.eigen_of_evans_eq_zero _ hL.valid 3 (by norm_num) _ hL.re_pos G hL.evans
  exact ⟨h1, h2, h3⟩

/-- A function continuous on `(0,∞)`, vanishing off `[a, 1]` and not identically zero has
`∫_0^∞ |g|² r dr > 0`. -/
theorem integral_sq_pos {g : ℝ → ℂ} (hc : ContinuousOn g (Ioi 0))
    (hs : ∀ r : ℝ, 0 < r → r ∉ Icc a 1 → g r = 0) {r₀ : ℝ} (hr₀ : 0 < r₀) (hne : g r₀ ≠ 0) :
    0 < ∫ r in Ioi (0 : ℝ), ‖g r‖ ^ 2 * r := by
  set F : ℝ → ℝ := fun r => ‖g r‖ ^ 2 * r with hF
  have hFc : ContinuousOn F (Ioi 0) :=
    ((continuous_norm.comp_continuousOn hc).pow 2).mul continuousOn_id
  have hsub : Icc a 1 ⊆ Ioi (0 : ℝ) := fun r hr => lt_of_lt_of_le a_pos hr.1
  have hint : IntegrableOn F (Ioi 0) := by
    refine ((hFc.mono hsub).integrableOn_Icc).of_forall_sdiff_eq_zero measurableSet_Ioi ?_
    intro r hr
    simp [hF, hs r hr.1 hr.2]
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi 0)] F := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_nonneg (sq_nonneg _) (le_of_lt hr)
  refine (setIntegral_pos_iff_support_of_nonneg_ae hnn hint).2 ?_
  have hopen : IsOpen (Ioi (0 : ℝ) ∩ F ⁻¹' {0}ᶜ) :=
    hFc.isOpen_inter_preimage isOpen_Ioi isOpen_compl_singleton
  have hpos : 0 < volume (Ioi (0 : ℝ) ∩ F ⁻¹' {0}ᶜ) := by
    refine hopen.measure_pos volume ⟨r₀, hr₀, ?_⟩
    simp only [mem_preimage, mem_compl_iff, mem_singleton_iff, hF]
    have : 0 < ‖g r₀‖ := norm_pos_iff.2 hne
    positivity
  refine lt_of_lt_of_le hpos (measure_mono ?_)
  rintro r ⟨hr1, hr2⟩
  exact ⟨hr2, hr1⟩

/-- `n_*(G) > 0` (`04_ring.tex:1308`). -/
theorem nstar_pos {χ : ℝ → ℝ} {G : ℝ} (hL : LamFacts χ G) : 0 < nstar χ G := by
  obtain ⟨hcont, hsupp, r₀, hr₀, hne⟩ := gstar_facts hL
  have hm : AEStronglyMeasurable (gstar χ G) (volume.restrict (Ioi 0)) :=
    hcont.continuousOn.aestronglyMeasurable measurableSet_Ioi
  have hl2 := (memLp_ofProfile_iff (ℓ := 3) hm).2
  have hI := integral_sq_pos hcont.continuousOn hsupp hr₀ hne
  have hsq : 0 < nstar χ G ^ 2 := by
    rw [nstar, hl2]
    exact mul_pos (by positivity) hI
  have hnn : 0 ≤ nstar χ G := by
    unfold nstar Sob.l2
    exact ENNReal.toReal_nonneg
  rcases hnn.lt_or_eq with h | h
  · exact h
  · rw [← h] at hsq
    norm_num at hsq

/-- `c g(r) e^{3iθ} ∈ X^s` for every `s`, for a profile smooth on `(0,∞)` and vanishing off
`[a, 1]`. -/
theorem memXFn_const_mul_ofProfile {g : ℝ → ℂ} (hc : ContDiffOn ℝ ∞ g (Ioi 0))
    (hs : ∀ r : ℝ, 0 < r → r ∉ Icc a 1 → g r = 0) (c : ℂ) (s : ℕ) :
    Lin.MemXFn s (fun x => c * ofProfile 3 g x) := by
  have h0 : ∀ r : ℝ, 0 < r → r < a → g r = 0 := fun r hr hra =>
    hs r hr fun hmem => not_le.2 hra hmem.1
  have h1 : ∀ r : ℝ, 1 < r → g r = 0 := fun r hr =>
    hs r (by linarith) fun hmem => not_le.2 hr hmem.2
  have hsm : ContDiff ℝ ∞ (fun x => c * ofProfile 3 g x) :=
    contDiff_const.mul (contDiff_ofProfile (by norm_num) hc a_pos h0)
  have hcs : HasCompactSupport (fun x => c * ofProfile 3 g x) :=
    (hasCompactSupport_ofProfile (ℓ := 3) h1).mul_left
  refine ⟨(memH_of_contDiff_hasCompactSupport hsm hcs s).1, ?_, ?_⟩
  · refine Eventually.of_forall fun x hx => ?_
    show c * ofProfile 3 g x = 0
    rw [RingData.mem_annN, not_and_or, not_le, not_le] at hx
    rcases hx with hx | hx
    · by_cases hx0 : x = 0
      · subst hx0
        simp [ofProfile, angPhase, zero_zpow (3 : ℤ) (by norm_num)]
      · rw [ofProfile, h0 ‖x‖ (norm_pos_iff.2 hx0) (by linarith [a_pos]), zero_mul, mul_zero]
    · rw [ofProfile, h1 ‖x‖ (by linarith), zero_mul, mul_zero]
  · refine Eventually.of_forall fun x => ?_
    simp only
    rw [ofProfile_three_rot]

/-- `φ_*(G) ∈ X^s` for every `s`. -/
theorem memXFn_phi {χ : ℝ → ℝ} {G : ℝ} (hL : LamFacts χ G) (s : ℕ) :
    Lin.MemXFn s (phi χ G) := by
  obtain ⟨hcont, hsupp, -⟩ := gstar_facts hL
  exact memXFn_const_mul_ofProfile hcont hsupp _ s

/-- The angular sector of `c f`. -/
theorem angularSector_const_mul (c : ℂ) (f : ℂ → ℂ) (ℓ : ℤ) (r : ℝ) :
    Polar.angularSector (fun x => c * f x) ℓ r = c * Polar.angularSector f ℓ r := by
  unfold Polar.angularSector
  have : ∀ θ : ℝ, c * f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
      Complex.exp (-((ℓ : ℂ) * θ * Complex.I)) =
      c * (f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
        Complex.exp (-((ℓ : ℂ) * θ * Complex.I))) := fun θ => by ring
  simp_rw [this, intervalIntegral.integral_const_mul]
  ring

/-- The angular sectors of `φ_*(G)`: `n_*⁻¹ g_*` in sector `3`, `0` elsewhere. -/
theorem angularSector_phi (χ : ℝ → ℝ) (G : ℝ) (m : ℤ) {r : ℝ} (hr : 0 < r) :
    Polar.angularSector (phi χ G) m r =
      if m = 3 then ((nstar χ G : ℝ) : ℂ)⁻¹ * gstar χ G r else 0 := by
  have h := angularSector_const_mul ((nstar χ G : ℝ) : ℂ)⁻¹ (ofProfile 3 (gstar χ G)) m r
  have h2 : (fun x => ((nstar χ G : ℝ) : ℂ)⁻¹ * ofProfile 3 (gstar χ G) x) = phi χ G := rfl
  rw [h2] at h
  rw [h, angularSector_ofProfile 3 m _ hr]
  split_ifs <;> simp

/-- `ℓ_*(G)(f) = n_* ℓ_*(h)` when the sector-`3` profile of `f` is `h` on `(0,∞)`. -/
theorem ellFn_eq_of_angularSector (χ : ℝ → ℝ) (G : ℝ) {f : ℂ → ℂ} {h : ℝ → ℂ}
    (hf : ∀ r : ℝ, 0 < r → Polar.angularSector f 3 r = h r) :
    ellFn χ G f = ((nstar χ G : ℝ) : ℂ) * (ringPhiSetting χ).ellStar 3 (lam χ G) G h := by
  unfold ellFn SectorSetting.ellStar
  congr 2
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  rw [hf r hr]

/-- `ℓ_*(c h) = c ℓ_*(h)`. -/
theorem ellStar_const_mul (S : SectorSetting) (ℓ : ℕ) (z : ℂ) (G : ℝ) (c : ℂ) (h : ℝ → ℂ) :
    S.ellStar ℓ z G (fun r => c * h r) = c * S.ellStar ℓ z G h := by
  unfold SectorSetting.ellStar
  have : ∀ r : ℝ, c * h r * S.psi ℓ z G (Real.log r) * S.Mres ℓ z G r * (r : ℂ) =
      c * (h r * S.psi ℓ z G (Real.log r) * S.Mres ℓ z G r * (r : ℂ)) := fun r => by ring
  simp_rw [this, integral_const_mul]
  ring

/-- `ℓ_*(G)(φ_*(G)) = 1` (`04_ring.tex:1315`). -/
theorem ellFn_phi {χ : ℝ → ℝ} {G : ℝ} (hL : LamFacts χ G) : ellFn χ G (phi χ G) = 1 := by
  have hn : ((nstar χ G : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (nstar_pos hL).ne'
  rw [ellFn_eq_of_angularSector χ G (h := fun r => ((nstar χ G : ℝ) : ℂ)⁻¹ * gstar χ G r)
    (fun r hr => by rw [angularSector_phi χ G 3 hr]; simp),
    ellStar_const_mul]
  have h1 : (ringPhiSetting χ).ellStar 3 (lam χ G) G (gstar χ G) = 1 :=
    SectorSetting.ellStar_gStar _ 3 _ G hL.J_ne
  rw [h1, mul_one, mul_inv_cancel₀ hn]

/-- `ℓ_*(G)(conj φ_*(G)) = 0` (`04_ring.tex:1316`). -/
theorem ellFn_conj_phi (χ : ℝ → ℝ) (G : ℝ) :
    ellFn χ G (fun x => conj (phi χ G x)) = 0 := by
  rw [ellFn_eq_of_angularSector χ G (h := fun _ => 0) (fun r hr => ?_)]
  · unfold SectorSetting.ellStar
    simp
  · have h := angularSector_conj (phi χ G) (-3) r
    rw [neg_neg] at h
    rw [h, angularSector_phi χ G (-3) hr]
    simp

end NonUniqueEuler.Eig.EigendataH
