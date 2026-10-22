import NonUniqueEuler.H.Sec4.PropU.LamCont
import NonUniqueEuler.H.Sec4.PropU.Cont
import NonUniqueEuler.I.Sec4.PropU.GstarDeriv
import NonUniqueEuler.I.Sec4.Resolvent
import NonUniqueEuler.I.Infra.AngularFourier.SectorL2
import NonUniqueEuler.I.Infra.AngularFourier.NormHCont
import NonUniqueEuler.I.Infra.Sobolev.Norm

/-!
# Helpers for `P/Sec4/PropU`: the eigendata as continuous functions of `G` (`prop:U`(b))

With `λ_*` continuous on `[0, G₁]` (`lam_continuousOn`):
* `gstar_iteratedDeriv_continuousOn`: `(G, r) ↦ ∂_r^j g_*(G)(r)` is continuous on
  `[0,G₁] × (0,∞)` (`I/Sec4/PropU/GstarDeriv.lean`);
* `nstar_continuousOn`: `n_*(G) = (2π ∫_a^1 |g_*|² r dr)^{1/2}` (`memLp_ofProfile_iff`);
* `J_continuousOn`: `J(G) = ∫_a^1 g_* ψ_*(log r) M_* r dr`;
* `normEll_continuousOn`: `‖ℓ_*(G)‖ = ‖ellRep‖_{L²}` (`ell_representer`), an explicit radial
  integral over `[a/2, 2]`;
* `normH_phi_continuousOn`: `‖φ_*(G)‖_{H^k} = n_*⁻¹ ‖g_* e^{3iθ}‖_{H^k}`
  (`I/Infra/AngularFourier/NormHCont.lean`).
-/

noncomputable section

open MeasureTheory Set Real ComplexConjugate Filter Topology
open scoped ContDiff

namespace NonUniqueEuler

namespace Eig

namespace PropUH

open RingData SectorSetting.PropUH

variable {χ : ℝ → ℝ}

theorem a_pos_lt_one : 0 < a ∧ a < 1 := by
  obtain ⟨-, -, -, -, -, -, -, h0, h1⟩ := ringData_order
  exact ⟨h0, h1⟩

theorem Icc_a_one_subset : Icc a 1 ⊆ Ioi (0 : ℝ) := fun _ hr => lt_of_lt_of_le a_pos_lt_one.1 hr.1

theorem Icc_a_two_subset : Icc (a / 2) 2 ⊆ Ioi (0 : ℝ) :=
  fun _ hr => lt_of_lt_of_le (by linarith [a_pos_lt_one.1]) hr.1

/-- At `G ∈ [0,G₁]`, `g_*(G)` is smooth on `(0,∞)` and vanishes off `[a,1]`
(`lem:resolvent`(2)). -/
theorem gstar_facts (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) {G : ℝ}
    (hG : G ∈ Icc (0 : ℝ) Gbar) :
    ContDiffOn ℝ ∞ (gstar χ G) (Ioi 0) ∧ (∀ r : ℝ, 0 < r → r ∉ Icc a 1 → gstar χ G r = 0) := by
  obtain ⟨-, hz, hE, -, -, -⟩ := eig_facts hχ hN hG
  have h := SectorSetting.eigen_of_evans_eq_zero _ (ringPhiSetting_valid hχ) 3 (by norm_num) _
    hz G hE
  exact ⟨h.1, h.2.1⟩

/-- `J(G) ≠ 0` (`thm:evans-simple`(1)). -/
theorem J_ne_zero (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) {G : ℝ}
    (hG : G ∈ Icc (0 : ℝ) Gbar) : J χ G ≠ 0 := by
  obtain ⟨-, hz, hE, -, hE', -⟩ := eig_facts hχ hN hG
  exact (SectorSetting.evansSimple_riesz _ (ringPhiSetting_valid hχ) 3 (by norm_num) _ hz G hE
    hE').1

theorem nstar_pos (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) {G : ℝ}
    (hG : G ∈ Icc (0 : ℝ) Gbar) : 0 < nstar χ G :=
  (eigendata_phi χ hχ hN hG).1

theorem gstar_iteratedDeriv_continuousOn (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    (j : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv j (gstar χ p.1) p.2) (Icc 0 Gbar ×ˢ Ioi 0) :=
  continuousOn_comp_path
    (SectorSetting.gStar_iteratedDeriv_continuousOn _ (ringPhiSetting_valid hχ) 3 (by norm_num) j)
    (lam_continuousOn hχ hN) (fun _ hG => (eig_facts hχ hN hG).2.1) subset_rfl

theorem gstar_continuousOn (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) :
    ContinuousOn (fun p : ℝ × ℝ => gstar χ p.1 p.2) (Icc 0 Gbar ×ˢ Ioi 0) := by
  simpa using gstar_iteratedDeriv_continuousOn hχ hN 0

theorem psiLog_path_continuousOn (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) :
    ContinuousOn (fun p : ℝ × ℝ => (ringPhiSetting χ).psi 3 (lam χ p.1) p.1 (Real.log p.2))
      (Icc 0 Gbar ×ˢ Ioi 0) :=
  continuousOn_comp_path (psiLog_continuousOn _ (ringPhiSetting_valid hχ) 3)
    (lam_continuousOn hχ hN) (fun _ hG => (eig_facts hχ hN hG).2.1) subset_rfl

theorem Mres_path_continuousOn (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) :
    ContinuousOn (fun p : ℝ × ℝ => (ringPhiSetting χ).Mres ((3 : ℕ) : ℤ) (lam χ p.1) p.1 p.2)
      (Icc 0 Gbar ×ˢ Ioi 0) :=
  continuousOn_comp_path (Mres_continuousOn _ (ringPhiSetting_valid hχ) ((3 : ℕ) : ℤ))
    (lam_continuousOn hχ hN) (fun _ hG => (eig_facts hχ hN hG).2.1) subset_rfl

/-! ### `n_*` -/

theorem nstar_eq (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) {G : ℝ}
    (hG : G ∈ Icc (0 : ℝ) Gbar) :
    nstar χ G = Real.sqrt (2 * π * ∫ r in a..1, ‖gstar χ G r‖ ^ 2 * r) := by
  obtain ⟨hsm, hsupp⟩ := gstar_facts hχ hN hG
  have hm : AEStronglyMeasurable (gstar χ G) (volume.restrict (Ioi 0)) :=
    hsm.continuousOn.aestronglyMeasurable measurableSet_Ioi
  have h2 := (Ang.memLp_ofProfile_iff (ℓ := 3) hm).2
  have hint : ∫ r in Ioi (0 : ℝ), ‖gstar χ G r‖ ^ 2 * r = ∫ r in a..1, ‖gstar χ G r‖ ^ 2 * r :=
    setIntegral_Ioi_eq_intervalIntegral a_pos_lt_one.1 a_pos_lt_one.2.le fun r hr hr' => by
      simp [hsupp r hr hr']
  have hnn : 0 ≤ Sob.l2 (Ang.ofProfile 3 (gstar χ G)) := ENNReal.toReal_nonneg
  rw [← hint, ← h2, Real.sqrt_sq hnn]
  rfl

theorem nstar_continuousOn (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) :
    ContinuousOn (nstar χ) (Icc 0 Gbar) := by
  have hF : ContinuousOn (fun p : ℝ × ℝ => ‖gstar χ p.1 p.2‖ ^ 2 * p.2) (Icc 0 Gbar ×ˢ Icc a 1) :=
    (((gstar_continuousOn hχ hN).mono (prod_mono subset_rfl Icc_a_one_subset)).norm.pow 2).mul
      continuousOn_snd
  have hI := continuousOn_intervalIntegral_rect (F := fun G r => ‖gstar χ G r‖ ^ 2 * r)
    Gbar_nonneg a_pos_lt_one.2.le hF
  have h := Real.continuous_sqrt.comp_continuousOn ((continuousOn_const (c := 2 * π)).mul hI)
  exact h.congr fun G hG => nstar_eq hχ hN hG

/-! ### `J` -/

theorem J_eq (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) {G : ℝ}
    (hG : G ∈ Icc (0 : ℝ) Gbar) :
    J χ G = ∫ r in a..1, gstar χ G r * (ringPhiSetting χ).psi 3 (lam χ G) G (Real.log r) *
      (ringPhiSetting χ).Mres ((3 : ℕ) : ℤ) (lam χ G) G r * (r : ℂ) := by
  obtain ⟨-, hsupp⟩ := gstar_facts hχ hN hG
  exact setIntegral_Ioi_eq_intervalIntegral a_pos_lt_one.1 a_pos_lt_one.2.le fun r hr hr' => by
    have h0 : (ringPhiSetting χ).gStar 3 (lam χ G) G r = 0 := hsupp r hr hr'
    rw [h0, zero_mul, zero_mul, zero_mul]

theorem J_continuousOn (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) :
    ContinuousOn (J χ) (Icc 0 Gbar) := by
  have hsub := prod_mono (subset_refl (Icc (0 : ℝ) Gbar)) Icc_a_one_subset
  have hF : ContinuousOn (fun p : ℝ × ℝ => gstar χ p.1 p.2 *
      (ringPhiSetting χ).psi 3 (lam χ p.1) p.1 (Real.log p.2) *
      (ringPhiSetting χ).Mres ((3 : ℕ) : ℤ) (lam χ p.1) p.1 p.2 * (p.2 : ℂ))
      (Icc 0 Gbar ×ˢ Icc a 1) :=
    ((((gstar_continuousOn hχ hN).mono hsub).mul ((psiLog_path_continuousOn hχ hN).mono hsub)).mul
      ((Mres_path_continuousOn hχ hN).mono hsub)).mul
      (Complex.continuous_ofReal.comp_continuousOn continuousOn_snd)
  have hI := continuousOn_intervalIntegral_rect (F := fun G r => gstar χ G r *
      (ringPhiSetting χ).psi 3 (lam χ G) G (Real.log r) *
      (ringPhiSetting χ).Mres ((3 : ℕ) : ℤ) (lam χ G) G r * (r : ℂ))
    Gbar_nonneg a_pos_lt_one.2.le hF
  exact hI.congr fun G hG => J_eq hχ hN hG

/-! ### `‖ℓ_*(G)‖` -/

/-- The constant `n_*/(2π conj J)` of the representer. -/
def cRep (χ : ℝ → ℝ) (G : ℝ) : ℂ := ((nstar χ G : ℝ) : ℂ) / (2 * π * conj (J χ G))

theorem ellRep_eq (χ : ℝ → ℝ) (G : ℝ) :
    ellRep χ G = Ang.ofProfile 3 ((Icc (a / 2) 2).indicator fun r =>
      cRep χ G * (ringPhiSetting χ).adjEig 3 (lam χ G) G r) := by
  classical
  funext x
  simp only [ellRep, Ang.ofProfile, Set.indicator_apply, cRep]
  by_cases hx : x ∈ annN
  · have hx' : ‖x‖ ∈ Icc (a / 2) 2 := hx
    rw [ite_eq_left hx, ite_eq_left hx']
    ring
  · have hx' : ‖x‖ ∉ Icc (a / 2) 2 := hx
    rw [ite_eq_right hx, ite_eq_right hx', zero_mul]

theorem adjEig_path_continuousOn (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) :
    ContinuousOn (fun p : ℝ × ℝ => (ringPhiSetting χ).adjEig 3 (lam χ p.1) p.1 p.2)
      (Icc 0 Gbar ×ˢ Ioi 0) :=
  Complex.continuous_conj.comp_continuousOn
    ((psiLog_path_continuousOn hχ hN).mul (Mres_path_continuousOn hχ hN))

theorem normEll_eq (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) {G : ℝ}
    (hG : G ∈ Icc (0 : ℝ) Gbar) :
    ‖ell χ 0 G‖ = Real.sqrt (2 * π * ∫ r in (a / 2)..2,
      ‖cRep χ G‖ ^ 2 * (‖(ringPhiSetting χ).adjEig 3 (lam χ G) G r‖ ^ 2 * r)) := by
  rw [(ell_representer χ hχ hN hG).2.2, ellRep_eq]
  set h : ℝ → ℂ := (Icc (a / 2) 2).indicator fun r =>
    cRep χ G * (ringPhiSetting χ).adjEig 3 (lam χ G) G r with hhdef
  have hpath : ContinuousOn (fun r : ℝ => ((G, r) : ℝ × ℝ)) (Ioi 0) :=
    continuousOn_const.prodMk continuousOn_id
  have hadj0 := (adjEig_path_continuousOn hχ hN).comp hpath fun r hr => ⟨hG, hr⟩
  have hadj : ContinuousOn (fun r => (ringPhiSetting χ).adjEig 3 (lam χ G) G r) (Ioi 0) :=
    hadj0.congr fun r _ => rfl
  have hm : AEStronglyMeasurable h (volume.restrict (Ioi 0)) :=
    ((continuousOn_const.mul hadj).aestronglyMeasurable measurableSet_Ioi).indicator
      measurableSet_Icc
  have h2 := (Ang.memLp_ofProfile_iff (ℓ := 3) hm).2
  have hint : ∫ r in Ioi (0 : ℝ), ‖h r‖ ^ 2 * r =
      ∫ r in (a / 2)..2, ‖cRep χ G‖ ^ 2 * (‖(ringPhiSetting χ).adjEig 3 (lam χ G) G r‖ ^ 2 * r) := by
    have ha2 : a / 2 ≤ 2 := by linarith [a_pos_lt_one.2]
    rw [setIntegral_Ioi_eq_intervalIntegral (by linarith [a_pos_lt_one.1]) ha2
      fun r _ hr' => by simp [hhdef, Set.indicator_of_notMem hr']]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le ha2] at hr
    simp only [hhdef, Set.indicator_of_mem hr, norm_mul]
    ring
  have hnn : 0 ≤ Sob.l2 (Ang.ofProfile 3 h) := ENNReal.toReal_nonneg
  rw [← hint, ← h2, Real.sqrt_sq hnn]

theorem cRep_continuousOn (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) :
    ContinuousOn (cRep χ) (Icc 0 Gbar) := by
  refine (Complex.continuous_ofReal.comp_continuousOn (nstar_continuousOn hχ hN)).div
    (continuousOn_const.mul (Complex.continuous_conj.comp_continuousOn (J_continuousOn hχ hN)))
    fun G hG => ?_
  refine mul_ne_zero (by simp [Real.pi_ne_zero]) ?_
  simpa using J_ne_zero hχ hN hG

theorem normEll_continuousOn (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) :
    ContinuousOn (fun G => ‖ell χ 0 G‖) (Icc 0 Gbar) := by
  have hsub := prod_mono (subset_refl (Icc (0 : ℝ) Gbar)) Icc_a_two_subset
  have hF : ContinuousOn (fun p : ℝ × ℝ => ‖cRep χ p.1‖ ^ 2 *
      (‖(ringPhiSetting χ).adjEig 3 (lam χ p.1) p.1 p.2‖ ^ 2 * p.2)) (Icc 0 Gbar ×ˢ Icc (a / 2) 2) :=
    (((cRep_continuousOn hχ hN).comp continuousOn_fst fun p hp => hp.1).norm.pow 2).mul
      ((((adjEig_path_continuousOn hχ hN).mono hsub).norm.pow 2).mul continuousOn_snd)
  have hI := continuousOn_intervalIntegral_rect (F := fun G r => ‖cRep χ G‖ ^ 2 *
      (‖(ringPhiSetting χ).adjEig 3 (lam χ G) G r‖ ^ 2 * r)) (c := a / 2) (d := 2)
    Gbar_nonneg (by linarith [a_pos_lt_one.2]) hF
  have h := Real.continuous_sqrt.comp_continuousOn ((continuousOn_const (c := 2 * π)).mul hI)
  exact h.congr fun G hG => normEll_eq hχ hN hG

/-! ### `‖φ_*(G)‖_{H^k}` -/

theorem normH_phi_eq (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) {G : ℝ}
    (hG : G ∈ Icc (0 : ℝ) Gbar) (k : ℕ) :
    Sob.normH k (phi χ G) = (nstar χ G)⁻¹ * Sob.normH k (Ang.ofProfile 3 (gstar χ G)) := by
  have hn := nstar_pos hχ hN hG
  have hX := (eigendata_phi χ hχ hN hG).2.1 k
  have hn' : ((nstar χ G : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hn.ne'
  have hphi : phi χ G = ((nstar χ G : ℝ) : ℂ)⁻¹ • Ang.ofProfile 3 (gstar χ G) := by
    funext x; simp [phi]
  have hof : Ang.ofProfile 3 (gstar χ G) = ((nstar χ G : ℝ) : ℂ) • phi χ G := by
    rw [hphi, smul_smul, mul_inv_cancel₀ hn', one_smul]
  have hmem : Sob.MemH k (Ang.ofProfile 3 (gstar χ G)) := by
    rw [hof]; exact (hX.1.const_smul _).1
  rw [hphi, (hmem.const_smul _).2, norm_inv, Complex.norm_real, Real.norm_of_nonneg hn.le]

theorem normH_phi_continuousOn (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    (k : ℕ) : ContinuousOn (fun G => Sob.normH k (phi χ G)) (Icc 0 Gbar) := by
  have h1 := Ang.continuousOn_normH_ofProfile k a_pos_lt_one.1 a_pos_lt_one.2 3
    (T := Icc 0 Gbar) (h := gstar χ)
    (fun G hG => (gstar_facts hχ hN hG).1) (fun G hG => (gstar_facts hχ hN hG).2)
    (fun j _ => (gstar_iteratedDeriv_continuousOn hχ hN j).mono
      (prod_mono subset_rfl Icc_a_one_subset))
  refine (((nstar_continuousOn hχ hN).inv₀ fun G hG => (nstar_pos hχ hN hG).ne').mul h1).congr
    fun G hG => normH_phi_eq hχ hN hG k

end PropUH

end Eig

end NonUniqueEuler
