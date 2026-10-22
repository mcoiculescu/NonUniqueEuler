import NonUniqueEuler.Defs.Sec4.Extra2Eigendata
import NonUniqueEuler.I.Sec4.SectorSetting
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.I.Sec4.PropU
import NonUniqueEuler.I.Infra.ODE.Param
import NonUniqueEuler.I.Infra.AngularFourier.SectorL2
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Helpers for `P/Sec4/Uniform/EllRepCont`: joint continuity of the eigendata in `(G, r)`

Manuscript `04_ring.tex:1540-1543` (proof of `lem:uniform`): "`ψ_*`, `M_*`, `n_*` and `J ≠ 0`
are continuous". Several lemmas are adapted from `H/Sec4/PropU/Cont.lean` and
`H/Sec4/PropU/Quant.lean` (from the proof of `Sec4/PropU`); they are restated here in
the private namespace `Eig.EllRepContH` (helper files of another proof may not be imported, and a
shared name would clash in the full library). Differences: `λ_*` continuity and `Re λ_* > 0` come
from `propU_a` (`I/Sec4/PropU.lean`); continuity and support of `g_* = M_* k_3 ψ_*(log r)` are
proved directly from the factors (no `C^k` regularity is needed); `J ≠ 0` comes from `propU_b`.

* `psi_continuousOn_param`, `psiLog_continuousOn`, `Mres_continuousOn`, `kcoef_continuousOn`,
  `gStar_continuousOn`: joint continuity on `(0,∞) × {Re λ > 0} × ℝ` in a valid sector setting;
* `continuousOn_comp_path`: composition with `G ↦ (λ_*(G), G)`;
* `continuousOn_intervalIntegral_rect`, `setIntegral_Ioi_eq_intervalIntegral`: parametric
  integrals over a compact interval;
* `nstar_continuousOn`, `J_continuousOn`, `J_ne_zero`, `cRep_continuousOn`: the constant
  `n_*/(2π conj J)` of the representer is continuous on `[0,G₁]`;
* `ellRep_eq`: `ellRep(G) = ofProfile 3 (1_{[a/2,2]} · cRep(G) · adjEig(G))`;
* `adjEig_path_continuousOn`: `(G, r) ↦ conj(ψ_*(log r) M_*(r))` is continuous on
  `[0,G₁] × (0,∞)`.
-/

noncomputable section

open MeasureTheory Set Real Filter Topology ComplexConjugate
open scoped ContDiff

namespace NonUniqueEuler

namespace Eig

namespace EllRepContH

open RingData

/-! ### A valid sector setting -/

/-- `r ↦ ω̄'(r)` is continuous. -/
theorem continuous_dom (S : SectorSetting) (hS : S.Valid) : Continuous S.dom := by
  have hom : ContDiff ℝ ∞ S.omR := hS.contDiff.comp Complex.ofRealCLM.contDiff
  exact hom.continuous_deriv (by simp)

/-- `Ω(r;G)` is jointly continuous on `(0,∞) × ℝ` (`Omega_eq_add`, `contDiffOn_Omega`). -/
theorem Omega_continuousOn₂ (S : SectorSetting) (hS : S.Valid) :
    ContinuousOn (fun p : ℝ × ℝ => S.Omega p.2 p.1) (Ioi 0 ×ˢ univ) := by
  have h0 := (SectorSetting.contDiffOn_Omega S hS 0).continuousOn
  have h1 : ContinuousOn (fun p : ℝ × ℝ => S.Omega 0 p.1) (Ioi 0 ×ˢ univ) :=
    h0.comp continuousOn_fst fun p hp => hp.1
  have h2 : ContinuousOn (fun p : ℝ × ℝ => p.2 * (p.1 ^ 2)⁻¹) (Ioi 0 ×ˢ univ) :=
    continuousOn_snd.mul ((continuousOn_fst.pow 2).inv₀ fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))
  refine (h1.add h2).congr fun p _ => ?_
  exact SectorSetting.Omega_eq_add S p.2 p.1

/-- `Ω(r;G)` as a function of `(r, λ, G)`. -/
theorem Omega_continuousOn (S : SectorSetting) (hS : S.Valid) :
    ContinuousOn (fun q : ℝ × ℂ × ℝ => S.Omega q.2.2 q.1)
      (Ioi 0 ×ˢ ({z : ℂ | 0 < z.re} ×ˢ univ)) :=
  (Omega_continuousOn₂ S hS).comp
    (continuous_fst.prodMk (continuous_snd.comp continuous_snd)).continuousOn
    fun _ hq => ⟨hq.1, mem_univ _⟩

theorem re_add_I_mul_ofReal (z : ℂ) (c : ℂ) (hc : c.im = 0) (x : ℝ) :
    (z + Complex.I * c * (x : ℂ)).re = z.re := by
  simp [Complex.add_re, Complex.mul_re, hc]

/-- `M_λ(r;G) = (λ + iℓΩ(r;G))⁻¹` is jointly continuous on `(0,∞) × {Re λ > 0} × ℝ`. -/
theorem Mres_continuousOn (S : SectorSetting) (hS : S.Valid) (ℓ : ℤ) :
    ContinuousOn (fun q : ℝ × ℂ × ℝ => S.Mres ℓ q.2.1 q.2.2 q.1)
      (Ioi 0 ×ˢ ({z : ℂ | 0 < z.re} ×ˢ univ)) := by
  have hΩ := (Complex.continuous_ofReal.comp_continuousOn (Omega_continuousOn S hS))
  have hden : ContinuousOn (fun q : ℝ × ℂ × ℝ =>
      q.2.1 + Complex.I * (ℓ : ℂ) * ((S.Omega q.2.2 q.1 : ℝ) : ℂ))
      (Ioi 0 ×ˢ ({z : ℂ | 0 < z.re} ×ˢ univ)) :=
    (continuous_fst.comp continuous_snd).continuousOn.add (continuousOn_const.mul hΩ)
  refine hden.inv₀ fun q hq => ?_
  intro h0
  have hre := congrArg Complex.re h0
  rw [re_add_I_mul_ofReal _ _ (by simp)] at hre
  simp only [Complex.zero_re] at hre
  exact (ne_of_gt hq.2.1) hre

/-- `ψ_ℓ(ξ;λ,G)` is jointly continuous in `(ξ, λ, G)` on `ℝ × {Re λ > 0} × ℝ`
(`04_ring.tex:1403-1404`; `LinODE.continuousOn_sol`). -/
theorem psi_continuousOn_param (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) :
    ContinuousOn (fun q : ℝ × ℂ × ℝ => S.psi ℓ q.2.1 q.2.2 q.1)
      (univ ×ˢ ({z : ℂ | 0 < z.re} ×ˢ univ)) := by
  have hdom := continuous_dom S hS
  have hfxi : Continuous S.fxi := Real.continuous_exp.mul (hdom.comp Real.continuous_exp)
  have hΩ : Continuous (fun p : ℝ × ℝ => S.Omega p.2 (Real.exp p.1)) :=
    continuousOn_univ.1 <| (Omega_continuousOn₂ S hS).comp
      ((Real.continuous_exp.comp continuous_fst).prodMk continuous_snd).continuousOn
      fun p _ => ⟨Real.exp_pos _, mem_univ _⟩
  set V : ℝ → ℂ × ℝ → ℂ := fun ξ p => S.Vric ℓ p.1 p.2 ξ with hVdef
  have hV : ContinuousOn (Function.uncurry V) (univ ×ˢ ({z : ℂ | 0 < z.re} ×ˢ univ)) := by
    have hnum : Continuous (fun q : ℝ × ℂ × ℝ => Complex.I * (ℓ : ℂ) * ((S.fxi q.1 : ℝ) : ℂ)) :=
      continuous_const.mul (Complex.continuous_ofReal.comp (hfxi.comp continuous_fst))
    have hden : Continuous (fun q : ℝ × ℂ × ℝ =>
        q.2.1 + Complex.I * (ℓ : ℂ) * ((S.Omega q.2.2 (Real.exp q.1) : ℝ) : ℂ)) :=
      (continuous_fst.comp continuous_snd).add (continuous_const.mul
        (Complex.continuous_ofReal.comp
          (hΩ.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))))
    have h := (continuous_const.continuousOn (s := univ ×ˢ ({z : ℂ | 0 < z.re} ×ˢ univ))
      (f := fun _ : ℝ × ℂ × ℝ => (ℓ : ℂ) ^ 2)).add
      (hnum.continuousOn.div hden.continuousOn fun q hq => by
        intro h0
        have hre := congrArg Complex.re h0
        rw [re_add_I_mul_ofReal _ _ (by simp)] at hre
        simp only [Complex.zero_re] at hre
        exact (ne_of_gt hq.2.1) hre)
    refine h.congr fun q _ => ?_
    simp only [hVdef, Function.uncurry, SectorSetting.Vric, Pi.add_apply, Pi.div_apply]
  have hsol := LinODE.continuousOn_sol hV S.ξ₁ (y₀ := fun _ => ((1 : ℂ), (ℓ : ℂ)))
    continuousOn_const
  exact (continuous_fst.comp_continuousOn hsol).congr fun q _ => rfl

/-- `ψ_ℓ(log r;λ,G)` is jointly continuous on `(0,∞) × {Re λ > 0} × ℝ`. -/
theorem psiLog_continuousOn (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) :
    ContinuousOn (fun q : ℝ × ℂ × ℝ => S.psi ℓ q.2.1 q.2.2 (Real.log q.1))
      (Ioi 0 ×ˢ ({z : ℂ | 0 < z.re} ×ˢ univ)) := by
  have hlog : ContinuousOn (fun q : ℝ × ℂ × ℝ => (Real.log q.1, q.2))
      (Ioi 0 ×ˢ ({z : ℂ | 0 < z.re} ×ˢ univ)) :=
    (Real.continuousOn_log.comp continuousOn_fst fun q hq => ne_of_gt hq.1).prodMk
      continuous_snd.continuousOn
  exact (psi_continuousOn_param S hS ℓ).comp hlog fun q hq => ⟨mem_univ _, hq.2⟩

/-- `k_ℓ(r) = iℓω̄'(r)/r` is continuous on `(0,∞)`. -/
theorem kcoef_continuousOn (S : SectorSetting) (hS : S.Valid) (ℓ : ℤ) :
    ContinuousOn (S.kcoef ℓ) (Ioi 0) := by
  have hnum : Continuous fun r : ℝ => Complex.I * (ℓ : ℂ) * ((S.dom r : ℝ) : ℂ) :=
    continuous_const.mul (Complex.continuous_ofReal.comp (continuous_dom S hS))
  refine (hnum.continuousOn.div Complex.continuous_ofReal.continuousOn fun r hr => ?_).congr
    fun r _ => rfl
  exact Complex.ofReal_ne_zero.2 (ne_of_gt hr)

/-- `g_λ(r;G) = M_λ k_ℓ ψ_ℓ(log r)` is jointly continuous on `(0,∞) × {Re λ > 0} × ℝ`. -/
theorem gStar_continuousOn (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) :
    ContinuousOn (fun q : ℝ × ℂ × ℝ => S.gStar ℓ q.2.1 q.2.2 q.1)
      (Ioi 0 ×ˢ ({z : ℂ | 0 < z.re} ×ˢ univ)) := by
  have hk : ContinuousOn (fun q : ℝ × ℂ × ℝ => S.kcoef (ℓ : ℤ) q.1)
      (Ioi 0 ×ˢ ({z : ℂ | 0 < z.re} ×ˢ univ)) :=
    (kcoef_continuousOn S hS ℓ).comp continuousOn_fst fun q hq => hq.1
  have h := ((Mres_continuousOn S hS (ℓ : ℤ)).mul hk).mul (psiLog_continuousOn S hS ℓ)
  exact h.congr fun q _ => rfl

/-- `g_λ` vanishes for `r > 0` off `[r₁, r₂]` (`ω̄' = 0` there). -/
theorem gStar_eq_zero (S : SectorSetting) (hS : S.Valid) (ℓ : ℕ) (z : ℂ) (G : ℝ) {r : ℝ}
    (hr : 0 < r) (hr' : r ∉ Icc S.r₁ S.r₂) : S.gStar ℓ z G r = 0 := by
  simp [SectorSetting.gStar, SectorSetting.kcoef, hS.dom_eq_zero r hr hr']

/-! ### Generic continuity tools -/

/-- Composition of a function continuous on `(0,∞) × {Re λ > 0} × ℝ` with a path
`G ↦ (Z(G), G)`. -/
theorem continuousOn_comp_path {E : Type*} [TopologicalSpace E] {f : ℝ × ℂ × ℝ → E}
    (hf : ContinuousOn f (Ioi 0 ×ˢ ({z : ℂ | 0 < z.re} ×ˢ univ))) {Z : ℝ → ℂ} {T : Set ℝ}
    (hZ : ContinuousOn Z T) (hZre : ∀ G ∈ T, 0 < (Z G).re) {U : Set ℝ} (hU : U ⊆ Ioi 0) :
    ContinuousOn (fun p : ℝ × ℝ => f (p.2, Z p.1, p.1)) (T ×ˢ U) := by
  have hg : ContinuousOn (fun p : ℝ × ℝ => (p.2, Z p.1, p.1)) (T ×ˢ U) :=
    continuousOn_snd.prodMk ((hZ.comp continuousOn_fst fun p hp => hp.1).prodMk continuousOn_fst)
  exact hf.comp hg fun p hp => ⟨hU hp.2, hZre p.1 hp.1, mem_univ _⟩

/-- `G ↦ ∫_c^d F(G,r) dr` is continuous on `[g₀, g₁]` when `F` is jointly continuous on
`[g₀,g₁] × [c,d]` (clamp both variables with `projIcc`). -/
theorem continuousOn_intervalIntegral_rect {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → ℝ → E} {g₀ g₁ c d : ℝ} (hg : g₀ ≤ g₁) (hcd : c ≤ d)
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Icc g₀ g₁ ×ˢ Icc c d)) :
    ContinuousOn (fun G => ∫ r in c..d, F G r) (Icc g₀ g₁) := by
  set F' : ℝ → ℝ → E := fun G r => F (projIcc g₀ g₁ hg G) (projIcc c d hcd r) with hF'
  have hc : Continuous (Function.uncurry F') := by
    have hmap : Continuous (fun p : ℝ × ℝ =>
        (((projIcc g₀ g₁ hg p.1 : Icc g₀ g₁) : ℝ), ((projIcc c d hcd p.2 : Icc c d) : ℝ))) :=
      ((continuous_subtype_val.comp continuous_projIcc).comp continuous_fst).prodMk
        ((continuous_subtype_val.comp continuous_projIcc).comp continuous_snd)
    exact hF.comp_continuous hmap fun p => ⟨Subtype.mem _, Subtype.mem _⟩
  have hcont := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) hc c d
  refine hcont.continuousOn.congr fun G hG => ?_
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le hcd] at hr
  simp only [hF', projIcc_of_mem hg hG, projIcc_of_mem hcd hr]

/-- An integral over `(0,∞)` of a function vanishing off `[c,d] ⊂ (0,∞)` is the interval
integral over `[c,d]`. -/
theorem setIntegral_Ioi_eq_intervalIntegral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    (hf : ∀ r : ℝ, 0 < r → r ∉ Icc c d → f r = 0) :
    ∫ r in Ioi (0 : ℝ), f r = ∫ r in c..d, f r := by
  rw [intervalIntegral.integral_of_le hcd, ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (fun r hr => lt_of_lt_of_le hc hr.1) fun r hr => hf r hr.1 hr.2

/-! ### The ring: the eigendata along `G ↦ (λ_*(G), G)` -/

variable {χ : ℝ → ℝ}

theorem a_pos_lt_one : 0 < a ∧ a < 1 := by
  obtain ⟨-, -, -, -, -, -, -, h0, h1⟩ := ringData_order
  exact ⟨h0, h1⟩

theorem Icc_a_one_subset : Icc a 1 ⊆ Ioi (0 : ℝ) := fun _ hr => lt_of_lt_of_le a_pos_lt_one.1 hr.1

theorem Icc_a_two_subset : Icc (a / 2) 2 ⊆ Ioi (0 : ℝ) :=
  fun _ hr => lt_of_lt_of_le (by linarith [a_pos_lt_one.1]) hr.1

theorem Gbar_nonneg : (0 : ℝ) ≤ Gbar := by
  rw [Gbar]; positivity

/-- `λ_*` is continuous on `[0,G₁]` (`prop:U`(a)). -/
theorem lam_continuousOn (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) :
    ContinuousOn (lam χ) (Icc 0 Gbar) :=
  (propU_a χ hχ hN).1

/-- `Re λ_*(G) > 0` on `[0,G₁]` (`prop:U`(a): `Re λ_*(G) ≥ σ_b > 211/2500`). -/
theorem lam_re_pos (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) {G : ℝ}
    (hG : G ∈ Icc (0 : ℝ) Gbar) : 0 < (lam χ G).re := by
  obtain ⟨-, -, ⟨G₁, -, hsb, hmin⟩, hgap, -⟩ := propU_a χ hχ hN
  have h1 := hmin G hG
  have h2 : sigma χ G = (lam χ G).re := rfl
  linarith

theorem gstar_continuousOn (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) :
    ContinuousOn (fun p : ℝ × ℝ => gstar χ p.1 p.2) (Icc 0 Gbar ×ˢ Ioi 0) :=
  continuousOn_comp_path (gStar_continuousOn _ (ringPhiSetting_valid hχ) 3)
    (lam_continuousOn hχ hN) (fun _ hG => lam_re_pos hχ hN hG) subset_rfl

theorem gstar_supp (hχ : IsAdmissibleCutoff χ) (G : ℝ) :
    ∀ r : ℝ, 0 < r → r ∉ Icc a 1 → gstar χ G r = 0 :=
  fun _ hr hr' => gStar_eq_zero _ (ringPhiSetting_valid hχ) 3 _ G hr hr'

theorem gstar_slice_continuousOn (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) : ContinuousOn (gstar χ G) (Ioi 0) := by
  have hpath : ContinuousOn (fun r : ℝ => ((G, r) : ℝ × ℝ)) (Ioi 0) :=
    continuousOn_const.prodMk continuousOn_id
  exact ((gstar_continuousOn hχ hN).comp hpath fun r hr => ⟨hG, hr⟩).congr fun _ _ => rfl

theorem psiLog_path_continuousOn (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) :
    ContinuousOn (fun p : ℝ × ℝ => (ringPhiSetting χ).psi 3 (lam χ p.1) p.1 (Real.log p.2))
      (Icc 0 Gbar ×ˢ Ioi 0) :=
  continuousOn_comp_path (psiLog_continuousOn _ (ringPhiSetting_valid hχ) 3)
    (lam_continuousOn hχ hN) (fun _ hG => lam_re_pos hχ hN hG) subset_rfl

theorem Mres_path_continuousOn (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) :
    ContinuousOn (fun p : ℝ × ℝ => (ringPhiSetting χ).Mres ((3 : ℕ) : ℤ) (lam χ p.1) p.1 p.2)
      (Icc 0 Gbar ×ˢ Ioi 0) :=
  continuousOn_comp_path (Mres_continuousOn _ (ringPhiSetting_valid hχ) ((3 : ℕ) : ℤ))
    (lam_continuousOn hχ hN) (fun _ hG => lam_re_pos hχ hN hG) subset_rfl

/-! ### `n_*` and `J` -/

theorem nstar_eq (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) {G : ℝ}
    (hG : G ∈ Icc (0 : ℝ) Gbar) :
    nstar χ G = Real.sqrt (2 * π * ∫ r in a..1, ‖gstar χ G r‖ ^ 2 * r) := by
  have hm : AEStronglyMeasurable (gstar χ G) (volume.restrict (Ioi 0)) :=
    (gstar_slice_continuousOn hχ hN hG).aestronglyMeasurable measurableSet_Ioi
  have h2 := (Ang.memLp_ofProfile_iff (ℓ := 3) hm).2
  have hint : ∫ r in Ioi (0 : ℝ), ‖gstar χ G r‖ ^ 2 * r = ∫ r in a..1, ‖gstar χ G r‖ ^ 2 * r :=
    setIntegral_Ioi_eq_intervalIntegral a_pos_lt_one.1 a_pos_lt_one.2.le fun r hr hr' => by
      simp [gstar_supp hχ G r hr hr']
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

theorem J_eq (hχ : IsAdmissibleCutoff χ) (G : ℝ) :
    J χ G = ∫ r in a..1, gstar χ G r * (ringPhiSetting χ).psi 3 (lam χ G) G (Real.log r) *
      (ringPhiSetting χ).Mres ((3 : ℕ) : ℤ) (lam χ G) G r * (r : ℂ) := by
  exact setIntegral_Ioi_eq_intervalIntegral a_pos_lt_one.1 a_pos_lt_one.2.le fun r hr hr' => by
    have h0 : (ringPhiSetting χ).gStar 3 (lam χ G) G r = 0 := gstar_supp hχ G r hr hr'
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
  exact hI.congr fun G _ => J_eq hχ G

/-- `J(G) ≠ 0` on `[0,G₁]` (`prop:U`(b), from `thm:evans-simple`(1)). -/
theorem J_ne_zero (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) {G : ℝ}
    (hG : G ∈ Icc (0 : ℝ) Gbar) : J χ G ≠ 0 :=
  norm_pos_iff.1 ((propU_b χ hχ hN).2.2.2.2.2.2 G hG).2.2.1

/-! ### The representer -/

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

theorem cRep_continuousOn (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) :
    ContinuousOn (cRep χ) (Icc 0 Gbar) := by
  refine (Complex.continuous_ofReal.comp_continuousOn (nstar_continuousOn hχ hN)).div
    (continuousOn_const.mul (Complex.continuous_conj.comp_continuousOn (J_continuousOn hχ hN)))
    fun G hG => ?_
  refine mul_ne_zero (by simp [Real.pi_ne_zero]) ?_
  simpa using J_ne_zero hχ hN hG

end EllRepContH

end Eig

end NonUniqueEuler
