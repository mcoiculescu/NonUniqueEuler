import NonUniqueEuler.Defs.Sec4.Eigendata
import NonUniqueEuler.I.Sec4.PropU
import NonUniqueEuler.I.Sec4.PropU.GstarDeriv
import NonUniqueEuler.I.Sec4.HypN
import NonUniqueEuler.I.Sec4.EvansUnits
import NonUniqueEuler.I.Sec4.Resolvent
import NonUniqueEuler.I.Sec4.Eigendata
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.I.Infra.AngularFourier.NormHCont
import NonUniqueEuler.I.Infra.AngularFourier.SectorL2
import NonUniqueEuler.I.Infra.Sobolev.Norm
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Proof: `φ_*(G)` is continuous into every `H^k` (step of `lem:uniform`)

Proof of `I/Sec4/Uniform/PhiCont.lean` (`04_ring.tex:1537-1540`, with the continuity of
`g_*(G)` in `C^k([a,1])` from the proof of `prop:U`(b), `04_ring.tex:1400-1415`). Same
declaration, statement copied verbatim.

Argument. Fix `G₀ ∈ [0,G₁]` and put, for `G ∈ [0,G₁]`,
`d_G(r) = n_*(G)⁻¹ g_*(G)(r) - n_*(G₀)⁻¹ g_*(G₀)(r)`, so that
`φ_*(G) - φ_*(G₀) = d_G(|x|) e^{3iθ}` pointwise (`phi_sub_eq`). Each `d_G` is smooth on `(0,∞)`
and vanishes off `[a,1]` (`lem:resolvent`(2): `eigen_of_evans_eq_zero`, at the zero `λ_*(G)` of
`E^Φ_3(·;G)`, `hypN_lamC`, `evans_units`). Its `r`-derivatives are
`∂_r^j d_G = n_*(G)⁻¹ ∂_r^j g_*(G) - n_*(G₀)⁻¹ ∂_r^j g_*(G₀)` on `(0,∞)`, jointly continuous in
`(G, r)` on `[0,G₁] × [a,1]`: `∂_r^j g_λ(r;G)` is jointly continuous in `(r,λ,G)`
(`I/Sec4/PropU/GstarDeriv.lean`), `λ_*` is continuous (`prop:U`(a), `propU_a`), and `n_*` is
continuous and positive (`n_*(G)² = 2π ∫_a^1 |g_*|² r dr`, `memLp_ofProfile_iff`;
`eigendata_phi`). Hence `G ↦ ‖d_G(|x|) e^{3iθ}‖_{H^k}` is continuous on `[0,G₁]`
(`I/Infra/AngularFourier/NormHCont.lean`), and its value at `G₀` is `‖0‖_{H^k} = 0`
(`MemH.const_smul` with `φ_*(G₀) ∈ H^k`).

This replaces steps 3-4 of the interface sketch (the `C^k(ℝ²)` bound of the difference and the
`H^k ≤ C^k` estimate on a fixed compact set) by the profile-level continuity statement
`continuousOn_normH_ofProfile`, applied to the family of differences.
-/

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff

namespace NonUniqueEuler

namespace Eig

open RingData

namespace PhiContH

variable {χ : ℝ → ℝ}

theorem a_pos_lt_one : 0 < a ∧ a < 1 := by
  obtain ⟨-, -, -, -, -, -, -, h0, h1⟩ := ringData_order
  exact ⟨h0, h1⟩

theorem Icc_a_one_subset : Icc a 1 ⊆ Ioi (0 : ℝ) := fun _ hr => lt_of_lt_of_le a_pos_lt_one.1 hr.1

theorem Gbar_nonneg : (0 : ℝ) ≤ Gbar := by
  rw [Gbar]; positivity

theorem Rc_sq_mul_mem {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) :
    Rc ^ 2 * G ∈ Icc (0 : ℝ) (1 / 50) := by
  have hR0 : 0 < Rc := Real.exp_pos _
  have hR : 0 < Rc ^ 2 := pow_pos hR0 2
  refine ⟨mul_nonneg hR.le hG.1, ?_⟩
  calc Rc ^ 2 * G ≤ Rc ^ 2 * Gbar := mul_le_mul_of_nonneg_left hG.2 hR.le
    _ = 1 / 50 := by have := hR0.ne'; rw [Gbar]; field_simp

/-- At `G ∈ [0,G₁]`: `Re λ_*(G) > 0` and `λ_*(G)` is a zero of `E^Φ_3(·;G)` (`hypN_lamC`,
`eq:evans-units`). -/
theorem lam_facts (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) {G : ℝ}
    (hG : G ∈ Icc (0 : ℝ) Gbar) :
    0 < (lam χ G).re ∧ (ringPhiSetting χ).evans 3 (lam χ G) G = 0 := by
  obtain ⟨h1, h2, -, -⟩ := hypN_lamC χ hN.n1 hN.n2 (Rc_sq_mul_mem hG)
  have hz : 0 < (lam χ G).re := lt_trans (by norm_num) h1
  refine ⟨hz, ?_⟩
  rw [evans_units hχ 3 (by norm_num) _ hz G]
  exact h2

/-- At `G ∈ [0,G₁]`, `g_*(G)` is smooth on `(0,∞)` and vanishes off `[a,1]`
(`lem:resolvent`(2)). -/
theorem gstar_facts (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) {G : ℝ}
    (hG : G ∈ Icc (0 : ℝ) Gbar) :
    ContDiffOn ℝ ∞ (gstar χ G) (Ioi 0) ∧ (∀ r : ℝ, 0 < r → r ∉ Icc a 1 → gstar χ G r = 0) := by
  obtain ⟨hz, hE⟩ := lam_facts hχ hN hG
  have h := SectorSetting.eigen_of_evans_eq_zero _ (ringPhiSetting_valid hχ) 3 (by norm_num) _
    hz G hE
  exact ⟨h.1, h.2.1⟩

theorem nstar_pos (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) {G : ℝ}
    (hG : G ∈ Icc (0 : ℝ) Gbar) : 0 < nstar χ G :=
  (eigendata_phi χ hχ hN hG).1

/-- `(G, r) ↦ ∂_r^j g_*(G)(r)` is continuous on `[0,G₁] × (0,∞)` (`I/Sec4/PropU/GstarDeriv.lean`
composed with `G ↦ (λ_*(G), G)`, continuous by `prop:U`(a)). -/
theorem gstar_iteratedDeriv_continuousOn (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    (j : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv j (gstar χ p.1) p.2) (Icc 0 Gbar ×ˢ Ioi 0) := by
  have hf := SectorSetting.gStar_iteratedDeriv_continuousOn _ (ringPhiSetting_valid hχ) 3
    (by norm_num) j
  have hg : ContinuousOn (fun p : ℝ × ℝ => (p.2, lam χ p.1, p.1)) (Icc 0 Gbar ×ˢ Ioi 0) :=
    continuousOn_snd.prodMk
      (((propU_a χ hχ hN).1.comp continuousOn_fst fun p hp => hp.1).prodMk continuousOn_fst)
  have h := hf.comp hg fun p hp => ⟨hp.2, (lam_facts hχ hN hp.1).1, mem_univ _⟩
  exact h

theorem gstar_continuousOn (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) :
    ContinuousOn (fun p : ℝ × ℝ => gstar χ p.1 p.2) (Icc 0 Gbar ×ˢ Ioi 0) := by
  simpa using gstar_iteratedDeriv_continuousOn hχ hN 0

/-! ### Continuity of `n_*` -/

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

/-- `n_*(G) = (2π ∫_a^1 |g_*|² r dr)^{1/2}` (`memLp_ofProfile_iff`). -/
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
  have hF : ContinuousOn (fun p : ℝ × ℝ => ‖gstar χ p.1 p.2‖ ^ 2 * p.2)
      (Icc 0 Gbar ×ˢ Icc a 1) :=
    (((gstar_continuousOn hχ hN).mono (prod_mono subset_rfl Icc_a_one_subset)).norm.pow 2).mul
      continuousOn_snd
  have hI := continuousOn_intervalIntegral_rect (F := fun G r => ‖gstar χ G r‖ ^ 2 * r)
    Gbar_nonneg a_pos_lt_one.2.le hF
  have h := Real.continuous_sqrt.comp_continuousOn ((continuousOn_const (c := 2 * π)).mul hI)
  exact h.congr fun G hG => nstar_eq hχ hN hG

/-- `G ↦ n_*(G)⁻¹` (as a complex number) is continuous on `[0,G₁]`. -/
theorem nstarInv_continuousOn (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) :
    ContinuousOn (fun G => ((nstar χ G : ℝ) : ℂ)⁻¹) (Icc 0 Gbar) :=
  (Complex.continuous_ofReal.comp_continuousOn (nstar_continuousOn hχ hN)).inv₀ fun _ hG =>
    Complex.ofReal_ne_zero.2 (nstar_pos hχ hN hG).ne'

/-! ### The difference `φ_*(G) - φ_*(G₀)` as a sector function -/

/-- `φ_*(G) - φ_*(G₀) = d_G(|x|) e^{3iθ}` with `d_G = n_*(G)⁻¹ g_*(G) - n_*(G₀)⁻¹ g_*(G₀)`. -/
theorem phi_sub_eq (χ : ℝ → ℝ) (G₀ G : ℝ) :
    (fun x => phi χ G x - phi χ G₀ x) = Ang.ofProfile 3 (fun r =>
      ((nstar χ G : ℝ) : ℂ)⁻¹ * gstar χ G r - ((nstar χ G₀ : ℝ) : ℂ)⁻¹ * gstar χ G₀ r) := by
  funext x
  simp only [phi, Ang.ofProfile]
  ring

/-- The `r`-derivatives of `d_G` on `(0,∞)`. -/
theorem iteratedDeriv_diff (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {G₀ G : ℝ} (hG₀ : G₀ ∈ Icc (0 : ℝ) Gbar) (hG : G ∈ Icc (0 : ℝ) Gbar) (j : ℕ) {r : ℝ}
    (hr : 0 < r) (c c₀ : ℂ) :
    iteratedDeriv j (fun r => c * gstar χ G r - c₀ * gstar χ G₀ r) r =
      c * iteratedDeriv j (gstar χ G) r - c₀ * iteratedDeriv j (gstar χ G₀) r := by
  have hca : ∀ G' ∈ Icc (0 : ℝ) Gbar, ContDiffAt ℝ j (gstar χ G') r := fun G' hG' =>
    ((gstar_facts hχ hN hG').1.contDiffAt (Ioi_mem_nhds hr)).of_le (by exact_mod_cast le_top)
  rw [iteratedDeriv_fun_sub (contDiffAt_const.mul (hca G hG)) (contDiffAt_const.mul (hca G₀ hG₀)),
    iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]

end PhiContH

open PhiContH in
/-- **`lem:uniform`, continuity of `φ_*`** (`04_ring.tex:1537-1540`): `φ_*(G) → φ_*(G₀)` in
`H^k` as `G → G₀` in `[0,G₁]`, for every `k`. -/
theorem phi_tendsto_normH (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    (k : ℕ) {G₀ : ℝ} (hG₀ : G₀ ∈ Icc (0 : ℝ) Gbar) :
    Tendsto (fun G => Sob.normH k (fun x => phi χ G x - phi χ G₀ x)) (𝓝[Icc 0 Gbar] G₀)
      (𝓝 0) := by
  set F : ℝ → ℝ → ℂ := fun G r =>
    ((nstar χ G : ℝ) : ℂ)⁻¹ * gstar χ G r - ((nstar χ G₀ : ℝ) : ℂ)⁻¹ * gstar χ G₀ r with hFdef
  have hsmooth : ∀ G ∈ Icc (0 : ℝ) Gbar, ContDiffOn ℝ ∞ (F G) (Ioi 0) := fun G hG =>
    (contDiffOn_const.mul (gstar_facts hχ hN hG).1).sub
      (contDiffOn_const.mul (gstar_facts hχ hN hG₀).1)
  have hsupp : ∀ G ∈ Icc (0 : ℝ) Gbar, ∀ r : ℝ, 0 < r → r ∉ Icc a 1 → F G r = 0 :=
    fun G hG r hr hr' => by
      simp only [hFdef, (gstar_facts hχ hN hG).2 r hr hr', (gstar_facts hχ hN hG₀).2 r hr hr',
        mul_zero, sub_zero]
  have hcont : ∀ j ≤ k, ContinuousOn (fun q : ℝ × ℝ => iteratedDeriv j (F q.1) q.2)
      (Icc 0 Gbar ×ˢ Icc a 1) := by
    intro j _
    have hsub : Icc (0 : ℝ) Gbar ×ˢ Icc a 1 ⊆ Icc 0 Gbar ×ˢ Ioi 0 :=
      prod_mono subset_rfl Icc_a_one_subset
    have hD := gstar_iteratedDeriv_continuousOn hχ hN j
    have h1 : ContinuousOn (fun q : ℝ × ℝ => ((nstar χ q.1 : ℝ) : ℂ)⁻¹ *
        iteratedDeriv j (gstar χ q.1) q.2) (Icc 0 Gbar ×ˢ Icc a 1) :=
      ((nstarInv_continuousOn hχ hN).comp continuousOn_fst fun q hq => hq.1).mul (hD.mono hsub)
    have hpath : ContinuousOn (fun q : ℝ × ℝ => ((G₀, q.2) : ℝ × ℝ)) (Icc 0 Gbar ×ˢ Icc a 1) :=
      continuousOn_const.prodMk continuousOn_snd
    have h2' := hD.comp hpath fun q hq => ⟨hG₀, Icc_a_one_subset hq.2⟩
    have h2 : ContinuousOn (fun q : ℝ × ℝ => iteratedDeriv j (gstar χ G₀) q.2)
        (Icc 0 Gbar ×ˢ Icc a 1) := h2'
    have h3 : ContinuousOn (fun q : ℝ × ℝ => ((nstar χ G₀ : ℝ) : ℂ)⁻¹ *
        iteratedDeriv j (gstar χ G₀) q.2) (Icc 0 Gbar ×ˢ Icc a 1) :=
      (continuousOn_const (c := ((nstar χ G₀ : ℝ) : ℂ)⁻¹)).mul h2
    refine (h1.sub h3).congr fun q hq => ?_
    exact iteratedDeriv_diff hχ hN hG₀ hq.1 j (Icc_a_one_subset hq.2) _ _
  have hmain := Ang.continuousOn_normH_ofProfile k a_pos_lt_one.1 a_pos_lt_one.2 3
    (T := Icc 0 Gbar) (h := F) hsmooth hsupp hcont
  -- the value at `G₀` is `‖0‖_{H^k} = 0`
  have hX : Sob.MemH k (phi χ G₀) := ((eigendata_phi χ hχ hN hG₀).2.1 k).1
  have hzero : Ang.ofProfile 3 (F G₀) = (0 : ℂ) • phi χ G₀ := by
    rw [hFdef, ← phi_sub_eq]
    funext x
    simp
  have h0 : Sob.normH k (Ang.ofProfile 3 (F G₀)) = 0 := by
    rw [hzero, (hX.const_smul 0).2, norm_zero, zero_mul]
  have hG := hmain G₀ hG₀
  rw [ContinuousWithinAt, h0] at hG
  refine hG.congr fun G => ?_
  rw [hFdef, ← phi_sub_eq]

end Eig

end NonUniqueEuler
