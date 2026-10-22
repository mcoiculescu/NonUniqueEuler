import NonUniqueEuler.Defs.Sec4.Extra2Eigendata
import NonUniqueEuler.Defs.Infra.CkNorm
import NonUniqueEuler.I.Sec4.PropU
import NonUniqueEuler.I.Sec4.Eigendata
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.I.Sec4.Uniform.PhiCont
import NonUniqueEuler.I.Sec4.Uniform.EllRepCont
import NonUniqueEuler.I.Infra.Sobolev.DotGradSharp
import NonUniqueEuler.I.Infra.Sobolev.Smooth
import NonUniqueEuler.I.Infra.Sobolev.Norm
import NonUniqueEuler.I.Infra.Sobolev.NormDeriv
import NonUniqueEuler.I.Infra.Polar.Power
import NonUniqueEuler.H.Sec4.Uniform.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Proof of `lem:uniform` (the uniform constants of the eigendata)

Proof of `I/Sec4/Uniform.lean` (`04_ring.tex:1502-1567`). Same declarations, statements copied
verbatim.

* `uniform_constants`: extrema of the continuous functions of `prop:U`(b) on the compact
  `[0,G₁]` (`IsCompact.isLeast_sInf`, `IsCompact.isGreatest_sSup`), positivity from `prop:U`(b).
* `uniform_inequalities`: (1) `h·∇Φ = DΦ(x)(h(x))` a.e., so `|h·∇Φ| ≤ ‖h‖_{C^0(N')}|∇Φ|`, and
  `ℓ_*(G)` is bounded on `L²(N)` by `‖ℓ_*‖`; (2) Cauchy–Schwarz with
  `‖|y|³‖²_{L²(N)} ≤ ∫_{B_2}|y|⁶ = 64π`; (3) the sharp transport bound
  `I/Infra/Sobolev/DotGradSharp.lean`.
* `uniform_continuous`: `λ_*` by `prop:U`(a); `φ_*` into `H^k` by `I/Sec4/Uniform/PhiCont.lean`;
  `ℓ_*(G)` in operator norm by the representer (`ell_representer`) and
  `I/Sec4/Uniform/EllRepCont.lean`; `β(G) = ℓ_*(G)(b e^{3iθ})` and `pout_*(G) = pout_3[φ_*(G)]`
  then follow (`pout_3` is bounded on `L²(N)`, inequality (2)).
-/

noncomputable section

open MeasureTheory Set Real Filter Topology ComplexConjugate Metric
open scoped ContDiff

namespace NonUniqueEuler

namespace Eig

open RingData Sect

/-! ### Generic facts -/

theorem Gbar_pos : 0 < Gbar := by
  unfold Gbar Rc
  positivity

/-- A continuous function on `[0,G₁]` attains its infimum and its supremum. -/
theorem extrema_of_continuousOn {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 Gbar)) :
    IsLeast (f '' Icc 0 Gbar) (sInf (f '' Icc 0 Gbar)) ∧
      IsGreatest (f '' Icc 0 Gbar) (sSup (f '' Icc 0 Gbar)) := by
  have hc : IsCompact (f '' Icc 0 Gbar) := isCompact_Icc.image_of_continuousOn hf
  have hne : (f '' Icc 0 Gbar).Nonempty := (nonempty_Icc.2 Gbar_pos.le).image f
  exact ⟨hc.isLeast_sInf hne, hc.isGreatest_sSup hne⟩

/-- **`lem:uniform`, the constants** (`04_ring.tex:1507-1518`): the extrema over `[0,G₁]` of `|β|`,
`|pout_*|`, `‖ℓ_*(G)‖`, `‖φ_*(G)‖_{H^k}` are attained; `c_N = min|β|·min|pout_*| > 0`,
`C_N = max|β|·max|pout_*|`, `c_out = 2π min|pout_*| > 0`, `‖ℓ_*‖ = max‖ℓ_*(G)‖`,
`max‖φ_*(G)‖_{H^k}` are finite, with the corresponding bounds at every `G ∈ [0,G₁]`. -/
theorem uniform_constants (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) :
    IsLeast ((fun G => ‖beta χ G‖) '' Icc 0 Gbar) (sInf ((fun G => ‖beta χ G‖) '' Icc 0 Gbar)) ∧
      IsGreatest ((fun G => ‖beta χ G‖) '' Icc 0 Gbar)
        (sSup ((fun G => ‖beta χ G‖) '' Icc 0 Gbar)) ∧
      IsLeast ((fun G => ‖pout χ G‖) '' Icc 0 Gbar) (sInf ((fun G => ‖pout χ G‖) '' Icc 0 Gbar)) ∧
      IsGreatest ((fun G => ‖pout χ G‖) '' Icc 0 Gbar)
        (sSup ((fun G => ‖pout χ G‖) '' Icc 0 Gbar)) ∧
      IsGreatest ((fun G => ‖ell χ 0 G‖) '' Icc 0 Gbar) (ellNorm χ) ∧
      (∀ k : ℕ, IsGreatest ((fun G => Sob.normH k (phi χ G)) '' Icc 0 Gbar) (phiNormMax χ k)) ∧
      0 < cN χ ∧ 0 < cout χ ∧
      ∀ G ∈ Icc (0 : ℝ) Gbar,
        cN χ ≤ ‖beta χ G‖ * ‖pout χ G‖ ∧ ‖beta χ G‖ * ‖pout χ G‖ ≤ CN χ ∧
          cout χ ≤ 2 * π * ‖pout χ G‖ ∧ ‖ell χ 0 G‖ ≤ ellNorm χ ∧
          ∀ k : ℕ, Sob.normH k (phi χ G) ≤ phiNormMax χ k := by
  obtain ⟨hpo, -, -, hbe, hel, hph, hpos⟩ := propU_b χ hχ hN
  obtain ⟨hbL, hbG⟩ := extrema_of_continuousOn hbe
  obtain ⟨hpL, hpG⟩ := extrema_of_continuousOn hpo
  have heG : IsGreatest ((fun G => ‖ell χ 0 G‖) '' Icc 0 Gbar) (ellNorm χ) :=
    (extrema_of_continuousOn hel).2
  have hphG : ∀ k : ℕ,
      IsGreatest ((fun G => Sob.normH k (phi χ G)) '' Icc 0 Gbar) (phiNormMax χ k) :=
    fun k => (extrema_of_continuousOn (hph k)).2
  -- the minima are positive
  have hbpos : 0 < sInf ((fun G => ‖beta χ G‖) '' Icc 0 Gbar) := by
    obtain ⟨G, hG, hGe⟩ := hbL.1
    rw [← hGe]
    exact (hpos G hG).2.2.2
  have hppos : 0 < sInf ((fun G => ‖pout χ G‖) '' Icc 0 Gbar) := by
    obtain ⟨G, hG, hGe⟩ := hpL.1
    rw [← hGe]
    exact (hpos G hG).1
  refine ⟨hbL, hbG, hpL, hpG, heG, hphG, mul_pos hbpos hppos,
    mul_pos (by positivity) hppos, fun G hG => ?_⟩
  have hb1 : sInf ((fun G => ‖beta χ G‖) '' Icc 0 Gbar) ≤ ‖beta χ G‖ :=
    hbL.2 (mem_image_of_mem _ hG)
  have hb2 : ‖beta χ G‖ ≤ sSup ((fun G => ‖beta χ G‖) '' Icc 0 Gbar) :=
    hbG.2 (mem_image_of_mem _ hG)
  have hp1 : sInf ((fun G => ‖pout χ G‖) '' Icc 0 Gbar) ≤ ‖pout χ G‖ :=
    hpL.2 (mem_image_of_mem _ hG)
  have hp2 : ‖pout χ G‖ ≤ sSup ((fun G => ‖pout χ G‖) '' Icc 0 Gbar) :=
    hpG.2 (mem_image_of_mem _ hG)
  refine ⟨?_, ?_, ?_, heG.2 (mem_image_of_mem _ hG),
    fun k => (hphG k).2 (mem_image_of_mem _ hG)⟩
  · exact mul_le_mul hb1 hp1 hppos.le (norm_nonneg _)
  · exact mul_le_mul hb2 hp2 (norm_nonneg _) ((norm_nonneg _).trans hb2)
  · exact mul_le_mul_of_nonneg_left hp1 (by positivity)

/-! ### The ring `Φ` -/

/-- The complexified ring `Φ`. -/
def PhiC (χ : ℝ → ℝ) : ℂ → ℂ := fun y => ((ringPhi χ y : ℝ) : ℂ)

theorem tsupport_ringPhi_subset {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) :
    tsupport (ringPhi χ) ⊆ annN ∩ annN' := by
  obtain ⟨-, -, -, -, -, hts, ha0, -⟩ := ringFacts_of_admissible hχ
  intro y hy
  obtain ⟨h1, h2⟩ := hts hy
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem contDiff_PhiC {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) : ContDiff ℝ ∞ (PhiC χ) :=
  Complex.ofRealCLM.contDiff.comp (ringFacts_of_admissible hχ).1

theorem hasCompactSupport_PhiC {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) :
    HasCompactSupport (PhiC χ) :=
  (ringFacts_of_admissible hχ).2.1.comp_left Complex.ofReal_zero

theorem fderiv_ringPhi_eq_zero {χ : ℝ → ℝ} {x : ℂ} (hx : x ∉ tsupport (ringPhi χ)) :
    fderiv ℝ (ringPhi χ) x = 0 := by
  by_contra h
  exact hx (support_fderiv_subset ℝ (Function.mem_support.2 h))

theorem fderiv_PhiC_apply {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (x v : ℂ) :
    fderiv ℝ (PhiC χ) x v = ((fderiv ℝ (ringPhi χ) x v : ℝ) : ℂ) := by
  have hd : DifferentiableAt ℝ (ringPhi χ) x :=
    ((ringFacts_of_admissible hχ).1.differentiable (by simp)) x
  have h := (Complex.ofRealCLM.hasFDerivAt.comp x hd.hasFDerivAt).fderiv
  have h2 : PhiC χ = Complex.ofRealCLM ∘ ringPhi χ := rfl
  rw [h2, h]
  rfl

/-- `h·∇Φ = DΦ(x)(h(x))` almost everywhere. -/
theorem hGradPhi_ae_eq {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (h : ℂ → ℂ) :
    hGradPhi χ h =ᵐ[volume] fun x => ((fderiv ℝ (ringPhi χ) x (h x) : ℝ) : ℂ) := by
  obtain ⟨-, hwp, -⟩ := Sob.memH_of_contDiff_hasCompactSupport (contDiff_PhiC hχ)
    (hasCompactSupport_PhiC hχ) 1
  have h1 := hwp (1, 0) (by simp [Sob.mem_multiIdx])
  have h2 := hwp (0, 1) (by simp [Sob.mem_multiIdx])
  filter_upwards [h1, h2] with x hx1 hx2
  have e1 : Sob.partialD (1, 0) (PhiC χ) x = fderiv ℝ (PhiC χ) x 1 := by
    simp [Sob.partialD, Sob.pdList, Sob.iterDirDeriv, Sob.dirDeriv]
  have e2 : Sob.partialD (0, 1) (PhiC χ) x = fderiv ℝ (PhiC χ) x Complex.I := by
    simp [Sob.partialD, Sob.pdList, Sob.iterDirDeriv, Sob.dirDeriv]
  have hdec : h x = (h x).re • (1 : ℂ) + (h x).im • Complex.I := by
    apply Complex.ext <;> simp
  change ((h x).re : ℂ) * Sob.weakPartial (1, 0) (PhiC χ) x +
      ((h x).im : ℂ) * Sob.weakPartial (0, 1) (PhiC χ) x = _
  rw [hx1, hx2, e1, e2, fderiv_PhiC_apply hχ, fderiv_PhiC_apply hχ]
  conv_rhs => rw [hdec, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  push_cast
  ring

/-- The function `|∇Φ| = ‖DΦ‖` (complexified) is in `L²`. -/
theorem memLp_gradPhi {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) :
    MemLp (fun y => ((‖fderiv ℝ (ringPhi χ) y‖ : ℝ) : ℂ)) 2 volume := by
  obtain ⟨hs, hc, -⟩ := ringFacts_of_admissible hχ
  have hcont : Continuous fun y => ((‖fderiv ℝ (ringPhi χ) y‖ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (hs.continuous_fderiv (by simp)).norm
  refine hcont.memLp_of_hasCompactSupport ?_
  refine HasCompactSupport.intro hc fun x hx => ?_
  rw [fderiv_ringPhi_eq_zero hx]
  simp

/-- `x ↦ DΦ(x)(h(x))` is continuous with compact support, for `h` continuous near `N'`. -/
theorem continuous_fderiv_apply {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {h : ℂ → ℂ}
    (hh : MemCk 0 annN' h) :
    Continuous fun x => ((fderiv ℝ (ringPhi χ) x (h x) : ℝ) : ℂ) := by
  obtain ⟨hs, -⟩ := ringFacts_of_admissible hχ
  obtain ⟨V, hVo, hNV, hcd⟩ := hh.near
  have hDc : Continuous fun x => fderiv ℝ (ringPhi χ) x := hs.continuous_fderiv (by simp)
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ tsupport (ringPhi χ)
  · have hxV : x ∈ V := hNV ((tsupport_ringPhi_subset hχ hx).2)
    have hhx : ContinuousAt h x := hcd.continuousOn.continuousAt (hVo.mem_nhds hxV)
    exact Complex.continuous_ofReal.continuousAt.comp (hDc.continuousAt.clm_apply hhx)
  · refine (continuousAt_const (y := (0 : ℂ))).congr ?_
    filter_upwards [(isClosed_tsupport (ringPhi χ)).isOpen_compl.mem_nhds hx] with y hy
    rw [fderiv_ringPhi_eq_zero hy]
    simp

/-- `|DΦ(x)(h(x))| ≤ ‖h‖_{C^0(N')} |∇Φ(x)|`. -/
theorem norm_fderiv_apply_le {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {h : ℂ → ℂ}
    (hh : MemCk 0 annN' h) (x : ℂ) :
    ‖((fderiv ℝ (ringPhi χ) x (h x) : ℝ) : ℂ)‖ ≤
      normCk 0 annN' h * ‖((‖fderiv ℝ (ringPhi χ) x‖ : ℝ) : ℂ)‖ := by
  rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, norm_norm]
  by_cases hx : x ∈ tsupport (ringPhi χ)
  · have hb := norm_le_normCk hh ((tsupport_ringPhi_subset hχ hx).2)
    calc |fderiv ℝ (ringPhi χ) x (h x)| = ‖fderiv ℝ (ringPhi χ) x (h x)‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ (ringPhi χ) x‖ * ‖h x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖fderiv ℝ (ringPhi χ) x‖ * normCk 0 annN' h := by gcongr
      _ = _ := mul_comm _ _
  · rw [fderiv_ringPhi_eq_zero hx]
    simp

/-! ### `pout_3` is bounded on `L²(N)` -/

theorem measurableSet_annN : MeasurableSet annN := (isClosed_closedAnnulus _ _).measurableSet

theorem closedBall_two_ae_eq_ball : closedBall (0 : ℂ) 2 =ᵐ[volume] ball (0 : ℂ) 2 := by
  refine ae_eq_set.2 ⟨?_, ?_⟩
  · refine measure_mono_null (fun x hx => ?_) (Measure.addHaar_sphere volume (0 : ℂ) 2)
    obtain ⟨h1, h2⟩ := hx
    rw [mem_closedBall] at h1
    rw [mem_ball, not_lt] at h2
    exact mem_sphere.2 (le_antisymm h1 h2)
  · rw [sdiff_eq_empty.2 ball_subset_closedBall]
    exact measure_empty

/-- `∫_N |y|⁶ ≤ ∫_{B_2} |y|⁶ = 64π`. -/
theorem integral_annN_norm_pow_six_le : ∫ x in annN, ‖x‖ ^ (6 : ℝ) ≤ 64 * π := by
  have hcont : Continuous fun x : ℂ => ‖x‖ ^ (6 : ℝ) :=
    continuous_norm.rpow_const fun _ => Or.inr (by norm_num)
  have hsub : annN ⊆ closedBall (0 : ℂ) 2 := fun x hx => by
    rw [mem_closedBall, dist_zero_right]
    exact hx.2
  calc ∫ x in annN, ‖x‖ ^ (6 : ℝ)
      ≤ ∫ x in closedBall (0 : ℂ) 2, ‖x‖ ^ (6 : ℝ) :=
        setIntegral_mono_set (hcont.continuousOn.integrableOn_compact (isCompact_closedBall _ _))
          (Eventually.of_forall fun x => by positivity) (Eventually.of_forall hsub)
    _ = ∫ x in ball (0 : ℂ) 2, ‖x‖ ^ (6 : ℝ) := setIntegral_congr_set closedBall_two_ae_eq_ball
    _ = 2 * π * 2 ^ ((6 : ℝ) + 2) / ((6 : ℝ) + 2) :=
        Polar.setIntegral_ball_norm_rpow (by norm_num) (by norm_num)
    _ = 64 * π := by
        have : (2 : ℝ) ^ ((6 : ℝ) + 2) = 256 := by
          rw [show (6 : ℝ) + 2 = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          norm_num
        rw [this]
        ring

/-- The weight `1_N ȳ³`. -/
def wt3 : ℂ → ℂ := annN.indicator fun w => conj w ^ (3 : ℤ)

theorem memLp_wt3 : MemLp wt3 2 volume := by
  unfold wt3
  rw [memLp_indicator_iff_restrict measurableSet_annN]
  have hfin : IsFiniteMeasure (volume.restrict annN) :=
    isFiniteMeasure_restrict.2 (isCompact_closedAnnulus _ _).measure_lt_top.ne
  have hcont : Continuous fun w : ℂ => conj w ^ (3 : ℤ) := by
    simp only [zpow_ofNat]
    exact (Complex.continuous_conj).pow 3
  refine MemLp.of_bound hcont.aestronglyMeasurable 8 ?_
  refine (ae_restrict_iff' measurableSet_annN).2 (Eventually.of_forall fun x hx => ?_)
  have h2 : ‖x‖ ≤ 2 := hx.2
  rw [zpow_ofNat, norm_pow, Complex.norm_conj]
  calc ‖x‖ ^ 3 ≤ 2 ^ 3 := by gcongr
    _ = 8 := by norm_num

theorem l2_wt3_le : Sob.l2 wt3 ≤ 8 * Real.sqrt π := by
  rw [UniformH.l2_eq_integral memLp_wt3]
  have hpt : (fun x => ‖wt3 x‖ ^ (2 : ℝ)) = annN.indicator fun x => ‖x‖ ^ (6 : ℝ) := by
    funext x
    by_cases hx : x ∈ annN
    · rw [wt3, indicator_of_mem hx, indicator_of_mem hx, zpow_ofNat, norm_pow,
        Complex.norm_conj, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
      norm_num
    · rw [wt3, indicator_of_notMem hx, indicator_of_notMem hx, norm_zero,
        Real.zero_rpow two_ne_zero]
  rw [hpt, integral_indicator measurableSet_annN]
  have h64 : (64 * π) ^ (1 / (2 : ℝ)) = 8 * Real.sqrt π := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num),
      show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [← h64]
  exact Real.rpow_le_rpow (setIntegral_nonneg measurableSet_annN fun x _ => by positivity)
    integral_annN_norm_pow_six_le (by norm_num)

/-- For `g ∈ L²(N)`: `g ȳ³` is integrable and `|∫ g ȳ³| ≤ 8√π ‖g‖_{L²}`. -/
theorem conjMoment_three_bound {g : ℂ → ℂ} (hg : MemLp g 2 volume)
    (hgN : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → g x = 0) :
    Integrable (fun w => g w * conj w ^ (3 : ℤ)) volume ∧
      ‖Multipole.conjMoment g 3‖ ≤ 8 * Real.sqrt π * Sob.l2 g := by
  have hae : (fun w => g w * wt3 w) =ᵐ[volume] fun w => g w * conj w ^ (3 : ℤ) := by
    filter_upwards [hgN] with x hx
    by_cases hxN : x ∈ annN
    · rw [wt3, indicator_of_mem hxN]
    · rw [hx hxN, zero_mul, zero_mul]
  refine ⟨(UniformH.integrable_mul_of_l2 hg memLp_wt3).congr hae, ?_⟩
  have h1 : Multipole.conjMoment g 3 = ∫ w, g w * wt3 w := by
    rw [Multipole.conjMoment]
    exact integral_congr_ae hae.symm
  rw [h1]
  calc ‖∫ w, g w * wt3 w‖ ≤ Sob.l2 g * Sob.l2 wt3 := UniformH.norm_integral_mul_le_l2 hg memLp_wt3
    _ ≤ Sob.l2 g * (8 * Real.sqrt π) := mul_le_mul_of_nonneg_left l2_wt3_le (Sob.l2_nonneg g)
    _ = 8 * Real.sqrt π * Sob.l2 g := mul_comm _ _

theorem Cp_eq : (2 * π)⁻¹ * (8 * Real.sqrt π) = Cp := by
  have hs0 : 0 < Real.sqrt π := Real.sqrt_pos.2 pi_pos
  rw [Cp, eq_div_iff hs0.ne', show (2 * π)⁻¹ * (8 * Real.sqrt π) * Real.sqrt π =
    (2 * π)⁻¹ * 8 * (Real.sqrt π * Real.sqrt π) by ring, Real.mul_self_sqrt pi_pos.le]
  field_simp
  ring

theorem norm_two_pi_inv : ‖(2 * π : ℂ)⁻¹‖ = (2 * π)⁻¹ := by
  rw [norm_inv]
  congr 1
  rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]

/-- `|pout_3[g]| ≤ C_p ‖g‖_{L²(N)}`. -/
theorem pout3_bound {g : ℂ → ℂ} (hg : MemLp g 2 volume)
    (hgN : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → g x = 0) :
    ‖(2 * π : ℂ)⁻¹ * Multipole.conjMoment g 3‖ ≤ Cp * Sob.l2 g := by
  rw [norm_mul, norm_two_pi_inv, ← Cp_eq, mul_assoc]
  gcongr
  exact (conjMoment_three_bound hg hgN).2


/-! ### Bridges between `ellFn` and `ell` -/

/-- A function in `L²(N)` is the function of an element of `Y^0(N)`, with the same norm. -/
theorem exists_Y0 {f : ℂ → ℂ} (hf : MemLp f 2 volume)
    (hfN : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → f x = 0) :
    ∃ w : Y 0 annN, w.fn =ᵐ[volume] f ∧ ‖w‖ = Sob.l2 f := by
  obtain ⟨hH, hn⟩ := Sob.normH_zero hf
  obtain ⟨w, hw⟩ := UniformH.exists_Y_of_memH hH hfN
  refine ⟨w, hw, ?_⟩
  obtain ⟨hwH, hwn⟩ := UniformH.Y_memH_fn w
  rw [← hwn, ← hn]
  exact (hwH.congr_ae hw).2.symm

/-- On `L²(N)`, the formula `ellFn` is the chosen functional `ell`. -/
theorem ellFn_eq_ell {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) {f : ℂ → ℂ} {w : Y 0 annN}
    (hw : w.fn =ᵐ[volume] f) : ellFn χ G f = ell χ 0 G w := by
  rw [ell_spec_of_exists (exists_ell χ hχ hN hG 0) w, UniformH.ellFn_congr_ae χ G hw]

/-- The first inequality: `|ℓ_*(G)(-h·∇Φ)| ≤ ‖ℓ_*‖ ‖∇Φ‖_{L²} ‖h‖_{C^0(N')}`. -/
theorem ellFn_hGradPhi_bound (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ)
    (hN : NumericalHypothesis χ) {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) {h : ℂ → ℂ}
    (hh : MemCk 0 annN' h) :
    ‖ellFn χ G (fun x => -hGradPhi χ h x)‖ ≤ Cls χ * normCk 0 annN' h := by
  set F : ℂ → ℂ := fun x => ((fderiv ℝ (ringPhi χ) x (h x) : ℝ) : ℂ) with hFdef
  have hFc : Continuous F := continuous_fderiv_apply hχ hh
  have hFsupp : ∀ x, x ∉ annN → F x = 0 := fun x hx => by
    have : x ∉ tsupport (ringPhi χ) := fun h' => hx (tsupport_ringPhi_subset hχ h').1
    simp [hFdef, fderiv_ringPhi_eq_zero this]
  have hFL : MemLp F 2 volume :=
    hFc.memLp_of_hasCompactSupport (HasCompactSupport.intro (isCompact_closedAnnulus _ _) hFsupp)
  have hae : (fun x => -hGradPhi χ h x) =ᵐ[volume] fun x => -F x := by
    filter_upwards [hGradPhi_ae_eq hχ h] with x hx
    rw [hx]
  have hfL : MemLp (fun x => -hGradPhi χ h x) 2 volume := hFL.neg.ae_eq hae.symm
  have hfN : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → -hGradPhi χ h x = 0 := by
    filter_upwards [hae] with x hx hxN
    rw [hx, hFsupp x hxN, neg_zero]
  obtain ⟨w, hw, hwn⟩ := exists_Y0 hfL hfN
  have hl2 : Sob.l2 (fun x => -hGradPhi χ h x) ≤ normCk 0 annN' h * gradPhiL2 χ := by
    refine UniformH.l2_le_of_ae_bound (normCk_nonneg _ _ _) (memLp_gradPhi hχ) ?_
    filter_upwards [hae] with x hx
    rw [hx, norm_neg]
    exact norm_fderiv_apply_le hχ hh x
  have hell : ‖ell χ 0 G‖ ≤ ellNorm χ :=
    ((uniform_constants χ hχ hN).2.2.2.2.2.2.2.2 G hG).2.2.2.1
  have hE0 : 0 ≤ ellNorm χ := (ContinuousLinearMap.opNorm_nonneg _).trans hell
  rw [ellFn_eq_ell hχ hN hG hw]
  calc ‖ell χ 0 G w‖ ≤ ‖ell χ 0 G‖ * ‖w‖ := (ell χ 0 G).le_opNorm w
    _ ≤ ellNorm χ * (normCk 0 annN' h * gradPhiL2 χ) := by
        rw [hwn]
        exact mul_le_mul hell hl2 (Sob.l2_nonneg _) hE0
    _ = Cls χ * normCk 0 annN' h := by rw [Cls]; ring

/-- **`lem:uniform`, the three inequalities** (`04_ring.tex:1519-1533`), with the constants
`C_ls = ‖ℓ_*‖‖∇Φ‖_{L²}`, `C_p = 4/√π`, `C_∇(k) = 2^k((k+1)(k+2)/2)^{1/2}‖Φ‖_{H^{k+1}}`: for
`G ∈ [0,G₁]`, vector fields `h ∈ C^k(N';ℝ²)` and `g ∈ L²(N)`,
`|ℓ_*(G)(-h·∇Φ)| ≤ C_ls‖h‖_{C^0(N')}`, `|pout_3[g]| ≤ C_p‖g‖_{L²(N)}`,
`‖h·∇Φ‖_{H^k} ≤ C_∇(k)‖h‖_{C^k(N')}` (and `h·∇Φ ∈ H^k`). -/
theorem uniform_inequalities (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ)
    (hN : NumericalHypothesis χ) :
    (∀ G ∈ Icc (0 : ℝ) Gbar, ∀ h : ℂ → ℂ, MemCk 0 annN' h →
      ‖ellFn χ G (fun x => -hGradPhi χ h x)‖ ≤ Cls χ * normCk 0 annN' h) ∧
      (∀ g : ℂ → ℂ, MemLp g 2 (volume : Measure ℂ) →
        (∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → g x = 0) →
        ‖(2 * π : ℂ)⁻¹ * Multipole.conjMoment g 3‖ ≤ Cp * Sob.l2 g) ∧
      ∀ k : ℕ, ∀ h : ℂ → ℂ, MemCk k annN' h →
        Sob.MemH k (hGradPhi χ h) ∧ Sob.normH k (hGradPhi χ h) ≤ Cnab χ k * normCk k annN' h := by
  refine ⟨fun G hG h hh => ellFn_hGradPhi_bound χ hχ hN hG hh,
    fun g hg hgN => pout3_bound hg hgN, fun k h hh => ?_⟩
  have hΦH : Sob.MemH (k + 1) (fun y => ((ringPhi χ y : ℝ) : ℂ)) :=
    (Sob.memH_of_contDiff_hasCompactSupport (contDiff_PhiC hχ) (hasCompactSupport_PhiC hχ)
      (k + 1)).1
  have hΦK : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN' → ((ringPhi χ x : ℝ) : ℂ) = 0 :=
    Eventually.of_forall fun x hx => by
      have : x ∉ tsupport (ringPhi χ) := fun h' => hx (tsupport_ringPhi_subset hχ h').2
      simp [image_eq_zero_of_notMem_tsupport this]
  have hK : IsCompact annN' := isCompact_closedAnnulus _ _
  obtain ⟨hm, hb⟩ := Sob.MemH.dotGrad_of_memCk_sharp (K := annN') hK hΦH hΦK hh
  refine ⟨hm, hb.trans_eq ?_⟩
  rw [Cnab]
  ring

/-! ### Continuity -/

theorem phi_memLp {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) :
    MemLp (phi χ G) 2 volume ∧ ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → phi χ G x = 0 := by
  obtain ⟨-, hX, -⟩ := eigendata_phi χ hχ hN hG
  exact ⟨(Sob.memH_iff.1 (hX 0).1).1, (hX 0).2.1⟩

theorem continuousOn_phiY (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ)
    (hN : NumericalHypothesis χ) (k : ℕ) :
    ContinuousOn (fun G => phiY χ k G) (Icc 0 Gbar) := by
  intro G₀ hG₀
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  refine (phi_tendsto_normH χ hχ hN k hG₀).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with G hG
  have hY := ((eigendata_phi χ hχ hN hG).2.2.1 k).1
  have hY₀ := ((eigendata_phi χ hχ hN hG₀).2.2.1 k).1
  have hfn : (phiY χ k G - phiY χ k G₀).fn =ᵐ[volume] fun x => phi χ G x - phi χ G₀ x := by
    filter_upwards [UniformH.Y_fn_sub (phiY χ k G) (phiY χ k G₀), hY, hY₀] with x h1 h2 h3
    rw [h1, h2, h3]
  obtain ⟨hH, hn⟩ := UniformH.Y_memH_fn (phiY χ k G - phiY χ k G₀)
  rw [← hn]
  exact (hH.congr_ae hfn).2

theorem l2_conj (u : ℂ → ℂ) : Sob.l2 (fun x => conj (u x)) = Sob.l2 u := by
  unfold Sob.l2
  rw [eLpNorm_congr_norm_ae (Eventually.of_forall fun x => Complex.norm_conj (u x))]

theorem norm_ell_sub_le (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {G G₀ : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) (hG₀ : G₀ ∈ Icc (0 : ℝ) Gbar) :
    ‖ell χ 0 G - ell χ 0 G₀‖ ≤ Sob.l2 (fun x => ellRep χ G x - ellRep χ G₀ x) := by
  obtain ⟨hR, hrep, -⟩ := ell_representer χ hχ hN hG
  obtain ⟨hR₀, hrep₀, -⟩ := ell_representer χ hχ hN hG₀
  have hRL : MemLp (ellRep χ G) 2 volume := (Sob.memH_iff.1 hR.1).1
  have hRL₀ : MemLp (ellRep χ G₀) 2 volume := (Sob.memH_iff.1 hR₀.1).1
  have hc1 : MemLp (fun x => conj (ellRep χ G x)) 2 volume := hRL.star
  have hc0 : MemLp (fun x => conj (ellRep χ G₀ x)) 2 volume := hRL₀.star
  have hcd : MemLp (fun x => conj (ellRep χ G x - ellRep χ G₀ x)) 2 volume := (hRL.sub hRL₀).star
  refine ContinuousLinearMap.opNorm_le_bound _ (Sob.l2_nonneg _) fun w => ?_
  have hwL := UniformH.Y_memLp_fn w
  rw [_root_.sub_apply, hrep w, hrep₀ w,
    ← integral_sub (UniformH.integrable_mul_of_l2 hwL hc1)
      (UniformH.integrable_mul_of_l2 hwL hc0)]
  have hfun : (fun x => w.fn x * conj (ellRep χ G x) - w.fn x * conj (ellRep χ G₀ x)) =
      fun x => w.fn x * conj (ellRep χ G x - ellRep χ G₀ x) := by
    funext x
    rw [map_sub, mul_sub]
  rw [hfun]
  have hw0 : Sob.l2 w.fn = ‖w‖ :=
    (Sob.normH_zero hwL).2.symm.trans (UniformH.Y_memH_fn w).2
  calc ‖∫ x, w.fn x * conj (ellRep χ G x - ellRep χ G₀ x)‖
      ≤ Sob.l2 w.fn * Sob.l2 (fun x => conj (ellRep χ G x - ellRep χ G₀ x)) :=
        UniformH.norm_integral_mul_le_l2 hwL hcd
    _ = Sob.l2 (fun x => ellRep χ G x - ellRep χ G₀ x) * ‖w‖ := by
        rw [l2_conj (fun x => ellRep χ G x - ellRep χ G₀ x), hw0, mul_comm]

theorem continuousOn_ell (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ)
    (hN : NumericalHypothesis χ) : ContinuousOn (fun G => ell χ 0 G) (Icc 0 Gbar) := by
  intro G₀ hG₀
  have key : Tendsto (fun G => ‖ell χ 0 G - ell χ 0 G₀‖) (𝓝[Icc 0 Gbar] G₀) (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _ => ContinuousLinearMap.opNorm_nonneg _) ?_
      (ellRep_tendsto_l2 χ hχ hN hG₀)
    filter_upwards [self_mem_nhdsWithin] with G hG
    exact norm_ell_sub_le χ hχ hN hG hG₀
  exact (tendsto_iff_norm_sub_tendsto_zero (E := Y 0 annN →L[ℂ] ℂ)).2 key


/-! ### `β` and `pout_*` -/

/-- `ω̄' = Φ'` of the ring setting is continuous. -/
theorem continuous_dom {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) :
    Continuous (ringPhiSetting χ).dom := by
  have h : ContDiff ℝ ∞ (ringPhiSetting χ).omR :=
    (ringFacts_of_admissible hχ).1.comp Complex.ofRealCLM.contDiff
  exact h.continuous_deriv (by simp)

/-- The profile `b(r) = -(i/2) r^{-4} Φ'(r)` vanishes for `0 ≤ r < a`. -/
theorem bprof_eq_zero_of_lt {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {r : ℝ} (hr : 0 ≤ r)
    (hra : r < a) : bprof χ r = 0 := by
  rcases hr.eq_or_lt with rfl | hr0
  · rw [bprof, SectorSetting.bfun, Complex.ofReal_zero,
      show (-((3 : ℕ) : ℤ) - 1) = -4 by norm_num, zero_zpow _ (by norm_num), mul_zero, zero_mul]
  · have h := (ringPhiSetting_valid hχ).dom_eq_zero r hr0 fun h' => (not_le.2 hra) h'.1
    rw [bprof, SectorSetting.bfun, h, Complex.ofReal_zero, mul_zero]

/-- The profile `b(r)` vanishes for `r > 1`. -/
theorem bprof_eq_zero_of_gt {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {r : ℝ} (hr : 1 < r) :
    bprof χ r = 0 := by
  have h := (ringPhiSetting_valid hχ).dom_eq_zero r (by linarith) fun h' => (not_le.2 hr) h'.2
  rw [bprof, SectorSetting.bfun, h, Complex.ofReal_zero, mul_zero]

theorem bfield_eq_zero_of_lt {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {x : ℂ} (hx : ‖x‖ < a) :
    Ang.ofProfile 3 (bprof χ) x = 0 := by
  rw [Ang.ofProfile, bprof_eq_zero_of_lt hχ (norm_nonneg x) hx, zero_mul]

theorem bfield_eq_zero_of_gt {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {x : ℂ} (hx : 1 < ‖x‖) :
    Ang.ofProfile 3 (bprof χ) x = 0 := by
  rw [Ang.ofProfile, bprof_eq_zero_of_gt hχ hx, zero_mul]

/-- The field `b(|x|) e^{3iθ}` is continuous (it vanishes near `0`). -/
theorem continuous_bfield {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) :
    Continuous (Ang.ofProfile 3 (bprof χ)) := by
  have ha : 0 < a := (ringFacts_of_admissible hχ).2.2.2.2.2.2.1
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : ‖x‖ < a
  · refine (continuousAt_const (y := (0 : ℂ))).congr ?_
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
    exact (bfield_eq_zero_of_lt hχ hy).symm
  · have hx0 : x ≠ 0 := by
      intro h
      rw [h, norm_zero] at hx
      exact hx ha
    have hn0 : ((‖x‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hx0)
    have hnc : Continuous fun y : ℂ => ((‖y‖ : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp continuous_norm
    unfold Ang.ofProfile Ang.angPhase bprof SectorSetting.bfun
    refine ContinuousAt.mul (ContinuousAt.mul (ContinuousAt.mul continuousAt_const ?_) ?_) ?_
    · exact hnc.continuousAt.zpow₀ _ (Or.inl hn0)
    · exact (Complex.continuous_ofReal.comp ((continuous_dom hχ).comp continuous_norm)).continuousAt
    · exact (continuousAt_id.div hnc.continuousAt hn0).zpow₀ _ (Or.inr (by norm_num))

/-- `b e^{3iθ} ∈ L²` and it vanishes off `N`. -/
theorem memLp_bfield {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) :
    MemLp (Ang.ofProfile 3 (bprof χ)) 2 volume ∧
      ∀ x, x ∉ annN → Ang.ofProfile 3 (bprof χ) x = 0 := by
  have ha : 0 < a := (ringFacts_of_admissible hχ).2.2.2.2.2.2.1
  have hz : ∀ x, x ∉ annN → Ang.ofProfile 3 (bprof χ) x = 0 := by
    intro x hx
    by_cases h1 : ‖x‖ < a
    · exact bfield_eq_zero_of_lt hχ h1
    by_cases h2 : 1 < ‖x‖
    · exact bfield_eq_zero_of_gt hχ h2
    have h1' : a ≤ ‖x‖ := not_lt.1 h1
    have h2' : ‖x‖ ≤ 1 := not_lt.1 h2
    exact absurd (⟨by linarith, by linarith⟩ : x ∈ annN) hx
  exact ⟨(continuous_bfield hχ).memLp_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_closedAnnulus _ _) hz), hz⟩

theorem continuousOn_beta (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ)
    (hN : NumericalHypothesis χ) : ContinuousOn (beta χ) (Icc 0 Gbar) := by
  obtain ⟨hL, hz⟩ := memLp_bfield hχ
  obtain ⟨w, hw, -⟩ := exists_Y0 hL (Eventually.of_forall hz)
  refine ((continuousOn_ell χ hχ hN).clm_apply (continuousOn_const (c := w))).congr fun G hG => ?_
  exact ellFn_eq_ell hχ hN hG hw

/-- `pout_*(G) - pout_*(G₀) = pout_3[φ_*(G) - φ_*(G₀)]`. -/
theorem pout_sub {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {G G₀ : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) (hG₀ : G₀ ∈ Icc (0 : ℝ) Gbar) :
    pout χ G - pout χ G₀ =
      (2 * π : ℂ)⁻¹ * Multipole.conjMoment (fun x => phi χ G x - phi χ G₀ x) 3 := by
  obtain ⟨hL, hz⟩ := phi_memLp hχ hN hG
  obtain ⟨hL₀, hz₀⟩ := phi_memLp hχ hN hG₀
  have i1 := (conjMoment_three_bound hL hz).1
  have i0 := (conjMoment_three_bound hL₀ hz₀).1
  rw [pout, pout, ← mul_sub]
  congr 1
  rw [Multipole.conjMoment, Multipole.conjMoment, Multipole.conjMoment, ← integral_sub i1 i0]
  congr 1
  funext w
  ring

theorem continuousOn_pout (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ)
    (hN : NumericalHypothesis χ) : ContinuousOn (pout χ) (Icc 0 Gbar) := by
  intro G₀ hG₀
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have h2 : Tendsto (fun G => Cp * Sob.normH 0 (fun x => phi χ G x - phi χ G₀ x))
      (𝓝[Icc 0 Gbar] G₀) (𝓝 0) := by
    have := (phi_tendsto_normH χ hχ hN 0 hG₀).const_mul Cp
    rwa [mul_zero] at this
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h2
  filter_upwards [self_mem_nhdsWithin] with G hG
  obtain ⟨hL, hz⟩ := phi_memLp hχ hN hG
  obtain ⟨hL₀, hz₀⟩ := phi_memLp hχ hN hG₀
  have hd : MemLp (fun x => phi χ G x - phi χ G₀ x) 2 volume := hL.sub hL₀
  have hdz : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ annN → phi χ G x - phi χ G₀ x = 0 := by
    filter_upwards [hz, hz₀] with x h1 h0 hx
    rw [h1 hx, h0 hx, sub_zero]
  rw [pout_sub hχ hN hG hG₀, (Sob.normH_zero hd).2]
  exact pout3_bound hd hdz

/-- **`lem:uniform`, continuity** (`04_ring.tex:1504-1506`): `λ_*`, `φ_*` (into `X^k` for every
`k`), `ℓ_*` (into `(X^0)^*`, here `(Y^0(N))^*`), `β`, `pout_*` are continuous on `[0,G₁]`. -/
theorem uniform_continuous (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) :
    ContinuousOn (lam χ) (Icc 0 Gbar) ∧
      (∀ k : ℕ, ContinuousOn (fun G => phiY χ k G) (Icc 0 Gbar) ∧
        ∀ G ∈ Icc (0 : ℝ) Gbar, Lin.MemX (phiY χ k G)) ∧
      ContinuousOn (fun G => ell χ 0 G) (Icc 0 Gbar) ∧
      ContinuousOn (beta χ) (Icc 0 Gbar) ∧
      ContinuousOn (pout χ) (Icc 0 Gbar) :=
  ⟨(propU_a χ hχ hN).1, fun k => ⟨continuousOn_phiY χ hχ hN k,
    fun _ hG => ((eigendata_phi χ hχ hN hG).2.2.1 k).2⟩, continuousOn_ell χ hχ hN,
    continuousOn_beta χ hχ hN, continuousOn_pout χ hχ hN⟩

end Eig

end NonUniqueEuler
