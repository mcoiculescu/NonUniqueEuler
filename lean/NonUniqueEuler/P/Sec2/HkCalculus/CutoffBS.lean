import NonUniqueEuler.Defs.Sec2.HkCalculus
import NonUniqueEuler.I.Sec2.BSBasic
import NonUniqueEuler.I.Infra.Sobolev.Density
import NonUniqueEuler.I.Infra.Sobolev.ReIm
import NonUniqueEuler.I.Infra.Sobolev.Norm
import NonUniqueEuler.I.Infra.Sobolev.NormDeriv
import NonUniqueEuler.H.Sec2.HkCalculus.CutoffBS.Closure
import NonUniqueEuler.H.Sec2.HkCalculus.CutoffBS.Smooth

/-!
# Proof of `I/Sec2/HkCalculus/CutoffBS`: `lem:Hk-calculus`(3) for real vorticities

Manuscript: `lem:Hk-calculus`(3), statement `02_prelim.tex:663-666`, proof `02_prelim.tex:748-766`.

1. Smooth case (`CutoffBSAux.exists_cutoffBS_smooth`, `H/Sec2/HkCalculus/CutoffBS/Smooth.lean`):
   for real `h ∈ C_c^∞` with `tsupport h ⊆ B_{2ρ}`, `‖χ (K ∗ h)‖_{H^{j+1}} ≤ C ‖h‖_{H^j}`.
2. General case: approximants `φ_n` of `g` in `H^j` supported in `B_{2ρ}`
   (`Sob.MemH.exists_seq_testFn_tendsto`) and their real parts `g_n = Re φ_n`; the sequence
   `χ (K ∗ g_n)` is Cauchy in `H^{j+1}` (step 1 for `g_n - g_m`, linearity of `K ∗ ·`) and
   converges to `χ (K ∗ g)` in `L²` (`lem:BS-basic`(c) for `g_n - g`); the closure lemma
   `CutoffBSAux.memH_of_cauchy` (`H/Sec2/HkCalculus/CutoffBS/Closure.lean`) concludes.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal ContDiff

namespace NonUniqueEuler.Sob

namespace CutoffBSAux

/-- Linearity of the Biot–Savart integral at a point where both integrals converge. -/
theorem velocity_sub_of_integrable {g₁ g₂ : ℂ → ℝ} {x : ℂ}
    (h₁ : Integrable (fun y => biotSavartKernel (x - y) * (g₁ y : ℂ)) volume)
    (h₂ : Integrable (fun y => biotSavartKernel (x - y) * (g₂ y : ℂ)) volume) :
    velocity (fun y => g₁ y - g₂ y) x = velocity g₁ x - velocity g₂ x := by
  unfold velocity
  rw [← integral_sub h₁ h₂]
  congr 1
  funext y
  push_cast
  ring

/-- For a continuous compactly supported real `h`, the Biot–Savart integral converges at every
point (`lem:BS-basic`(b)). -/
theorem integrable_biotSavart_of_continuous {h : ℂ → ℝ} (hc : Continuous h)
    (hcs : HasCompactSupport h) (x : ℂ) :
    Integrable (fun y => biotSavartKernel (x - y) * (h y : ℂ)) volume :=
  (BS.integrable_and_norm_velocity_le_sqrt_L1_Linf (hc.memLp_of_hasCompactSupport hcs)
    (hc.memLp_of_hasCompactSupport hcs) x).1

end CutoffBSAux

open CutoffBSAux in
/-- `lem:Hk-calculus`(3) for real vorticities: `‖χ (K_BS ∗ g)‖_{H^{j+1}} ≤ C' ‖g‖_{H^j}` for real
`g ∈ H^j` vanishing outside `B_ρ`, `χ ∈ C_c^∞(B_ρ)` real. -/
theorem exists_cutoffBS_real (j : ℕ) {ρ : ℝ} (hρ : 0 < ρ) {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ ball (0 : ℂ) ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℂ → ℝ, MemH j (fun x => (g x : ℂ)) →
      (∀ᵐ x, x ∉ ball (0 : ℂ) ρ → g x = 0) →
      MemH (j + 1) (fun x => (χ x : ℂ) * velocity g x) ∧
        normH (j + 1) (fun x => (χ x : ℂ) * velocity g x) ≤ C * normH j (fun x => (g x : ℂ)) := by
  obtain ⟨C, hC, hsm⟩ := exists_cutoffBS_smooth j hρ hχ hχc hχs
  refine ⟨C, hC, fun g hg hgs => ?_⟩
  set G : ℂ → ℂ := fun x => (g x : ℂ) with hG
  have h2ρ : (0 : ℝ) < 2 * ρ := by linarith
  have hball2 : ball (0 : ℂ) ρ ⊆ ball (0 : ℂ) (2 * ρ) := ball_subset_ball (by linarith)
  -- `g ∈ L²`
  have hGL2 : MemLp G 2 volume := (memH_iff.1 hg).1
  have hgL2 : MemLp g 2 volume := by simpa [G] using hGL2.re
  -- the approximants
  have hKV : closedBall (0 : ℂ) ρ ⊆ ball (0 : ℂ) (2 * ρ) := closedBall_subset_ball (by linarith)
  have hgK : ∀ᵐ x, x ∉ closedBall (0 : ℂ) ρ → G x = 0 := by
    filter_upwards [hgs] with x hx hxK
    simp [G, hx fun h => hxK (ball_subset_closedBall h)]
  obtain ⟨φ, hφ, hφmem, hφlim⟩ :=
    hg.exists_seq_testFn_tendsto (isCompact_closedBall _ _) isOpen_ball hKV hgK
  set gn : ℕ → ℂ → ℝ := fun n x => (φ n x).re with hgn
  have hgn_smooth : ∀ n, ContDiff ℝ ∞ (gn n) := fun n =>
    Complex.reCLM.contDiff.comp (hφ n).smooth
  have hgn_cpt : ∀ n, HasCompactSupport (gn n) := fun n =>
    (hφ n).compact.comp_left Complex.zero_re
  have hgn_ts : ∀ n, tsupport (gn n) ⊆ ball (0 : ℂ) (2 * ρ) := fun n =>
    (tsupport_comp_subset Complex.zero_re _).trans (hφ n).subset
  have hgn_int : ∀ n x, Integrable (fun y => biotSavartKernel (x - y) * (gn n y : ℂ)) volume :=
    fun n x => integrable_biotSavart_of_continuous (hgn_smooth n).continuous (hgn_cpt n) x
  have hgn_L2 : ∀ n, MemLp (gn n) 2 volume := fun n =>
    (hgn_smooth n).continuous.memLp_of_hasCompactSupport (hgn_cpt n)
  -- the errors `D n = g - g_n`
  set D : ℕ → ℂ → ℂ := fun n x => ((g x - gn n x : ℝ) : ℂ) with hDdef
  set e : ℕ → ℝ := fun n => normH j (G - φ n) with hedef
  have he : Tendsto e atTop (𝓝 0) := hφlim
  have hD : ∀ n, MemH j (D n) ∧ normH j (D n) ≤ e n := by
    intro n
    obtain ⟨hre, -, hsq⟩ := (hφmem n).re_im
    have heq : (fun x => (((G - φ n) x).re : ℂ)) = D n := by
      funext x
      simp [D, G, gn]
    rw [heq] at hre hsq
    refine ⟨hre, ?_⟩
    have hle : normH j (D n) ^ 2 ≤ normH j (G - φ n) ^ 2 := by
      rw [← hsq]
      nlinarith [sq_nonneg (normH j fun x => (((G - φ n) x).im : ℂ))]
    exact (pow_le_pow_iff_left₀ (normH_nonneg _ _) (normH_nonneg _ _) (by norm_num)).1 hle
  -- the sequence `u n = χ (K ∗ g_n)`
  set u : ℕ → ℂ → ℂ := fun n x => (χ x : ℂ) * velocity (gn n) x with hudef
  have hu : ∀ n, MemH (j + 1) (u n) ∧
      normH (j + 1) (u n) ≤ C * normH j (fun x => (gn n x : ℂ)) := fun n =>
    hsm (gn n) (hgn_smooth n) (hgn_cpt n) (hgn_ts n)
  -- Cauchy estimate
  have hcau : ∀ n m, normH (j + 1) (u n - u m) ≤ C * e n + C * e m := by
    intro n m
    have hfun : u n - u m = fun x => (χ x : ℂ) * velocity (fun y => gn n y - gn m y) x := by
      funext x
      simp only [Pi.sub_apply, u]
      rw [velocity_sub_of_integrable (hgn_int n x) (hgn_int m x)]
      ring
    have hts : tsupport (fun y => gn n y - gn m y) ⊆ ball (0 : ℂ) (2 * ρ) :=
      (tsupport_sub _ _).trans (union_subset (hgn_ts n) (hgn_ts m))
    have hcs : HasCompactSupport (fun y => gn n y - gn m y) :=
      (hgn_cpt n).sub (hgn_cpt m)
    obtain ⟨-, hb⟩ := hsm _ ((hgn_smooth n).sub (hgn_smooth m)) hcs hts
    have hDeq : (fun x => (((gn n x - gn m x : ℝ)) : ℂ)) = D m - D n := by
      funext x
      simp only [Pi.sub_apply, D]
      push_cast
      ring
    have hsub := ((hD m).1.sub (hD n).1).2
    rw [hfun]
    refine hb.trans ?_
    rw [hDeq]
    calc C * normH j (D m - D n) ≤ C * (normH j (D m) + normH j (D n)) :=
          mul_le_mul_of_nonneg_left hsub hC.le
      _ ≤ C * (e m + e n) :=
          mul_le_mul_of_nonneg_left (add_le_add (hD m).2 (hD n).2) hC.le
      _ = C * e n + C * e m := by ring
  -- uniform bound
  have hbd : ∀ n, normH (j + 1) (u n) ≤ C * normH j G + C * e n := by
    intro n
    have hGeq : (fun x => (gn n x : ℂ)) = G - D n := by
      funext x
      simp only [Pi.sub_apply, D, G]
      push_cast
      ring
    have hadd := (hg.sub (hD n).1).2
    refine (hu n).2.trans ?_
    rw [hGeq]
    calc C * normH j (G - D n) ≤ C * (normH j G + normH j (D n)) :=
          mul_le_mul_of_nonneg_left hadd hC.le
      _ ≤ C * (normH j G + e n) :=
          mul_le_mul_of_nonneg_left (add_le_add le_rfl (hD n).2) hC.le
      _ = C * normH j G + C * e n := by ring
  -- the limit function
  obtain ⟨hgae, hvL2, -⟩ := BS.velocity_L2_ball_le hρ hρ hgL2 hgs
  have hχball : ∀ x, x ∉ ball (0 : ℂ) ρ → χ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hχs h)
  have hfind : (fun x => (χ x : ℂ) * velocity g x) =
      (ball (0 : ℂ) ρ).indicator (fun x => (χ x : ℂ) * velocity g x) := by
    funext x
    by_cases hx : x ∈ ball (0 : ℂ) ρ
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, hχball x hx]
      simp
  have hfmeas : AEStronglyMeasurable (fun x => (χ x : ℂ) * velocity g x) volume := by
    rw [hfind, aestronglyMeasurable_indicator_iff measurableSet_ball]
    exact (Complex.continuous_ofReal.comp hχ.continuous).aestronglyMeasurable.mul hvL2.1
  -- `L²` convergence
  obtain ⟨M, hM⟩ := hχc.exists_bound_of_continuous hχ.continuous
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hL2bound : ∀ n, eLpNorm (u n - fun x => (χ x : ℂ) * velocity g x) 2 volume ≤
      ENNReal.ofReal (M * (3 * ρ) * e n) := by
    intro n
    set h' : ℂ → ℝ := fun y => gn n y - g y with hh'
    have hh'L2 : MemLp h' 2 volume := (hgn_L2 n).sub hgL2
    have hh'supp : ∀ᵐ y, y ∉ ball (0 : ℂ) (2 * ρ) → h' y = 0 := by
      filter_upwards [hgs] with y hy hy2
      have h1 : gn n y = 0 := image_eq_zero_of_notMem_tsupport fun h => hy2 (hgn_ts n h)
      have h2 : g y = 0 := hy fun h => hy2 (hball2 h)
      simp [h', h1, h2]
    obtain ⟨-, -, hh'le⟩ := BS.velocity_L2_ball_le h2ρ hρ hh'L2 hh'supp
    have hpt : ∀ᵐ x, ‖(u n - fun x => (χ x : ℂ) * velocity g x) x‖ ≤
        M * ‖(ball (0 : ℂ) ρ).indicator (velocity h') x‖ := by
      filter_upwards [hgae] with x hx
      simp only [Pi.sub_apply, u]
      by_cases hxb : x ∈ ball (0 : ℂ) ρ
      · rw [indicator_of_mem hxb, ← mul_sub, ← velocity_sub_of_integrable (hgn_int n x) hx,
          norm_mul]
        have : ‖(χ x : ℂ)‖ ≤ M := by simpa using hM x
        exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
      · rw [hχball x hxb]
        simp only [Complex.ofReal_zero, zero_mul, sub_zero, norm_zero]
        exact mul_nonneg hM0 (norm_nonneg _)
    have hD2 : eLpNorm h' 2 volume ≤ ENNReal.ofReal (e n) := by
      have hcongr : eLpNorm h' 2 volume = eLpNorm (D n) 2 volume := by
        refine eLpNorm_congr_norm_ae (Eventually.of_forall fun x => ?_)
        simp only [h', D, Complex.norm_real, Real.norm_eq_abs]
        exact abs_sub_comm _ _
      have hDL2 : MemLp (D n) 2 volume := (memH_iff.1 (hD n).1).1
      rw [hcongr, ← ENNReal.ofReal_toReal hDL2.eLpNorm_ne_top]
      exact ENNReal.ofReal_le_ofReal (((hD n).1.l2_le).trans (hD n).2)
    have hen : 0 ≤ e n := normH_nonneg _ _
    calc eLpNorm (u n - fun x => (χ x : ℂ) * velocity g x) 2 volume
        ≤ ENNReal.ofReal M * eLpNorm ((ball (0 : ℂ) ρ).indicator (velocity h')) 2 volume :=
          eLpNorm_le_mul_eLpNorm_of_ae_le_mul hpt 2
      _ = ENNReal.ofReal M * eLpNorm (velocity h') 2 (volume.restrict (ball (0 : ℂ) ρ)) := by
          rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball]
      _ ≤ ENNReal.ofReal M * (ENNReal.ofReal (ρ + 2 * ρ) * ENNReal.ofReal (e n)) := by
          gcongr
          exact hh'le.trans (by gcongr)
      _ = ENNReal.ofReal (M * (3 * ρ) * e n) := by
          rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul hM0]
          congr 1
          ring
  have hL2 : Tendsto (fun n => eLpNorm (u n - fun x => (χ x : ℂ) * velocity g x) 2 volume)
      atTop (𝓝 0) := by
    have hlim : Tendsto (fun n => ENNReal.ofReal (M * (3 * ρ) * e n)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => M * (3 * ρ) * e n) atTop (𝓝 (M * (3 * ρ) * 0)) :=
        he.const_mul _
      rw [mul_zero] at h1
      simpa using ENNReal.tendsto_ofReal h1
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun n => zero_le) hL2bound
  -- conclusion
  have hε : Tendsto (fun n => C * e n) atTop (𝓝 0) := by
    simpa using he.const_mul C
  exact memH_of_cauchy (ε := fun n => C * e n) (fun n => (hu n).1) hcau hε hbd hfmeas hL2

end NonUniqueEuler.Sob
