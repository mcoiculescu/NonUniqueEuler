import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import NonUniqueEuler.Defs.Infra.SobolevSpace
import NonUniqueEuler.Defs.Infra.Polar
import NonUniqueEuler.Statement.Plane
import NonUniqueEuler.I.Infra.Sobolev.Space
import NonUniqueEuler.I.Infra.Sobolev.Symmetry
import NonUniqueEuler.I.Infra.Sobolev.Density
import NonUniqueEuler.I.Infra.Sobolev.Local
import NonUniqueEuler.I.Infra.Sobolev.Smooth
import NonUniqueEuler.I.Infra.CkNorm.Continuity

/-!
# Proof of `I/Infra/AngularFourier/Derivatives/RotPath.lean`: rotations act continuously on `H^k`

For `g ∈ H^k`, the path `θ ↦ g ∘ O_θ` is continuous into the Hilbert space `Sob.Hk k`.
Manuscript: `04_ring.tex:181-185` ("rotations act on `H^s(ℝ²)`").

Proof (the sketch of the interface file).
1. Test functions `ψ` (`continuous_toHk_comp_rot_testFn`): the family `h θ = ψ ∘ O_θ` is jointly
   smooth and supported in `closedBall 0 R`, so
   `‖toHk (h θ) - toHk (h θ₀)‖ = ‖h θ - h θ₀‖_{H^k} = ‖h θ - h θ₀‖_{H^k(B_{R+1})}
   ≤ (k+1) |B_{R+1}|^{1/2} ‖h θ - h θ₀‖_{C^k(closedBall 0 (R+1))} → 0`.
2. General `g`: uniform approximation by `ψ ∘ O_θ` with `ψ` a test function,
   `‖toHk (g ∘ O_θ) - toHk (ψ ∘ O_θ)‖ ≤ 2^k ‖g - ψ‖_{H^k}` for every `θ`
   (`continuous_of_uniform_approx_of_continuous`).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace NonUniqueEuler.Sob

namespace RotPathAux

/-- Joint smoothness of `(θ, x) ↦ O_θ x`. -/
theorem contDiff_rot_joint : ContDiff ℝ ∞ (fun p : ℝ × ℂ => rot p.1 p.2) := by
  unfold rot
  have h1 : ContDiff ℝ ∞ (fun p : ℝ × ℂ => ((p.1 : ℂ) * Complex.I)) :=
    (Complex.ofRealCLM.contDiff.comp contDiff_fst).mul contDiff_const
  exact (Complex.contDiff_exp.comp h1).mul contDiff_snd

theorem contDiff_rot (θ : ℝ) : ContDiff ℝ ∞ (rot θ) := by
  unfold rot
  exact contDiff_const.mul contDiff_id

/-- `ψ ∘ O_θ` vanishes off `closedBall 0 R` when `tsupport ψ ⊆ closedBall 0 R`. -/
theorem comp_rot_eq_zero {ψ : ℂ → ℂ} {R : ℝ} (hR : tsupport ψ ⊆ Metric.closedBall 0 R)
    (θ : ℝ) {x : ℂ} (hx : x ∉ Metric.closedBall (0 : ℂ) R) : ψ (rot θ x) = 0 := by
  refine image_eq_zero_of_notMem_tsupport fun hmem => hx ?_
  have := hR hmem
  rwa [Metric.mem_closedBall, dist_zero_right, Polar.norm_rot, ← dist_zero_right] at this

theorem isTestFn_comp_rot {ψ : ℂ → ℂ} (hψ : IsTestFn univ ψ) (θ : ℝ) :
    IsTestFn univ (fun x => ψ (rot θ x)) := by
  obtain ⟨R, hR⟩ := hψ.compact.isCompact.isBounded.subset_closedBall 0
  refine ⟨hψ.smooth.comp (contDiff_rot θ), ?_, subset_univ _⟩
  exact HasCompactSupport.intro (isCompact_closedBall 0 R) fun x hx => comp_rot_eq_zero hR θ hx

/-- Step 1: for a test function `ψ`, `θ ↦ ψ ∘ O_θ` is continuous into `Hk k`. -/
theorem continuous_toHk_comp_rot_testFn {k : ℕ} {ψ : ℂ → ℂ} (hψ : IsTestFn univ ψ) :
    Continuous (fun θ : ℝ => toHk k (fun x => ψ (rot θ x))) := by
  obtain ⟨R, hR⟩ := hψ.compact.isCompact.isBounded.subset_closedBall 0
  set h : ℝ → ℂ → ℂ := fun θ x => ψ (rot θ x) with hh_def
  have hjoint : ContDiff ℝ ∞ (fun p : ℝ × ℂ => h p.1 p.2) := hψ.smooth.comp contDiff_rot_joint
  set U : Set ℂ := Metric.closedBall 0 (R + 1) with hU_def
  set V : Set ℂ := Metric.ball 0 (R + 1) with hV_def
  have hU : IsCompact U := isCompact_closedBall 0 (R + 1)
  have hV : IsOpen V := Metric.isOpen_ball
  have hVU : V ⊆ U := Metric.ball_subset_closedBall
  have hVfin : volume V < ⊤ := measure_ball_lt_top
  have hKV : Metric.closedBall (0 : ℂ) R ⊆ V := Metric.closedBall_subset_ball (lt_add_one R)
  set C : ℝ := ((k : ℝ) + 1) * Real.sqrt (volume V).toReal with hC_def
  have key : ∀ θ₀ θ : ℝ, dist (toHk k (h θ)) (toHk k (h θ₀)) ≤ C * normCk k U (h θ - h θ₀) := by
    intro θ₀ θ
    have hT0 : IsTestFn univ (h θ₀) := isTestFn_comp_rot hψ θ₀
    have hT : IsTestFn univ (h θ) := isTestFn_comp_rot hψ θ
    have hD : IsTestFn univ (h θ - h θ₀) :=
      ⟨hT.smooth.sub hT0.smooth, hT.compact.sub hT0.compact, subset_univ _⟩
    have hsplit : toHk k (h θ) = toHk k (h θ - h θ₀) + toHk k (h θ₀) := by
      rw [← toHk_add (hD.memH k) (hT0.memH k), sub_add_cancel]
    rw [dist_eq_norm, hsplit, add_sub_cancel_right, norm_toHk (hD.memH k)]
    have hfK : ∀ᵐ x, x ∉ Metric.closedBall (0 : ℂ) R → (h θ - h θ₀) x = 0 :=
      Filter.Eventually.of_forall fun x hx => by
        simp [h, comp_rot_eq_zero hR θ hx, comp_rot_eq_zero hR θ₀ hx]
    have hloc := (memHOn_iff_memH_of_support (k := k) (isCompact_closedBall 0 R) hV hKV hfK).2
      (hD.memH k)
    have hdiff : ContDiffOn ℝ k (fun p : ℝ × ℂ => (fun t => h t - h θ₀) p.1 p.2) univ := by
      have h2 : ContDiff ℝ ∞ (fun p : ℝ × ℂ => h θ₀ p.2) :=
        hT0.smooth.comp contDiff_snd
      exact (contDiff_infty.1 (hjoint.sub h2) k).contDiffOn
    have hCk : MemCk k U (h θ - h θ₀) :=
      memCk_slice_of_contDiffOn (h := fun t => h t - h θ₀) hU isOpen_univ (subset_univ _) hdiff
        (mem_univ θ)
    rw [← hloc]
    exact (MemCk.memHOn hV hVU hVfin hCk).2
  refine continuous_iff_continuousAt.2 fun θ₀ => ?_
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have ht := tendsto_normCk_sub_of_contDiffOn (k := k) hU isOpen_univ (subset_univ _)
    (contDiff_infty.1 hjoint k).contDiffOn (mem_univ θ₀)
  rw [nhdsWithin_univ] at ht
  refine squeeze_zero (fun θ => dist_nonneg) (fun θ => key θ₀ θ) ?_
  simpa using ht.const_mul C

end RotPathAux

open RotPathAux in
/-- Rotations act continuously on `H^k`: `θ ↦ g ∘ O_θ` is a continuous path in `Hk k`. -/
theorem continuous_toHk_comp_rot {k : ℕ} {g : ℂ → ℂ} (hg : MemH k g) :
    Continuous (fun θ : ℝ => toHk k (fun x => g (rot θ x))) := by
  refine continuous_of_uniform_approx_of_continuous fun u hu => ?_
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.1 hu
  have hpos : (0 : ℝ) < ε / (2 * 2 ^ k) := by positivity
  obtain ⟨ψ, hψ, hdiff, hlt⟩ := hg.exists_testFn_approx hpos
  refine ⟨_, continuous_toHk_comp_rot_testFn (k := k) hψ, fun θ => hεu ?_⟩
  have hψθ := isTestFn_comp_rot hψ θ
  obtain ⟨hDθ, hDle⟩ := hdiff.comp_rot θ
  have hsplit : (fun x => g (rot θ x)) =
      (fun x => (g - ψ) (rot θ x)) + fun x => ψ (rot θ x) := by
    funext x; simp
  show dist (toHk k (fun x => g (rot θ x))) (toHk k (fun x => ψ (rot θ x))) < ε
  rw [hsplit, toHk_add hDθ (hψθ.memH k), dist_eq_norm, add_sub_cancel_right, norm_toHk hDθ]
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  calc normH k (fun x => (g - ψ) (rot θ x)) ≤ 2 ^ k * normH k (g - ψ) := hDle
    _ ≤ 2 ^ k * (ε / (2 * 2 ^ k)) := by gcongr
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

end NonUniqueEuler.Sob
