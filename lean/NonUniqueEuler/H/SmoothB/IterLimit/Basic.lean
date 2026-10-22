import NonUniqueEuler.Defs.SmoothB.Iteration
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Helper for `prop:iter-limit`: generic calculus and limit lemmas

Helper of `P/SmoothB/IterLimit.lean` (`B_global_smooth.tex:381-473`). Generic facts, independent
of the iterates:
* `spaceD` of order `0` and `1` (`spaceD_zero`, `spaceD_one_zero`, `spaceD_zero_one`) and the
  derivative of a real function viewed as complex valued (`fderiv_ofReal_apply`);
* spatial derivatives of a `C^∞` space–time function are `C^∞` in `(t, x)` (`contDiff_spaceD`);
* a function that is the uniform limit of continuous functions on every slab
  `[-T, T] × ℝ²` is continuous (`continuous_of_tendstoUniformlyOn_slabs`);
* `L^p` norms pass to uniform limits of continuous functions vanishing outside a fixed ball
  (`eLpNorm_eq_of_tendstoUniformly`);
* an operator-norm bound passes to limits taken on the basis `1, i`
  (`norm_clm_le_of_tendsto`).
-/

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace NonUniqueEuler.Smooth.IterLimitAux

/-! ### Low-order spatial derivatives -/

theorem spaceD_zero (F : ℝ → ℂ → ℂ) (t : ℝ) (x : ℂ) : spaceD (0, 0) F t x = F t x := rfl

theorem spaceD_one_zero (F : ℝ → ℂ → ℂ) (t : ℝ) (x : ℂ) :
    spaceD (1, 0) F t x = fderiv ℝ (F t) x 1 := rfl

theorem spaceD_zero_one (F : ℝ → ℂ → ℂ) (t : ℝ) (x : ℂ) :
    spaceD (0, 1) F t x = fderiv ℝ (F t) x Complex.I := rfl

/-- The derivative of a real function viewed as complex valued. -/
theorem fderiv_ofReal_apply {g : ℂ → ℝ} {x : ℂ} (hg : DifferentiableAt ℝ g x) (v : ℂ) :
    fderiv ℝ (fun y => (g y : ℂ)) x v = ((fderiv ℝ g x v : ℝ) : ℂ) := by
  have hd : HasFDerivAt (fun y => (g y : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ g x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x hg.hasFDerivAt
  rw [hd.fderiv]
  rfl

/-! ### Joint smoothness of spatial derivatives -/

theorem contDiff_iterDirDeriv_uncurry {F : ℝ → ℂ → ℂ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry F)) (vs : List ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℂ => Sob.iterDirDeriv vs (F p.1) p.2) := by
  induction vs with
  | nil => exact hF
  | cons v vs ih =>
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (Function.uncurry fun (p : ℝ × ℂ) (y : ℂ) => Sob.iterDirDeriv vs (F p.1) y) :=
      ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
    exact h1.fderiv_apply contDiff_snd contDiff_const (by simp)

/-- Spatial derivatives of a `C^∞` space–time function are `C^∞` in `(t, x)`. -/
theorem contDiff_spaceD {F : ℝ → ℂ → ℂ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry F)) (γ : ℕ × ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℂ => spaceD γ F p.1 p.2) :=
  contDiff_iterDirDeriv_uncurry hF _

theorem contDiff_ofRealST {f : ℝ → ℂ → ℝ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry f)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry (ofRealST f)) :=
  Complex.ofRealCLM.contDiff.comp hf

/-- A slice `x ↦ f(t, x)` of a `C^∞` space–time function is `C^∞`. -/
theorem contDiff_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → ℂ → E}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry f)) (t : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f t) :=
  hf.comp (contDiff_const.prodMk contDiff_id)

/-! ### Uniform limits on slabs -/

theorem mem_nhds_slab (p : ℝ × ℂ) :
    Icc (-(|p.1| + 1)) (|p.1| + 1) ×ˢ (univ : Set ℂ) ∈ 𝓝 p := by
  refine mem_of_superset ((isOpen_Ioo.prod isOpen_univ).mem_nhds ?_)
    (prod_mono Ioo_subset_Icc_self subset_rfl)
  refine ⟨⟨?_, ?_⟩, mem_univ _⟩
  · linarith [neg_abs_le p.1]
  · linarith [le_abs_self p.1]

theorem mem_slab (p : ℝ × ℂ) : p ∈ Icc (-(|p.1| + 1)) (|p.1| + 1) ×ˢ (univ : Set ℂ) :=
  mem_of_mem_nhds (mem_nhds_slab p)

/-- The uniform limit on every slab of continuous functions is continuous. -/
theorem continuous_of_tendstoUniformlyOn_slabs {F : ℕ → ℝ × ℂ → ℂ} {f : ℝ × ℂ → ℂ}
    (hF : ∀ j, Continuous (F j))
    (h : ∀ T : ℝ, 0 < T → TendstoUniformlyOn F f atTop (Icc (-T) T ×ˢ univ)) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  have hT : 0 < |p.1| + 1 := by positivity
  have hcont : ContinuousOn f (Icc (-(|p.1| + 1)) (|p.1| + 1) ×ˢ univ) :=
    (h _ hT).continuousOn (Frequently.of_forall fun j => (hF j).continuousOn)
  exact hcont.continuousAt (mem_nhds_slab p)

/-! ### `L^p` norms of uniform limits -/

/-- `L^p` norms (`p ≥ 1`) pass to uniform limits of continuous functions vanishing outside a
fixed ball. -/
theorem eLpNorm_eq_of_tendstoUniformly {f : ℕ → ℂ → ℝ} {g : ℂ → ℝ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {ρ : ℝ} {c : ℝ≥0∞} (hf : ∀ j, Continuous (f j)) (hg : Continuous g)
    (hfs : ∀ j x, ρ < ‖x‖ → f j x = 0) (hgs : ∀ x, ρ < ‖x‖ → g x = 0)
    (hconv : TendstoUniformly f g atTop) (hc : ∀ j, eLpNorm (f j) p volume = c) :
    eLpNorm g p volume = c := by
  set M : ℝ≥0∞ := volume (closedBall (0 : ℂ) ρ) ^ p.toReal⁻¹ with hM
  have hMtop : M ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
      measure_closedBall_lt_top.ne
  -- the error bound
  have herr : ∀ ε : ℝ, 0 < ε → ∃ j, eLpNorm (g - f j) p volume ≤ M * ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨j, hj⟩ := (Metric.tendstoUniformly_iff.1 hconv ε hε).exists
    refine ⟨j, ?_⟩
    have hsupp : Function.support (g - f j) ⊆ closedBall (0 : ℂ) ρ := by
      intro x hx
      by_contra hxb
      have hx' : ρ < ‖x‖ := by simpa [mem_closedBall, dist_zero_right, not_le] using hxb
      exact hx (by simp [hgs x hx', hfs j x hx'])
    rw [← eLpNorm_restrict_eq_of_support_subset hsupp]
    have hb : ∀ᵐ x ∂(volume.restrict (closedBall (0 : ℂ) ρ)), ‖(g - f j) x‖ ≤ ε :=
      Eventually.of_forall fun x => by
        have := (hj x).le
        rwa [dist_eq_norm] at this
    refine (eLpNorm_le_of_ae_bound hb).trans ?_
    rw [Measure.restrict_apply_univ]
  -- the error tends to zero
  have hlim : Tendsto (fun ε : ℝ => M * ENNReal.ofReal ε) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun ε : ℝ => ENNReal.ofReal ε) (𝓝[>] 0) (𝓝 0) := by
      have := (ENNReal.continuous_ofReal.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa using this
    simpa using ENNReal.Tendsto.const_mul h0 (Or.inr hMtop)
  have hmf : ∀ j, AEStronglyMeasurable (f j) volume := fun j =>
    (hf j).aestronglyMeasurable
  have hmg : AEStronglyMeasurable g volume := hg.aestronglyMeasurable
  apply le_antisymm
  · -- `‖g‖ ≤ ‖f j‖ + ‖g - f j‖`
    have hbound : ∀ ε : ℝ, 0 < ε → eLpNorm g p volume ≤ c + M * ENNReal.ofReal ε := by
      intro ε hε
      obtain ⟨j, hj⟩ := herr ε hε
      calc eLpNorm g p volume = eLpNorm (f j + (g - f j)) p volume := by
            congr 1; abel
        _ ≤ eLpNorm (f j) p volume + eLpNorm (g - f j) p volume :=
            eLpNorm_add_le (hmf j) (hmg.sub (hmf j)) hp
        _ ≤ c + M * ENNReal.ofReal ε := by rw [hc j]; gcongr
    have ht : Tendsto (fun ε : ℝ => c + M * ENNReal.ofReal ε) (𝓝[>] 0) (𝓝 (c + 0)) :=
      tendsto_const_nhds.add hlim
    rw [add_zero] at ht
    exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε => hbound ε hε)
  · have hbound : ∀ ε : ℝ, 0 < ε → c ≤ eLpNorm g p volume + M * ENNReal.ofReal ε := by
      intro ε hε
      obtain ⟨j, hj⟩ := herr ε hε
      calc c = eLpNorm (g + (f j - g)) p volume := by
            rw [← hc j]; congr 1; abel
        _ ≤ eLpNorm g p volume + eLpNorm (f j - g) p volume :=
            eLpNorm_add_le hmg ((hmf j).sub hmg) hp
        _ ≤ eLpNorm g p volume + M * ENNReal.ofReal ε := by
            rw [eLpNorm_sub_comm]; gcongr
    have ht : Tendsto (fun ε : ℝ => eLpNorm g p volume + M * ENNReal.ofReal ε) (𝓝[>] 0)
        (𝓝 (eLpNorm g p volume + 0)) :=
      tendsto_const_nhds.add hlim
    rw [add_zero] at ht
    exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε => hbound ε hε)

/-! ### Operator norms -/

theorem clm_apply_eq_re_im {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : ℂ →L[ℝ] E) (v : ℂ) : L v = v.re • L 1 + v.im • L Complex.I := by
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul]

/-- An operator-norm bound passes to a limit taken on the basis `1, i`. -/
theorem norm_clm_le_of_tendsto {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L : ℕ → ℂ →L[ℝ] E} {L' : ℂ →L[ℝ] E} {B : ℝ} (hB : 0 ≤ B)
    (h1 : Tendsto (fun j => L j 1) atTop (𝓝 (L' 1)))
    (hI : Tendsto (fun j => L j Complex.I) atTop (𝓝 (L' Complex.I)))
    (hb : ∀ j, ‖L j‖ ≤ B) : ‖L'‖ ≤ B := by
  refine ContinuousLinearMap.opNorm_le_bound _ hB fun v => ?_
  have hv : Tendsto (fun j => L j v) atTop (𝓝 (L' v)) := by
    simp only [clm_apply_eq_re_im _ v]
    exact (h1.const_smul v.re).add (hI.const_smul v.im)
  exact le_of_tendsto' hv.norm fun j => ((L j).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (hb j) (norm_nonneg v))

end NonUniqueEuler.Smooth.IterLimitAux
