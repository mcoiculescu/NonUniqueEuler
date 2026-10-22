import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.Algebra.Module.FiniteDimension
import NonUniqueEuler.Vendor.ODE.GlobalPicard

/-!
# Proof of `I/SmoothB/ODE/LinearFlow.lean`: the linear variational equation with parameters

Sub-step of `lem:ode`(ii), `B_global_smooth.tex:30-35` (the variational equation, cited from
Teschl, Theorem 2.10).

Proof, following the docstring of the interface file:
1. `LinearFlowH.exists_global_solution_of_lipschitzOn`: global existence for a jointly
   continuous field that is Lipschitz in the state, uniformly for times in each `[-R, R]`.
   The field is clamped in time (`projIcc`), the vendored global Picard theorem
   (`Vendor.GlobalPicard.exists_global_solution`) is applied, and the solutions on `[-R, R]` are
   glued by uniqueness (`ODE_solution_unique_of_mem_Ioo`), as in the vendored proof.
2. `LinearFlowH.dist_le_gronwall_twoSided`: the approximate-trajectory Grönwall estimate
   (`dist_le_of_approx_trajectories_ODE_of_mem`) on `[-R, R]`, from time `0` in both directions
   (the backward direction by time reversal).
3. Joint continuity at `(r₀, p₀)`: tube lemma (`IsCompact.eventually_forall_of_forall_eventually`)
   for `sup_{|t| ≤ R} ‖B t p - B t p₀‖`, then step 2 with `f = A(·, p₀)` an approximate solution
   of the equation of `p`, and `g = A(·, p)` an exact one.
-/

noncomputable section

open Set Function Filter Metric
open scoped Topology NNReal

namespace NonUniqueEuler.Smooth

namespace LinearFlowH

/-- Global existence for a jointly continuous time-dependent field that is Lipschitz in the
state variable, uniformly for times in each compact interval `[-R, R]`. -/
theorem exists_global_solution_of_lipschitzOn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E → E} (hf : Continuous (uncurry f))
    (hLip : ∀ R : ℝ, ∃ K : ℝ≥0, ∀ t ∈ Icc (-R) R, LipschitzWith K (f t)) (x : E) :
    ∃ u : ℝ → E, u 0 = x ∧ ∀ t, HasDerivAt u (f t (u t)) t := by
  classical
  have hlocal : ∀ R : ℝ, 0 < R → ∃ u : ℝ → E, u 0 = x ∧
      ∀ t ∈ Icc (-R) R, HasDerivAt u (f t (u t)) t := by
    intro R hR
    obtain ⟨K, hK⟩ := hLip R
    have hRR : -R ≤ R := by linarith
    let g : ℝ → E → E := fun t y => f (projIcc (-R) R hRR t) y
    have hg : Continuous (uncurry g) :=
      hf.comp ((continuous_subtype_val.comp
        ((continuous_projIcc (h := hRR)).comp continuous_fst)).prodMk continuous_snd)
    have hgL : ∀ t, LipschitzWith K (g t) := fun t => hK _ (projIcc (-R) R hRR t).2
    obtain ⟨u, hu0, hud⟩ := NonUniqueEuler.Vendor.GlobalPicard.exists_global_solution hg hgL x
    refine ⟨u, hu0, fun t ht => ?_⟩
    have h := hud t
    have hgt : g t = f t := by
      funext y
      simp only [g, projIcc_of_mem hRR ht]
    rwa [hgt] at h
  choose v hv0 hvd using hlocal
  let u : ℝ → E := fun t => v (|t| + 1) (by positivity) t
  have hagree : ∀ R (hR : 0 < R), EqOn u (v R hR) (Ioo (-R) R) := by
    intro R hR s hs
    let R' := |s| + 1
    have hR' : 0 < R' := by dsimp [R']; positivity
    let B := min R R'
    have hB : 0 < B := lt_min hR hR'
    have hBR : B ≤ R := min_le_left _ _
    have hBR' : B ≤ R' := min_le_right _ _
    have hzero : (0 : ℝ) ∈ Ioo (-B) B := by constructor <;> linarith
    have hsB : s ∈ Ioo (-B) B := by
      apply abs_lt.mp
      apply lt_min (abs_lt.mpr hs)
      dsimp [R']
      linarith
    obtain ⟨K, hK⟩ := hLip B
    have heq := ODE_solution_unique_of_mem_Ioo (v := f) (s := fun _ => (univ : Set E)) (K := K)
      (fun t ht => (hK t (Ioo_subset_Icc_self ht)).lipschitzOnWith) hzero
      (fun t ht => ⟨hvd R hR t (by constructor <;> linarith [ht.1, ht.2]), mem_univ _⟩)
      (fun t ht => ⟨hvd R' hR' t (by constructor <;> linarith [ht.1, ht.2]), mem_univ _⟩)
      (by rw [hv0 R hR, hv0 R' hR'])
    exact (heq hsB).symm
  refine ⟨u, ?_, ?_⟩
  · exact hv0 (|0| + 1) (by positivity)
  · intro t
    let R := |t| + 1
    have hR : 0 < R := by dsimp [R]; positivity
    have ht : t ∈ Ioo (-R) R := by
      apply abs_lt.mp
      dsimp [R]
      linarith
    have heq : u =ᶠ[𝓝 t] v R hR := Filter.eventually_of_mem
      (Ioo_mem_nhds ht.1 ht.2) (fun s hs => hagree R hR hs)
    have hd := hvd R hR t (Ioo_subset_Icc_self ht)
    rw [hagree R hR ht]
    exact hd.congr_of_eventuallyEq heq

/-- Derivative of a time reversal. -/
theorem hasDerivAt_comp_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {f' : E} {t : ℝ} (hf : HasDerivAt f f' (-t)) :
    HasDerivAt (fun s => f (-s)) (-f') t := by
  have h := HasDerivAt.comp_const_sub (0 : ℝ) t (by simpa using hf)
  simpa using h

/-- Forward Grönwall estimate for approximate trajectories on `[0, R]`, with full derivatives. -/
theorem dist_le_gronwall_forward {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ℝ → E → E} {K : ℝ≥0} {R : ℝ} {f g f' g' : ℝ → E} {εf εg δ : ℝ}
    (hv : ∀ t ∈ Icc 0 R, LipschitzWith K (v t))
    (hf : ∀ t ∈ Icc 0 R, HasDerivAt f (f' t) t)
    (hg : ∀ t ∈ Icc 0 R, HasDerivAt g (g' t) t)
    (f_bound : ∀ t ∈ Icc 0 R, dist (f' t) (v t (f t)) ≤ εf)
    (g_bound : ∀ t ∈ Icc 0 R, dist (g' t) (v t (g t)) ≤ εg)
    (h0 : dist (f 0) (g 0) ≤ δ) :
    ∀ t ∈ Icc 0 R, dist (f t) (g t) ≤ gronwallBound δ K (εf + εg) t := by
  intro t ht
  have h := dist_le_of_approx_trajectories_ODE_of_mem (s := fun _ => (univ : Set E))
    (fun t ht => (hv t (Ico_subset_Icc_self ht)).lipschitzOnWith)
    (fun t ht => (hf t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hf t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht => f_bound t (Ico_subset_Icc_self ht)) (fun _ _ => mem_univ _)
    (fun t ht => (hg t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hg t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht => g_bound t (Ico_subset_Icc_self ht)) (fun _ _ => mem_univ _) h0 t ht
  simpa using h

/-- Two-sided Grönwall estimate for approximate trajectories on `[-R, R]`, starting from
time `0`. -/
theorem dist_le_gronwall_twoSided {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ℝ → E → E} {K : ℝ≥0} {R : ℝ} {f g f' g' : ℝ → E} {εf εg δ : ℝ}
    (hv : ∀ t ∈ Icc (-R) R, LipschitzWith K (v t))
    (hf : ∀ t ∈ Icc (-R) R, HasDerivAt f (f' t) t)
    (hg : ∀ t ∈ Icc (-R) R, HasDerivAt g (g' t) t)
    (f_bound : ∀ t ∈ Icc (-R) R, dist (f' t) (v t (f t)) ≤ εf)
    (g_bound : ∀ t ∈ Icc (-R) R, dist (g' t) (v t (g t)) ≤ εg)
    (h0 : dist (f 0) (g 0) ≤ δ) :
    ∀ t ∈ Icc (-R) R, dist (f t) (g t) ≤ gronwallBound δ K (εf + εg) |t| := by
  have hsub : ∀ t ∈ Icc 0 R, t ∈ Icc (-R) R := fun t ht => ⟨by linarith [ht.1, ht.2], ht.2⟩
  have hsubn : ∀ t ∈ Icc 0 R, -t ∈ Icc (-R) R := fun t ht =>
    ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩
  intro t ht
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h]
    exact dist_le_gronwall_forward (fun s hs => hv s (hsub s hs)) (fun s hs => hf s (hsub s hs))
      (fun s hs => hg s (hsub s hs)) (fun s hs => f_bound s (hsub s hs))
      (fun s hs => g_bound s (hsub s hs)) h0 t ⟨h, ht.2⟩
  · rw [abs_of_nonpos h]
    have hb := dist_le_gronwall_forward (R := R) (K := K) (v := fun s y => -v (-s) y)
      (f := fun s => f (-s)) (g := fun s => g (-s)) (f' := fun s => -f' (-s))
      (g' := fun s => -g' (-s))
      (fun s hs => (hv (-s) (hsubn s hs)).neg)
      (fun s hs => hasDerivAt_comp_neg (by simpa using hf (-s) (hsubn s hs)))
      (fun s hs => hasDerivAt_comp_neg (by simpa using hg (-s) (hsubn s hs)))
      (fun s hs => by simpa only [dist_neg_neg] using f_bound (-s) (hsubn s hs))
      (fun s hs => by simpa only [dist_neg_neg] using g_bound (-s) (hsubn s hs))
      (by simpa using h0) (-t) ⟨by linarith, by linarith [ht.1]⟩
    simpa using hb

end LinearFlowH

open LinearFlowH in
/-- The linear variational equation `Ȧ = B(r, p) ∘ A`, `A(0) = id`, with a jointly continuous
coefficient has a global, jointly continuous solution (sub-step of `lem:ode`(ii)). -/
theorem exists_linearVariationalFlow {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] {P : Type*} [TopologicalSpace P] {B : ℝ → P → (W →L[ℝ] W)}
    (hB : Continuous (Function.uncurry B)) :
    ∃ A : ℝ → P → (W →L[ℝ] W), Continuous (Function.uncurry A) ∧
      (∀ p, A 0 p = ContinuousLinearMap.id ℝ W) ∧
      ∀ r p, HasDerivAt (fun r => A r p) ((B r p).comp (A r p)) r := by
  have : CompleteSpace W := FiniteDimensional.complete ℝ W
  -- continuity of `t ↦ B t p`
  have hBt : ∀ p, Continuous fun t => B t p := fun p =>
    hB.comp (continuous_id.prodMk continuous_const)
  -- bounds of `B` on compact time intervals
  have hBbd : ∀ p (R : ℝ), ∃ C : ℝ, ∀ t ∈ Icc (-R) R, ‖B t p‖ ≤ C := fun p R =>
    isCompact_Icc.exists_bound_of_continuousOn (hBt p).continuousOn
  -- Lipschitz estimate for `X ↦ M ∘ X`
  have hcompLip : ∀ (M : W →L[ℝ] W) (C : ℝ), ‖M‖ ≤ C →
      LipschitzWith (Real.toNNReal C) (fun X : W →L[ℝ] W => M.comp X) := by
    intro M C hM
    refine LipschitzWith.of_dist_le' fun X Y => ?_
    rw [dist_eq_norm, dist_eq_norm, ← ContinuousLinearMap.comp_sub]
    calc ‖M.comp (X - Y)‖ ≤ ‖M‖ * ‖X - Y‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C * ‖X - Y‖ := by gcongr
  -- existence for each fixed parameter
  have hex : ∀ p, ∃ u : ℝ → (W →L[ℝ] W), u 0 = ContinuousLinearMap.id ℝ W ∧
      ∀ t, HasDerivAt u ((B t p).comp (u t)) t := by
    intro p
    refine exists_global_solution_of_lipschitzOn (f := fun t X => (B t p).comp X) ?_ ?_ _
    · exact ((hBt p).comp continuous_fst).clm_comp continuous_snd
    · intro R
      obtain ⟨C, hC⟩ := hBbd p R
      exact ⟨Real.toNNReal C, fun t ht => hcompLip _ _ (hC t ht)⟩
  choose U hU0 hUd using hex
  refine ⟨fun r p => U p r, ?_, hU0, fun r p => hUd p r⟩
  -- joint continuity
  rw [continuous_iff_continuousAt]
  rintro ⟨r₀, p₀⟩
  rw [Metric.continuousAt_iff']
  intro ε hε
  set R : ℝ := |r₀| + 1 with hRdef
  have hR0 : 0 ≤ R := by positivity
  obtain ⟨CB, hCB⟩ := hBbd p₀ R
  have hU₀c : Continuous (U p₀) := continuous_iff_continuousAt.2 fun t => (hUd p₀ t).continuousAt
  obtain ⟨CA, hCA⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-R) R) hU₀c.continuousOn
  set K' : ℝ := max CB 0 + 1 with hK'def
  have hK'0 : 0 < K' := by positivity
  set CA' : ℝ := max CA 0 with hCA'def
  have hCA'0 : 0 ≤ CA' := le_max_right _ _
  -- choice of the tube size `η`
  have hlim : Tendsto (fun η : ℝ => gronwallBound 0 K' (η * CA') R) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun η : ℝ => gronwallBound 0 K' (η * CA') R :=
      (gronwallBound_continuous_ε 0 K' R).comp (continuous_id.mul continuous_const)
    have h := hc.tendsto 0
    simp only [zero_mul, gronwallBound_ε0_δ0] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hη1 : ∀ᶠ η : ℝ in 𝓝[>] 0, η < 1 :=
    (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  have hηpos : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < η := self_mem_nhdsWithin
  obtain ⟨η, hηg, hηlt, hηp⟩ :=
    ((hlim.eventually (gt_mem_nhds (half_pos hε))).and (hη1.and hηpos)).exists
  -- tube lemma
  have htube : ∀ᶠ p in 𝓝 p₀, ∀ t ∈ Icc (-R) R, ‖B t p - B t p₀‖ < η := by
    refine isCompact_Icc.eventually_forall_of_forall_eventually fun t _ => ?_
    have hc : Continuous fun z : P × ℝ => B z.2 z.1 - B z.2 p₀ :=
      (hB.comp continuous_swap).sub ((hBt p₀).comp continuous_snd)
    have h := hc.tendsto (p₀, t)
    simp only [sub_self] at h
    filter_upwards [h.eventually (Metric.ball_mem_nhds (0 : W →L[ℝ] W) hηp)] with z hz
    simpa [dist_eq_norm] using hz
  -- the Grönwall comparison for parameters in the tube
  have hclose : ∀ᶠ p in 𝓝 p₀, ∀ t ∈ Icc (-R) R, dist (U p₀ t) (U p t) < ε / 2 := by
    filter_upwards [htube] with p hp t ht
    have hBp : ∀ s ∈ Icc (-R) R, ‖B s p‖ ≤ K' := by
      intro s hs
      have h1 := hCB s hs
      have h2 := (hp s hs).le
      have h3 : ‖B s p‖ ≤ ‖B s p - B s p₀‖ + ‖B s p₀‖ := norm_le_norm_sub_add _ _
      have h4 : CB ≤ max CB 0 := le_max_left _ _
      linarith
    have hK'nn : (Real.toNNReal K' : ℝ) = K' := Real.coe_toNNReal _ hK'0.le
    have hg := dist_le_gronwall_twoSided (v := fun s X => (B s p).comp X)
      (K := Real.toNNReal K') (f := U p₀) (g := U p)
      (f' := fun s => (B s p₀).comp (U p₀ s)) (g' := fun s => (B s p).comp (U p s))
      (εf := η * CA') (εg := 0) (δ := 0)
      (fun s hs => hcompLip _ _ (hBp s hs)) (fun s _ => hUd p₀ s) (fun s _ => hUd p s)
      (fun s hs => by
        rw [dist_eq_norm, ← ContinuousLinearMap.sub_comp]
        calc ‖(B s p₀ - B s p).comp (U p₀ s)‖ ≤ ‖B s p₀ - B s p‖ * ‖U p₀ s‖ :=
              ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ η * CA' := by
              rw [norm_sub_rev]
              gcongr
              · exact (hp s hs).le
              · exact (hCA s hs).trans (le_max_left _ _))
      (fun s _ => by simp)
      (by simp [hU0]) t ht
    rw [add_zero, hK'nn] at hg
    have hmono : gronwallBound 0 K' (η * CA') |t| ≤ gronwallBound 0 K' (η * CA') R :=
      gronwallBound_mono le_rfl (mul_nonneg hηp.le hCA'0) hK'0.le (abs_le.2 ⟨by linarith [ht.1],
        ht.2⟩)
    linarith
  -- combine
  have hr : ∀ᶠ r in 𝓝 r₀, r ∈ Icc (-R) R ∧ dist (U p₀ r) (U p₀ r₀) < ε / 2 := by
    have hmem : Icc (-R) R ∈ 𝓝 r₀ := Icc_mem_nhds (by
      have := neg_abs_le r₀; linarith) (by have := le_abs_self r₀; linarith)
    have hc := (Metric.continuousAt_iff'.1 (hU₀c.continuousAt (x := r₀))) (ε / 2) (half_pos hε)
    filter_upwards [hmem, hc] with r h1 h2 using ⟨h1, h2⟩
  rw [nhds_prod_eq]
  filter_upwards [hr.prod_mk hclose] with z hz
  obtain ⟨⟨hzR, hz1⟩, hz2⟩ := hz
  have h2 := hz2 z.1 hzR
  calc dist (U z.2 z.1) (U p₀ r₀) ≤ dist (U z.2 z.1) (U p₀ z.1) + dist (U p₀ z.1) (U p₀ r₀) :=
        dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by rw [dist_comm] at h2; gcongr
    _ = ε := add_halves ε

end NonUniqueEuler.Smooth
