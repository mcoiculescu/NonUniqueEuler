import NonUniqueEuler.Defs.SmoothB.ODE
import NonUniqueEuler.H.SmoothB.ODE.MaxSol
import NonUniqueEuler.H.SmoothB.ODE.Cutoff
import NonUniqueEuler.H.SmoothB.ODE.Scaling
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Proof of `lem:ode` (maximal solutions, local smooth dependence, global existence)

Proof of the interface `I/SmoothB/ODE.lean` (same declarations, statements verbatim).

* (i) `ode_exists_isMaxSol`: local existence from the cut-off field and the vendored global flow
  (`ODEH.local_flow_package`), then the union of all local solutions
  (`ODEH.exists_isMaxSol_of_local`, uniqueness by `ODEH.IsLocalSol.eqOn_inter`).
* (ii) `ode_local_contDiff`: on the box `I × 𝒰` of `ODEH.local_flow_package` the maximal flow is
  the flow of the cut-off field, which is `C^k` jointly in `(t, s, y)`
  (`ODEH.flow_contDiff_of_velocity`, scaling trick + the autonomous `C^k` core) and satisfies the
  variational equation (`ODEH.flow_fderiv_hasDerivAt`).
* (iii) `ode_global`: for `T > |s|`, cut `F` off outside `[-T', T'] × closedBall 0 R` with `R` the
  Grönwall bound of the linear growth; the cut-off field obeys the same growth bound, so its
  flow stays where it equals `F` and solves the original equation on `(-T, T)`; maximality gives
  `(-T, T) ⊆ maxDomain`.
-/

noncomputable section

open Set Function Metric Filter
open scoped Topology NNReal

namespace NonUniqueEuler.Smooth

open NonUniqueEuler.Vendor.BoundedLipschitzFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

namespace ODEH

/-- The flow of the cut-off datum of `local_flow_package` solves the original problem on
`(p.1 - a, p.1 + a)`. -/
theorem isLocalSol_of_package {F : ℝ → E → E} {U : Set (ℝ × E)} {V : Data E} {ρ a : ℝ}
    {p : ℝ × E} (hball : ball p ρ ⊆ U)
    (hVeq : ∀ q ∈ ball p ρ, uncurry V.velocity q = uncurry F q)
    (hstay : ∀ s ∈ Ioo (p.1 - a) (p.1 + a), ∀ t ∈ Ioo (p.1 - a) (p.1 + a),
      ∀ y ∈ ball p.2 (ρ / 2), (t, V.flow s t y) ∈ ball p ρ)
    {s : ℝ} (hs : s ∈ Ioo (p.1 - a) (p.1 + a)) {y : E} (hy : y ∈ ball p.2 (ρ / 2)) :
    IsLocalSol F U s y (Ioo (p.1 - a) (p.1 + a)) (fun t => V.flow s t y) := by
  refine ⟨isOpen_Ioo, ordConnected_Ioo, hs, V.flow_initial s y,
    fun t ht => hball (hstay s hs t ht y hy), fun t ht => ?_⟩
  have h := V.flow_hasDerivAt s t y
  have he : V.velocity t (V.flow s t y) = F t (V.flow s t y) := hVeq _ (hstay s hs t ht y hy)
  rw [he] at h
  exact h

end ODEH

/-- `lem:ode`(i): for `U` open and `F ∈ C¹(U)` (hence for `F ∈ C^k(U)`, `k ≥ 1`), every
`(s, y) ∈ U` has a unique maximal solution of `ẋ = F(t, x)`, `x(s) = y`, defined on an open
interval containing `s` (uniqueness is built into `IsMaxSol`). -/
theorem ode_exists_isMaxSol {F : ℝ → E → E} {U : Set (ℝ × E)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ 1 (Function.uncurry F) U) {s : ℝ} {y : E} (hsy : (s, y) ∈ U) :
    ∃ (J : Set ℝ) (γ : ℝ → E), IsMaxSol F U s y J γ := by
  obtain ⟨V, ρ, a, hρ, ha, -, -, hball, hVeq, hstay⟩ :=
    ODEH.local_flow_package (k := 1) le_rfl hU (by exact_mod_cast hF) hsy
  apply ODEH.exists_isMaxSol_of_local hU hF
  refine ⟨Ioo (s - a) (s + a), fun t => V.flow s t y, ?_⟩
  exact ODEH.isLocalSol_of_package (p := (s, y)) hball hVeq hstay
    ⟨by simp only; linarith, by simp only; linarith⟩ (mem_ball_self (by positivity))

/-- `lem:ode`(i), in terms of the chosen solution map: `t ↦ Φ_F(t, s, y)` on `maxDomain F U s y`
is the maximal solution. -/
theorem ode_isMaxSol_maxFlow {F : ℝ → E → E} {U : Set (ℝ × E)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ 1 (Function.uncurry F) U) {s : ℝ} {y : E} (hsy : (s, y) ∈ U) :
    IsMaxSol F U s y (maxDomain F U s y) (fun t => maxFlow F U t s y) :=
  isMaxSol_maxFlow (ode_exists_isMaxSol hU hF hsy)

/-- `lem:ode`(ii): for `F ∈ C^k(U)`, `k ≥ 1`, around each point of `U` there is an open set
`I × 𝒰 ⊆ U`, `I` an open interval, such that `Φ_F(t, s, y)` is defined for `t, s ∈ I`, `y ∈ 𝒰`,
`Φ_F` and `∂_t Φ_F = F(t, Φ_F)` are `C^k` on `I × I × 𝒰`, and there `D_y Φ_F` solves the
variational equation `∂_t D_y Φ_F(t,s,y) = D_x F(t, Φ_F(t,s,y)) D_y Φ_F(t,s,y)`. -/
theorem ode_local_contDiff {F : ℝ → E → E} {U : Set (ℝ × E)} (hU : IsOpen U) {k : ℕ}
    (hk : 1 ≤ k) (hF : ContDiffOn ℝ k (Function.uncurry F) U) {p : ℝ × E} (hp : p ∈ U) :
    ∃ (I : Set ℝ) (𝒰 : Set E), IsOpen I ∧ I.OrdConnected ∧ IsOpen 𝒰 ∧ p.1 ∈ I ∧ p.2 ∈ 𝒰 ∧
      I ×ˢ 𝒰 ⊆ U ∧
      (∀ t ∈ I, ∀ s ∈ I, ∀ y ∈ 𝒰, t ∈ maxDomain F U s y) ∧
      ContDiffOn ℝ k (fun q : ℝ × ℝ × E => maxFlow F U q.1 q.2.1 q.2.2) (I ×ˢ I ×ˢ 𝒰) ∧
      ContDiffOn ℝ k (fun q : ℝ × ℝ × E => F q.1 (maxFlow F U q.1 q.2.1 q.2.2))
        (I ×ˢ I ×ˢ 𝒰) ∧
      ∀ t ∈ I, ∀ s ∈ I, ∀ y ∈ 𝒰,
        HasDerivAt (fun τ => maxFlow F U τ s y) (F t (maxFlow F U t s y)) t ∧
        HasDerivAt (fun τ => fderiv ℝ (maxFlow F U τ s) y)
          ((fderiv ℝ (F t) (maxFlow F U t s y)).comp (fderiv ℝ (maxFlow F U t s) y)) t := by
  have hk' : (1 : WithTop ℕ∞) ≤ k := by exact_mod_cast hk
  have hF1 : ContDiffOn ℝ 1 (uncurry F) U := hF.of_le hk'
  obtain ⟨V, ρ, a, hρ, ha, haρ, hVc, hball, hVeq, hstay⟩ :=
    ODEH.local_flow_package hk hU hF hp
  have hmem : ∀ t ∈ Ioo (p.1 - a) (p.1 + a), ∀ x ∈ ball p.2 ρ, (t, x) ∈ ball p ρ := by
    intro t ht x hx
    rw [mem_ball, Prod.dist_eq]
    refine max_lt ?_ hx
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2]
  have h𝒰 : ball p.2 (ρ / 2) ⊆ ball p.2 ρ := ball_subset_ball (by linarith)
  have hloc : ∀ s ∈ Ioo (p.1 - a) (p.1 + a), ∀ y ∈ ball p.2 (ρ / 2),
      IsLocalSol F U s y (Ioo (p.1 - a) (p.1 + a)) (fun t => V.flow s t y) :=
    fun s hs y hy => ODEH.isLocalSol_of_package hball hVeq hstay hs hy
  have hmax : ∀ s ∈ Ioo (p.1 - a) (p.1 + a), ∀ y ∈ ball p.2 (ρ / 2),
      IsMaxSol F U s y (maxDomain F U s y) (fun t => maxFlow F U t s y) :=
    fun s hs y hy => ode_isMaxSol_maxFlow hU hF1 (hball (hmem s hs y (h𝒰 hy)))
  have hdom : ∀ t ∈ Ioo (p.1 - a) (p.1 + a), ∀ s ∈ Ioo (p.1 - a) (p.1 + a),
      ∀ y ∈ ball p.2 (ρ / 2), t ∈ maxDomain F U s y :=
    fun t ht s hs y hy => ((hmax s hs y hy).maximal _ _ (hloc s hs y hy)).1 ht
  have hflow : ∀ t ∈ Ioo (p.1 - a) (p.1 + a), ∀ s ∈ Ioo (p.1 - a) (p.1 + a),
      ∀ y ∈ ball p.2 (ρ / 2), maxFlow F U t s y = V.flow s t y :=
    fun t ht s hs y hy => (((hmax s hs y hy).maximal _ _ (hloc s hs y hy)).2 ht).symm
  have hVk : ContDiff ℝ k (fun q : ℝ × ℝ × E => V.flow q.2.1 q.1 q.2.2) :=
    ODEH.flow_contDiff_of_velocity V hk hVc
  have hV1 : ContDiff ℝ 1 (uncurry V.velocity) := hVc.of_le hk'
  refine ⟨Ioo (p.1 - a) (p.1 + a), ball p.2 (ρ / 2), isOpen_Ioo, ordConnected_Ioo, isOpen_ball,
    ⟨by linarith, by linarith⟩, mem_ball_self (by linarith), ?_, hdom, ?_, ?_, ?_⟩
  · rintro ⟨t, x⟩ ⟨ht, hx⟩
    exact hball (hmem t ht x (h𝒰 hx))
  · refine hVk.contDiffOn.congr ?_
    rintro ⟨t, s, y⟩ ⟨ht, hs, hy⟩
    exact hflow t ht s hs y hy
  · have hc : ContDiff ℝ k (fun q : ℝ × ℝ × E => V.velocity q.1 (V.flow q.2.1 q.1 q.2.2)) :=
      hVc.comp (contDiff_fst.prodMk hVk)
    refine hc.contDiffOn.congr ?_
    rintro ⟨t, s, y⟩ ⟨ht, hs, hy⟩
    change F t (maxFlow F U t s y) = V.velocity t (V.flow s t y)
    rw [hflow t ht s hs y hy]
    exact (hVeq _ (hstay s hs t ht y hy)).symm
  · intro t ht s hs y hy
    refine ⟨(hmax s hs y hy).hasDerivAt t (hdom t ht s hs y hy), ?_⟩
    have hev : ∀ τ ∈ Ioo (p.1 - a) (p.1 + a),
        fderiv ℝ (maxFlow F U τ s) y = fderiv ℝ (V.flow s τ) y := by
      intro τ hτ
      apply Filter.EventuallyEq.fderiv_eq
      exact Filter.mem_of_superset (isOpen_ball.mem_nhds hy) (fun x hx => hflow τ hτ s hs x hx)
    have hevt : (fun τ => fderiv ℝ (maxFlow F U τ s) y) =ᶠ[𝓝 t]
        fun τ => fderiv ℝ (V.flow s τ) y :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht) hev
    have hFeq : fderiv ℝ (F t) (V.flow s t y) = fderiv ℝ (V.velocity t) (V.flow s t y) := by
      apply Filter.EventuallyEq.fderiv_eq
      have hopen : IsOpen {x : E | (t, x) ∈ ball p ρ} :=
        isOpen_ball.preimage (Continuous.prodMk_right t)
      exact Filter.mem_of_superset (hopen.mem_nhds (hstay s hs t ht y hy))
        (fun x hx => (hVeq _ hx).symm)
    rw [hflow t ht s hs y hy, hev t ht, hFeq]
    exact (ODEH.flow_fderiv_hasDerivAt V hV1 s t y).congr_of_eventuallyEq hevt

namespace ODEH

omit [FiniteDimensional ℝ E] in
/-- Linear-growth bound for a field `f` on `[-T, T]` gives a Grönwall bound for its trajectories
through `(s, y)` on `[-T, T]`. -/
theorem norm_le_of_linear_growth {f : ℝ → E → E} {γ : ℝ → E} {T M L : ℝ} {s : ℝ} {y : E}
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hs : |s| < T)
    (hf : ∀ t ∈ Icc (-T) T, ∀ x : E, ‖f t x‖ ≤ M + L * ‖x‖)
    (hγ : ∀ t, HasDerivAt γ (f t (γ t)) t) (hγs : γ s = y) :
    ∀ t ∈ Icc (-T) T, ‖γ t‖ ≤ gronwallBound ‖y‖ L M (2 * T) := by
  have hγc : Continuous γ := continuous_iff_continuousAt.2 fun t => (hγ t).continuousAt
  have hs' := abs_lt.1 hs
  have hmono := gronwallBound_mono (norm_nonneg y) hM hL
  intro t ht
  rcases le_total s t with hst | hts
  · have h := norm_le_gronwallBound_of_norm_deriv_right_le (f := γ)
      (f' := fun t => f t (γ t)) (δ := ‖y‖) (K := L) (ε := M) (a := s) (b := T)
      hγc.continuousOn (fun x _ => (hγ x).hasDerivWithinAt) (by rw [hγs])
      (fun x hx => by
        have := hf x ⟨by linarith [hx.1], hx.2.le⟩ (γ x)
        linarith) t ⟨hst, ht.2⟩
    exact h.trans (hmono (by linarith [ht.2]))
  · let g : ℝ → E := fun τ => γ (-τ)
    have hg : ∀ τ, HasDerivAt g (-f (-τ) (g τ)) τ := by
      intro τ
      have h := (hγ (-τ)).scomp τ (hasDerivAt_neg τ)
      simpa [g, Function.comp_def] using h
    have hgc : Continuous g := hγc.comp continuous_neg
    have h := norm_le_gronwallBound_of_norm_deriv_right_le (f := g)
      (f' := fun τ => -f (-τ) (g τ)) (δ := ‖y‖) (K := L) (ε := M) (a := -s) (b := T)
      hgc.continuousOn (fun x _ => (hg x).hasDerivWithinAt) (by simp [g, hγs])
      (fun x hx => by
        have := hf (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩ (g x)
        rw [norm_neg]
        linarith) (-t) ⟨by linarith, by linarith [ht.1]⟩
    simp only [g, neg_neg] at h
    exact h.trans (hmono (by linarith [ht.1]))

/-- Under the linear growth bound of `lem:ode`(iii), the problem through `(s, y)` has a local
solution on `(-T, T)` for every `T > |s|`. -/
theorem isLocalSol_Ioo_of_growth {F : ℝ → E → E} (hF : ContDiff ℝ 1 (uncurry F))
    (hgrowth : ∀ T : ℝ, 0 < T → ∃ M L : ℝ, ∀ t ∈ Icc (-T) T, ∀ x : E, ‖F t x‖ ≤ M + L * ‖x‖)
    {s : ℝ} (y : E) {T : ℝ} (hT : |s| < T) :
    ∃ γ : ℝ → E, IsLocalSol F univ s y (Ioo (-T) T) γ := by
  have hT0 : 0 < T := lt_of_le_of_lt (abs_nonneg s) hT
  obtain ⟨M, L, hML⟩ := hgrowth T hT0
  set M' := max M 0
  set L' := max L 0
  have hM' : 0 ≤ M' := le_max_right _ _
  have hL' : 0 ≤ L' := le_max_right _ _
  have hML' : ∀ t ∈ Icc (-T) T, ∀ x : E, ‖F t x‖ ≤ M' + L' * ‖x‖ := by
    intro t ht x
    have h1 := hML t ht x
    have h2 : M ≤ M' := le_max_left _ _
    have h3 : L * ‖x‖ ≤ L' * ‖x‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    linarith
  set R₀ := gronwallBound ‖y‖ L' M' (2 * T)
  set ρ := max T R₀ + 1
  have hρ : 0 < ρ := by
    have : T ≤ max T R₀ := le_max_left _ _
    linarith
  obtain ⟨V, -, hVeq, hVnorm⟩ := exists_cutoff_data (k := 1) le_rfl isOpen_univ
    (hF.contDiffOn) (c := 0) hρ (subset_univ _)
  have hbd : ∀ t ∈ Icc (-T) T, ‖V.flow s t y‖ ≤ R₀ :=
    norm_le_of_linear_growth hM' hL' hT
      (fun t ht x => (hVnorm t x).trans (hML' t ht x)) (fun t => V.flow_hasDerivAt s t y)
      (V.flow_initial s y)
  have hs := abs_lt.1 hT
  refine ⟨fun t => V.flow s t y, isOpen_Ioo, ordConnected_Ioo, ⟨hs.1, hs.2⟩,
    V.flow_initial s y, fun t _ => mem_univ _, fun t ht => ?_⟩
  have hin : (t, V.flow s t y) ∈ closedBall (0 : ℝ × E) ρ := by
    rw [mem_closedBall, Prod.dist_eq]
    simp only [Prod.fst_zero, Prod.snd_zero, dist_zero_right, Real.norm_eq_abs]
    refine max_le ?_ ?_
    · have : |t| ≤ T := abs_le.2 ⟨ht.1.le, ht.2.le⟩
      have : T ≤ max T R₀ := le_max_left _ _
      linarith
    · have := hbd t ⟨ht.1.le, ht.2.le⟩
      have : R₀ ≤ max T R₀ := le_max_right _ _
      linarith
  have h := V.flow_hasDerivAt s t y
  have he : V.velocity t (V.flow s t y) = F t (V.flow s t y) := hVeq _ hin
  rw [he] at h
  exact h

end ODEH

/-- `lem:ode`(iii): if `U = ℝ × E`, `F ∈ C¹`, and for every `T > 0` there are `M(T)`, `L(T)` with
`|F(t, x)| ≤ M(T) + L(T)|x|` on `[-T, T] × E`, then every maximal solution is defined on all of
`ℝ`: the maximal solution through `(s, y)` is `t ↦ Φ_F(t, s, y)` on `ℝ`. -/
theorem ode_global {F : ℝ → E → E} (hF : ContDiff ℝ 1 (Function.uncurry F))
    (hgrowth : ∀ T : ℝ, 0 < T → ∃ M L : ℝ, ∀ t ∈ Icc (-T) T, ∀ x : E, ‖F t x‖ ≤ M + L * ‖x‖)
    (s : ℝ) (y : E) :
    maxDomain F univ s y = univ ∧ IsMaxSol F univ s y univ (fun t => maxFlow F univ t s y) := by
  have hmax := ode_isMaxSol_maxFlow isOpen_univ hF.contDiffOn (mem_univ (s, y))
  have key : ∀ T : ℝ, |s| < T → Ioo (-T) T ⊆ maxDomain F univ s y := by
    intro T hT
    obtain ⟨γ, hγ⟩ := ODEH.isLocalSol_Ioo_of_growth hF hgrowth y hT
    exact (hmax.maximal _ _ hγ).1
  have hdom : maxDomain F univ s y = univ := by
    apply eq_univ_of_forall
    intro t
    apply key (|s| + |t| + 1) (by linarith [abs_nonneg t])
    constructor
    · linarith [neg_abs_le t, abs_nonneg s]
    · linarith [le_abs_self t, abs_nonneg s]
  refine ⟨hdom, ?_⟩
  rw [hdom] at hmax
  exact hmax

end NonUniqueEuler.Smooth
