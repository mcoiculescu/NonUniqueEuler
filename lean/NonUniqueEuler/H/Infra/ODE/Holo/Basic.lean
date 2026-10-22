import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.Compactness.Compact

/-!
# Helpers for `P/Infra/ODE/Holo.lean`: uniform estimates

Generic lemmas (independent of the ODE) used to prove holomorphic dependence of solutions of
`ψ'' = V(·, z) ψ` on the complex parameter `z`.

* `Holo.eventually_forall_norm_sub_lt`: a generalized tube lemma. If `g` is continuous on
  `S ×ˢ T` (`T` open) and `K ⊆ T` is compact, then `g (x, ·) → g (x₀, ·)` uniformly on `K` as
  `x → x₀` within `S`.
* `Holo.continuousOn_deriv_param'`: joint continuity of the complex derivative of a function
  that is jointly continuous and holomorphic in its first variable (Cauchy's estimate for the
  difference `f(·, p) - f(·, p₀)` plus continuity of `deriv f(·, p₀)`).
* `Holo.eventually_norm_sub_sub_deriv_le`: a first-order Taylor bound for `V ξ` at `z`, uniform
  in `ξ` in a compact set (mean value inequality, joint continuity of `∂_z V`).
* `Holo.gronwallBound_zero_le`: `gronwallBound 0 K δ x ≤ δ * gronwallBound 0 K 1 X` for
  `0 ≤ x ≤ X`.
-/

noncomputable section

open Set Filter Topology Metric

namespace NonUniqueEuler.LinODE.Holo

/-- **Generalized tube lemma** (uniform convergence on a compact set). -/
theorem eventually_forall_norm_sub_lt {X Y E : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SeminormedAddCommGroup E] {g : X × Y → E} {S : Set X} {T : Set Y} {x₀ : X}
    (hx₀ : x₀ ∈ S) {K : Set Y} (hK : IsCompact K) (hKT : K ⊆ T) (hT : IsOpen T)
    (hg : ContinuousOn g (S ×ˢ T)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝[S] x₀, ∀ y ∈ K, ‖g (x, y) - g (x₀, y)‖ < ε := by
  rw [eventually_nhdsWithin_iff]
  have key : ∀ y ∈ K, ∀ᶠ q : X × Y in 𝓝 (x₀, y),
      q.1 ∈ S → ‖g (q.1, q.2) - g (x₀, q.2)‖ < ε := by
    intro y hy
    have hyT : y ∈ T := hKT hy
    have hc : ContinuousWithinAt g (S ×ˢ T) (x₀, y) := hg _ ⟨hx₀, hyT⟩
    have h1 : ∀ᶠ q in 𝓝[S ×ˢ T] (x₀, y), dist (g q) (g (x₀, y)) < ε / 2 :=
      Metric.tendsto_nhds.1 hc (ε / 2) (by linarith)
    rw [eventually_nhdsWithin_iff] at h1
    have hc2 : ContinuousAt (fun y' => g (x₀, y')) y := by
      have : ContinuousWithinAt (fun y' => g (x₀, y')) T y :=
        hc.comp (continuousWithinAt_const.prodMk continuousWithinAt_id)
          (fun y' hy' => ⟨hx₀, hy'⟩)
      exact this.continuousAt (hT.mem_nhds hyT)
    have h2 : ∀ᶠ y' in 𝓝 y, dist (g (x₀, y')) (g (x₀, y)) < ε / 2 :=
      Metric.tendsto_nhds.1 hc2 (ε / 2) (by linarith)
    have h2' : ∀ᶠ q : X × Y in 𝓝 (x₀, y), dist (g (x₀, q.2)) (g (x₀, y)) < ε / 2 :=
      (continuous_snd.tendsto (x₀, y)).eventually h2
    have h3 : ∀ᶠ q : X × Y in 𝓝 (x₀, y), q.2 ∈ T :=
      (continuous_snd.tendsto (x₀, y)).eventually (hT.mem_nhds hyT)
    filter_upwards [h1, h2', h3] with q hq1 hq2 hq3 hqS
    have hq1' := hq1 ⟨hqS, hq3⟩
    rw [dist_eq_norm] at hq1' hq2
    calc ‖g (q.1, q.2) - g (x₀, q.2)‖
        = ‖(g q - g (x₀, y)) - (g (x₀, q.2) - g (x₀, y))‖ := by
          congr 1; abel
      _ ≤ ‖g q - g (x₀, y)‖ + ‖g (x₀, q.2) - g (x₀, y)‖ := norm_sub_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add hq1' hq2
      _ = ε := by ring
  filter_upwards [hK.eventually_forall_of_forall_eventually
    (P := fun x y => x ∈ S → ‖g (x, y) - g (x₀, y)‖ < ε) key] with x hx hxS y hy
  exact hx y hy hxS

/-- **Joint continuity of the complex derivative** of a function that is jointly continuous and
holomorphic in its first variable. -/
theorem continuousOn_deriv_param' {P : Type*} [TopologicalSpace P] {f : ℂ → P → ℂ}
    {U : Set ℂ} (hU : IsOpen U) {S : Set P} (hf : ContinuousOn (Function.uncurry f) (U ×ˢ S))
    (hfd : ∀ p ∈ S, DifferentiableOn ℂ (fun z => f z p) U) :
    ContinuousOn (fun q : ℂ × P => deriv (fun z => f z q.2) q.1) (U ×ˢ S) := by
  rintro ⟨z₀, p₀⟩ ⟨hz₀, hp₀⟩
  obtain ⟨r₀, hr₀, hr₀U⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
  set r := r₀ / 4 with hr_def
  have hr : 0 < r := by positivity
  have hrU : closedBall z₀ (2 * r) ⊆ U :=
    (closedBall_subset_ball (by rw [hr_def]; linarith)).trans hr₀U
  show Tendsto _ _ _
  rw [Metric.tendsto_nhds, nhdsWithin_prod_eq]
  intro ε hε
  -- uniform closeness of `f(·, p)` to `f(·, p₀)` on `closedBall z₀ (2r)`
  have ha : ∀ᶠ p in 𝓝[S] p₀, ∀ ζ ∈ closedBall z₀ (2 * r),
      ‖(fun q : P × ℂ => f q.2 q.1) (p, ζ) - (fun q : P × ℂ => f q.2 q.1) (p₀, ζ)‖
        < ε * r / 2 := by
    refine eventually_forall_norm_sub_lt (g := fun q : P × ℂ => f q.2 q.1) hp₀ (isCompact_closedBall z₀ (2 * r)) hrU hU ?_
      (by positivity)
    exact hf.comp continuous_swap.continuousOn (fun q hq => ⟨hq.2, hq.1⟩)
  have hS : ∀ᶠ p in 𝓝[S] p₀, p ∈ S := self_mem_nhdsWithin
  -- continuity of `deriv f(·, p₀)` at `z₀`
  have hb : ContinuousAt (deriv (fun z => f z p₀)) z₀ :=
    ((hfd p₀ hp₀).deriv hU).continuousOn.continuousAt (hU.mem_nhds hz₀)
  have hb' : ∀ᶠ z in 𝓝[U] z₀,
      dist (deriv (fun z => f z p₀) z) (deriv (fun z => f z p₀) z₀) < ε / 2 :=
    nhdsWithin_le_nhds (Metric.tendsto_nhds.1 hb (ε / 2) (by linarith))
  have hball : ∀ᶠ z in 𝓝[U] z₀, z ∈ ball z₀ r :=
    mem_nhdsWithin_of_mem_nhds (ball_mem_nhds z₀ hr)
  filter_upwards [(hball.and hb').prod_inl (𝓝[S] p₀), (ha.and hS).prod_inr (𝓝[U] z₀)] with
    q h1 h2
  obtain ⟨z, p⟩ := q
  obtain ⟨hzb, hzd⟩ := h1
  obtain ⟨hpa, hpS⟩ := h2
  simp only at hzb hzd hpa hpS ⊢
  have hzU : closedBall z r ⊆ U := by
    refine (closedBall_subset_closedBall' ?_).trans hrU
    rw [mem_ball] at hzb
    linarith
  have hdp : DifferentiableOn ℂ (fun ζ => f ζ p - f ζ p₀) U :=
    (hfd p hpS).sub (hfd p₀ hp₀)
  have hzU' : z ∈ U := hzU (mem_closedBall_self hr.le)
  have hderiv : deriv (fun ζ => f ζ p - f ζ p₀) z =
      deriv (fun ζ => f ζ p) z - deriv (fun ζ => f ζ p₀) z :=
    deriv_sub ((hfd p hpS).differentiableAt (hU.mem_nhds hzU'))
      ((hfd p₀ hp₀).differentiableAt (hU.mem_nhds hzU'))
  have hcauchy : ‖deriv (fun ζ => f ζ p - f ζ p₀) z‖ ≤ (ε * r / 2) / r := by
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr ?_ ?_
    · refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball z hr.ne']
      exact hdp.mono hzU
    · intro ζ hζ
      refine (hpa ζ ?_).le
      rw [mem_closedBall]
      rw [mem_sphere] at hζ
      rw [mem_ball] at hzb
      calc dist ζ z₀ ≤ dist ζ z + dist z z₀ := dist_triangle _ _ _
        _ ≤ 2 * r := by linarith
  have hεr : (ε * r / 2) / r = ε / 2 := by field_simp
  rw [hεr, hderiv] at hcauchy
  rw [dist_eq_norm] at hzd ⊢
  calc ‖deriv (fun ζ => f ζ p) z - deriv (fun ζ => f ζ p₀) z₀‖
      = ‖(deriv (fun ζ => f ζ p) z - deriv (fun ζ => f ζ p₀) z) +
          (deriv (fun ζ => f ζ p₀) z - deriv (fun ζ => f ζ p₀) z₀)‖ := by
        congr 1; ring
    _ ≤ ‖deriv (fun ζ => f ζ p) z - deriv (fun ζ => f ζ p₀) z‖ +
          ‖deriv (fun ζ => f ζ p₀) z - deriv (fun ζ => f ζ p₀) z₀‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt hcauchy hzd
    _ = ε := by ring

/-- **Uniform first-order Taylor bound**: for `V ξ` holomorphic on `U` with `∂_z V` jointly
continuous, `V ξ w - V ξ z - (w - z) ∂_z V(ξ, z) = o(w - z)` uniformly in `ξ ∈ s` compact. -/
theorem eventually_norm_sub_sub_deriv_le {V : ℝ → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hdV : ContinuousOn (fun q : ℂ × ℝ => deriv (V q.2) q.1) (U ×ˢ univ))
    (hVd : ∀ ξ, DifferentiableOn ℂ (V ξ) U) {z : ℂ} (hz : z ∈ U) {s : Set ℝ}
    (hs : IsCompact s) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ w in 𝓝 z, ∀ ξ ∈ s, ‖V ξ w - V ξ z - (w - z) * deriv (V ξ) z‖ ≤ η * ‖w - z‖ := by
  have ht : ∀ᶠ c in 𝓝[U] z, ∀ ξ ∈ s,
      ‖(fun q : ℂ × ℝ => deriv (V q.2) q.1) (c, ξ) -
        (fun q : ℂ × ℝ => deriv (V q.2) q.1) (z, ξ)‖ < η :=
    eventually_forall_norm_sub_lt hz hs (subset_univ s) isOpen_univ hdV hη
  rw [hU.nhdsWithin_eq hz] at ht
  obtain ⟨r, hr, hrb⟩ := Metric.eventually_nhds_iff_ball.1 (ht.and (hU.mem_nhds hz))
  filter_upwards [ball_mem_nhds z hr] with w hw ξ hξ
  set d := deriv (V ξ) z
  have hdiff : ∀ c ∈ ball z r, HasDerivAt (fun c => V ξ c - c * d) (deriv (V ξ) c - d) c := by
    intro c hc
    have h1 : HasDerivAt (V ξ) (deriv (V ξ) c) c :=
      ((hVd ξ).differentiableAt (hU.mem_nhds (hrb c hc).2)).hasDerivAt
    have h2 : HasDerivAt (fun c => c * d) d c := by
      simpa using (hasDerivAt_id c).mul_const d
    exact h1.sub h2
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun c => V ξ c - c * d)
    (s := ball z r) (C := η) (fun c hc => (hdiff c hc).differentiableAt)
    (fun c hc => by
      rw [(hdiff c hc).deriv]
      exact ((hrb c hc).1 ξ hξ).le)
    (convex_ball z r) (mem_ball_self hr) hw
  calc ‖V ξ w - V ξ z - (w - z) * d‖ = ‖(V ξ w - w * d) - (V ξ z - z * d)‖ := by
        congr 1; ring
    _ ≤ η * ‖w - z‖ := hmv

/-- `gronwallBound 0 K δ x ≤ δ * gronwallBound 0 K 1 X` for `0 ≤ x ≤ X`, `K > 0`, `δ ≥ 0`. -/
theorem gronwallBound_zero_le {K δ x X : ℝ} (hK : 0 < K) (hδ : 0 ≤ δ) (hx : 0 ≤ x)
    (hxX : x ≤ X) : gronwallBound 0 K δ x ≤ δ * gronwallBound 0 K 1 X := by
  rw [gronwallBound_of_K_ne_0 hK.ne', gronwallBound_of_K_ne_0 hK.ne']
  simp only [zero_mul, zero_add]
  have he : Real.exp (K * x) ≤ Real.exp (K * X) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hxX hK.le)
  have h1 : 0 ≤ Real.exp (K * x) - 1 := by
    have := Real.add_one_le_exp (K * x)
    nlinarith [mul_nonneg hK.le hx]
  calc δ / K * (Real.exp (K * x) - 1) ≤ δ / K * (Real.exp (K * X) - 1) := by
        gcongr
    _ = δ * (1 / K * (Real.exp (K * X) - 1)) := by ring

theorem gronwallBound_zero_one_nonneg {K X : ℝ} (hK : 0 < K) (hX : 0 ≤ X) :
    0 ≤ gronwallBound 0 K 1 X := by
  rw [gronwallBound_of_K_ne_0 hK.ne']
  simp only [zero_mul, zero_add]
  have h1 : 0 ≤ Real.exp (K * X) - 1 := by
    have := Real.add_one_le_exp (K * X)
    nlinarith [mul_nonneg hK.le hX]
  positivity

/-- Elementary: if `0 ≤ c` and `0 ≤ t ≤ ε / (2 (c + 1))`, then `c t ≤ ε / 2`. -/
theorem mul_le_half_of_le {c t ε : ℝ} (hc : 0 ≤ c) (ht : t ≤ ε / (2 * (c + 1))) (hε : 0 < ε) :
    c * t ≤ ε / 2 := by
  have hc1 : 0 < c + 1 := by linarith
  have h2 : c * t ≤ c * (ε / (2 * (c + 1))) := mul_le_mul_of_nonneg_left ht hc
  have h3 : c * (ε / (2 * (c + 1))) ≤ ε / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

end NonUniqueEuler.LinODE.Holo
