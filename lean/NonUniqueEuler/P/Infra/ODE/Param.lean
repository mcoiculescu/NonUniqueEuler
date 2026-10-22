import NonUniqueEuler.Defs.Infra.ODE
import NonUniqueEuler.I.Infra.ODE.Existence
import NonUniqueEuler.I.Infra.ODE.Gronwall
import NonUniqueEuler.I.Infra.ODE.Smooth
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Proof of the interface (I-ODE): continuous dependence on parameters

Proves `continuousOn_sol` and `continuousOn_iteratedDeriv_sol` of `I/Infra/ODE/Param.lean`.

Proof.
* `continuousOn_sol`. Fix `(ξ₁, p₁)` with `p₁ ∈ S` and the compact interval
  `I = [ξ₀ - R, ξ₀ + R]`, `R = |ξ₁ - ξ₀| + 1`, a neighbourhood of `ξ₁`. By the tube lemma
  (`IsCompact.mem_uniformity_of_prod`), `sup_I |V(·, p) - V(·, p₁)| < δ` for `p` near `p₁` in
  `S`, and `|y₀ p - y₀ p₁| < δ` there. With `K = max M 0 + 1`, `M = sup_I |V(·, p₁)|`, the
  a priori bound `IsSolOn.norm_le` gives `|Y(·; p)| ≤ B := (|y₀ p₁| + 1) e^{K R}` on `I`, and
  `norm_sub_le_of_isSolOn` gives `sup_I |Y(·; p) - Y(·; p₁)| ≤ δ (1 + B) e^{K R}`
  (`eventually_dist_sol_lt`). Together with the continuity of `Y(·; p₁)` in `ξ` this is the joint
  continuity at `(ξ₁, p₁)`.
* `continuousOn_iteratedDeriv_sol`. Strong induction on `k`. For `k = 0, 1` the derivative is
  `Y.1`, `Y.2` (`IsSolOn.contDiff`: `deriv ψ = ψ'`). For `k + 2`,
  `ψ^{(k+2)} = (Vψ)^{(k)} = ∑_{i ≤ k} C(k, i) V^{(i)} ψ^{(k-i)}` (`iteratedDeriv_succ'`,
  `iteratedDeriv_fun_mul`), a finite sum of products of functions continuous on `ℝ × S`.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace NonUniqueEuler.LinODE

variable {P : Type*} [TopologicalSpace P]

/-- For `p ∈ S` the coefficient `V(·, p)` is continuous. -/
private theorem continuous_slice {V : ℝ → P → ℂ} {S : Set P}
    (hV : ContinuousOn (Function.uncurry V) (univ ×ˢ S)) {p : P} (hp : p ∈ S) :
    Continuous (fun ξ => V ξ p) := by
  have : ContinuousOn (Function.uncurry V ∘ fun ξ : ℝ => (ξ, p)) univ :=
    hV.comp (Continuous.continuousOn (by fun_prop)) (fun ξ _ => ⟨mem_univ ξ, hp⟩)
  exact continuousOn_univ.1 this

/-- For `p ∈ S` the chosen global solution solves the equation with the prescribed data. -/
private theorem sol_isSolOn {V : ℝ → P → ℂ} {S : Set P}
    (hV : ContinuousOn (Function.uncurry V) (univ ×ˢ S)) (ξ₀ : ℝ) (y₀ : P → ℂ × ℂ) {p : P}
    (hp : p ∈ S) :
    IsSolOn (fun ξ => V ξ p) univ (fun ξ => (sol (fun η => V η p) ξ₀ (y₀ p) ξ).1)
        (fun ξ => (sol (fun η => V η p) ξ₀ (y₀ p) ξ).2) ∧
      sol (fun η => V η p) ξ₀ (y₀ p) ξ₀ = y₀ p :=
  sol_spec (continuous_slice hV hp) ξ₀ (y₀ p)

/-- An explicit bound for `gronwallBound` on `[0, R]`. -/
private theorem gronwallBound_le {d K e x R : ℝ} (hd : 0 ≤ d) (hK : 1 ≤ K) (he : 0 ≤ e)
    (hx0 : 0 ≤ x) (hxR : x ≤ R) :
    gronwallBound d K e x ≤ (d + e) * Real.exp (K * R) := by
  have hK0 : K ≠ 0 := by linarith
  rw [gronwallBound_of_K_ne_0 hK0]
  have hKx : 0 ≤ K * x := mul_nonneg (by linarith) hx0
  have h1 : Real.exp (K * x) ≤ Real.exp (K * R) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hxR (by linarith))
  have h2 : e / K ≤ e := div_le_self he hK
  have h3 : 0 ≤ Real.exp (K * x) - 1 := by
    have := Real.one_le_exp hKx
    linarith
  have h4 : e / K * (Real.exp (K * x) - 1) ≤ e * Real.exp (K * R) := by
    calc e / K * (Real.exp (K * x) - 1) ≤ e * (Real.exp (K * x) - 1) :=
          mul_le_mul_of_nonneg_right h2 h3
      _ ≤ e * Real.exp (K * R) := mul_le_mul_of_nonneg_left (by linarith) he
  have h5 : d * Real.exp (K * x) ≤ d * Real.exp (K * R) := mul_le_mul_of_nonneg_left h1 hd
  show d * Real.exp (K * x) + e / K * (Real.exp (K * x) - 1) ≤ (d + e) * Real.exp (K * R)
  rw [add_mul]
  linarith

/-- **Uniform closeness on a compact interval.** For `p` close to `p₁` within `S`, the solutions
`Y(·; p)` and `Y(·; p₁)` are uniformly `ε`-close on `[ξ₀ - R, ξ₀ + R]`. -/
private theorem eventually_dist_sol_lt {V : ℝ → P → ℂ} {S : Set P}
    (hV : ContinuousOn (Function.uncurry V) (univ ×ˢ S)) (ξ₀ : ℝ) {y₀ : P → ℂ × ℂ}
    (hy₀ : ContinuousOn y₀ S) {p₁ : P} (hp₁ : p₁ ∈ S) {R : ℝ} (hR : 0 ≤ R) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ p in 𝓝[S] p₁, ∀ ξ ∈ Icc (ξ₀ - R) (ξ₀ + R),
      dist (sol (fun η => V η p) ξ₀ (y₀ p) ξ) (sol (fun η => V η p₁) ξ₀ (y₀ p₁) ξ) < ε := by
  set I := Icc (ξ₀ - R) (ξ₀ + R) with hI
  have hIc : IsCompact I := isCompact_Icc
  have hIo : I.OrdConnected := ordConnected_Icc
  have hξ₀ : ξ₀ ∈ I := ⟨by linarith, by linarith⟩
  have hV₁ := continuous_slice hV hp₁
  obtain ⟨M, hM⟩ := hIc.exists_bound_of_continuousOn hV₁.continuousOn
  set K : ℝ := max M 0 + 1 with hK
  have hK1 : 1 ≤ K := by have := le_max_right M 0; linarith
  have hMK : ∀ ξ ∈ I, ‖V ξ p₁‖ ≤ K - 1 := fun ξ hξ =>
    (hM ξ hξ).trans (by have := le_max_left M 0; linarith)
  set B : ℝ := (‖y₀ p₁‖ + 1) * Real.exp (K * R) with hB
  have hB0 : 0 < B := by positivity
  set C : ℝ := (1 + B) * Real.exp (K * R) with hC
  have hC0 : 0 < C := by positivity
  set δ : ℝ := min 1 (ε / (2 * C)) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (div_pos hε (by positivity))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδC : δ * C < ε := by
    have h1 : δ ≤ ε / (2 * C) := min_le_right _ _
    have h2 : δ * C ≤ ε / (2 * C) * C := mul_le_mul_of_nonneg_right h1 hC0.le
    have h3 : ε / (2 * C) * C = ε / 2 := by field_simp
    linarith
  -- the three eventual facts
  have hS : ∀ᶠ p in 𝓝[S] p₁, p ∈ S := self_mem_nhdsWithin
  have hVclose : ∀ᶠ p in 𝓝[S] p₁, ∀ ξ ∈ I, dist (V ξ p) (V ξ p₁) < δ := by
    have hf : ContinuousOn (Function.uncurry fun (p : P) (ξ : ℝ) => V ξ p) (S ×ˢ I) := by
      have : ContinuousOn (Function.uncurry V ∘ Prod.swap) (S ×ˢ I) :=
        hV.comp continuous_swap.continuousOn (fun q hq => ⟨mem_univ _, hq.1⟩)
      exact this
    obtain ⟨v, hv, hvp⟩ := hIc.mem_uniformity_of_prod hf hp₁ (Metric.dist_mem_uniformity hδ0)
    exact Filter.mem_of_superset hv fun p hp ξ hξ => hvp p hp ξ hξ
  have hyclose : ∀ᶠ p in 𝓝[S] p₁, dist (y₀ p) (y₀ p₁) < δ :=
    Metric.tendsto_nhds.1 (hy₀ p₁ hp₁) δ hδ0
  filter_upwards [hS, hVclose, hyclose] with p hpS hVp hyp ξ hξ
  obtain ⟨hsol, hsol0⟩ := sol_isSolOn hV ξ₀ y₀ hpS
  obtain ⟨hsol₁, hsol₁0⟩ := sol_isSolOn hV ξ₀ y₀ hp₁
  set Y := sol (fun η => V η p) ξ₀ (y₀ p) with hY
  set Y₁ := sol (fun η => V η p₁) ξ₀ (y₀ p₁) with hY₁
  have hVp' : ∀ ξ ∈ I, ‖V ξ p - V ξ p₁‖ ≤ δ := fun ξ hξ => by
    rw [← dist_eq_norm]; exact (hVp ξ hξ).le
  have hVpK : ∀ ξ ∈ I, ‖V ξ p‖ ≤ K := fun ξ hξ => by
    have h1 := norm_sub_norm_le (V ξ p) (V ξ p₁)
    have h2 := hVp' ξ hξ
    have h3 := hMK ξ hξ
    linarith
  -- a priori bound on `Y(·; p)` on `I`
  have hyp' : ‖y₀ p‖ ≤ ‖y₀ p₁‖ + 1 := by
    have h1 := norm_sub_norm_le (y₀ p) (y₀ p₁)
    rw [← dist_eq_norm] at h1
    linarith
  have hBnd : ∀ ξ ∈ I, ‖(Y ξ).1‖ ≤ B := fun ξ hξ => by
    have h1 := IsSolOn.norm_le hIo hK1 hVpK (hsol.mono (subset_univ I)) hξ₀ ξ hξ
    have h2 : ‖(Y ξ).1‖ ≤ ‖((Y ξ).1, (Y ξ).2)‖ := norm_fst_le _
    have h3 : |ξ - ξ₀| ≤ R := abs_sub_le_iff.2 ⟨by linarith [hξ.2], by linarith [hξ.1]⟩
    have h4 : Real.exp (K * |ξ - ξ₀|) ≤ Real.exp (K * R) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h3 (by linarith))
    have h5 : ‖((Y ξ₀).1, (Y ξ₀).2)‖ = ‖y₀ p‖ := by rw [hsol0]
    rw [h5] at h1
    calc ‖(Y ξ).1‖ ≤ ‖y₀ p‖ * Real.exp (K * |ξ - ξ₀|) := h2.trans h1
      _ ≤ (‖y₀ p₁‖ + 1) * Real.exp (K * R) :=
          mul_le_mul hyp' h4 (Real.exp_pos _).le (by positivity)
  -- continuous dependence on the coefficient
  have key := norm_sub_le_of_isSolOn hIo hK1 (fun ξ hξ => (hMK ξ hξ).trans (by linarith)) hVp'
    hBnd (hsol₁.mono (subset_univ I)) (hsol.mono (subset_univ I)) hξ₀ ξ hξ
  have hd : ‖((Y₁ ξ₀).1 - (Y ξ₀).1, (Y₁ ξ₀).2 - (Y ξ₀).2)‖ < δ := by
    have : ((Y₁ ξ₀).1 - (Y ξ₀).1, (Y₁ ξ₀).2 - (Y ξ₀).2) = y₀ p₁ - y₀ p := by
      rw [hsol0, hsol₁0]; rfl
    rw [this, ← dist_eq_norm, dist_comm]
    exact hyp
  have hx0 : 0 ≤ |ξ - ξ₀| := abs_nonneg _
  have hxR : |ξ - ξ₀| ≤ R := abs_sub_le_iff.2 ⟨by linarith [hξ.2], by linarith [hξ.1]⟩
  have hgb := gronwallBound_le (norm_nonneg _) hK1 (mul_nonneg hδ0.le hB0.le) hx0 hxR
    (d := ‖((Y₁ ξ₀).1 - (Y ξ₀).1, (Y₁ ξ₀).2 - (Y ξ₀).2)‖) (e := δ * B)
  have hdist : dist (Y ξ) (Y₁ ξ) = ‖((Y₁ ξ).1 - (Y ξ).1, (Y₁ ξ).2 - (Y ξ).2)‖ := by
    rw [dist_comm, dist_eq_norm]; rfl
  rw [hdist]
  have hexp : 0 < Real.exp (K * R) := Real.exp_pos _
  calc ‖((Y₁ ξ).1 - (Y ξ).1, (Y₁ ξ).2 - (Y ξ).2)‖
      ≤ gronwallBound ‖((Y₁ ξ₀).1 - (Y ξ₀).1, (Y₁ ξ₀).2 - (Y ξ₀).2)‖ K (δ * B) |ξ - ξ₀| := key
    _ ≤ (‖((Y₁ ξ₀).1 - (Y ξ₀).1, (Y₁ ξ₀).2 - (Y ξ₀).2)‖ + δ * B) * Real.exp (K * R) := hgb
    _ ≤ (δ + δ * B) * Real.exp (K * R) :=
        mul_le_mul_of_nonneg_right (by linarith) hexp.le
    _ = δ * C := by rw [hC]; ring
    _ < ε := hδC

/-- **Continuous dependence on parameters** (and on the data). -/
theorem continuousOn_sol {V : ℝ → P → ℂ} {S : Set P}
    (hV : ContinuousOn (Function.uncurry V) (univ ×ˢ S)) (ξ₀ : ℝ) {y₀ : P → ℂ × ℂ}
    (hy₀ : ContinuousOn y₀ S) :
    ContinuousOn (fun q : ℝ × P => sol (fun ξ => V ξ q.2) ξ₀ (y₀ q.2) q.1) (univ ×ˢ S) := by
  rintro ⟨ξ₁, p₁⟩ ⟨-, hp₁⟩
  rw [ContinuousWithinAt, nhdsWithin_prod_eq, nhdsWithin_univ, Metric.tendsto_nhds]
  intro ε hε
  set R : ℝ := |ξ₁ - ξ₀| + 1 with hR
  have hR0 : 0 ≤ R := by positivity
  have h1 := eventually_dist_sol_lt hV ξ₀ hy₀ hp₁ hR0 (half_pos hε)
  obtain ⟨hsol₁, -⟩ := sol_isSolOn hV ξ₀ y₀ hp₁
  have hcont : Continuous (sol (fun η => V η p₁) ξ₀ (y₀ p₁)) :=
    (continuousOn_univ.1 hsol₁.continuousOn).prodMk (continuousOn_univ.1 hsol₁.continuousOn')
  have h2 : ∀ᶠ ξ in 𝓝 ξ₁,
      dist (sol (fun η => V η p₁) ξ₀ (y₀ p₁) ξ) (sol (fun η => V η p₁) ξ₀ (y₀ p₁) ξ₁) < ε / 2 :=
    Metric.tendsto_nhds.1 (hcont.tendsto ξ₁) _ (half_pos hε)
  have h3 : ∀ᶠ ξ in 𝓝 ξ₁, ξ ∈ Icc (ξ₀ - R) (ξ₀ + R) := by
    have := abs_sub_lt_iff.1 (show |ξ₁ - ξ₀| < R by linarith)
    exact Icc_mem_nhds (by linarith) (by linarith)
  refine Filter.mem_of_superset ((h2.and h3).prod_mk h1) ?_
  rintro ⟨ξ, p⟩ ⟨⟨hξ2, hξI⟩, hp⟩
  show dist (sol (fun η => V η p) ξ₀ (y₀ p) ξ) (sol (fun η => V η p₁) ξ₀ (y₀ p₁) ξ₁) < ε
  calc _ ≤ dist (sol (fun η => V η p) ξ₀ (y₀ p) ξ) (sol (fun η => V η p₁) ξ₀ (y₀ p₁) ξ) +
        dist (sol (fun η => V η p₁) ξ₀ (y₀ p₁) ξ) (sol (fun η => V η p₁) ξ₀ (y₀ p₁) ξ₁) :=
        dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hp ξ hξI) hξ2
    _ = ε := add_halves ε

/-- **Continuity of all `ξ`-derivatives in `(ξ, p)`.** -/
theorem continuousOn_iteratedDeriv_sol {V : ℝ → P → ℂ} {S : Set P}
    (hV : ∀ p ∈ S, ContDiff ℝ ∞ (fun ξ => V ξ p))
    (hVd : ∀ k : ℕ, ContinuousOn (fun q : ℝ × P => iteratedDeriv k (fun ξ => V ξ q.2) q.1)
      (univ ×ˢ S))
    (ξ₀ : ℝ) {y₀ : P → ℂ × ℂ} (hy₀ : ContinuousOn y₀ S) (k : ℕ) :
    ContinuousOn
      (fun q : ℝ × P => iteratedDeriv k (fun ξ => (sol (fun η => V η q.2) ξ₀ (y₀ q.2) ξ).1) q.1)
      (univ ×ˢ S) := by
  have hV0 : ContinuousOn (Function.uncurry V) (univ ×ˢ S) := by
    refine (hVd 0).congr ?_
    intro q _
    dsimp only
    rw [iteratedDeriv_zero]
    rfl
  have hY := continuousOn_sol hV0 ξ₀ hy₀
  have hsm : ∀ p ∈ S,
      ContDiff ℝ ∞ (fun ξ => (sol (fun η => V η p) ξ₀ (y₀ p) ξ).1) ∧
      ContDiff ℝ ∞ (fun ξ => (sol (fun η => V η p) ξ₀ (y₀ p) ξ).2) ∧
      deriv (fun ξ => (sol (fun η => V η p) ξ₀ (y₀ p) ξ).1) =
        (fun ξ => (sol (fun η => V η p) ξ₀ (y₀ p) ξ).2) ∧
      ∀ ξ, deriv (deriv (fun ξ => (sol (fun η => V η p) ξ₀ (y₀ p) ξ).1)) ξ =
        V ξ p * (sol (fun η => V η p) ξ₀ (y₀ p) ξ).1 := fun p hp =>
    IsSolOn.contDiff (hV p hp) (sol_isSolOn hV0 ξ₀ y₀ hp).1
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | _ | k
    · refine (continuous_fst.comp_continuousOn hY).congr ?_
      intro q _
      dsimp only [Function.comp_apply]
      rw [iteratedDeriv_zero]
    · refine (continuous_snd.comp_continuousOn hY).congr ?_
      intro q hq
      obtain ⟨-, -, hd, -⟩ := hsm q.2 hq.2
      dsimp only [Function.comp_apply]
      rw [zero_add, iteratedDeriv_one, hd]
    · have hsum : ContinuousOn (fun q : ℝ × P => ∑ i ∈ Finset.range (k + 1),
          ((k.choose i : ℕ) : ℂ) * iteratedDeriv i (fun ξ => V ξ q.2) q.1 *
            iteratedDeriv (k - i) (fun ξ => (sol (fun η => V η q.2) ξ₀ (y₀ q.2) ξ).1) q.1)
          (univ ×ˢ S) := by
        apply continuousOn_finsetSum
        intro i _
        exact (continuousOn_const.mul (hVd i)).mul (ih (k - i) (by omega))
      refine hsum.congr ?_
      intro q hq
      obtain ⟨hψ, -, -, hdd⟩ := hsm q.2 hq.2
      have hdd' : deriv (deriv (fun ξ => (sol (fun η => V η q.2) ξ₀ (y₀ q.2) ξ).1)) =
          fun ξ => V ξ q.2 * (sol (fun η => V η q.2) ξ₀ (y₀ q.2) ξ).1 := funext hdd
      show iteratedDeriv (k + 1 + 1) _ q.1 = _
      rw [iteratedDeriv_succ', iteratedDeriv_succ', hdd',
        iteratedDeriv_fun_mul ((contDiff_infty.1 (hV q.2 hq.2) k).contDiffAt)
          ((contDiff_infty.1 hψ k).contDiffAt)]

end NonUniqueEuler.LinODE
