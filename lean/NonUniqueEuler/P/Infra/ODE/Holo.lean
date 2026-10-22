import NonUniqueEuler.Defs.Infra.ODE
import NonUniqueEuler.I.Infra.ODE.Existence
import NonUniqueEuler.I.Infra.ODE.Gronwall
import NonUniqueEuler.H.Infra.ODE.Holo.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Topology.Order.Compact
import Mathlib.Algebra.Order.Group.Pointwise.Interval

/-!
# Proof (I-ODE): holomorphic dependence on a complex parameter

Proof of `I/Infra/ODE/Holo.lean`.

* `continuousOn_deriv_param` is `Holo.continuousOn_deriv_param'`
  (`H/Infra/ODE/Holo/Basic.lean`): Cauchy's estimate for `f(·, p) - f(·, p₀)` on a small circle,
  uniform smallness of this difference on a compact disc (generalized tube lemma), and
  continuity of `∂_z f(·, p₀)`.
* `differentiableOn_sol` and `isInhomSolOn_deriv_sol` both follow from
  `Holo.hasDerivAt_sol`: for `z ∈ U`, let `D = (D₁, D₂)` solve the variational equation
  `D'' = V(·, z) D + ∂_z V(·, z) ψ(·; z)` with zero data at `ξ₀` (it exists since `∂_z V(·, z)`
  is continuous, by `continuousOn_deriv_param`). Then `w ↦ Y(ξ₁; w)` has complex derivative
  `D(ξ₁)` at `z`. Proof (instead of the Picard iteration of the interface sketch, a direct
  difference-quotient argument): on `s = [ξ₀, ξ₁]`, the error
  `E_w = Y(·; w) - Y(·; z) - (w - z) D` solves `E'' = V(·, z) E + F_w` with
  `F_w = (V(w) - V(z) - (w - z) ∂_z V(z)) ψ(z) + (V(w) - V(z)) (ψ(w) - ψ(z))` and zero data.
  The uniform Taylor bound (`Holo.eventually_norm_sub_sub_deriv_le`) gives
  `|V(w) - V(z) - (w - z) ∂_z V(z)| ≤ η |w - z|` and `|V(w) - V(z)| ≤ (1 + A) |w - z|` on `s`;
  Grönwall (`norm_sub_le_of_isSolOn`) gives `|ψ(w) - ψ(z)| ≤ C |w - z|` on `s`; so
  `|F_w| ≤ |w - z| (η B + C' |w - z|)` and Grönwall (`IsInhomSolOn.norm_le`) gives
  `|E_w(ξ₁)| = o(|w - z|)`.
-/

noncomputable section

open Set Filter Topology Metric

namespace NonUniqueEuler.LinODE

namespace Holo

variable {V : ℝ → ℂ → ℂ} {U : Set ℂ}

theorem continuous_slice (hV : ContinuousOn (Function.uncurry V) (univ ×ˢ U)) {w : ℂ}
    (hw : w ∈ U) : Continuous (fun η => V η w) :=
  hV.comp_continuous (continuous_id.prodMk continuous_const) (fun _ => ⟨mem_univ _, hw⟩)

theorem continuousOn_deriv_slice (hU : IsOpen U)
    (hV : ContinuousOn (Function.uncurry V) (univ ×ˢ U))
    (hVd : ∀ ξ, DifferentiableOn ℂ (V ξ) U) :
    ContinuousOn (fun q : ℂ × ℝ => deriv (V q.2) q.1) (U ×ˢ univ) :=
  continuousOn_deriv_param' (f := fun z ξ => V ξ z) hU
    (hV.comp continuous_swap.continuousOn (fun _ hq => ⟨hq.2, hq.1⟩)) (fun ξ _ => hVd ξ)

theorem continuous_deriv_slice (hU : IsOpen U)
    (hV : ContinuousOn (Function.uncurry V) (univ ×ˢ U))
    (hVd : ∀ ξ, DifferentiableOn ℂ (V ξ) U) {z : ℂ} (hz : z ∈ U) :
    Continuous (fun ξ => deriv (V ξ) z) :=
  (continuousOn_deriv_slice hU hV hVd).comp_continuous (continuous_const.prodMk continuous_id)
    (fun _ => ⟨hz, mem_univ _⟩)

/-- The variational equation has a global solution with zero data at `ξ₀`. -/
theorem exists_variational (hU : IsOpen U)
    (hV : ContinuousOn (Function.uncurry V) (univ ×ˢ U))
    (hVd : ∀ ξ, DifferentiableOn ℂ (V ξ) U) (ξ₀ : ℝ) (y₀ : ℂ × ℂ) {z : ℂ} (hz : z ∈ U) :
    ∃ D₁ D₂ : ℝ → ℂ, IsInhomSolOn (fun ξ => V ξ z)
        (fun ξ => deriv (V ξ) z * (sol (fun η => V η z) ξ₀ y₀ ξ).1) univ D₁ D₂ ∧
      D₁ ξ₀ = 0 ∧ D₂ ξ₀ = 0 :=
  exists_isInhomSolOn_univ (continuous_slice hV hz)
    ((continuous_deriv_slice hU hV hVd hz).mul
      (continuousOn_univ.1 (sol_spec (continuous_slice hV hz) ξ₀ y₀).1.continuousOn)) ξ₀ 0 0

/-- **Main estimate.** The solution is complex-differentiable in the parameter, and its
derivative is the solution `D` of the variational equation with zero data. -/
theorem hasDerivAt_sol (hU : IsOpen U)
    (hV : ContinuousOn (Function.uncurry V) (univ ×ˢ U))
    (hVd : ∀ ξ, DifferentiableOn ℂ (V ξ) U) (ξ₀ : ℝ) (y₀ : ℂ × ℂ) {z : ℂ} (hz : z ∈ U)
    {D₁ D₂ : ℝ → ℂ}
    (hD : IsInhomSolOn (fun ξ => V ξ z)
      (fun ξ => deriv (V ξ) z * (sol (fun η => V η z) ξ₀ y₀ ξ).1) univ D₁ D₂)
    (hD0 : D₁ ξ₀ = 0) (hD0' : D₂ ξ₀ = 0) (ξ₁ : ℝ) :
    HasDerivAt (fun w => sol (fun η => V η w) ξ₀ y₀ ξ₁) (D₁ ξ₁, D₂ ξ₁) z := by
  set s := uIcc ξ₀ ξ₁ with hs_def
  have hs : IsCompact s := isCompact_uIcc
  have hso : s.OrdConnected := ordConnected_uIcc
  have hξ₀s : ξ₀ ∈ s := left_mem_uIcc
  have hξ₁s : ξ₁ ∈ s := right_mem_uIcc
  set X := |ξ₁ - ξ₀| with hX_def
  have hX0 : 0 ≤ X := abs_nonneg _
  have hXs : ∀ ξ ∈ s, |ξ - ξ₀| ≤ X := fun ξ hξ => abs_sub_left_of_mem_uIcc hξ
  have hψ : ∀ w ∈ U, IsSolOn (fun η => V η w) univ (fun ξ => (sol (fun η => V η w) ξ₀ y₀ ξ).1)
      (fun ξ => (sol (fun η => V η w) ξ₀ y₀ ξ).2) ∧ sol (fun η => V η w) ξ₀ y₀ ξ₀ = y₀ :=
    fun w hw => sol_spec (continuous_slice hV hw) ξ₀ y₀
  -- bounds on `s`
  obtain ⟨K₀, hK₀⟩ := hs.exists_bound_of_continuousOn (continuous_slice hV hz).continuousOn
  set K := max K₀ 1 with hK_def
  have hK1 : 1 ≤ K := le_max_right _ _
  have hK : ∀ ξ ∈ s, ‖V ξ z‖ ≤ K := fun ξ hξ => (hK₀ ξ hξ).trans (le_max_left _ _)
  obtain ⟨A, hA⟩ :=
    hs.exists_bound_of_continuousOn (continuous_deriv_slice hU hV hVd hz).continuousOn
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA ξ₀ hξ₀s)
  obtain ⟨B, hB⟩ :=
    hs.exists_bound_of_continuousOn ((hψ z hz).1.continuousOn.mono (subset_univ s))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB ξ₀ hξ₀s)
  have hG₁ : 0 ≤ gronwallBound 0 (K + 1) 1 X := gronwallBound_zero_one_nonneg (by linarith) hX0
  have hG₂ : 0 ≤ gronwallBound 0 K 1 X := gronwallBound_zero_one_nonneg (by linarith) hX0
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨η, hη, hη1, hηε⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧
      η ≤ ε / (2 * (gronwallBound 0 K 1 X * B + 1)) :=
    ⟨min 1 (ε / (2 * (gronwallBound 0 K 1 X * B + 1))), lt_min one_pos (by positivity),
      min_le_left _ _, min_le_right _ _⟩
  obtain ⟨ρ, hρ, hρ1, hρε⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / (1 + A) ∧
      ρ ≤ ε / (2 * (gronwallBound 0 K 1 X * ((1 + A) * ((1 + A) * B *
        gronwallBound 0 (K + 1) 1 X)) + 1)) :=
    ⟨min (1 / (1 + A)) (ε / (2 * (gronwallBound 0 K 1 X * ((1 + A) * ((1 + A) * B *
        gronwallBound 0 (K + 1) 1 X)) + 1))), lt_min (by positivity) (by positivity),
      min_le_left _ _, min_le_right _ _⟩
  filter_upwards [eventually_norm_sub_sub_deriv_le hU (continuousOn_deriv_slice hU hV hVd) hVd
    hz hs hη, hU.mem_nhds hz, ball_mem_nhds z hρ] with w hTw hwU hwρ
  rw [mem_ball, dist_eq_norm] at hwρ
  set t := ‖w - z‖ with ht_def
  have ht0 : 0 ≤ t := norm_nonneg _
  -- Lipschitz bound for `V` in the parameter, uniformly on `s`
  have hLip : ∀ ξ ∈ s, ‖V ξ w - V ξ z‖ ≤ (1 + A) * t := by
    intro ξ hξ
    calc ‖V ξ w - V ξ z‖
        = ‖(V ξ w - V ξ z - (w - z) * deriv (V ξ) z) + (w - z) * deriv (V ξ) z‖ := by
          congr 1; ring
      _ ≤ ‖V ξ w - V ξ z - (w - z) * deriv (V ξ) z‖ + ‖(w - z) * deriv (V ξ) z‖ :=
          norm_add_le _ _
      _ ≤ η * t + t * A := by
          rw [norm_mul]
          exact add_le_add (hTw ξ hξ) (mul_le_mul_of_nonneg_left (hA ξ hξ) ht0)
      _ ≤ 1 * t + t * A := by gcongr
      _ = (1 + A) * t := by ring
  have htA : (1 + A) * t ≤ 1 := by
    have h1 : t ≤ 1 / (1 + A) := hwρ.le.trans hρ1
    rwa [le_div_iff₀ (by linarith), mul_comm] at h1
  have hKw : ∀ ξ ∈ s, ‖V ξ w‖ ≤ K + 1 := by
    intro ξ hξ
    calc ‖V ξ w‖ = ‖V ξ z + (V ξ w - V ξ z)‖ := by congr 1; ring
      _ ≤ ‖V ξ z‖ + ‖V ξ w - V ξ z‖ := norm_add_le _ _
      _ ≤ K + 1 := add_le_add (hK ξ hξ) ((hLip ξ hξ).trans htA)
  -- Lipschitz bound for the solution in the parameter, uniformly on `s`
  have hdiff : ∀ ξ ∈ s, ‖(sol (fun η => V η w) ξ₀ y₀ ξ).1 - (sol (fun η => V η z) ξ₀ y₀ ξ).1‖
      ≤ (1 + A) * t * B * gronwallBound 0 (K + 1) 1 X := by
    intro ξ hξ
    have h := norm_sub_le_of_isSolOn hso (by linarith : (1 : ℝ) ≤ K + 1) hKw
      (fun ξ hξ => by rw [norm_sub_rev]; exact hLip ξ hξ) hB
      ((hψ w hwU).1.mono (subset_univ s)) ((hψ z hz).1.mono (subset_univ s)) hξ₀s ξ hξ
    rw [(hψ w hwU).2, (hψ z hz).2] at h
    simp only [sub_self, Prod.mk_zero_zero, norm_zero] at h
    calc ‖(sol (fun η => V η w) ξ₀ y₀ ξ).1 - (sol (fun η => V η z) ξ₀ y₀ ξ).1‖
        ≤ ‖((sol (fun η => V η w) ξ₀ y₀ ξ).1 - (sol (fun η => V η z) ξ₀ y₀ ξ).1,
            (sol (fun η => V η w) ξ₀ y₀ ξ).2 - (sol (fun η => V η z) ξ₀ y₀ ξ).2)‖ := by
          rw [Prod.norm_mk]; exact le_max_left _ _
      _ ≤ _ := h
      _ ≤ (1 + A) * t * B * gronwallBound 0 (K + 1) 1 X :=
          gronwallBound_zero_le (by linarith) (by positivity) (abs_nonneg _) (hXs ξ hξ)
  -- the error `E_w` solves an inhomogeneous equation with small forcing
  set F : ℝ → ℂ := fun ξ => (V ξ w - V ξ z - (w - z) * deriv (V ξ) z) *
      (sol (fun η => V η z) ξ₀ y₀ ξ).1 +
    (V ξ w - V ξ z) * ((sol (fun η => V η w) ξ₀ y₀ ξ).1 - (sol (fun η => V η z) ξ₀ y₀ ξ).1)
    with hF_def
  set E₁ : ℝ → ℂ := fun ξ => (sol (fun η => V η w) ξ₀ y₀ ξ).1 -
    (sol (fun η => V η z) ξ₀ y₀ ξ).1 - (w - z) * D₁ ξ with hE₁_def
  set E₂ : ℝ → ℂ := fun ξ => (sol (fun η => V η w) ξ₀ y₀ ξ).2 -
    (sol (fun η => V η z) ξ₀ y₀ ξ).2 - (w - z) * D₂ ξ with hE₂_def
  have hE : IsInhomSolOn (fun ξ => V ξ z) F univ E₁ E₂ := by
    obtain ⟨hw1, hw2⟩ := (hψ w hwU).1
    obtain ⟨hz1, hz2⟩ := (hψ z hz).1
    obtain ⟨hD1, hD2⟩ := hD
    constructor
    · intro ξ hξ
      exact ((hw1 ξ hξ).sub (hz1 ξ hξ)).sub ((hD1 ξ hξ).const_mul (w - z))
    · intro ξ hξ
      refine (((hw2 ξ hξ).sub (hz2 ξ hξ)).sub ((hD2 ξ hξ).const_mul (w - z))).congr_deriv ?_
      simp only [hF_def, hE₁_def]
      ring
  have hF : ∀ ξ ∈ s, ‖F ξ‖ ≤
      t * (η * B + (1 + A) * ((1 + A) * t * B * gronwallBound 0 (K + 1) 1 X)) := by
    intro ξ hξ
    calc ‖F ξ‖ ≤ ‖(V ξ w - V ξ z - (w - z) * deriv (V ξ) z) *
            (sol (fun η => V η z) ξ₀ y₀ ξ).1‖ +
          ‖(V ξ w - V ξ z) * ((sol (fun η => V η w) ξ₀ y₀ ξ).1 -
            (sol (fun η => V η z) ξ₀ y₀ ξ).1)‖ := norm_add_le _ _
      _ = ‖V ξ w - V ξ z - (w - z) * deriv (V ξ) z‖ * ‖(sol (fun η => V η z) ξ₀ y₀ ξ).1‖ +
          ‖V ξ w - V ξ z‖ * ‖(sol (fun η => V η w) ξ₀ y₀ ξ).1 -
            (sol (fun η => V η z) ξ₀ y₀ ξ).1‖ := by rw [norm_mul, norm_mul]
      _ ≤ (η * t) * B + ((1 + A) * t) * ((1 + A) * t * B * gronwallBound 0 (K + 1) 1 X) := by
          gcongr
          · exact hTw ξ hξ
          · exact hB ξ hξ
          · exact hLip ξ hξ
          · exact hdiff ξ hξ
      _ = t * (η * B + (1 + A) * ((1 + A) * t * B * gronwallBound 0 (K + 1) 1 X)) := by ring
  have hgr := (hE.mono (subset_univ s)).norm_le hso hK1 hK hF hξ₀s ξ₁ hξ₁s
  have h0 : ‖(E₁ ξ₀, E₂ ξ₀)‖ = 0 := by
    simp [hE₁_def, hE₂_def, (hψ w hwU).2, (hψ z hz).2, hD0, hD0']
  rw [h0] at hgr
  have hvec : sol (fun η => V η w) ξ₀ y₀ ξ₁ - sol (fun η => V η z) ξ₀ y₀ ξ₁ -
      (w - z) • (D₁ ξ₁, D₂ ξ₁) = (E₁ ξ₁, E₂ ξ₁) := by
    ext <;> simp [hE₁_def, hE₂_def]
  have hδ0 : 0 ≤ t * (η * B + (1 + A) * ((1 + A) * t * B * gronwallBound 0 (K + 1) 1 X)) := by
    positivity
  have hc₁ : gronwallBound 0 K 1 X * B * η ≤ ε / 2 :=
    mul_le_half_of_le (by positivity) hηε hε
  have hc₂ : gronwallBound 0 K 1 X * ((1 + A) * ((1 + A) * B * gronwallBound 0 (K + 1) 1 X)) *
      t ≤ ε / 2 :=
    mul_le_half_of_le (by positivity) (hwρ.le.trans hρε) hε
  show ‖sol (fun η => V η w) ξ₀ y₀ ξ₁ - sol (fun η => V η z) ξ₀ y₀ ξ₁ -
      (w - z) • (D₁ ξ₁, D₂ ξ₁)‖ ≤ ε * t
  rw [hvec]
  calc ‖(E₁ ξ₁, E₂ ξ₁)‖
      ≤ gronwallBound 0 K
          (t * (η * B + (1 + A) * ((1 + A) * t * B * gronwallBound 0 (K + 1) 1 X))) X := hgr
    _ ≤ t * (η * B + (1 + A) * ((1 + A) * t * B * gronwallBound 0 (K + 1) 1 X)) *
          gronwallBound 0 K 1 X :=
        gronwallBound_zero_le (by linarith) hδ0 hX0 le_rfl
    _ = t * (gronwallBound 0 K 1 X * B * η + gronwallBound 0 K 1 X *
          ((1 + A) * ((1 + A) * B * gronwallBound 0 (K + 1) 1 X)) * t) := by ring
    _ ≤ t * (ε / 2 + ε / 2) := by gcongr
    _ = ε * t := by ring

end Holo

/-- **Holomorphic dependence on a complex parameter.** -/
theorem differentiableOn_sol {V : ℝ → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hV : ContinuousOn (Function.uncurry V) (univ ×ˢ U))
    (hVd : ∀ ξ, DifferentiableOn ℂ (V ξ) U) (ξ₀ : ℝ) (y₀ : ℂ × ℂ) (ξ : ℝ) :
    DifferentiableOn ℂ (fun z => sol (fun η => V η z) ξ₀ y₀ ξ) U := by
  intro z hz
  obtain ⟨D₁, D₂, hD, hD0, hD0'⟩ := Holo.exists_variational hU hV hVd ξ₀ y₀ hz
  exact (Holo.hasDerivAt_sol hU hV hVd ξ₀ y₀ hz hD hD0 hD0' ξ).differentiableAt.differentiableWithinAt

/-- **The variational equation.** The `z`-derivative of the solution solves
`φ'' = V φ + (∂_z V) ψ` with zero data at `ξ₀`. -/
theorem isInhomSolOn_deriv_sol {V : ℝ → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hV : ContinuousOn (Function.uncurry V) (univ ×ˢ U))
    (hVd : ∀ ξ, DifferentiableOn ℂ (V ξ) U) (ξ₀ : ℝ) (y₀ : ℂ × ℂ) {z : ℂ} (hz : z ∈ U) :
    IsInhomSolOn (fun ξ => V ξ z)
        (fun ξ => deriv (V ξ) z * (sol (fun η => V η z) ξ₀ y₀ ξ).1) univ
        (fun ξ => deriv (fun w => (sol (fun η => V η w) ξ₀ y₀ ξ).1) z)
        (fun ξ => deriv (fun w => (sol (fun η => V η w) ξ₀ y₀ ξ).2) z) ∧
      deriv (fun w => (sol (fun η => V η w) ξ₀ y₀ ξ₀).1) z = 0 ∧
      deriv (fun w => (sol (fun η => V η w) ξ₀ y₀ ξ₀).2) z = 0 := by
  obtain ⟨D₁, D₂, hD, hD0, hD0'⟩ := Holo.exists_variational hU hV hVd ξ₀ y₀ hz
  have h1 : ∀ ξ, deriv (fun w => (sol (fun η => V η w) ξ₀ y₀ ξ).1) z = D₁ ξ := by
    intro ξ
    have h := (hasFDerivAt_fst (𝕜 := ℂ) (E := ℂ) (F := ℂ)
      (p := sol (fun η => V η z) ξ₀ y₀ ξ)).comp_hasDerivAt z
      (Holo.hasDerivAt_sol hU hV hVd ξ₀ y₀ hz hD hD0 hD0' ξ)
    exact h.deriv
  have h2 : ∀ ξ, deriv (fun w => (sol (fun η => V η w) ξ₀ y₀ ξ).2) z = D₂ ξ := by
    intro ξ
    have h := (hasFDerivAt_snd (𝕜 := ℂ) (E := ℂ) (F := ℂ)
      (p := sol (fun η => V η z) ξ₀ y₀ ξ)).comp_hasDerivAt z
      (Holo.hasDerivAt_sol hU hV hVd ξ₀ y₀ hz hD hD0 hD0' ξ)
    exact h.deriv
  simp only [h1, h2]
  exact ⟨hD, hD0, hD0'⟩

/-- **Joint continuity of the complex derivative** of a function that is jointly continuous and
holomorphic in its first variable (Cauchy's formula). -/
theorem continuousOn_deriv_param {P : Type*} [TopologicalSpace P] {f : ℂ → P → ℂ}
    {U : Set ℂ} (hU : IsOpen U) {S : Set P} (hf : ContinuousOn (Function.uncurry f) (U ×ˢ S))
    (hfd : ∀ p ∈ S, DifferentiableOn ℂ (fun z => f z p) U) :
    ContinuousOn (fun q : ℂ × P => deriv (fun z => f z q.2) q.1) (U ×ˢ S) :=
  Holo.continuousOn_deriv_param' hU hf hfd

end NonUniqueEuler.LinODE
