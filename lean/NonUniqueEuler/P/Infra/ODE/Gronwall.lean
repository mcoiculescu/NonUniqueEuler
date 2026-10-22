import NonUniqueEuler.Defs.Infra.ODE
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Order.LeftRightNhds

/-!
# Proof of the interface (I-ODE): Grönwall bounds for `ψ'' = V ψ + F`

Proves the declarations of `NonUniqueEuler/I/Infra/ODE/Gronwall.lean` (statements copied
verbatim). Norms on `ℂ × ℂ` are the max norm.

* `IsInhomSolOn.norm_le`: for `ξ ≥ ξ₀`, Mathlib's `norm_le_gronwallBound_of_norm_deriv_right_le`
  applied to `Y = (ψ, ψ')` on `[ξ₀, ξ] ⊆ s` (`‖Y'‖ ≤ K ‖Y‖ + δ`, `GronwallAux.norm_deriv_pair_le`;
  derivatives within `s` become right derivatives since `s ∈ 𝓝[≥] x`,
  `Set.OrdConnected.mem_nhdsGE`). For `ξ ≤ ξ₀` the same bound is applied to the reflected
  system `t ↦ (ψ (-t), -ψ' (-t))`, which solves `ψ'' = V(-·) ψ + F(-·)` on `-s`
  (`GronwallAux.IsInhomSolOn.comp_neg`); the max norm is invariant under `ψ' ↦ -ψ'`.
* `IsSolOn.norm_le`: the case `F = 0`, `δ = 0` (`gronwallBound_ε0`).
* `norm_sub_le_of_isSolOn`: `(ψ₁ - ψ₂, ψ₁' - ψ₂')` solves `ψ'' = V₁ ψ + (V₁ - V₂) ψ₂`.
* `int_gronwall`: `b, u` are extended continuously to `ℝ` through `Set.projIcc`; then
  `G = R e^{-B}`, `R = c + ∫_α^· b (c + u)`, `B = ∫_α^· b`, has `G' = b e^{-B} (c + u - R) ≤ 0`
  on `(α, β)`, so `G` is antitone on `[α, β]` (`antitoneOn_of_hasDerivWithinAt_nonpos`) and
  `c + u x ≤ R x ≤ c e^{B x}`.
-/

noncomputable section

open Set Filter Topology

namespace NonUniqueEuler.LinODE

variable {V F : ℝ → ℂ} {s : Set ℝ} {ψ ψ' : ℝ → ℂ}

namespace GronwallAux

/-- The first-order bound `‖(ψ', V ψ + F)‖ ≤ K ‖(ψ, ψ')‖ + δ` (pointwise, `K ≥ 1`, `δ ≥ 0`). -/
theorem norm_deriv_pair_le {K δ : ℝ} (hK : 1 ≤ K) (hδ : 0 ≤ δ) {v f a a' : ℂ}
    (hv : ‖v‖ ≤ K) (hf : ‖f‖ ≤ δ) :
    ‖(a', v * a + f)‖ ≤ K * ‖(a, a')‖ + δ := by
  have h1 : ‖a‖ ≤ ‖(a, a')‖ := norm_fst_le (a, a')
  have h2 : ‖a'‖ ≤ ‖(a, a')‖ := norm_snd_le (a, a')
  have hY : 0 ≤ ‖(a, a')‖ := norm_nonneg _
  have hKY : ‖(a, a')‖ ≤ K * ‖(a, a')‖ := le_mul_of_one_le_left hY hK
  rw [Prod.norm_mk]
  refine max_le (by linarith) ?_
  calc ‖v * a + f‖ ≤ ‖v * a‖ + ‖f‖ := norm_add_le _ _
    _ = ‖v‖ * ‖a‖ + ‖f‖ := by rw [norm_mul]
    _ ≤ K * ‖(a, a')‖ + δ :=
        add_le_add (mul_le_mul hv h1 (norm_nonneg _) (by linarith)) hf

/-- The forward Grönwall bound (`ξ₀ ≤ ξ`). -/
theorem IsInhomSolOn.norm_le_of_le (hs : s.OrdConnected) {K δ : ℝ} (hK : 1 ≤ K)
    (hV : ∀ ξ ∈ s, ‖V ξ‖ ≤ K) (hF : ∀ ξ ∈ s, ‖F ξ‖ ≤ δ) (h : IsInhomSolOn V F s ψ ψ')
    {ξ₀ : ℝ} (hξ₀ : ξ₀ ∈ s) {ξ : ℝ} (hξ : ξ ∈ s) (hle : ξ₀ ≤ ξ) :
    ‖(ψ ξ, ψ' ξ)‖ ≤ gronwallBound ‖(ψ ξ₀, ψ' ξ₀)‖ K δ (ξ - ξ₀) := by
  have hsub : Icc ξ₀ ξ ⊆ s := hs.out hξ₀ hξ
  have hδ : 0 ≤ δ := (norm_nonneg _).trans (hF ξ₀ hξ₀)
  have hY : ∀ x ∈ s,
      HasDerivWithinAt (fun t => (ψ t, ψ' t)) (ψ' x, V x * ψ x + F x) s x :=
    fun x hx => (h.hasDerivWithinAt x hx).prodMk (h.hasDerivWithinAt' x hx)
  refine norm_le_gronwallBound_of_norm_deriv_right_le (f := fun t => (ψ t, ψ' t))
    (f' := fun x => (ψ' x, V x * ψ x + F x)) (a := ξ₀) (b := ξ) ?_ ?_ le_rfl ?_ ξ
    ⟨hle, le_rfl⟩
  · exact fun x hx => ((hY x (hsub hx)).continuousWithinAt).mono hsub
  · intro x hx
    have hxs : x ∈ s := hsub (Ico_subset_Icc_self hx)
    exact (hY x hxs).mono_of_mem_nhdsWithin (hs.mem_nhdsGE hxs hξ hx.2)
  · intro x hx
    have hxs : x ∈ s := hsub (Ico_subset_Icc_self hx)
    exact norm_deriv_pair_le hK hδ (hV x hxs) (hF x hxs)

/-- Reflection `ξ ↦ -ξ`: `(ψ(-·), -ψ'(-·))` solves `ψ'' = V(-·) ψ + F(-·)` on `-s`. -/
theorem IsInhomSolOn.comp_neg (h : IsInhomSolOn V F s ψ ψ') :
    IsInhomSolOn (fun t => V (-t)) (fun t => F (-t)) (-s) (fun t => ψ (-t))
      (fun t => -ψ' (-t)) := by
  have hmaps : MapsTo (Neg.neg : ℝ → ℝ) (-s) s := fun t ht => Set.mem_neg.1 ht
  constructor
  · intro t ht
    have := (h.hasDerivWithinAt (-t) (Set.mem_neg.1 ht)).scomp t
      (hasDerivWithinAt_neg t (-s)) hmaps
    simpa [Function.comp_def] using this
  · intro t ht
    have := ((h.hasDerivWithinAt' (-t) (Set.mem_neg.1 ht)).scomp t
      (hasDerivWithinAt_neg t (-s)) hmaps).neg
    exact this.congr_deriv (by simp only [neg_smul, one_smul, neg_neg])

theorem ordConnected_neg (hs : s.OrdConnected) : (-s).OrdConnected :=
  hs.preimage_anti (f := (Neg.neg : ℝ → ℝ)) fun _ _ hab => neg_le_neg hab

end GronwallAux

open GronwallAux in
/-- **Grönwall bound** for the inhomogeneous equation on an interval, in both directions. -/
theorem IsInhomSolOn.norm_le (hs : s.OrdConnected) {K δ : ℝ} (hK : 1 ≤ K)
    (hV : ∀ ξ ∈ s, ‖V ξ‖ ≤ K) (hF : ∀ ξ ∈ s, ‖F ξ‖ ≤ δ) (h : IsInhomSolOn V F s ψ ψ')
    {ξ₀ : ℝ} (hξ₀ : ξ₀ ∈ s) :
    ∀ ξ ∈ s, ‖(ψ ξ, ψ' ξ)‖ ≤ gronwallBound ‖(ψ ξ₀, ψ' ξ₀)‖ K δ |ξ - ξ₀| := by
  intro ξ hξ
  rcases le_total ξ₀ ξ with hle | hle
  · rw [abs_of_nonneg (sub_nonneg.2 hle)]
    exact GronwallAux.IsInhomSolOn.norm_le_of_le hs hK hV hF h hξ₀ hξ hle
  · have key := GronwallAux.IsInhomSolOn.norm_le_of_le (ordConnected_neg hs) hK
      (fun t ht => hV (-t) (Set.mem_neg.1 ht)) (fun t ht => hF (-t) (Set.mem_neg.1 ht))
      (GronwallAux.IsInhomSolOn.comp_neg h) (ξ₀ := -ξ₀)
      (Set.mem_neg.2 (by rwa [neg_neg])) (ξ := -ξ) (Set.mem_neg.2 (by rwa [neg_neg]))
      (neg_le_neg hle)
    have e : -ξ - -ξ₀ = ξ₀ - ξ := by ring
    rw [e] at key
    rw [abs_of_nonpos (sub_nonpos.2 hle), neg_sub]
    simpa only [neg_neg, Prod.norm_mk, norm_neg] using key

/-- **Grönwall bound** for the homogeneous equation on an interval, in both directions. -/
theorem IsSolOn.norm_le (hs : s.OrdConnected) {K : ℝ} (hK : 1 ≤ K)
    (hV : ∀ ξ ∈ s, ‖V ξ‖ ≤ K) (h : IsSolOn V s ψ ψ') {ξ₀ : ℝ} (hξ₀ : ξ₀ ∈ s) :
    ∀ ξ ∈ s, ‖(ψ ξ, ψ' ξ)‖ ≤ ‖(ψ ξ₀, ψ' ξ₀)‖ * Real.exp (K * |ξ - ξ₀|) := by
  intro ξ hξ
  have := h.toInhom.norm_le hs hK hV (δ := 0) (fun ξ _ => by simp) hξ₀ ξ hξ
  rwa [gronwallBound_ε0] at this

/-- **Continuous dependence on the coefficient.** -/
theorem norm_sub_le_of_isSolOn {V₁ V₂ ψ₁ ψ₁' ψ₂ ψ₂' : ℝ → ℂ} (hs : s.OrdConnected)
    {K δ B : ℝ} (hK : 1 ≤ K) (hV₁ : ∀ ξ ∈ s, ‖V₁ ξ‖ ≤ K) (hV : ∀ ξ ∈ s, ‖V₂ ξ - V₁ ξ‖ ≤ δ)
    (hB : ∀ ξ ∈ s, ‖ψ₂ ξ‖ ≤ B) (h₁ : IsSolOn V₁ s ψ₁ ψ₁') (h₂ : IsSolOn V₂ s ψ₂ ψ₂')
    {ξ₀ : ℝ} (hξ₀ : ξ₀ ∈ s) :
    ∀ ξ ∈ s, ‖(ψ₁ ξ - ψ₂ ξ, ψ₁' ξ - ψ₂' ξ)‖ ≤
      gronwallBound ‖(ψ₁ ξ₀ - ψ₂ ξ₀, ψ₁' ξ₀ - ψ₂' ξ₀)‖ K (δ * B) |ξ - ξ₀| := by
  have hδ : 0 ≤ δ := (norm_nonneg _).trans (hV ξ₀ hξ₀)
  have hD : IsInhomSolOn V₁ (fun ξ => (V₁ ξ - V₂ ξ) * ψ₂ ξ) s (fun ξ => ψ₁ ξ - ψ₂ ξ)
      (fun ξ => ψ₁' ξ - ψ₂' ξ) := by
    refine ⟨fun ξ hξ => (h₁.hasDerivWithinAt ξ hξ).sub (h₂.hasDerivWithinAt ξ hξ),
      fun ξ hξ => ?_⟩
    exact ((h₁.hasDerivWithinAt' ξ hξ).sub (h₂.hasDerivWithinAt' ξ hξ)).congr_deriv (by ring)
  refine hD.norm_le hs hK hV₁ (fun ξ hξ => ?_) hξ₀
  rw [norm_mul, norm_sub_rev]
  exact mul_le_mul (hV ξ hξ) (hB ξ hξ) (norm_nonneg _) hδ

/-- **Integral Grönwall inequality** with a variable coefficient. -/
theorem int_gronwall {u b : ℝ → ℝ} {c α β : ℝ} (hu : ContinuousOn u (Icc α β))
    (hb : ContinuousOn b (Icc α β)) (hb0 : ∀ x ∈ Icc α β, 0 ≤ b x) (hc : 0 ≤ c)
    (h : ∀ x ∈ Icc α β, u x ≤ ∫ t in α..x, b t * (c + u t)) :
    ∀ x ∈ Icc α β, c + u x ≤ c * Real.exp (∫ t in α..x, b t) := by
  -- the hypothesis `hc : 0 ≤ c` is not needed
  intro x hx
  have hαβ : α ≤ β := hx.1.trans hx.2
  -- continuous extensions of `b` and `u` to `ℝ`
  obtain ⟨e, he_def⟩ : ∃ e : ℝ → ℝ, e = fun t => (projIcc α β hαβ t : ℝ) := ⟨_, rfl⟩
  have he_cont : Continuous e := he_def ▸ continuous_subtype_val.comp continuous_projIcc
  have he_mem : ∀ t, e t ∈ Icc α β := fun t => he_def ▸ (projIcc α β hαβ t).2
  have he_eq : ∀ t ∈ Icc α β, e t = t := fun t ht => by
    rw [he_def]; simp only [projIcc_of_mem hαβ ht]
  have hb' : Continuous fun t => b (e t) := hb.comp_continuous he_cont he_mem
  have hu' : Continuous fun t => u (e t) := hu.comp_continuous he_cont he_mem
  have hint_b : ∀ y ∈ Icc α β, ∫ t in α..y, b (e t) = ∫ t in α..y, b t := by
    intro y hy
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [uIcc_of_le hy.1] at ht
    simp only [he_eq t ⟨ht.1, ht.2.trans hy.2⟩]
  have hint_bu : ∀ y ∈ Icc α β,
      ∫ t in α..y, b (e t) * (c + u (e t)) = ∫ t in α..y, b t * (c + u t) := by
    intro y hy
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [uIcc_of_le hy.1] at ht
    simp only [he_eq t ⟨ht.1, ht.2.trans hy.2⟩]
  -- `B = ∫_α^· b`, `R = c + ∫_α^· b (c + u)`, `G = R e^{-B}`
  obtain ⟨B, hB_def⟩ : ∃ B : ℝ → ℝ, B = fun y => ∫ t in α..y, b (e t) := ⟨_, rfl⟩
  obtain ⟨R, hR_def⟩ : ∃ R : ℝ → ℝ, R = fun y => c + ∫ t in α..y, b (e t) * (c + u (e t)) :=
    ⟨_, rfl⟩
  have hB : ∀ y, HasDerivAt B (b (e y)) y := fun y => by
    rw [hB_def]; exact (hb'.integral_hasStrictDerivAt α y).hasDerivAt
  have hR : ∀ y, HasDerivAt R (b (e y) * (c + u (e y))) y := fun y => by
    rw [hR_def]
    exact (((hb'.mul (continuous_const.add hu')).integral_hasStrictDerivAt α y).hasDerivAt).const_add c
  have hG : ∀ y, HasDerivAt (fun y => R y * Real.exp (-B y))
      (b (e y) * (c + u (e y)) * Real.exp (-B y) + R y * (Real.exp (-B y) * -b (e y))) y :=
    fun y => (hR y).mul (hB y).neg.exp
  have hanti : AntitoneOn (fun y => R y * Real.exp (-B y)) (Icc α β) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc α β)
      (fun y _ => (hG y).continuousAt.continuousWithinAt) (fun y _ => (hG y).hasDerivWithinAt)
      ?_
    intro y hy
    rw [interior_Icc] at hy
    have hyI : y ∈ Icc α β := Ioo_subset_Icc_self hy
    have h1 : c + u (e y) ≤ R y := by
      rw [hR_def, he_eq y hyI]
      simp only
      rw [hint_bu y hyI]
      linarith [h y hyI]
    have h2 : 0 ≤ b (e y) := by rw [he_eq y hyI]; exact hb0 y hyI
    have h3 := Real.exp_pos (-B y)
    have hrw : b (e y) * (c + u (e y)) * Real.exp (-B y) + R y * (Real.exp (-B y) * -b (e y))
        = b (e y) * Real.exp (-B y) * ((c + u (e y)) - R y) := by ring
    rw [hrw]
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg h2 h3.le) (by linarith)
  have hGx : R x * Real.exp (-B x) ≤ R α * Real.exp (-B α) :=
    hanti ⟨le_rfl, hαβ⟩ hx hx.1
  have hRα : R α = c := by rw [hR_def]; simp
  have hBα : B α = 0 := by rw [hB_def]; simp
  rw [hRα, hBα, neg_zero, Real.exp_zero, mul_one] at hGx
  have hRx : R x ≤ c * Real.exp (B x) := by
    have hE : Real.exp (-B x) * Real.exp (B x) = 1 := by
      rw [← Real.exp_add]; simp
    calc R x = R x * Real.exp (-B x) * Real.exp (B x) := by rw [mul_assoc, hE, mul_one]
      _ ≤ c * Real.exp (B x) := mul_le_mul_of_nonneg_right hGx (Real.exp_pos _).le
  have hux : c + u x ≤ R x := by
    rw [hR_def]
    simp only
    rw [hint_bu x hx]
    linarith [h x hx]
  calc c + u x ≤ R x := hux
    _ ≤ c * Real.exp (B x) := hRx
    _ = c * Real.exp (∫ t in α..x, b t) := by rw [hB_def]; simp only; rw [hint_b x hx]

end NonUniqueEuler.LinODE
