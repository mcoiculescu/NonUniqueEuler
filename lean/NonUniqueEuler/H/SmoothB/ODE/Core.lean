import NonUniqueEuler.I.SmoothB.ODE.LinearFlow
import NonUniqueEuler.I.SmoothB.ODE.FlowDeriv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Helper for `lem:ode`(ii): `C^k` dependence of a global autonomous flow on its initial point

For `G : W → W` of class `C^k` (`k ≥ 1`, `W` finite-dimensional) and a global, jointly continuous
flow `Ψ` of `ż = G(z)`:
* `flow_C1`: each `Ψ(r, ·)` is differentiable, `(r, z) ↦ D_zΨ(r, z)` is jointly continuous, and
  `D_zΨ` solves the variational equation `∂_r D_zΨ = DG(Ψ) ∘ D_zΨ`
  (from `I/SmoothB/ODE/LinearFlow.lean` and `I/SmoothB/ODE/FlowDeriv.lean`);
* `flow_contDiff`: each `Ψ(r, ·)` is `C^k`. Induction on `k`: the pair `(Ψ, D_zΨ)` is the flow
  of the augmented field `(z, M) ↦ (G z, DG(z) ∘ M)`, which is `C^{k-1}` (Teschl, proof of
  Theorem 2.10).
-/

noncomputable section

open Set Function

namespace NonUniqueEuler.Smooth.ODEH

universe u

/-- The `C¹` core of `lem:ode`(ii) for a global autonomous flow. -/
theorem flow_C1 {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {G : W → W} (hG : ContDiff ℝ 1 G) {Ψ : ℝ → W → W}
    (hΨc : Continuous (uncurry Ψ)) (hΨ0 : ∀ z, Ψ 0 z = z)
    (hΨ : ∀ r z, HasDerivAt (fun r => Ψ r z) (G (Ψ r z)) r) :
    (∀ r z, HasFDerivAt (Ψ r) (fderiv ℝ (Ψ r) z) z) ∧
    Continuous (fun q : ℝ × W => fderiv ℝ (Ψ q.1) q.2) ∧
    ∀ r z, HasDerivAt (fun r => fderiv ℝ (Ψ r) z)
      ((fderiv ℝ G (Ψ r z)).comp (fderiv ℝ (Ψ r) z)) r := by
  have hB : Continuous (uncurry fun r z => fderiv ℝ G (Ψ r z)) :=
    (hG.continuous_fderiv one_ne_zero).comp hΨc
  obtain ⟨A, hAc, hA0, hA⟩ := exists_linearVariationalFlow hB
  have hD : ∀ r z, HasFDerivAt (Ψ r) (A r z) z := fun r z =>
    hasFDerivAt_flow_of_variational hG hΨc hΨ0 hΨ (hA0 z) (fun r => hA r z) r
  have hfd : ∀ r z, fderiv ℝ (Ψ r) z = A r z := fun r z => (hD r z).fderiv
  refine ⟨fun r z => by rw [hfd]; exact hD r z, ?_, ?_⟩
  · have : (fun q : ℝ × W => fderiv ℝ (Ψ q.1) q.2) = uncurry A := by
      funext q; exact hfd q.1 q.2
    rw [this]; exact hAc
  · intro r z
    have : (fun r => fderiv ℝ (Ψ r) z) = fun r => A r z := by funext r; exact hfd r z
    rw [this, hfd]; exact hA r z

/-- `C^k` dependence of a global autonomous flow on its initial point (`k = n + 1`). -/
theorem flow_contDiff (n : ℕ) : ∀ {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] {G : W → W} {Ψ : ℝ → W → W}, ContDiff ℝ (n + 1) G →
    Continuous (uncurry Ψ) → (∀ z, Ψ 0 z = z) →
    (∀ r z, HasDerivAt (fun r => Ψ r z) (G (Ψ r z)) r) → ∀ r, ContDiff ℝ (n + 1) (Ψ r) := by
  induction n with
  | zero =>
    intro W _ _ _ G Ψ hG hΨc hΨ0 hΨ r
    have hG1 : ContDiff ℝ 1 G := by simpa using hG
    obtain ⟨h1, h2, -⟩ := flow_C1 hG1 hΨc hΨ0 hΨ
    have : ContDiff ℝ 1 (Ψ r) := contDiff_one_iff_fderiv.2
      ⟨fun z => (h1 r z).differentiableAt, h2.comp (Continuous.prodMk_right r)⟩
    simpa using this
  | succ n ih =>
    intro W _ _ _ G Ψ hG hΨc hΨ0 hΨ r
    have hG1 : ContDiff ℝ 1 G := hG.of_le (by norm_cast; omega)
    obtain ⟨h1, h2, h3⟩ := flow_C1 hG1 hΨc hΨ0 hΨ
    let G' : W × (W →L[ℝ] W) → W × (W →L[ℝ] W) := fun q => (G q.1, (fderiv ℝ G q.1).comp q.2)
    let Ψ' : ℝ → W × (W →L[ℝ] W) → W × (W →L[ℝ] W) :=
      fun r q => (Ψ r q.1, (fderiv ℝ (Ψ r) q.1).comp q.2)
    have hG' : ContDiff ℝ (n + 1) G' := by
      have hd : ContDiff ℝ (n + 1) (fderiv ℝ G) :=
        hG.fderiv_right (m := (n + 1 : ℕ)) (by norm_cast)
      exact (hG.of_le (by norm_cast; omega)).comp contDiff_fst |>.prodMk
        ((hd.comp contDiff_fst).clm_comp contDiff_snd)
    have hΨ'c : Continuous (uncurry Ψ') := by
      refine (hΨc.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk ?_
      exact (h2.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).clm_comp
        (continuous_snd.comp continuous_snd)
    have hΨid : Ψ 0 = id := funext hΨ0
    have hΨ'0 : ∀ q, Ψ' 0 q = q := by
      intro q
      simp only [Ψ', hΨid, fderiv_id, ContinuousLinearMap.id_comp, id_eq]
    have hΨ' : ∀ r q, HasDerivAt (fun r => Ψ' r q) (G' (Ψ' r q)) r := by
      intro r q
      have h := (hΨ r q.1).prodMk ((h3 r q.1).clm_comp (hasDerivAt_const r q.2))
      convert h using 1
      simp only [G', Ψ', ContinuousLinearMap.comp_zero, add_zero,
        ContinuousLinearMap.comp_assoc]
    have key := ih hG' hΨ'c hΨ'0 hΨ' r
    have hfd : fderiv ℝ (Ψ r) = fun z => (Ψ' r (z, ContinuousLinearMap.id ℝ W)).2 := by
      funext z; simp [Ψ']
    have hc : ContDiff ℝ (n + 1) (fderiv ℝ (Ψ r)) := by
      rw [hfd]; exact contDiff_snd.comp (key.comp (contDiff_id.prodMk contDiff_const))
    refine contDiff_succ_iff_fderiv.2 ⟨fun z => (h1 r z).differentiableAt, ?_, by exact_mod_cast hc⟩
    intro h
    exact absurd h (by simp)

end NonUniqueEuler.Smooth.ODEH
