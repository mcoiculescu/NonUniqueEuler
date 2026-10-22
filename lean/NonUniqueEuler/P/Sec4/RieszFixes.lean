import NonUniqueEuler.Defs.Infra.Dunford

/-!
# Proof: the Riesz projection fixes generalized eigenvectors (remark before `lem:resolvent`)

Proof of `NonUniqueEuler/I/Sec4/RieszFixes.lean` (`04_ring.tex:361-364`), in the Laurent form R2
of the Riesz projection (`Dunford.IsSimpleSpectralProj`).

**Argument.** Write `N = A - z₀`. From `P A = z₀ P` we get `P N = 0`, and from `A P = z₀ P` we
get `N P = 0`.

* Key step: if `N u = 0` and `P u = 0`, then `u = 0`. Indeed, for `z ≠ z₀` in the resolvent set,
  `(z - A) u = (z - z₀) u`, so `(z - z₀) (z - A)⁻¹ u = u`. The Laurent condition gives
  `(z - A)⁻¹ u - (z - z₀)⁻¹ P u = (z - A)⁻¹ u → R₀ u`; multiplying by `z - z₀ → 0` gives that the
  constant `u` tends to `0` along the punctured neighbourhood filter, so `u = 0`.
* Induction on `k`. For `k = 0` the hypothesis is `v = 0`. For `k + 1`, the vector `N v`
  satisfies `N^k (N v) = 0`, so `P (N v) = N v` by induction; but `P N = 0`, hence `N v = 0`.
  Then `u = v - P v` satisfies `N u = N v - N P v = 0` and `P u = P v - P² v = 0`, so `u = 0` by
  the key step.

This replaces the manuscript's explicit Neumann-sum formula for `(λ - A)⁻¹ v` by the same
mechanism (the `(z - z₀)⁻¹` blow-up) applied one Jordan level at a time; it is the downward
induction of the interface docstring, run upwards on `k` with the vector `N v`.
-/

noncomputable section

open Filter Topology

namespace NonUniqueEuler

namespace Dunford

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- If `A u = z₀ u` and `z` is in the resolvent set, then `(z - z₀) (z - A)⁻¹ u = u`. -/
private lemma rieszFixes_smul_resolvent_apply {A : X →L[ℂ] X} {z₀ z : ℂ}
    (hz : z ∈ resolventSet ℂ A) {u : X} (hu : A u = z₀ • u) :
    (z - z₀) • resolvent A z u = u := by
  have hinv : resolvent A z * (algebraMap ℂ (X →L[ℂ] X) z - A) = 1 :=
    Ring.inverse_mul_cancel _ hz
  have hT : (algebraMap ℂ (X →L[ℂ] X) z - A) u = (z - z₀) • u := by
    rw [sub_apply, Algebra.algebraMap_eq_smul_one,
      smul_apply, one_apply_eq_self, hu, sub_smul]
  calc (z - z₀) • resolvent A z u = resolvent A z ((z - z₀) • u) := (map_smul _ _ _).symm
    _ = (resolvent A z * (algebraMap ℂ (X →L[ℂ] X) z - A)) u := by
        rw [mul_apply_eq_comp, hT]
    _ = u := by rw [hinv, one_apply_eq_self]

/-- Key step: an eigenvector of `A` at `z₀` that is killed by the spectral projection is zero. -/
private lemma rieszFixes_eq_zero_of_eigen {A P : X →L[ℂ] X} {z₀ : ℂ}
    (h : IsSimpleSpectralProj A P z₀) {u : X} (hAu : A u = z₀ • u) (hPu : P u = 0) : u = 0 := by
  obtain ⟨R₀, hR₀⟩ := h.laurent
  have h1 : Tendsto (fun z : ℂ => (resolvent A z - (z - z₀)⁻¹ • P) u) (𝓝[≠] z₀)
      (𝓝 (R₀ u)) :=
    ((ContinuousLinearMap.apply ℂ X u).continuous.tendsto R₀).comp hR₀
  have hlin : Tendsto (fun z : ℂ => z - z₀) (𝓝[≠] z₀) (𝓝 (z₀ - z₀)) :=
    tendsto_nhdsWithin_of_tendsto_nhds ((continuous_id.sub continuous_const).tendsto z₀)
  have h2 : Tendsto (fun z : ℂ => (z - z₀) • (resolvent A z - (z - z₀)⁻¹ • P) u) (𝓝[≠] z₀)
      (𝓝 ((z₀ - z₀) • R₀ u)) :=
    hlin.smul h1
  rw [sub_self, zero_smul] at h2
  have h3 : (fun z : ℂ => (z - z₀) • (resolvent A z - (z - z₀)⁻¹ • P) u) =ᶠ[𝓝[≠] z₀]
      fun _ => u := by
    filter_upwards [h.eventually_mem_resolventSet] with z hz
    rw [sub_apply, smul_apply, hPu, smul_zero, sub_zero]
    exact rieszFixes_smul_resolvent_apply hz hAu
  have h4 : Tendsto (fun _ : ℂ => u) (𝓝[≠] z₀) (𝓝 0) := h2.congr' h3
  exact tendsto_nhds_unique tendsto_const_nhds h4

/-- The spectral projection of `A` at `z₀` (Laurent form R2) fixes every generalized eigenvector:
`(A - z₀)^k v = 0` implies `P v = v` (`04_ring.tex:361-364`). -/
theorem IsSimpleSpectralProj.apply_eq_self_of_pow_apply_eq_zero {A P : X →L[ℂ] X} {z₀ : ℂ}
    (h : IsSimpleSpectralProj A P z₀) {v : X} {k : ℕ}
    (hv : ((A - z₀ • (1 : X →L[ℂ] X)) ^ k) v = 0) : P v = v := by
  have hPA : ∀ x, P (A x) = z₀ • P x := fun x => by
    simpa using congrArg (fun T : X →L[ℂ] X => T x) h.proj_mul
  have hAP : ∀ x, A (P x) = z₀ • P x := fun x => by
    simpa using congrArg (fun T : X →L[ℂ] X => T x) h.mul_proj
  have hPP : ∀ x, P (P x) = P x := fun x => by
    simpa using congrArg (fun T : X →L[ℂ] X => T x) h.idem
  induction k generalizing v with
  | zero =>
    rw [pow_zero, one_apply_eq_self] at hv
    rw [hv, map_zero]
  | succ k ih =>
    have hNv : ((A - z₀ • (1 : X →L[ℂ] X)) ^ k) ((A - z₀ • (1 : X →L[ℂ] X)) v) = 0 := by
      rw [pow_succ, mul_apply_eq_comp] at hv
      exact hv
    have h1 := ih hNv
    have h2 : P ((A - z₀ • (1 : X →L[ℂ] X)) v) = 0 := by
      rw [sub_apply, smul_apply,
        one_apply_eq_self, map_sub, map_smul, hPA, sub_self]
    have hAv : A v = z₀ • v := by
      have h3 : (A - z₀ • (1 : X →L[ℂ] X)) v = 0 := by rw [← h1, h2]
      rw [sub_apply, smul_apply,
        one_apply_eq_self, sub_eq_zero] at h3
      exact h3
    have hu : v - P v = 0 := by
      refine rieszFixes_eq_zero_of_eigen h ?_ ?_
      · rw [map_sub, hAv, hAP, smul_sub]
      · rw [map_sub, hPP, sub_self]
    exact (sub_eq_zero.mp hu).symm

end Dunford

end NonUniqueEuler
