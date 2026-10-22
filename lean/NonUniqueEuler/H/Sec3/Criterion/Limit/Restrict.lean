import NonUniqueEuler.Statement.WeakSolution
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Helper for `P/Sec3/Criterion/Limit`: restriction of solutions to a shorter time interval

Manuscript: proof of `thm:criterion`, `03_compactness.tex:989-992`: "since `𝒟_{T'} ⊂ 𝒟_{T_j}`,
the restriction of `ω^{[j]}` to `[0, T']` is a renormalized weak solution in `X₂(T')` with datum
`f`".

* `isTestFunction_mono`: `𝒟_{T'} ⊆ 𝒟_T` for `T' ≤ T`;
* `transportIntegrand_eq_zero_of_notMem_tsupport`: the integrand `u (∂_t φ + w · ∇φ)` vanishes
  outside `tsupport φ`;
* `solvesTransport_mono`, `memX_mono`, `isWeakSolution_mono`, `isRenormalizedWeakSolution_mono`:
  the restriction from `T` to `T' ∈ (0, T]`. For a test function in `𝒟_{T'}` the integrand of the
  transport identity vanishes for `t ≥ T'`, so the time integrals over `(0, T)` and `(0, T')`
  agree.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.Compact.CriterionLimitAux

/-- `slab T' ⊆ slab T` for `T' ≤ T`. -/
theorem slab_mono {T T' : ℝ} (hT : T' ≤ T) : slab T' ⊆ slab T :=
  prod_mono (Ioo_subset_Ioo_right hT) subset_rfl

/-- `𝒟_{T'} ⊆ 𝒟_T` for `T' ≤ T`. -/
theorem isTestFunction_mono {T T' : ℝ} {φ : ℝ × ℂ → ℝ} (h : IsTestFunction T' φ)
    (hT : T' ≤ T) : IsTestFunction T φ :=
  ⟨h.contDiff, h.hasCompactSupport, fun p hp => (h.support_lt p hp).trans_le hT⟩

/-- Outside `tsupport φ` the transport integrand vanishes. -/
theorem transportIntegrand_eq_zero_of_notMem_tsupport {u : ℝ → ℂ → ℝ} {w : ℝ → ℂ → ℂ}
    {φ : ℝ × ℂ → ℝ} {p : ℝ × ℂ} (hp : p ∉ tsupport φ) : transportIntegrand u w φ p = 0 := by
  have hev : φ =ᶠ[𝓝 p] 0 := notMem_tsupport_iff_eventuallyEq.1 hp
  have ht1 : Tendsto (fun s : ℝ => (s, p.2)) (𝓝 p.1) (𝓝 p) := by
    have := (continuous_id.prodMk (continuous_const (y := p.2))).tendsto p.1
    simpa using this
  have ht2 : Tendsto (fun y : ℂ => (p.1, y)) (𝓝 p.2) (𝓝 p) := by
    have := ((continuous_const (y := p.1)).prodMk continuous_id).tendsto p.2
    simpa using this
  have h1 : (fun s => φ (s, p.2)) =ᶠ[𝓝 p.1] fun _ => (0 : ℝ) := ht1.eventually hev
  have h2 : (fun y => φ (p.1, y)) =ᶠ[𝓝 p.2] fun _ => (0 : ℝ) := ht2.eventually hev
  have e1 : timeDeriv φ p.1 p.2 = 0 := by
    rw [timeDeriv, h1.deriv_eq]
    simp
  have e2 : spaceDeriv φ p.1 p.2 (w p.1 p.2) = 0 := by
    rw [spaceDeriv, h2.fderiv_eq]
    simp
  simp [transportIntegrand, e1, e2]

/-- Restriction of the transport identity `(te)` from `[0, T)` to `[0, T')`, `T' ≤ T`. -/
theorem solvesTransport_mono {T T' : ℝ} {u : ℝ → ℂ → ℝ} {w : ℝ → ℂ → ℂ} {u₀ : ℂ → ℝ}
    (h : SolvesTransport T u w u₀) (hT : T' ≤ T) : SolvesTransport T' u w u₀ where
  integrableOn φ hφ := (h.integrableOn φ (isTestFunction_mono hφ hT)).mono_set (slab_mono hT)
  datum_integrable φ hφ := h.datum_integrable φ (isTestFunction_mono hφ hT)
  identity φ hφ := by
    have h1 := h.identity φ (isTestFunction_mono hφ hT)
    rwa [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo
      (Ioo_subset_Ioo_right hT) ?_] at h1
    intro t ht
    have htT' : T' ≤ t := by
      by_contra hlt
      exact ht.2 ⟨ht.1.1, lt_of_not_ge hlt⟩
    have hz : ∀ x : ℂ, transportIntegrand u w φ (t, x) = 0 := fun x =>
      transportIntegrand_eq_zero_of_notMem_tsupport fun hp =>
        absurd (hφ.support_lt _ hp) (not_lt.2 htT')
    simp [hz]

/-- `X_q(T) ⊆ X_q(T')` for `T' ≤ T` (restriction in time). -/
theorem memX_mono {q T T' : ℝ} {ω : ℝ → ℂ → ℝ} (h : MemX q T ω) (hT : T' ≤ T) : MemX q T' ω where
  aestronglyMeasurable :=
    h.aestronglyMeasurable.mono_measure (Measure.restrict_mono_set _ (slab_mono hT))
  essBounded := by
    obtain ⟨M, hM⟩ := h.essBounded
    exact ⟨M, ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right hT) hM⟩

/-- A weak solution in `X_q(T)` restricts to a weak solution in `X_q(T')`, `0 < T' ≤ T`. -/
theorem isWeakSolution_mono {q T T' : ℝ} {ωin : ℂ → ℝ} {ω : ℝ → ℂ → ℝ}
    (h : IsWeakSolution q T ωin ω) (hT' : 0 < T') (hT : T' ≤ T) : IsWeakSolution q T' ωin ω where
  q_gt := h.q_gt
  T_pos := hT'
  datum_memLp_one := h.datum_memLp_one
  datum_memLp_q := h.datum_memLp_q
  memX := memX_mono h.memX hT
  velocity_convergent :=
    ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right hT) h.velocity_convergent
  weak := solvesTransport_mono h.weak hT

/-- A renormalized weak solution in `X_q(T)` restricts to a renormalized weak solution in
`X_q(T')`, `0 < T' ≤ T` (`03_compactness.tex:989-992`). -/
theorem isRenormalizedWeakSolution_mono {q T T' : ℝ} {ωin : ℂ → ℝ} {ω : ℝ → ℂ → ℝ}
    (h : IsRenormalizedWeakSolution q T ωin ω) (hT' : 0 < T') (hT : T' ≤ T) :
    IsRenormalizedWeakSolution q T' ωin ω :=
  { isWeakSolution_mono h.toIsWeakSolution hT' hT with
    renormalized := fun Υ hΥ => solvesTransport_mono (h.renormalized Υ hΥ) hT }

end NonUniqueEuler.Compact.CriterionLimitAux
