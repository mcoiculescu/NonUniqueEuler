import NonUniqueEuler.H.Sec3.Transport.Limit
import NonUniqueEuler.I.Sec3.Transport.Mollified

/-!
# Helper for `P/Sec3/Transport`: `(te)` for `Υ(u)`, `Υ` a renormalization

`lem:transport`(i) for `C¹` renormalizations (`03_compactness.tex:494-518`):
`solvesTE_renormalization`. For `φ ∈ 𝒟_T` the mollified identity
(`transport_mollified_identity`, `I/Sec3/Transport/Mollified.lean`) holds for every
`ε_n = 1/(n+1)`; its three terms converge (`H/Sec3/Transport/Limit.lean`) to the transport term
of `Υ(u)`, the datum term of `Υ(u₀)` and `0`. The integrability conjuncts of `(te)` for `Υ(u)` are
`integrableOn_transportIntegrand_comp` and `integrable_datum_comp`
(`H/Sec3/Transport/Basic.lean`).
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace NonUniqueEuler.Weak.TransportH

/-- `lem:transport`(i) for renormalizations `Υ` (`C¹`, `Υ'` bounded, `Υ(0) = 0`). -/
theorem solvesTE_renormalization {T t₀ : ℝ} (hT : 0 < T) (ht₀ : t₀ ∈ Ico 0 T)
    {w : ℝ → ℂ → ℂ} (hw : IsBddH1DivFreeField (Ioo 0 T) w) {u : ℝ → ℂ → ℝ} {u₀ : ℂ → ℝ}
    (hu1 : Prelim.MemLinfLp (Ioo 0 T) univ 1 u) (hu2 : Prelim.MemLinfLp (Ioo 0 T) univ 2 u)
    (huw : Integrable (fun p : ℝ × ℂ => u p.1 p.2 • w p.1 p.2) (volume.restrict (slab T)))
    (hu₀1 : MemLp u₀ 1 volume) (hu₀2 : MemLp u₀ 2 volume) (hte : SolvesTE t₀ T u w u₀)
    {Υ : ℝ → ℝ} (hΥ : IsRenormalization Υ) :
    SolvesTE t₀ T (fun t x => Υ (u t x)) w (fun x => Υ (u₀ x)) := by
  obtain ⟨L, hL0, hL⟩ := exists_abs_le_of_isRenormalization hΥ
  have hΥc := continuous_of_isRenormalization hΥ
  refine ⟨fun φ hφ => integrableOn_transportIntegrand_comp ht₀.1 hw hu1 huw hΥc hL0 hL hφ,
    fun φ hφ => integrable_datum_comp hu₀1 hΥc hL0 hL hφ, fun φ hφ => ?_⟩
  have hf := integrableOn_transportIntegrand_comp ht₀.1 hw hu1 huw hΥc hL0 hL hφ
  have hd := integrable_datum_comp (t₀ := t₀) hu₀1 hΥc hL0 hL hφ
  have key := fun n : ℕ => transport_mollified_identity isMollifier_rho (epsSeq_pos n) hT ht₀
    hw hu1 hu2 huw hu₀1 hu₀2 hte hΥ hφ
  -- the transport term
  have h1 : Tendsto (fun n : ℕ => ∫ p in slabFrom t₀ T,
      transportIntegrand (fun t x => Υ (mollify rho (epsSeq n) (u t) x)) w φ p) atTop
      (𝓝 (∫ p in slabFrom t₀ T, transportIntegrand (fun t x => Υ (u t x)) w φ p)) :=
    tendsto_integral_of_L1 _ hf.aestronglyMeasurable (Eventually.of_forall fun n => (key n).1)
      (tendsto_lintegral_transportIntegrand_mollify isMollifier_rho ht₀ hw hu2 hΥ hφ
        fun n => (key n).1.sub hf)
  -- the datum term
  have h2 : Tendsto (fun n : ℕ => ∫ x, Υ (mollify rho (epsSeq n) u₀ x) * φ (t₀, x)) atTop
      (𝓝 (∫ x, Υ (u₀ x) * φ (t₀, x))) :=
    tendsto_integral_of_L1 _ hd.aestronglyMeasurable
      (Eventually.of_forall fun n => integrable_datum_mollify isMollifier_rho (epsSeq_pos n)
        hu₀2 hΥ hφ t₀)
      (tendsto_lintegral_datum_mollify isMollifier_rho hu₀2 hΥ hφ t₀)
  -- the commutator term
  have h3 : Tendsto (fun n : ℕ => ∫ p in slabFrom t₀ T,
      φ p * deriv Υ (mollify rho (epsSeq n) (u p.1) p.2) * commEps rho (epsSeq n) u w p.1 p.2)
      atTop (𝓝 0) := by
    have := tendsto_integral_of_L1 (μ := volume.restrict (slabFrom t₀ T)) (fun _ => (0 : ℝ))
      aestronglyMeasurable_const (Eventually.of_forall fun n => (key n).2.1)
      (by simpa using tendsto_lintegral_comm_mollify isMollifier_rho ht₀ hw hu2 hΥ hφ)
    simpa using this
  -- the identity for each `n`
  have hk : ∀ n : ℕ, (∫ p in slabFrom t₀ T,
        transportIntegrand (fun t x => Υ (mollify rho (epsSeq n) (u t) x)) w φ p) +
        ∫ x, Υ (mollify rho (epsSeq n) u₀ x) * φ (t₀, x) =
      -∫ p in slabFrom t₀ T,
        φ p * deriv Υ (mollify rho (epsSeq n) (u p.1) p.2) *
          commEps rho (epsSeq n) u w p.1 p.2 := by
    intro n
    rw [← integral_Ioo_integral_eq (key n).1, ← integral_Ioo_integral_eq (key n).2.1]
    exact (key n).2.2
  have hA := h1.add h2
  have hB : Tendsto (fun n : ℕ => (∫ p in slabFrom t₀ T,
        transportIntegrand (fun t x => Υ (mollify rho (epsSeq n) (u t) x)) w φ p) +
        ∫ x, Υ (mollify rho (epsSeq n) u₀ x) * φ (t₀, x)) atTop (𝓝 (-0)) :=
    h3.neg.congr fun n => (hk n).symm
  rw [integral_Ioo_integral_eq hf]
  have := tendsto_nhds_unique hA hB
  simpa using this

end NonUniqueEuler.Weak.TransportH
