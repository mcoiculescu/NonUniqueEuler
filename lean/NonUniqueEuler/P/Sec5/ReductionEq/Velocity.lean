import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Sec5.ReductionVelocity

/-!
# Proof: the velocity decomposition of `lem:reduction`(2)

Proof of `I/Sec5/ReductionEq/Velocity.lean` (same declaration, same statement). The statement
is the second conjunct of `OneRing.reduction_velocity` (`I/Sec5/ReductionVelocity.lean`,
`05_single_ring.tex:110-115`).
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace OneRing

open RingData

/-- **`lem:reduction`(2), the velocity decomposition** (`05_single_ring.tex:110-115`; second
conjunct of `reduction_velocity`). Under the hypotheses of `lem:reduction` on `[0,T]`, on
`[0,T] × N'`: `v = K_BS * ω = Ω(|x|;G)x^⊥ + h + K_BS * (ω_r - Φ)`. -/
theorem velocity_sol_eq_decomp (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) {c : RingConfig}
    {T : ℝ} (hc : c.Hyp T) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ annN',
      velocity (c.sol t) x = omegaField χ c.G x + c.h t x +
        velocity (fun y => c.ringPart t y - ringPhi χ y) x :=
  (reduction_velocity χ hχ hc).2.1

end OneRing

end NonUniqueEuler
