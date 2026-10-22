import NonUniqueEuler.Defs.Sec5.All
import NonUniqueEuler.I.Sec5.Active

/-!
# Proof of `cor:active-moment` (the sector-3 moment of an active ring)

Proof of `NonUniqueEuler/I/Sec5/ActiveMoment.lean` (`05_single_ring.tex:1104-1122`).

By the D11 packaging (constants as existentials), the conclusion `RingConfig.ActiveConcl` of
`thm:active` already contains the bound of the corollary (its last conjunct), with the constant
`C₃` chosen in `thm:active`. So the corollary is read off `activeConsts_spec (active …)`: apply
the last field of `IsActiveConst` to `C₀`, the configuration and the hypotheses, and take the last
conjunct of `ActiveConcl`. The manuscript's argument (`:1112-1122`) lives inside the proof of
`active`.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace OneRing

open RingData

/-- **`cor:active-moment`** (`05_single_ring.tex:1104-1111`). Under the assumptions of
`thm:active` (with its constants `d_H = dH χ s σ'`, `C₃ = C3 χ s σ'`, `κ₀ = kappa0 χ s σ'`), put
`q(u) = 2π pout_3[w(u)]`. Then for every `u ∈ [0, min(ū, T̂)]`,
`|q(u) - 2π pout_*(G) c(u)e^{λu}| ≤ 2π C₃ â(u)[ρ̂(u) + â(u) + κ^{1/2} + η_b]`. -/
theorem active_moment (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ)
    {s : ℕ} (hs : 3 ≤ s) {σ' : ℝ} (hσ' : σ' ∈ Ioo (9 / 200 : ℝ) (Eig.sigb χ))
    {C₀ : ℝ} (hC₀ : 1 ≤ C₀) {c : RingConfig} {ubar : ℝ} (hc : c.Hyp ubar)
    (hG : c.G ∈ Icc (0 : ℝ) Gbar) {κ ηb δ₀ : ℝ} (hκ : 0 < κ) (hηb : ηb ∈ Icc (0 : ℝ) etaMax)
    (hδ₀ : δ₀ ∈ Ioc (0 : ℝ) (dH χ s σ')) (hInit : c.ActiveInit χ s C₀ κ)
    (hField : c.ActiveField χ s ubar C₀ κ ηb) (hCoef : c.ActiveCoef χ ubar C₀ κ)
    (hSmall : κ ≤ kappa0 χ s σ' C₀) :
    ∀ u ∈ Icc (0 : ℝ) (min ubar (That (Eig.sigma χ c.G) δ₀ κ)),
      ‖2 * Real.pi * BS.pout 3 (c.w χ u) -
          2 * Real.pi * Eig.pout χ c.G *
            (runCoef χ c.G (c.pert0 χ) c.h u * Complex.exp (Eig.lam χ c.G * u))‖ ≤
        2 * Real.pi * C3 χ s σ' * ahat κ (Eig.sigma χ c.G) u *
          (rhoHatOf (Eig.sigma χ c.G) σ' C₀ u + ahat κ (Eig.sigma χ c.G) u + Real.sqrt κ + ηb) := by
  intro u hu
  have hK := activeConsts_spec (active χ hχ hN hs hσ')
  exact (hK.2.2.2.2 C₀ hC₀ c ubar hc hG κ ηb δ₀ hκ hηb hδ₀ hInit hField hCoef hSmall u
    hu).2.2.2.2

end OneRing

end NonUniqueEuler
