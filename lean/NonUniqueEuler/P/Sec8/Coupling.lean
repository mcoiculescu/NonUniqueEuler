import NonUniqueEuler.Defs.Sec8.All
import NonUniqueEuler.H.Sec8.Coupling.PartOne
import NonUniqueEuler.H.Sec8.Coupling.PartTwo
import NonUniqueEuler.H.Sec8.Coupling.PartThree

/-!
# Proof: `lem:coupling` and `eq:kick` (the coupling of ring `k` to its inner region)

Proof of `I/Sec8/Coupling.lean` (`coupling_one`, `coupling_two`, `coupling_three`), following the
manuscript proof `08_kick.tex:65-154`. The work is in the helpers `H/Sec8/Coupling/*.lean`
(namespace `NonUniqueEuler.CouplingAux`):

1. (`PartOne.lean`, `coupling_one_aux`) `h^in_k(τ)` is a `3`-fold symmetric field in every
   `C^M(N')` (`Symmetry.lean`, `hIn_continuous`), so `-h^in_k·∇Φ ∈ X^s` (`Forcing.lean`, via
   `lem:uniform` and `lem:bilinear`(3)); the monopole is orthogonal to `e_r` and the sector-`3`
   profile of `(K_BS*ν^in_k)·e_r` is `(i/2)pout_3 r^{-4}` (sub-interface
   `I/Sec8/Coupling/RadialSector.lean`, `ν^in_k` vanishes for `|y| ≥ a/8`); `-h·∇Φ = -Φ'(r)h·e_r`
   a.e., so `ℓ_*(G_k)(-h^in_k·∇Φ) = pout_3 β(G_k)` (`Sector.lean`), and
   `pout_3 = μs_k⁵q_{k+1}/(2π)` (`Moment.lean`).
2. (`PartTwo.lean`, `coupling_two_aux`) `forcing_pathC` gives the paths; `lem:running` with
   `w₀ = 0` and part (1) give `c^in(τ_K) = e^{λ_ku}∫₀ᵘe^{-λ_kv}μβ_kq_{k+1}(v/A_k)dv`,
   `u = (τ_K - τ₀)/μ`, which is `Kick.coef ζ₀ β_k τ₀ q_{k+1}` (`KickFormula.lean`); FTC gives
   `eq:kick` on `[τ₀, T_pin]`; `t̄♯_k = (T_pin - τ₀)/μ` gives `c^in_k = c^in(T_pin)`.
3. (`PartThree.lean`, `coupling_three_aux`) the same for `h^out_k`, and the Duhamel integral is
   additive in the field (`Bridge.lean`, `wlin_add`).
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Kick

open RingData Datum

/-- **`lem:coupling`(1)** (`08_kick.tex:26-33`). For `1 ≤ k < n` and `t ≥ 0` with
`D_{k+1}(t) ⊂ B_{a r_k/8}`, `τ = A_k t`: `-h^in_k(τ)·∇Φ ∈ X^s` for every `s`,
`ℓ_*(G_k)(-h^in_k(τ)·∇Φ) = μβ_kq_{k+1}(t)`, and the sector-`3` profile of `h^in_k(τ)·e_r` is
`(i/2)pout_3[ν^in_k]r^{-4}` on `a/4 ≤ r ≤ 3`. -/
theorem coupling_one (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k < P.n) {t : ℝ} (ht : 0 ≤ t) (hin : P.HInDefined k t) :
    (∀ s : ℕ, Lin.MemXFn s (OneRing.forcing P.χ (P.hIn k) (P.A k * t))) ∧
    Eig.ellFn P.χ (P.G k) (OneRing.forcing P.χ (P.hIn k) (P.A k * t)) =
      (P.μ : ℂ) * P.betaK k * P.q (k + 1) t ∧
    ∀ r ∈ Icc (a / 4) 3,
      Polar.angularSector (fun y => ((OneRing.radComp (P.hIn k (P.A k * t)) y : ℝ) : ℂ)) 3 r =
        Complex.I / 2 * BS.pout 3 (fun y => ((P.nuIn k t y : ℝ) : ℂ)) * (r : ℂ) ^ (-4 : ℤ) :=
  CouplingAux.coupling_one_aux P hP hN hk hkn ht hin

/-- **`lem:coupling`(2) and `eq:kick`** (`08_kick.tex:34-53`). Assume `G_i ≤ G₁` for all levels,
the clock defined up to level `k+1` (`1 ≤ k < n`) and `D_{k+1}(t) ⊂ B_{a r_k/8}` on `[0,t♯_k]`. Then
`τ ↦ -h^in_k(τ)·∇Φ ∈ C([0,t̄♯_k];X^s)` for every `s`; in kick time `τ_K ∈ [τ₀,T_pin]`, `q_{k+1}` is
continuous and `c^in = ℓ_*(G_k)(wlin_{in,k})` solves `dc^in/dτ_K = ζ₀c^in + β_kq_{k+1}`,
`c^in(τ₀) = 0` (`ζ₀ = λ_k/μ`); and `c^in_k = e^{ζ₀T_pin}A^in(T_pin)`. -/
theorem coupling_two (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) (hG : P.GSmall)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k < P.n) (hc : P.ClockUpTo (k + 1))
    (hin : ∀ t ∈ Icc (0 : ℝ) (P.tsh k), P.HInDefined k t) :
    (∀ s : ℕ, OneRing.PathC s (P.tash k) (OneRing.forcing P.χ (P.hIn k))) ∧
    ContinuousOn (P.qKick k) (Icc (P.tau0 k) P.Tpin) ∧
    (∀ τK ∈ Icc (P.tau0 k) P.Tpin, HasDerivWithinAt (P.cin k)
      (P.zeta0 k * P.cin k τK + P.betaK k * P.qKick k τK) (Icc (P.tau0 k) P.Tpin) τK) ∧
    P.cin k (P.tau0 k) = 0 ∧
    P.cinK k = Complex.exp (P.zeta0 k * P.Tpin) * P.Ain k P.Tpin :=
  CouplingAux.coupling_two_aux P hP hN hG hk hkn hc hin

set_option linter.unusedVariables false in
/-- **`lem:coupling`(3)** (`08_kick.tex:54-63`). Under the hypotheses of (2) and if moreover the
rings `i < k` lie outside `B_{6r_k}` on `[0,t♯_k]`: `τ ↦ -h^out_k(τ)·∇Φ ∈ C([0,t̄♯_k];X^s)` and
`wlin_{in,k} + wlin_{out,k} = wlin` on `[0,t̄♯_k]`, `wlin` the linear response of `thm:quiet` for
ring `k` (`G = G_k`, `h = h_k`). (`hG`, `hc` are the standing hypotheses of (2); the proof
does not use them.) -/
theorem coupling_three (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) (hG : P.GSmall)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k < P.n) (hc : P.ClockUpTo (k + 1))
    (hdef : ∀ t ∈ Icc (0 : ℝ) (P.tsh k), P.HDefined k t) (s : ℕ) :
    OneRing.PathC s (P.tash k) (OneRing.forcing P.χ (P.hOut k)) ∧
    ∀ τ ∈ Icc (0 : ℝ) (P.tash k),
      P.wlinIn s k τ + P.wlinOut s k τ = OneRing.wlin P.χ s (P.G k) (P.hField k) τ :=
  CouplingAux.coupling_three_aux P hP hN hk hkn hdef s

end Kick

end NonUniqueEuler
