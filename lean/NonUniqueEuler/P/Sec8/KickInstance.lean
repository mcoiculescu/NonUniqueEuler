import NonUniqueEuler.Defs.Sec8.All
import NonUniqueEuler.I.Sec8.Coupling
import NonUniqueEuler.I.Sec8.KickODE
import NonUniqueEuler.I.Sec4.PropSU
import NonUniqueEuler.I.Sec6.InnerCirc
import NonUniqueEuler.I.Sec6.Clock

/-!
# Proof: the kick instance of `lem:coupling` (`08_kick.tex:168-171`)

Proof of `I/Sec8/KickInstance.lean` (`kick_instance`), following the proof sketch there:
1. `G_k ∈ [0,G₁]` (`inner_circ`, `GSmall`), so `Re λ_k > 211/2500 > 0` (`lam_SU`) and
   `Re ζ₀ = Re λ_k/μ = σ_k/μ = x_k > 0`;
2. `clock_order` at level `k+1` gives `0 ≤ t♯_{k+1} < T_{k+1}`, so `τ₀ = -A_{k+1}T_{k+1} < 0 < T_pin`;
3. `coupling_two` gives continuity of `q_{k+1}` on `[τ₀,T_pin]`, the ODE `eq:kick` and
   `c^in(τ₀) = 0`; `amp_of_ode` identifies `A^in = e^{-ζ₀τ_K}c^in` with `Kick.amp`.
-/

noncomputable section

open MeasureTheory Set

namespace NonUniqueEuler

namespace Kick

open RingData Datum

/-- `G_k ∈ [0,G₁]` for `1 ≤ k ≤ n` (`lem:inner-circ` and `GSmall`). -/
private lemma G_mem_of_GSmall (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ)
    (hG : P.GSmall) {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ P.n) : P.G k ∈ Icc (0 : ℝ) Gbar := by
  have hmem : k ∈ Finset.Icc 1 P.n := Finset.mem_Icc.mpr ⟨hk, hkn⟩
  exact ⟨((Approx.inner_circ P hP hN).2.2.1 k hmem).1, hG k hmem⟩

/-- `Re ζ₀ = x_k` (`ζ₀ = λ_k/μ`, `μ` real). -/
private lemma zeta0_re (P : Approx) (k : ℕ) : (P.zeta0 k).re = P.xk k := by
  simp only [Approx.zeta0, Approx.xk, Approx.sigma, Approx.lam, Eig.sigma, Complex.div_ofReal_re]

/-- `τ₀ < 0` (`lem:clock`(1) at level `k+1`: `0 ≤ t♯_{k+1} < T_{k+1}`). -/
private lemma tau0_neg (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ)
    (hG : P.GSmall) {k : ℕ} (hkn : k < P.n) (hc : P.ClockUpTo (k + 1)) : P.tau0 k < 0 := by
  have hmem : k + 1 ∈ Finset.Icc (k + 1) P.n := Finset.mem_Icc.mpr ⟨le_rfl, hkn⟩
  have hord := Approx.clock_order P hP hN hG (Nat.le_add_left 1 k) hc
  have hT : 0 < P.T (k + 1) := lt_of_le_of_lt (hord.2.2.2 (k + 1) hmem) (hord.1 (k + 1) hmem)
  have hA : 0 < P.A (k + 1) := hP.A_pos (k + 1)
  simp only [Approx.tau0, neg_lt_zero]
  exact mul_pos hA hT

/-- **The kick instance** (`08_kick.tex:168-171`). Under (N1)–(N3), `G_i ≤ G₁` for all levels, the
clock defined up to level `k+1` (`1 ≤ k < n`) and `D_{k+1}(t) ⊂ B_{a r_k/8}` on `[0,t♯_k]`: the kick
time functions of ring `k` form an instance of the setting of Section 8 with `ζ₀ = λ_k/μ`,
`β = β_k`, `τ₀ = -A_{k+1}T_{k+1} < 0`, `τ₁ = T_pin`, `q = q_{k+1}`; `Re ζ₀ = σ_k/μ > 0`; and the
kick amplitude `A^in` is `Kick.amp ζ₀ β_k τ₀ q_{k+1}` on `[τ₀,T_pin]`. -/
theorem kick_instance (P : Approx) (hP : P.Valid) (hN : NumericalHypothesis P.χ) (hG : P.GSmall)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k < P.n) (hc : P.ClockUpTo (k + 1))
    (hin : ∀ t ∈ Icc (0 : ℝ) (P.tsh k), P.HInDefined k t) :
    IsSetting (P.zeta0 k) (P.betaK k) (P.tau0 k) (P.Tpin : EReal) (P.qKick k) ∧
    (P.zeta0 k).re = P.xk k ∧ 0 < P.xk k ∧ P.tau0 k < 0 ∧
    ∀ τK ∈ Icc (P.tau0 k) P.Tpin,
      P.Ain k τK = amp (P.zeta0 k) (P.betaK k) (P.tau0 k) (P.qKick k) τK := by
  -- Step 1: `G_k ∈ [0,G₁]`, `Re λ_k > 0`, `x_k > 0`.
  have hGk : P.G k ∈ Icc (0 : ℝ) Gbar := G_mem_of_GSmall P hP hN hG hk hkn.le
  have hlam : 211 / 2500 < (Eig.lam P.χ (P.G k)).re :=
    (Eig.lam_SU P.χ hP.admissible hN hGk 0).1
  have hμ : 0 < P.μ := by linarith [hP.datumParams.one_lt_μ]
  have hre : (P.zeta0 k).re = P.xk k := zeta0_re P k
  have hx : 0 < P.xk k := by
    simp only [Approx.xk, Approx.sigma, Eig.sigma]
    exact div_pos (by linarith) hμ
  -- Step 2: `τ₀ < 0 < T_pin`.
  have hτ₀ : P.tau0 k < 0 := tau0_neg P hP hN hG hkn hc
  have hTpin : 0 < P.Tpin := hP.Tpin_pos
  -- Step 3: `lem:coupling`(2) and `eq:kick-A`.
  obtain ⟨-, hqcont, hderiv, hcin0, -⟩ := coupling_two P hP hN hG hk hkn hc hin
  have hset : IsSetting (P.zeta0 k) (P.betaK k) (P.tau0 k) (P.Tpin : EReal) (P.qKick k) :=
    { re_pos := hre ▸ hx
      lt := EReal.coe_lt_coe_iff.mpr (hτ₀.trans hTpin)
      continuousOn := by rw [interval_coe]; exact hqcont }
  refine ⟨hset, hre, hx, hτ₀, ?_⟩
  intro τK hτK
  have hode : ∀ τ ∈ interval (P.tau0 k) (P.Tpin : EReal),
      HasDerivWithinAt (P.cin k) (P.zeta0 k * P.cin k τ + P.betaK k * P.qKick k τ)
        (interval (P.tau0 k) (P.Tpin : EReal)) τ := by
    rw [interval_coe]
    exact hderiv
  have hamp := amp_of_ode hset hode hcin0 τK (by rw [interval_coe]; exact hτK)
  rw [Approx.Ain_def]
  exact hamp

end Kick

end NonUniqueEuler
