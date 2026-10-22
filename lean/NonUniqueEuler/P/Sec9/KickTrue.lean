import NonUniqueEuler.Defs.Sec9.All
import NonUniqueEuler.I.Sec8.Kick
import NonUniqueEuler.I.Sec8.KickInstance
import NonUniqueEuler.H.Sec9.KickTrue.Hyp

/-!
# Proof: `lem:kicktrue` (the kick on the true field)

Proof of `I/Sec9/KickTrue.lean` (`09_relay.tex:1179-1231`, proof `:1233-1397`). We apply `prop:kick`
(`Kick.kick`) to the instance of `lem:coupling`(2) (`Kick.kick_instance`) with `(Q̄, p) = (C_mom, 3)`,
`err = errE(· + T_g) + |q^deep|` and `Q_pre = |q_{k+1}|`; its hypotheses are `KickTrueAux.kickHyp_of`
(helpers `H/Sec9/KickTrue/*`). For `k + 1 < n` we use `T_g` itself (`τ₀ = -t̄♯_{k+1} - T_g < -T_g`,
(Kick4) by `lem:prehistory` and (e)); at the seeded level `k + 1 = n` (`τ₀ = -T_g`) we use a
`T'_g ∈ [17T_g/24, T_g)` close to `T_g` (`KickTrueAux.pre_seeded`), as in the manuscript.

Deviation (harmless): in `err` the transient term `2πC₃â(u)ρ̂(u)` is replaced by its upper bound
`2πC₃C(C₀)κ⟨u⟩³e^{σ'u}` of `thm:active` ("Moreover"), so that `err` is continuous up to `|q^deep|`.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

open RingData Datum

/-- **`lem:kicktrue`** (`09_relay.tex:1179-1231`). Assume (SA), (Det), `C₀ ≥ 1`, `K₁ > 0`,
`1 ≤ k < n`, the clock defined up to level `k+1`, and the hypotheses `S.KickTrueHyp C₀ K₁ k`. Then
`|q_s| ∈ [15/16, 17/16]·2π|pout_*(G_{k+1})|δ₀` and, for every `τ_K ∈ [0, T_pin]`,
`|β_k||q_s|/(10|z|(μ-1)) ≤ |A^in(τ_K)| ≤ 3|β_k||q_s|μ/(|z|(μ-1))`. -/
theorem kicktrue (S : Standing) (hS : S.Holds) (hDet : S.Det) {C₀ K₁ : ℝ} (hC₀ : 1 ≤ C₀)
    (hK₁ : 0 < K₁) {k : ℕ} (hk : 1 ≤ k) (hkn : k < S.P.n) (hc : S.P.ClockUpTo (k + 1))
    (h : S.KickTrueHyp C₀ K₁ k) :
    ‖S.P.kickQs k‖ ∈ Icc (15 / 16 * (2 * Real.pi * ‖Eig.pout S.P.χ (S.P.G (k + 1))‖ * S.P.δ₀))
      (17 / 16 * (2 * Real.pi * ‖Eig.pout S.P.χ (S.P.G (k + 1))‖ * S.P.δ₀)) ∧
    ∀ τK ∈ Icc (0 : ℝ) S.P.Tpin,
      ‖S.P.betaK k‖ * ‖S.P.kickQs k‖ / (10 * ‖S.z‖ * (S.P.μ - 1)) ≤ ‖S.P.Ain k τK‖ ∧
      ‖S.P.Ain k τK‖ ≤ 3 * ‖S.P.betaK k‖ * ‖S.P.kickQs k‖ * S.P.μ / (‖S.z‖ * (S.P.μ - 1)) := by
  obtain ⟨hrange, hne, -⟩ := KickTrueAux.qs_facts S hS hDet hk hkn hc h
  refine ⟨hrange, ?_⟩
  have hG : S.P.GSmall := (standing_levels S hS).2.2.1
  obtain ⟨hset, -, -, hτ₀neg, hAin⟩ := Kick.kick_instance S.P hS.valid hS.hN hG hk hkn hc h.hin
  obtain ⟨-, hτ₀, -, htashpos, htsh0⟩ := KickTrueAux.clock_facts S hS hk hkn hc
  obtain ⟨-, -, -, -, -, hTg0⟩ := KickTrueAux.kappa_facts S hS hDet hk hkn hc h.ineqC
  obtain ⟨-, -, -, -, -, -, hx0, -, -⟩ := KickTrueAux.rew_facts S hS hDet hk hkn
  obtain ⟨-, -, -, -, hz⟩ := KickTrueAux.sigma_facts S hS
  have hμ1 : 0 < S.P.μ - 1 := by linarith [hS.one_lt_μ]
  have hB' : 0 < ‖S.P.kickQs k‖ / (20 * ‖S.z‖ * (S.P.μ - 1)) :=
    div_pos (norm_pos_iff.2 hne) (by positivity)
  have hcont : ContinuousOn (S.P.qKick k) (Icc (S.P.tau0 k) S.P.Tpin) := by
    have := hset.continuousOn
    rwa [Kick.interval_coe] at this
  -- the hypotheses of `prop:kick` for a suitable `T'_g`
  have hKH : ∃ Tg' : ℝ, Kick.KickHyp S.P.χ S.P.μ (S.P.G k) (S.P.G (k + 1)) (S.P.betaK k)
      (S.P.tau0 k) (S.P.Tpin : EReal) (S.P.qKick k) Tg' Rings.Cmom 3 (S.P.kickQs k)
      (fun τ => KickTrueAux.kickErrE S C₀ K₁ k (τ + S.P.That (k + 1)) + ‖S.P.qDeep k τ‖)
      (fun τ => ‖S.P.qKick k τ‖) := by
    by_cases hlt : k + 1 < S.P.n
    · -- `k + 1 < n`: `T'_g = T_g`, (Kick4) by `lem:prehistory` and (e)
      refine ⟨S.P.That (k + 1), KickTrueAux.kickHyp_of S hS hDet hC₀ hk hkn hc h hset
        (by linarith) le_rfl ?_ ?_⟩
      · rw [hτ₀]; linarith [htashpos hlt]
      · refine (KickTrueAux.pre_bound S hS hDet hK₁ hk hkn hc h hlt).trans ?_
        have hE := mul_le_mul_of_nonneg_left h.ineqE hS.δ₀_pos.le
        refine hE.trans ?_
        have e : S.P.δ₀ * (15 / 16 * (Eig.cout S.P.χ / (20 * ‖S.z‖ * (S.P.μ - 1)))) =
            15 / 16 * Eig.cout S.P.χ * S.P.δ₀ / (20 * ‖S.z‖ * (S.P.μ - 1)) := by ring
        rw [e]
        exact KickTrueAux.budget_le S hS hDet hk hkn hc h
    · -- the seeded level `k + 1 = n`: `τ₀ = -T_g`, `T'_g ∈ [17T_g/24, T_g)` close to `T_g`
      have heq : k + 1 = S.P.n := by omega
      have hτ₀' : S.P.tau0 k = -S.P.That (k + 1) := by
        rw [hτ₀, Approx.tash, htsh0 heq, mul_zero]; ring
      have hcont' : ContinuousOn (S.P.qKick k) (Icc (-S.P.That (k + 1)) 0) :=
        hcont.mono (Icc_subset_Icc (le_of_eq hτ₀') hS.Tpin_pos.le)
      obtain ⟨Tg', h1, h2, hpre⟩ := KickTrueAux.pre_seeded hx0.le hTg0 hB' hcont'
      refine ⟨Tg', KickTrueAux.kickHyp_of S hS hDet hC₀ hk hkn hc h hset h1 h2.le ?_ ?_⟩
      · rw [hτ₀']; linarith
      · rw [hτ₀']; exact hpre
  obtain ⟨Tg', hKH⟩ := hKH
  intro τK hτK
  have hmem : τK ∈ Kick.interval (S.P.tau0 k) (S.P.Tpin : EReal) := by
    rw [Kick.interval_coe]
    exact ⟨by linarith [hτK.1], hτK.2⟩
  have hkick := (Kick.kick S.P.χ hS.admissible hS.hN hKH).2.2 τK hmem hτK.1
  rw [hAin τK ⟨by linarith [hτK.1], hτK.2⟩]
  exact hkick

end Relay

end NonUniqueEuler
