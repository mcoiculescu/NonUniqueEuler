import NonUniqueEuler.H.Sec10.Nonempty.SbarA
import NonUniqueEuler.I.Sec9.Standing

/-!
# Helper for `lem:nonempty`: (B4), and the level conditions (B5), (B8) of (P6), for small `s̄`

Helper of `P/Sec10/Nonempty.lean`, the treatment of (P6) in the proof of `lem:nonempty`
(`10_parameters.tex:352-371`):
* (B4) is `det_of_small` (`I/Sec9/Standing.lean`; `λ_*` continuous at `0`);
* (B5): `Λ^conf_k = α₀ + β₀ log(1/s_k)`; `s(α₀ + β₀log(1/s)) → 0` and
  `s(α₀ + β₀log(1/s))² → 0` give `s₅ > 0` with both inequalities at every scale `s ∈ (0, s₅]`,
  and `0 < s_k ≤ s̄`;
* (B8) at `k ≥ 2`: with `s_k = s_{k-1}/(2μ)` the `k`-th inequality is `F(s_{k-1}) ≤ 1/32`,
  `F(s) = (C_lsC_op/(σ'σ_b(μ-1))) s^{2m}[(m+2)(log(1/s) + log(2μ)) + log₊(δ₀/K_lo)] → 0`.

All lemmas are fully proved. Namespace `NonUniqueEuler.Relay.NonemptyH`.
-/

noncomputable section

open Set Filter Topology

namespace NonUniqueEuler

namespace Relay

open RingData Datum

namespace NonemptyH

variable {p : Params}

/-- **(B4)** for small `s̄` (`det_of_small`). -/
theorem eventually_b4 (hχ : IsAdmissibleCutoff p.χ) (hN : NumericalHypothesis p.χ)
    (hp : p.Structural) :
    ∀ᶠ sb in 𝓝[>] (0 : ℝ), ∀ G ∈ Icc (0 : ℝ) (CG p.ref.P.χ * p.ref.P.μ * sb ^ 2),
      Kick.Detuned p.ref.P.χ p.ref.P.μ G := by
  obtain ⟨s₀, hs₀, h⟩ := det_of_small p.χ hχ hN hp.p2.one_lt_μ
  exact eventually_of_Ioc hs₀ h

/-- `Λ^conf` as a function of the scale `s` (`(B5)`, `10_parameters.tex:145-146`). -/
def LconfOf (p : Params) (s : ℝ) : ℝ :=
  2 + 2 * Cstar * (p.ref.P.μ * (p.ref.P.Tpin + 1 + 1 / p.ref.σ' *
    ((3 + 2) * Real.log (1 / s) + Real.posLog (p.ref.P.δ₀ / p.ref.Klo))))

/-- `Λ^conf = α₀ + β₀ log(1/s)` (`10_parameters.tex:356-358`). -/
theorem LconfOf_eq (p : Params) (s : ℝ) :
    LconfOf p s =
      (2 + 2 * Cstar * (p.ref.P.μ * (p.ref.P.Tpin + 1 +
          1 / p.ref.σ' * Real.posLog (p.ref.P.δ₀ / p.ref.Klo)))) +
        2 * Cstar * (p.ref.P.μ * (1 / p.ref.σ' * (3 + 2))) * Real.log (1 / s) := by
  unfold LconfOf
  ring

/-- (B5) at one scale `s`, for small `s`. -/
theorem eventually_b5_scale (hp : p.Structural) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), LconfOf p s * s ≤ a / 8 ∧
      8 / 3 * (2 / a) ^ 3 * LconfOf p s ^ (3 - 1) * s ^ (3 - 2) ≤ p.ref.P.μ * Cstar := by
  set α₀ : ℝ := 2 + 2 * Cstar * (p.ref.P.μ * (p.ref.P.Tpin + 1 +
      1 / p.ref.σ' * Real.posLog (p.ref.P.δ₀ / p.ref.Klo))) with hα₀
  set β₀ : ℝ := 2 * Cstar * (p.ref.P.μ * (1 / p.ref.σ' * (3 + 2))) with hβ₀
  have h1 : Tendsto (fun s : ℝ => LconfOf p s * s) (𝓝[>] 0) (𝓝 0) := by
    refine (tendsto_rpow_mul_affine_log_pow one_pos 1 α₀ β₀).congr' ?_
    filter_upwards with s
    rw [Real.rpow_one, pow_one, LconfOf_eq, mul_comm]
  have h2 : Tendsto (fun s : ℝ => 8 / 3 * (2 / a) ^ 3 * LconfOf p s ^ (3 - 1) * s ^ (3 - 2))
      (𝓝[>] 0) (𝓝 0) := by
    have h := (tendsto_rpow_mul_affine_log_pow one_pos 2 α₀ β₀).const_mul (8 / 3 * (2 / a) ^ 3)
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards with s
    rw [Real.rpow_one, LconfOf_eq]
    norm_num
    ring
  have hμ : 0 < p.ref.P.μ := by linarith [hp.p2.one_lt_μ]
  exact (eventually_le_of_tendsto_zero h1 (div_pos zero_lt_a (by norm_num))).and
    (eventually_le_of_tendsto_zero h2 (mul_pos hμ Cstar_pos))

/-- `0 < s_k ≤ s̄` for `s_k = s̄/(2μ)^k`, `μ ≥ 1/2`. -/
theorem ratio_mem {μ sb : ℝ} (hμ : 1 < μ) (hsb : 0 < sb) (k : ℕ) :
    0 < sb / (2 * μ) ^ k ∧ sb / (2 * μ) ^ k ≤ sb := by
  have h2 : 1 ≤ 2 * μ := by linarith
  exact ⟨div_pos hsb (pow_pos (by linarith) k), div_le_self hsb.le (one_le_pow₀ h2)⟩

/-- **(B5)** at every level `k ≥ 1`, for small `s̄` (`10_parameters.tex:358-362`). -/
theorem eventually_b5 (hp : p.Structural) :
    ∀ᶠ sb in 𝓝[>] (0 : ℝ), ∀ k : ℕ, 1 ≤ k →
      LconfOf p (sb / (2 * p.ref.P.μ) ^ k) * (sb / (2 * p.ref.P.μ) ^ k) ≤ a / 8 ∧
        8 / 3 * (2 / a) ^ 3 * LconfOf p (sb / (2 * p.ref.P.μ) ^ k) ^ (3 - 1) *
            (sb / (2 * p.ref.P.μ) ^ k) ^ (3 - 2) ≤ p.ref.P.μ * Cstar := by
  obtain ⟨s₅, hs₅, h⟩ := exists_Ioc_of_eventually (eventually_b5_scale hp)
  refine eventually_of_Ioc hs₅ fun sb hsb k _ => h _ ?_
  obtain ⟨h1, h2⟩ := ratio_mem hp.p2.one_lt_μ hsb.1 k
  exact ⟨h1, h2.trans hsb.2⟩

/-- The function `F` of (B8) (`10_parameters.tex:364-368`), at the scale `s = s_{k-1}`. -/
theorem eventually_b8_scale :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      Eig.Cls p.ref.P.χ * (p.ref.Cop p.ref.C0 p.ref.K1 * t ^ (2 * 3) /
          (p.ref.sigb * (p.ref.P.μ - 1))) / p.ref.σ' *
        ((3 + 2) * (Real.log (1 / t) + Real.log (2 * p.ref.P.μ)) +
          Real.posLog (p.ref.P.δ₀ / p.ref.Klo)) ≤ 1 / 32 := by
  have hγ : (0 : ℝ) < ((2 * 3 : ℕ) : ℝ) := by norm_num
  have h := (tendsto_rpow_mul_affine_log_pow hγ 1
    ((3 + 2) * Real.log (2 * p.ref.P.μ) + Real.posLog (p.ref.P.δ₀ / p.ref.Klo)) (3 + 2)).const_mul
    (Eig.Cls p.ref.P.χ * p.ref.Cop p.ref.C0 p.ref.K1 / (p.ref.sigb * (p.ref.P.μ - 1)) / p.ref.σ')
  rw [mul_zero] at h
  refine eventually_le_of_tendsto_zero (h.congr' ?_) (by norm_num)
  filter_upwards with t
  rw [Real.rpow_natCast, pow_one]
  ring

/-- **(B8)** at every level `k ≥ 2`, for small `s̄` (`10_parameters.tex:362-371`). -/
theorem eventually_b8_level (κ : ℝ) (hp : p.Structural) :
    ∀ᶠ sb in 𝓝[>] (0 : ℝ), ∀ k : ℕ, 2 ≤ k →
      Eig.Cls (sbarRef p κ sb).P.χ *
          (sbarRef p κ sb).etabK (sbarRef p κ sb).C0 (sbarRef p κ sb).K1 k /
          (sbarRef p κ sb).σ' *
        ((3 + 2) * Real.log (1 / (sbarRef p κ sb).P.s k) +
          Real.posLog ((sbarRef p κ sb).P.δ₀ / (sbarRef p κ sb).Klo)) ≤ 1 / 32 := by
  obtain ⟨s₈, hs₈, h⟩ := exists_Ioc_of_eventually (eventually_b8_scale (p := p))
  refine eventually_of_Ioc hs₈ fun sb hsb k hk => ?_
  have hμ : 1 < p.μ := hp.p2.one_lt_μ
  rw [Standing.etabK_of_two_le _ _ _ hk]
  have ht : (sbarRef p κ sb).P.s k = (sbarRef p κ sb).P.s (k - 1) / (2 * p.μ) := by
    show sb / (2 * p.μ) ^ k = sb / (2 * p.μ) ^ (k - 1) / (2 * p.μ)
    rw [div_div, ← pow_succ, Nat.sub_add_cancel (by omega)]
  obtain ⟨htpos, htle⟩ := ratio_mem hμ hsb.1 (k - 1)
  have htpos' : 0 < (sbarRef p κ sb).P.s (k - 1) := htpos
  have htle' : (sbarRef p κ sb).P.s (k - 1) ≤ sb := htle
  rw [ht]
  set t : ℝ := (sbarRef p κ sb).P.s (k - 1) with ht_def
  have h2μ : 0 < 2 * p.μ := by linarith
  have hlog : Real.log (1 / (t / (2 * p.μ))) = Real.log (1 / t) + Real.log (2 * p.μ) := by
    rw [one_div_div, Real.log_div h2μ.ne' htpos'.ne', one_div, Real.log_inv]
    ring
  rw [hlog]
  exact h t ⟨htpos', htle'.trans hsb.2⟩

end NonemptyH

end Relay

end NonUniqueEuler
