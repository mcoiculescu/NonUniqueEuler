import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import NonUniqueEuler.Defs.Sec10.All
import NonUniqueEuler.I.Sec10.ConstantsPos

/-!
# Proof: `eq:E22` holds for small `s̄` (a step of `lem:nonempty`)

Proof of `I/Sec10/Nonempty/E22.lean` (`Relay.e22_small`), the condition `eq:E22` of (B7) in the
proof of `lem:nonempty` (`10_parameters.tex:345-352`; `eq:E22` is `:151-154`).

`Standing.CondE22` is the multiplicative form
`4C_OC_QC_τ · K_O s̄^{2m}[T_z + 2log(1/s̄) + 1/(μ-1)] ≤ (μ-1) · min{1/2, 1/(4C_lsK₁)}`.

**Proof** (the manuscript's argument, `10_parameters.tex:345-352`).
1. `f(s̄) = K_O s̄^6 [T_z + 2log(1/s̄) + 1/(μ-1)] = K_O s̄^6 (A - 2 log s̄)` with
   `A = T_z + 1/(μ-1)`; `s̄^6 → 0` and `s̄^6 log s̄ → 0` (`tendsto_log_mul_rpow_nhdsGT_zero`), so
   `4C_OC_QC_τ f(s̄) → 0` as `s̄ → 0⁺` (`E22H.tendsto_pow_mul_affine_log`).
2. The right side `(μ-1)·min{1/2, 1/(4C_lsK₁)}` is positive: `μ > 1` ((P2)), `C_ls > 0`, `K₁ > 0`
   (`constants_pos`). So the inequality holds on some `(0, s₀]`
   (`mem_nhdsGT_iff_exists_Ioc_subset`).
The constants of `({ p with κs := κ, sbar := s̄ }).ref` other than `s̄` are those of `p.ref` by
`rfl` (none reads `κ_seed` or `s̄`). No sign of `C_O`, `C_Q`, `C_τ` is needed: the left side tends
to `0` whatever the constant factor is.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace NonUniqueEuler

namespace Relay

open RingData Datum

namespace E22H

/-- `s^n (A + B log(1/s)) → 0` as `s → 0⁺` (`n ≥ 1`). -/
theorem tendsto_pow_mul_affine_log {n : ℕ} (hn : n ≠ 0) (A B : ℝ) :
    Tendsto (fun s : ℝ => s ^ n * (A + B * Real.log (1 / s))) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun s : ℝ => s ^ n) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun s : ℝ => s ^ n) (𝓝 0) (𝓝 ((0 : ℝ) ^ n)) :=
      (continuous_pow n).tendsto 0
    rw [zero_pow hn] at h
    exact h.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun s : ℝ => Real.log s * s ^ (n : ℝ)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_log_mul_rpow_nhdsGT_zero (by exact_mod_cast Nat.pos_of_ne_zero hn)
  have h3 := (h1.const_mul A).sub (h2.const_mul B)
  rw [mul_zero, mul_zero, sub_zero] at h3
  refine h3.congr' (Eventually.of_forall fun s => ?_)
  show A * s ^ n - B * (Real.log s * s ^ (n : ℝ)) = s ^ n * (A + B * Real.log (1 / s))
  rw [Real.rpow_natCast, one_div, Real.log_inv]
  ring

end E22H

/-- **`eq:E22` for small `s̄`** (`10_parameters.tex:151-154`, `:345-352`): for parameters satisfying
(P0)–(P4) and any seed size `κ`, `eq:E22` holds for every `s̄ ∈ (0, s₀]`, some `s₀ > 0`. -/
theorem e22_small (p : Params) (hχ : IsAdmissibleCutoff p.χ) (hN : NumericalHypothesis p.χ)
    (hp : p.Structural) (κ : ℝ) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ sbar ∈ Ioc (0 : ℝ) s₀,
      ({ p with κs := κ, sbar := sbar } : Params).ref.CondE22 := by
  have hpos : p.ref.ConstPos :=
    constants_pos p.ref hχ hN hp.p0.σ'_gt hp.p0.σ'_lt_sigma hp.p1.δ₀_pos hp.p2.one_lt_μ
      hp.p3.Tpin_pos
  have hμ : 1 < p.ref.P.μ := hp.p2.one_lt_μ
  -- the right side is positive
  have hc : 0 < (p.ref.P.μ - 1) * min (1 / 2) (1 / (4 * Eig.Cls p.ref.P.χ * p.ref.K1)) := by
    have h4 : 0 < 4 * Eig.Cls p.ref.P.χ * p.ref.K1 :=
      mul_pos (mul_pos (by norm_num) hpos.Cls_pos) hpos.K1_pos
    exact mul_pos (by linarith) (lt_min (by norm_num) (one_div_pos.2 h4))
  -- the left side tends to `0`
  have hlim : Tendsto (fun s : ℝ => 4 * p.ref.CO * p.ref.CQ * p.ref.Ctau *
      (p.ref.KO * s ^ (2 * 3) * (p.ref.Tz + 2 * Real.log (1 / s) + 1 / (p.ref.P.μ - 1))))
      (𝓝[>] 0) (𝓝 0) := by
    have h := (E22H.tendsto_pow_mul_affine_log (n := 2 * 3) (by norm_num)
      (p.ref.Tz + 1 / (p.ref.P.μ - 1)) 2).const_mul
      (4 * p.ref.CO * p.ref.CQ * p.ref.Ctau * p.ref.KO)
    rw [mul_zero] at h
    refine h.congr' (Eventually.of_forall fun s => ?_)
    ring
  obtain ⟨u, hu, hsub⟩ :=
    mem_nhdsGT_iff_exists_Ioc_subset.1 (hlim.eventually (eventually_le_nhds hc))
  refine ⟨u, hu, fun sb hsb => ?_⟩
  have h := hsub hsb
  unfold Standing.CondE22
  exact h

end Relay

end NonUniqueEuler
