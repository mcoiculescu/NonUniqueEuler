import NonUniqueEuler.H.Sec10.Nonempty.Structural

/-!
# Helper for `lem:nonempty`: (κ1)–(κ4), (κ6), (κ7) for small `κ`

Helper of `P/Sec10/Nonempty.lean`, the treatment of (P5) in the proof of `lem:nonempty`
(`10_parameters.tex:317-327`): (κ1), (κ4), (κ6) have positive thresholds
`δ₀4^{-μ/(μ-1)}`, `κ₀(C₀)`, `κ_L`; the left sides of (κ2), (κ3), (κ7) are finite sums of terms
`Cκ^{1/2}` and `C(κ/δ₀)^γ⟨log(δ₀/κ)⟩^N` with `γ ∈ {γ_μ, ϑ_μ, γ'_μ}` positive (`μ > 1`, `c_γ > 0`),
which tend to `0`, while the right sides are positive. (κ5) is `H/Sec10/Nonempty/KappaFive.lean`.

All lemmas are fully proved. Namespace `NonUniqueEuler.Relay.NonemptyH`.
-/

noncomputable section

open Set Filter Topology

namespace NonUniqueEuler

namespace Relay

open RingData Datum

namespace NonemptyH

/-! ### Shapes of the left sides -/

theorem tendsto_id_nhdsGT : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) :=
  tendsto_id.mono_left nhdsWithin_le_nhds

theorem tendsto_const_mul_ratio_log (C : ℝ) {δ γ : ℝ} (hδ : 0 < δ) (hγ : 0 < γ) (N : ℕ) :
    Tendsto (fun κ : ℝ => C * (κ / δ) ^ γ * Real.log (δ / κ) ^ N) (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_ratio_rpow_mul_log_pow hδ hγ N).const_mul C
  rw [mul_zero] at h
  exact h.congr fun κ => by ring

theorem tendsto_const_mul_ratio_jap (C : ℝ) {δ γ : ℝ} (hδ : 0 < δ) (hγ : 0 < γ) (N : ℕ) :
    Tendsto (fun κ : ℝ => C * (κ / δ) ^ γ * Prelim.jap (Real.log (δ / κ)) ^ N) (𝓝[>] 0)
      (𝓝 0) := by
  have h := (tendsto_ratio_rpow_mul_jap_log_pow hδ hγ N).const_mul C
  rw [mul_zero] at h
  exact h.congr fun κ => by ring

theorem tendsto_const_mul_ratio_rpow (C : ℝ) {δ γ : ℝ} (hδ : 0 < δ) (hγ : 0 < γ) :
    Tendsto (fun κ : ℝ => C * (κ / δ) ^ γ) (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_ratio_rpow_mul_log_pow hδ hγ 0).const_mul C
  rw [mul_zero] at h
  exact h.congr fun κ => by rw [pow_zero, mul_one]

theorem tendsto_sqrt_shape (c μ D : ℝ) :
    Tendsto (fun κ : ℝ => c * Real.sqrt κ * μ / D) (𝓝[>] 0) (𝓝 0) := by
  have h := ((tendsto_sqrt_nhdsGT.const_mul c).mul_const μ).div_const D
  rwa [mul_zero, zero_mul, zero_div] at h

/-! ### The exponents and the signs -/

variable {p : Params}

theorem varthetaMu_pos (hp : p.Structural) : 0 < p.ref.varthetaMu :=
  div_pos (sub_pos.2 hp.p2.one_lt_μ) (by norm_num)

theorem gammaMu_pos (hpos : p.ref.ConstPos) (hp : p.Structural) : 0 < p.ref.gammaMu :=
  lt_min (varthetaMu_pos hp) hpos.cgamma_pos

theorem gammaMu'_pos (hpos : p.ref.ConstPos) (hp : p.Structural) : 0 < p.ref.gammaMu' := by
  have hμ : 1 < p.ref.P.μ := hp.p2.one_lt_μ
  have hμ0 : 0 < p.ref.P.μ := by linarith
  exact lt_min (mul_pos (by norm_num) (div_pos (sub_pos.2 hμ) hμ0)) hpos.cgamma_pos

/-! ### The conditions -/

/-- (κ1) for small `κ`. -/
theorem eventually_k1 (hp : p.Structural) : ∀ᶠ κ in 𝓝[>] (0 : ℝ), p.ref.kickIneqC κ := by
  have hc : 0 < p.ref.P.δ₀ * (4 : ℝ) ^ (-(p.ref.P.μ / (p.ref.P.μ - 1))) :=
    mul_pos hp.p1.δ₀_pos (Real.rpow_pos_of_pos (by norm_num) _)
  filter_upwards [eventually_le_of_tendsto_zero tendsto_id_nhdsGT hc] with κ hκ
  exact hκ

/-- (κ2) for small `κ`. -/
theorem eventually_k2 (hpos : p.ref.ConstPos) (hp : p.Structural) :
    ∀ᶠ κ in 𝓝[>] (0 : ℝ), p.ref.kickIneqD p.ref.C0 κ := by
  have hδ := hp.p1.δ₀_pos
  have hμ : 0 < p.ref.P.μ - 1 := sub_pos.2 hp.p2.one_lt_μ
  have hc : 0 < 1 / 2 * (15 / 16) *
      (Eig.cout p.ref.P.χ / (20 * ‖p.ref.z‖ * (p.ref.P.μ - 1))) := by
    have := hpos.cout_pos
    have := hpos.z_norm_pos
    positivity
  have h1 := tendsto_sqrt_shape (2 * Real.pi * p.ref.C3) p.ref.P.μ
    (3 / 4 * p.ref.sigma0 * (p.ref.P.μ - 1))
  have h2 := tendsto_const_mul_ratio_log (p.ref.Ctr p.ref.C0) hδ (gammaMu_pos hpos hp) (3 + 1)
  have h3 := tendsto_const_mul_ratio_log
    (p.ref.Cdeep + p.ref.Cid * p.ref.rT p.ref.P.Tpin * Ip 3 (p.ref.sigma0 / 8)) hδ
    (varthetaMu_pos hp) 3
  have h := (h1.add h2).add h3
  rw [add_zero, add_zero] at h
  filter_upwards [eventually_le_of_tendsto_zero h hc] with κ hκ
  exact hκ

/-- (κ3) for small `κ`. -/
theorem eventually_k3 (hpos : p.ref.ConstPos) (hp : p.Structural) :
    ∀ᶠ κ in 𝓝[>] (0 : ℝ), p.ref.kickIneqE p.ref.K1 κ := by
  have hδ := hp.p1.δ₀_pos
  have hμ : 0 < p.ref.P.μ - 1 := sub_pos.2 hp.p2.one_lt_μ
  have hc : 0 < 15 / 16 * (Eig.cout p.ref.P.χ / (20 * ‖p.ref.z‖ * (p.ref.P.μ - 1))) := by
    have := hpos.cout_pos
    have := hpos.z_norm_pos
    positivity
  have h := tendsto_const_mul_ratio_rpow
    (Cqr * (4 * p.ref.P.μ * Rings.CL1 * p.ref.CQ / (3 * p.ref.sigma0 * (p.ref.P.μ - 1)) + 1) *
      p.ref.K1) hδ (varthetaMu_pos hp)
  filter_upwards [eventually_le_of_tendsto_zero h hc] with κ hκ
  exact hκ

/-- (κ4) for small `κ`. -/
theorem eventually_k4 (hpos : p.ref.ConstPos) :
    ∀ᶠ κ in 𝓝[>] (0 : ℝ), κ ≤ p.ref.kappa0 p.ref.C0 :=
  eventually_le_of_tendsto_zero tendsto_id_nhdsGT hpos.kappa0_pos

/-- (κ6) for small `κ`. -/
theorem eventually_k6 (hpos : p.ref.ConstPos) :
    ∀ᶠ κ in 𝓝[>] (0 : ℝ), κ ≤ OneRing.kL p.ref.P.χ :=
  eventually_le_of_tendsto_zero tendsto_id_nhdsGT hpos.kL_pos

/-- (κ7) for small `κ`. -/
theorem eventually_k7 (hpos : p.ref.ConstPos) (hp : p.Structural) :
    ∀ᶠ κ in 𝓝[>] (0 : ℝ),
      p.ref.CXi p.ref.C0 p.ref.K1 * (1 + 1 / (p.ref.sigb * (p.ref.P.μ - 1))) *
          (κ / p.ref.P.δ₀) ^ p.ref.gammaMu' * Prelim.jap (Real.log (p.ref.P.δ₀ / κ)) ^ (3 + 1) ≤
        1 / (p.ref.sigb * (p.ref.P.μ - 1)) := by
  have hδ := hp.p1.δ₀_pos
  have hμ : 0 < p.ref.P.μ - 1 := sub_pos.2 hp.p2.one_lt_μ
  have hc : 0 < 1 / (p.ref.sigb * (p.ref.P.μ - 1)) := by
    have := hpos.sigb_pos
    positivity
  have h := tendsto_const_mul_ratio_jap
    (p.ref.CXi p.ref.C0 p.ref.K1 * (1 + 1 / (p.ref.sigb * (p.ref.P.μ - 1)))) hδ
    (gammaMu'_pos hpos hp) (3 + 1)
  exact eventually_le_of_tendsto_zero h hc

end NonemptyH

end Relay

end NonUniqueEuler
