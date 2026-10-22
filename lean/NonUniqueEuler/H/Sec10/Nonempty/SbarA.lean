import NonUniqueEuler.H.Sec10.Nonempty.Structural

/-!
# Helper for `lem:nonempty`: the "power" conditions of (P6) for small `s̄`

Helper of `P/Sec10/Nonempty.lean`, the treatment of (P6) in the proof of `lem:nonempty`
(`10_parameters.tex:345-352`): (B1)–(B3), (B6), the first three parts of (B7), (B9)–(B11), the
first and the last part of (B8) have left sides that are finite sums of terms `C s̄^α` (with
`η_b = C_op s̄^{2m}/(σ_b(μ-1))`, `m = 3`), which tend to `0`, while the right sides are fixed positive
numbers (the constants are those of (P0)–(P5), which do not depend on `s̄`).

The statements are written with the constants of `p.ref` and the variable `sb` for `s̄`; they are
definitionally the fields of `Standing.SbarList` for `({ p with κs := κ, sbar := sb } : Params).ref`
(none of these constants reads `κ_seed` or `s̄`).

All lemmas are fully proved. Namespace `NonUniqueEuler.Relay.NonemptyH`.
-/

noncomputable section

open Set Filter Topology

namespace NonUniqueEuler

namespace Relay

open RingData Datum

namespace NonemptyH

/-- The standing datum with the parameters of `p`, the seed size `κ` and the scale ratio `sb`. -/
abbrev sbarRef (p : Params) (κ sb : ℝ) : Standing := ({ p with κs := κ, sbar := sb } : Params).ref

/-- A continuous function vanishing at `0` is eventually `≤ c` near `0⁺`, for `c > 0`. -/
theorem eventually_le_of_continuous {f : ℝ → ℝ} (hf : Continuous f) (h0 : f 0 = 0) {c : ℝ}
    (hc : 0 < c) : ∀ᶠ x in 𝓝[>] (0 : ℝ), f x ≤ c := by
  have h : Tendsto f (𝓝 0) (𝓝 (f 0)) := hf.tendsto 0
  rw [h0] at h
  exact (h.mono_left nhdsWithin_le_nhds).eventually (eventually_le_nhds hc)

/-- `C_* > 0` (`c₄ = (2π/(2-4/3))^{3/4} > 0`, `M_vort > 0`). -/
theorem Cstar_pos : 0 < Cstar := by
  have h1 : 0 ≤ BS.cLpLinf 4 := by
    unfold BS.cLpLinf
    refine Real.rpow_nonneg ?_ _
    have : (2 : ℝ) - Real.conjExponent 4 = 2 / 3 := by
      norm_num [Real.conjExponent]
    rw [this]
    positivity
  have h2 : 0 < Real.sqrt Mvort := Real.sqrt_pos.2 Mvort_pos
  unfold Cstar
  have : 0 < (1 + BS.cLpLinf 4) / (2 * Real.pi) := by positivity
  positivity

variable {p : Params}

theorem eventually_sbar_pos : ∀ᶠ sb in 𝓝[>] (0 : ℝ), 0 < sb := self_mem_nhdsWithin

/-- (B1), first part. -/
theorem eventually_b1_le : ∀ᶠ sb in 𝓝[>] (0 : ℝ), sb ≤ a / 16 :=
  eventually_le_of_continuous (f := fun sb => sb) continuous_id rfl
    (div_pos zero_lt_a (by norm_num))

/-- (B1), second part. -/
theorem eventually_b1_pow : ∀ᶠ sb in 𝓝[>] (0 : ℝ), sb ^ (3 - 2) ≤ 1 / 2 :=
  eventually_le_of_continuous (f := fun sb : ℝ => sb ^ (3 - 2)) (by fun_prop) (by norm_num)
    (by norm_num)

/-- (B2). -/
theorem eventually_b2 : ∀ᶠ sb in 𝓝[>] (0 : ℝ), p.ref.P.μ ^ 4 * sb ^ 2 ≤ 1 / 8 :=
  eventually_le_of_continuous (f := fun sb : ℝ => p.ref.P.μ ^ 4 * sb ^ 2) (by fun_prop)
    (by simp) (by norm_num)

/-- (B3). -/
theorem eventually_b3 : ∀ᶠ sb in 𝓝[>] (0 : ℝ), CG p.ref.P.χ * p.ref.P.μ * sb ^ 2 ≤ Gbar :=
  eventually_le_of_continuous (f := fun sb : ℝ => CG p.ref.P.χ * p.ref.P.μ * sb ^ 2)
    (by fun_prop) (by simp) Gbar_pos

/-- (B6), for a seed size `κ > 0`. -/
theorem eventually_b6 {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ sb in 𝓝[>] (0 : ℝ), p.ref.Kup * sb ^ (3 + 2) ≤ κ :=
  eventually_le_of_continuous (f := fun sb : ℝ => p.ref.Kup * sb ^ (3 + 2)) (by fun_prop)
    (by simp) hκ

/-- (B7), first part (`K_O s̄^{2m} ≤ 1/4`). -/
theorem eventually_b7_KO : ∀ᶠ sb in 𝓝[>] (0 : ℝ), p.ref.KO * sb ^ (2 * 3) ≤ 1 / 4 :=
  eventually_le_of_continuous (f := fun sb : ℝ => p.ref.KO * sb ^ (2 * 3)) (by fun_prop)
    (by simp) (by norm_num)

/-- (B7), second part (`16C_OC_QC_DuhK_Os̄^{2m} ≤ 1`). -/
theorem eventually_b7_CO :
    ∀ᶠ sb in 𝓝[>] (0 : ℝ),
      16 * p.ref.CO * p.ref.CQ * p.ref.CDuh * p.ref.KO * sb ^ (2 * 3) ≤ 1 :=
  eventually_le_of_continuous
    (f := fun sb : ℝ => 16 * p.ref.CO * p.ref.CQ * p.ref.CDuh * p.ref.KO * sb ^ (2 * 3))
    (by fun_prop) (by simp) (by norm_num)

/-- (B7), third part (`K_Oμs̄^{m+2} ≤ 1/2`). -/
theorem eventually_b7_mu :
    ∀ᶠ sb in 𝓝[>] (0 : ℝ), p.ref.KO * p.ref.P.μ * sb ^ (3 + 2) ≤ 1 / 2 :=
  eventually_le_of_continuous (f := fun sb : ℝ => p.ref.KO * p.ref.P.μ * sb ^ (3 + 2))
    (by fun_prop) (by simp) (by norm_num)

/-- (B8), first part (`η_b ≤ ½η_max`). -/
theorem eventually_b8_etab :
    ∀ᶠ sb in 𝓝[>] (0 : ℝ),
      p.ref.Cop p.ref.C0 p.ref.K1 * sb ^ (2 * 3) / (p.ref.sigb * (p.ref.P.μ - 1)) ≤
        1 / 2 * OneRing.etaMax :=
  eventually_le_of_continuous
    (f := fun sb : ℝ => p.ref.Cop p.ref.C0 p.ref.K1 * sb ^ (2 * 3) /
      (p.ref.sigb * (p.ref.P.μ - 1)))
    (by fun_prop) (by simp) (by norm_num [OneRing.etaMax])

/-- (B8), last part (`C_lsη_bσ'⁻¹log(2δ₀/κ_seed) ≤ 1/32`), for a fixed seed size `κ`. -/
theorem eventually_b8_seed (κ : ℝ) :
    ∀ᶠ sb in 𝓝[>] (0 : ℝ),
      Eig.Cls p.ref.P.χ * (p.ref.Cop p.ref.C0 p.ref.K1 * sb ^ (2 * 3) /
          (p.ref.sigb * (p.ref.P.μ - 1))) * p.ref.σ'⁻¹ * Real.log (2 * p.ref.P.δ₀ / κ) ≤
        1 / 32 :=
  eventually_le_of_continuous
    (f := fun sb : ℝ => Eig.Cls p.ref.P.χ * (p.ref.Cop p.ref.C0 p.ref.K1 * sb ^ (2 * 3) /
          (p.ref.sigb * (p.ref.P.μ - 1))) * p.ref.σ'⁻¹ * Real.log (2 * p.ref.P.δ₀ / κ))
    (by fun_prop) (by simp) (by norm_num)

/-- (B9), first part (`2Āμs̄^{m+2} ≤ maj_*`). -/
theorem eventually_b9_maj (hpos : p.ref.ConstPos) :
    ∀ᶠ sb in 𝓝[>] (0 : ℝ), 2 * p.ref.Abar * p.ref.P.μ * sb ^ (3 + 2) ≤ p.ref.majst :=
  eventually_le_of_continuous (f := fun sb : ℝ => 2 * p.ref.Abar * p.ref.P.μ * sb ^ (3 + 2))
    (by fun_prop) (by simp) hpos.majst_pos

/-- (B9), second part (`C_η(μs̄² + s̄^{m-2}) ≤ 1`). -/
theorem eventually_b9_eta :
    ∀ᶠ sb in 𝓝[>] (0 : ℝ),
      Rings.Ceta p.ref.P.χ p.ref.Mh * (p.ref.P.μ * sb ^ 2 + sb ^ (3 - 2)) ≤ 1 :=
  eventually_le_of_continuous
    (f := fun sb : ℝ => Rings.Ceta p.ref.P.χ p.ref.Mh * (p.ref.P.μ * sb ^ 2 + sb ^ (3 - 2)))
    (by fun_prop) (by simp) (by norm_num)

/-- (B10). -/
theorem eventually_b10 :
    ∀ᶠ sb in 𝓝[>] (0 : ℝ),
      4 * p.ref.CM * (2 * p.ref.CQ / (p.ref.sigb * (p.ref.P.μ - 1)) + 1) * p.ref.P.μ *
          sb ^ (3 + 2) ≤ 1 / 2 :=
  eventually_le_of_continuous
    (f := fun sb : ℝ => 4 * p.ref.CM * (2 * p.ref.CQ / (p.ref.sigb * (p.ref.P.μ - 1)) + 1) *
      p.ref.P.μ * sb ^ (3 + 2))
    (by fun_prop) (by simp) (by norm_num)

/-- (B11), first part (`‖ℓ_*‖C_QK_1Āμs̄^{m+2} ≤ 1/2`). -/
theorem eventually_b11_handoff :
    ∀ᶠ sb in 𝓝[>] (0 : ℝ),
      Eig.ellNorm p.ref.P.χ * p.ref.CQ * p.ref.K1 * p.ref.Abar * p.ref.P.μ * sb ^ (3 + 2) ≤
        1 / 2 :=
  eventually_le_of_continuous
    (f := fun sb : ℝ => Eig.ellNorm p.ref.P.χ * p.ref.CQ * p.ref.K1 * p.ref.Abar * p.ref.P.μ *
      sb ^ (3 + 2))
    (by fun_prop) (by simp) (by norm_num)

/-- (B11), second part (hypothesis (f) of `lem:kicktrue`, with `η_b = C_op s̄^{2m}/(σ_b(μ-1))`). -/
theorem eventually_b11_kick (hpos : p.ref.ConstPos) (hp : p.Structural) :
    ∀ᶠ sb in 𝓝[>] (0 : ℝ),
      p.ref.Cod * (p.ref.Cop p.ref.C0 p.ref.K1 * sb ^ (2 * 3) /
            (p.ref.sigb * (p.ref.P.μ - 1))) * p.ref.P.δ₀ *
          (p.ref.P.μ ^ 2 / (p.ref.sigma0 ^ 2 * (p.ref.P.μ - 1) ^ 2)) +
        2 * Real.pi * p.ref.C3 * (p.ref.Cop p.ref.C0 p.ref.K1 * sb ^ (2 * 3) /
            (p.ref.sigb * (p.ref.P.μ - 1))) *
          (4 * p.ref.P.μ * p.ref.P.δ₀ / (3 * p.ref.sigma0 * (p.ref.P.μ - 1))) ≤
      1 / 4 * (15 / 16) *
        (Eig.cout p.ref.P.χ * p.ref.P.δ₀ / (20 * ‖p.ref.z‖ * (p.ref.P.μ - 1))) := by
  have hδ : 0 < p.ref.P.δ₀ := hp.p1.δ₀_pos
  have hμ : 0 < p.ref.P.μ - 1 := sub_pos.2 hp.p2.one_lt_μ
  have hc : 0 < 1 / 4 * (15 / 16) *
      (Eig.cout p.ref.P.χ * p.ref.P.δ₀ / (20 * ‖p.ref.z‖ * (p.ref.P.μ - 1))) := by
    have := hpos.cout_pos
    have := hpos.z_norm_pos
    positivity
  exact eventually_le_of_continuous
    (f := fun sb : ℝ => p.ref.Cod * (p.ref.Cop p.ref.C0 p.ref.K1 * sb ^ (2 * 3) /
            (p.ref.sigb * (p.ref.P.μ - 1))) * p.ref.P.δ₀ *
          (p.ref.P.μ ^ 2 / (p.ref.sigma0 ^ 2 * (p.ref.P.μ - 1) ^ 2)) +
        2 * Real.pi * p.ref.C3 * (p.ref.Cop p.ref.C0 p.ref.K1 * sb ^ (2 * 3) /
            (p.ref.sigb * (p.ref.P.μ - 1))) *
          (4 * p.ref.P.μ * p.ref.P.δ₀ / (3 * p.ref.sigma0 * (p.ref.P.μ - 1))))
    (by fun_prop) (by simp) hc

end NonemptyH

end Relay

end NonUniqueEuler
