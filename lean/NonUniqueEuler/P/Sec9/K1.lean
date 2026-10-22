import NonUniqueEuler.Defs.Sec9.All
import NonUniqueEuler.I.Sec4.Uniform
import NonUniqueEuler.I.Sec8.Coupling
import NonUniqueEuler.I.Sec8.KickInstance
import NonUniqueEuler.I.Sec9.Detuning
import NonUniqueEuler.I.Sec9.Standing

/-!
# Proof: `lem:K1` and `eq:Abar` (`09_relay.tex:947-994`)

Proof of `I/Sec9/K1.lean` (`Relay.K1_bound`), following the manuscript proof
(`09_relay.tex:968-994`):
1. `Ξ ≤ δ₀/(σ_b(μ-1))` and `relayBound_mono` give the first inequality of `eq:Abar`;
2. `x_k ≤ 17σ/16` (`detuning`) and `T_pin > 0` give the second;
3. `|c^in_k| = e^{x_kT_pin}|A^in(T_pin)|` (`coupling_two`, `kick_instance`) and
   `|β(G_k)||pout_*(G_{k+1})| ≥ c_N` (`uniform_constants`, `standing_levels`) give the lower bound
   on `|c^in_k|`;
4. multiplying by `½K_1` and using `eq:K1` gives `½K_1|c^in_k| ≥ 2maj_k(t̄♯_k)`.

The positivity facts `C_M > 0`, `C₂ ≥ 1` and `C_* > 0` hold unconditionally (the junk values of the
chosen constants are positive too); they are proved here as private lemmas.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

open RingData Datum

/-! ### Private positivity facts -/

/-- `C^T_M > 0` (the spec of `lem:transfer`, or the junk value `1`). -/
private theorem K1_CTM_pos (χ : ℝ → ℝ) (Mh : ℕ) : 0 < Rings.CTM χ Mh := by
  classical
  by_cases h : ∃ CTM CTO : ℝ, Rings.IsTransferConst χ Mh CTM CTO
  · exact (Rings.transferConsts_spec h).CTM_pos
  · have h' : ¬ ∃ x : ℝ × ℝ, Rings.IsTransferConst χ Mh x.1 x.2 :=
      fun ⟨x, hx⟩ => h ⟨x.1, x.2, hx⟩
    simp only [Rings.CTM, Rings.transferConsts, dite_eq_right h']
    norm_num

/-- `C_M = C^T_M max(1, C_{L1}) > 0`. -/
private theorem K1_CM_pos (S : Standing) : 0 < S.CM := by
  show 0 < Rings.CM S.P.χ S.Mh
  rw [Rings.CM_def]
  exact mul_pos (K1_CTM_pos _ _) (lt_of_lt_of_le one_pos (le_max_left _ _))

/-- `C₂ ≥ 1` (the spec of `thm:active`, or the junk value `1`). -/
private theorem K1_one_le_C2 (S : Standing) : 1 ≤ S.C2 := by
  classical
  show 1 ≤ OneRing.C2 S.P.χ S.s S.σ'
  by_cases h : ∃ (dH C₂ C₃ : ℝ) (κ₀ : ℝ → ℝ), OneRing.IsActiveConst S.P.χ S.s S.σ' dH C₂ C₃ κ₀
  · exact (OneRing.activeConsts_spec h).2.1
  · have h' : ¬ ∃ x : ℝ × ℝ × ℝ × (ℝ → ℝ),
        OneRing.IsActiveConst S.P.χ S.s S.σ' x.1 x.2.1 x.2.2.1 x.2.2.2 :=
      fun ⟨x, hx⟩ => h ⟨x.1, x.2.1, x.2.2.1, x.2.2.2, hx⟩
    simp only [OneRing.C2, OneRing.activeConsts, dite_eq_right h']
    exact le_refl _

/-- `C_* = (1 + c₄)/(2π) M_vort^{1/2} > 0` (`c₄ = (2π/(2 - 4/3))^{3/4} ≥ 0`). -/
private theorem K1_Cstar_pos : 0 < Cstar := by
  have hc : 0 ≤ BS.cLpLinf 4 := by
    unfold BS.cLpLinf
    apply Real.rpow_nonneg
    have h43 : (4 : ℝ).conjExponent = 4 / 3 := by
      unfold Real.conjExponent; norm_num
    rw [h43]
    have := Real.pi_pos
    apply div_nonneg <;> linarith
  unfold Cstar
  have hpi := Real.pi_pos
  have hM := Mvort_pos
  have : 0 < Real.sqrt Mvort := Real.sqrt_pos.mpr hM
  positivity

/-- `C_D(T) ≥ 0` for `T ≥ 0`. -/
private theorem K1_CD_nonneg {T : ℝ} (hT : 0 ≤ T) : 0 ≤ CD T := by
  rw [CD_def]
  have := K1_Cstar_pos
  positivity

/-! ### Algebraic steps -/

/-- `‖β_k‖ = ‖β(G_k)‖ s_k⁵/(2π)` (`s_k > 0`). -/
private theorem K1_norm_betaK (P : Approx) (hP : P.Valid) (k : ℕ) :
    ‖P.betaK k‖ = ‖Eig.beta P.χ (P.G k)‖ * P.s k ^ 5 / (2 * Real.pi) := by
  have hs := hP.s_pos k
  have hpi := Real.pi_pos
  unfold Approx.betaK
  rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  congr 1
  rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity)]

/-- The lower bound `|c^in_k| ≥ c_Kε_kδ₀e^{x_kT_pin}/(|z|(μ-1))` from its ingredients
(`09_relay.tex:979-988`; `(15/16)(1/10) = 3/32`), over named real variables. -/
private theorem K1_cin_lower {cN βn pn qn Ain cin s5 μ δ₀ E zn : ℝ} (hβ : 0 ≤ βn)
    (hcN : cN ≤ βn * pn) (hs5 : 0 < s5) (hμ : 1 < μ) (hδ : 0 < δ₀) (hE : 0 < E) (hz : 0 < zn)
    (hq : 15 / 16 * (2 * Real.pi * pn * δ₀) ≤ qn)
    (hA : βn * s5 / (2 * Real.pi) * qn / (10 * zn * (μ - 1)) ≤ Ain) (hcin : cin = E * Ain) :
    3 * cN / (32 * μ) * (μ * s5) * δ₀ * E / (zn * (μ - 1)) ≤ cin := by
  have hpi := Real.pi_pos
  have hμ1 : 0 < μ - 1 := by linarith
  have hμ0 : 0 < μ := by linarith
  have hβ0 : 0 ≤ βn * s5 / (2 * Real.pi) := by positivity
  have h1 : 15 / 16 * cN * s5 * δ₀ ≤ βn * s5 / (2 * Real.pi) * qn := by
    calc 15 / 16 * cN * s5 * δ₀ ≤ 15 / 16 * (βn * pn) * s5 * δ₀ := by
          have := mul_le_mul_of_nonneg_left hcN (by norm_num : (0 : ℝ) ≤ 15 / 16)
          have := mul_le_mul_of_nonneg_right this hs5.le
          exact mul_le_mul_of_nonneg_right this hδ.le
      _ = βn * s5 / (2 * Real.pi) * (15 / 16 * (2 * Real.pi * pn * δ₀)) := by
          field_simp
      _ ≤ βn * s5 / (2 * Real.pi) * qn := mul_le_mul_of_nonneg_left hq hβ0
  have h2 : 15 / 16 * cN * s5 * δ₀ / (10 * zn * (μ - 1)) ≤ Ain :=
    le_trans (div_le_div_of_nonneg_right h1 (by positivity)) hA
  calc 3 * cN / (32 * μ) * (μ * s5) * δ₀ * E / (zn * (μ - 1))
        = E * (15 / 16 * cN * s5 * δ₀ / (10 * zn * (μ - 1))) := by
          field_simp
          ring
    _ ≤ E * Ain := mul_le_mul_of_nonneg_left h2 hE.le
    _ = cin := hcin.symm

/-- The identity `½K_1 · c_Kε_kδ₀E/(|z|(μ-1)) = 4C_Mε_kE[(4C₂+1)δ₀/(σ_b(μ-1)) + C_D]`
(`eq:K1`, `09_relay.tex:989-993`), over named real variables. -/
private theorem K1_identity {CM zn cK C2 sb CDT μ δ₀ e E : ℝ} (hz : 0 < zn) (hcK : 0 < cK)
    (hsb : 0 < sb) (hμ : 1 < μ) (hδ : 0 < δ₀) :
    1 / 2 * (8 * CM * zn / cK * ((4 * C2 + 1) / sb + CDT * (μ - 1) / δ₀)) *
        (cK * e * δ₀ * E / (zn * (μ - 1))) =
      2 * (2 * CM * e * E * ((4 * C2 + 1) * δ₀ / (sb * (μ - 1)) + CDT)) := by
  have hμ1 : (μ - 1) ≠ 0 := by
    have : 0 < μ - 1 := by linarith
    exact this.ne'
  field_simp
  ring

/-! ### `lem:K1` -/

/-- **`lem:K1`** (`09_relay.tex:947-966`). Assume (SA), (Det), `1 ≤ k < n`, the clock defined up to
level `k+1`, and `h_k` defined on `[0, t♯_k]`. If `eq:relay` holds at `t̄♯_k` with
`Ξ_{k+1} = Ξ ≤ δ₀/(σ_b(μ-1))`, then `eq:Abar` holds; and for every `q_s` with
`|q_s| ≥ (15/16)2π|pout_*(G_{k+1})|δ₀` and `|A^in(T_pin)| ≥ |β_k||q_s|/(10|z|(μ-1))`:
`|c^in_k| ≥ c_Kε_kδ₀e^{x_kT_pin}/(|z|(μ-1))` and `2maj_k(t̄♯_k) ≤ ½K_1|c^in_k|`. -/
theorem K1_bound (S : Standing) (hS : S.Holds) (hDet : S.Det) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k < S.P.n) (hc : S.P.ClockUpTo (k + 1))
    (hdef : ∀ t ∈ Icc (0 : ℝ) (S.P.tsh k), S.P.HDefined k t) {Ξ : ℝ}
    (hrelay : S.maj k (S.P.tash k) ≤ S.relayBound k Ξ)
    (hΞ : Ξ ≤ S.P.δ₀ / (S.sigb * (S.P.μ - 1))) :
    S.maj k (S.P.tash k) ≤ 2 * S.CM * S.P.eps k * Real.exp (S.P.xk k * S.P.Tpin) *
        ((4 * S.C2 + 1) * S.P.δ₀ / (S.sigb * (S.P.μ - 1)) + CD S.P.Tpin) ∧
      2 * S.CM * S.P.eps k * Real.exp (S.P.xk k * S.P.Tpin) *
          ((4 * S.C2 + 1) * S.P.δ₀ / (S.sigb * (S.P.μ - 1)) + CD S.P.Tpin) ≤
        S.Abar * S.P.eps k ∧
      ∀ qs : ℂ, 15 / 16 * (2 * Real.pi * ‖Eig.pout S.P.χ (S.P.G (k + 1))‖ * S.P.δ₀) ≤ ‖qs‖ →
        ‖S.P.betaK k‖ * ‖qs‖ / (10 * ‖S.z‖ * (S.P.μ - 1)) ≤ ‖S.P.Ain k S.P.Tpin‖ →
        S.cK * S.P.eps k * S.P.δ₀ * Real.exp (S.P.xk k * S.P.Tpin) / (‖S.z‖ * (S.P.μ - 1)) ≤
            ‖S.P.cinK k‖ ∧
          2 * S.maj k (S.P.tash k) ≤ 1 / 2 * S.K1 * ‖S.P.cinK k‖ := by
  -- standing facts
  obtain ⟨hsb, hsbσ, hG, hlev⟩ := standing_levels S hS
  have hμ := hS.one_lt_μ
  have hδ := hS.δ₀_pos
  have hT := hS.Tpin_pos
  have hμ1 : 0 < S.P.μ - 1 := by linarith
  have hCM := K1_CM_pos S
  have hC2 := K1_one_le_C2 S
  have hCD := K1_CD_nonneg hT.le
  have he := hS.valid.eps_pos k
  set E := Real.exp (S.P.xk k * S.P.Tpin) with hE_def
  have hE : 0 < E := Real.exp_pos _
  set B := (4 * S.C2 + 1) * S.P.δ₀ / (S.sigb * (S.P.μ - 1)) + CD S.P.Tpin with hB_def
  have hB : 0 ≤ B := by
    have : 0 ≤ (4 * S.C2 + 1) * S.P.δ₀ / (S.sigb * (S.P.μ - 1)) := by
      apply div_nonneg _ (by positivity)
      exact mul_nonneg (by linarith) hδ.le
    linarith
  -- Step 1: the first inequality of `eq:Abar`
  have hstep1 : S.maj k (S.P.tash k) ≤ 2 * S.CM * S.P.eps k * E * B := by
    refine hrelay.trans ((S.relayBound_mono k hΞ (mul_nonneg hCM.le he.le)).trans (le_of_eq ?_))
    rw [Standing.relayBound_def, hB_def]
    ring
  refine ⟨hstep1, ?_, ?_⟩
  · -- Step 2: `x_k ≤ 17σ/16`, so `e^{x_kT_pin} ≤ e^{17σT_pin/16}`
    have hkmem : k ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.mpr ⟨hk, hkn.le⟩
    have hxk : S.P.xk k ≤ 17 / 16 * S.sigma0 := ((detuning S hS hDet).2.2 k hkmem).2.2.2.2.1
    have hexp : E ≤ Real.exp (17 * S.sigma0 * S.P.Tpin / 16) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_right hxk hT.le
      linarith
    have h0 : 0 ≤ 2 * S.CM * S.P.eps k * B := by positivity
    calc 2 * S.CM * S.P.eps k * E * B = 2 * S.CM * S.P.eps k * B * E := by ring
      _ ≤ 2 * S.CM * S.P.eps k * B * Real.exp (17 * S.sigma0 * S.P.Tpin / 16) :=
          mul_le_mul_of_nonneg_left hexp h0
      _ = S.Abar * S.P.eps k := by rw [Standing.Abar_def, hB_def]; ring
  · intro qs hq hA
    -- `|z| > 0` from `Re z = σ ≥ σ_b > 0`
    have hz : 0 < ‖S.z‖ := by
      have hre : S.z.re = S.sigma0 := rfl
      have := Complex.re_le_norm S.z
      linarith
    -- `c_N ≤ |β(G_k)||pout_*(G_{k+1})|`
    have hU := Eig.uniform_constants S.P.χ hS.admissible hS.hN
    have hk1mem : k + 1 ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.mpr ⟨by omega, hkn⟩
    have hkmem : k ∈ Finset.Icc 1 S.P.n := Finset.mem_Icc.mpr ⟨hk, hkn.le⟩
    have hGk := (hlev k hkmem).2.1
    have hGk1 := (hlev (k + 1) hk1mem).2.1
    have hβmin := hU.1
    have hpmin := hU.2.2.1
    have hcNpos : 0 < Eig.cN S.P.χ := hU.2.2.2.2.2.2.1
    have hβle : sInf ((fun G => ‖Eig.beta S.P.χ G‖) '' Icc 0 Gbar) ≤
        ‖Eig.beta S.P.χ (S.P.G k)‖ := hβmin.2 ⟨S.P.G k, hGk, rfl⟩
    have hple : sInf ((fun G => ‖Eig.pout S.P.χ G‖) '' Icc 0 Gbar) ≤
        ‖Eig.pout S.P.χ (S.P.G (k + 1))‖ := hpmin.2 ⟨S.P.G (k + 1), hGk1, rfl⟩
    have hβ0 : 0 ≤ sInf ((fun G => ‖Eig.beta S.P.χ G‖) '' Icc 0 Gbar) := by
      obtain ⟨G, -, hG'⟩ := hβmin.1
      rw [← hG']
      exact norm_nonneg _
    have hcN : Eig.cN S.P.χ ≤ ‖Eig.beta S.P.χ (S.P.G k)‖ * ‖Eig.pout S.P.χ (S.P.G (k + 1))‖ := by
      show sInf _ * sInf _ ≤ _
      exact mul_le_mul hβle hple (by
        obtain ⟨G, -, hG'⟩ := hpmin.1
        rw [← hG']
        exact norm_nonneg _) (hβ0.trans hβle)
    -- `|c^in_k| = e^{x_kT_pin}|A^in(T_pin)|`
    have hin : ∀ t ∈ Icc (0 : ℝ) (S.P.tsh k), S.P.HInDefined k t := fun t ht => (hdef t ht).1
    have hcpl := (Kick.coupling_two S.P hS.valid hS.hN hG hk hkn hc hin).2.2.2.2
    have hre := (Kick.kick_instance S.P hS.valid hS.hN hG hk hkn hc hin).2.1
    have hcin : ‖S.P.cinK k‖ = E * ‖S.P.Ain k S.P.Tpin‖ := by
      rw [hcpl, norm_mul, Complex.norm_exp, Complex.re_mul_ofReal, hre]
    -- the lower bound on `|c^in_k|`
    have hs5 : 0 < S.P.s k ^ 5 := pow_pos (hS.valid.s_pos k) 5
    have hlow : S.cK * S.P.eps k * S.P.δ₀ * E / (‖S.z‖ * (S.P.μ - 1)) ≤ ‖S.P.cinK k‖ := by
      rw [Standing.cK_def, Approx.eps_def]
      rw [K1_norm_betaK S.P hS.valid k] at hA
      exact K1_cin_lower (norm_nonneg _) hcN hs5 hμ hδ hE hz hq hA hcin
    refine ⟨hlow, ?_⟩
    -- Step 4: multiply by `½K_1`
    have hcK : 0 < S.cK := by
      rw [Standing.cK_def]
      have : 0 < S.P.μ := by linarith
      positivity
    have hK1 : 0 ≤ S.K1 := by
      rw [Standing.K1_def]
      have : 0 ≤ (4 * S.C2 + 1) / S.sigb := div_nonneg (by linarith) hsb.le
      have : 0 ≤ CD S.P.Tpin * (S.P.μ - 1) / S.P.δ₀ := by positivity
      positivity
    calc 2 * S.maj k (S.P.tash k) ≤ 2 * (2 * S.CM * S.P.eps k * E * B) := by linarith
      _ = 1 / 2 * S.K1 * (S.cK * S.P.eps k * S.P.δ₀ * E / (‖S.z‖ * (S.P.μ - 1))) := by
          rw [Standing.K1_def, hB_def]
          exact (K1_identity hz hcK hsb hμ hδ).symm
      _ ≤ 1 / 2 * S.K1 * ‖S.P.cinK k‖ :=
          mul_le_mul_of_nonneg_left hlow (by positivity)

end Relay

end NonUniqueEuler
